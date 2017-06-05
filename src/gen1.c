#include <stdio.h>
#include <pthread.h>
#include "prover.h"
#include "symbol_table.h"
#include "clauses.h"

typedef struct listsclauseslist {
  clauseslist *clauses;
  struct listsclauseslist *next;
} listsclauseslist;

extern void insert_clause_set (tclause **clause, int type, int set);
extern int size_clause (literalslist *l);
extern int max_lit_clause (literalslist *l);
extern int classify_clause (literalslist *l);
extern tclause *get_clause (int clause);
extern literalslist *simplify_clause(literalslist *l);
extern clauseslist *build_modal_candidates(hml_mclauses *set,int agent,int modal_level,int type, int literal);
extern listsclauseslist *build_resolvents_gen (listsclauseslist *candidates);
extern clauseslist *delete_clauses_list (clauseslist *l);

extern void print_candidates(listsclauseslist *aux);

extern int ml_prover;
extern int numagents;
extern int numclause;

extern hml_mclauses *m_sos;
extern pthread_mutex_t mutexnumclause;

listsclauseslist *check_resolvents_gen1(tclause *chosen, listsclauseslist *resolvents) {
  listsclauseslist *first = NULL;
  while (resolvents != NULL) {    
    clauseslist *aux = resolvents->clauses;
    int sizeclause = 0;
    int negative = 0;
    while (aux != NULL) {
      tclause *clause = get_clause(aux->clause);
      if (clause->type == MNEGATIVE)
	negative++;
      sizeclause++;
      aux = aux->next;
    }
    if (sizeclause == chosen->size && negative == 1) { // It must be the same size as chosen (note this was not simplified yet); it must have just one negative clause
      listsclauseslist *new = malloc(sizeof(listsclauseslist));
      new->clauses = resolvents->clauses;
      new->next = first;
      first = new;
    }
    else delete_clauses_list(resolvents->clauses);
    
    listsclauseslist *auxres = resolvents;
    resolvents = resolvents->next;
    free(auxres);
  }
  return first;
}

void try_gen1(tclause *chosen, listsclauseslist *negative, listsclauseslist *positive) {

  while (negative != NULL) {

    listsclauseslist *candidates = malloc(sizeof(listsclauseslist));
    candidates->clauses = negative->clauses;
    candidates->next = NULL;

    tclause *c1 = get_clause(candidates->clauses->clause);

    listsclauseslist *aux = positive;
    
    while (aux != NULL) {
      tclause *c2 = get_clause(aux->clauses->clause);
      
      if (c2->max_literal != c1->max_literal) {
	listsclauseslist *new = malloc(sizeof(listsclauseslist));
	new->clauses = aux->clauses;
	new->next = candidates;
	candidates = new;
      }
      aux=aux->next;
    }
    
    listsclauseslist *resolvents = build_resolvents_gen(candidates);      

    aux = candidates;
    while (aux != NULL) {
      aux = aux->next;
      free(candidates);
      candidates = aux;
    }
      
    resolvents = check_resolvents_gen1(chosen,resolvents);
  
    while (resolvents != NULL) {
      tclause *resolvent = malloc(sizeof(tclause));

      justification *just = malloc(sizeof(justification));
      just->rule = GEN1;
      clauseslist *parents = malloc(sizeof(clauseslist));
      parents->clause = chosen->number;
      parents->next = NULL;
      literalslist *literals = NULL; // not including the literals from the literal clause in the justification
      literalslist *right = NULL;

      clauseslist *auxres = resolvents->clauses;

      while (auxres != NULL) {
	tclause *pos = get_clause(auxres->clause);
	clauseslist *newparent = malloc(sizeof(clauseslist));
	newparent->clause = pos->number;
	newparent->next = parents;
	parents = newparent;
	literalslist *newliteral = malloc(sizeof(literalslist));
	newliteral->literal = pos->right->literal;
	newliteral->next = literals;
	literals = newliteral;
	literalslist *newright = malloc(sizeof(literalslist));
	newright->literal = -pos->left;
	newright->next = right;
	right = newright;
	auxres = auxres->next;
      }
      if (right == NULL) {
	right = malloc(sizeof(literalslist));
	right->literal = CFALSE;
	right->next = NULL;
	resolvent->right = right;
      }
      else resolvent->right = simplify_clause(right);
      just->parents = parents;
      just->literals = literals;
      resolvent->deleted = NULL;
      resolvent->just = just;
	
      pthread_mutex_lock (&mutexnumclause);
      resolvent->number = numclause++;
      pthread_mutex_unlock (&mutexnumclause);
      
      resolvent->type = LITERAL;
      resolvent->agent = 0;
      if (!ml_prover)
	resolvent->modal_level = 1;
      else resolvent->modal_level = chosen->modal_level - 1;
      resolvent->left = CTRUE;
      resolvent->size = size_clause(resolvent->right);
      resolvent->max_literal = max_lit_clause(resolvent->right);
      resolvent->class = classify_clause(resolvent->right);

      insert_clause_set(&resolvent,resolvent->type,SOS);
      
      listsclauseslist *tmpres = resolvents;
      delete_clauses_list(tmpres->clauses);
      resolvents = resolvents->next;
      free(tmpres);
    }
    negative = negative->next;
  }
}


void do_gen1(int clause) {
  tclause *chosen = get_clause(clause);
  if (chosen != NULL) {
    literalslist *aux;
    listsclauseslist *first_neg = NULL;
    listsclauseslist *first_pos = NULL;
    int agent;
    int modal_level;

    if (!ml_prover)
      modal_level = 1;
    else modal_level = chosen->modal_level - 1;
  
    for (agent = 1; agent < numagents; agent++) {
      aux = chosen->right;
      while (aux != NULL) {
	clauseslist *negcandidates = build_modal_candidates(m_sos,agent,modal_level,MNEGATIVE,-aux->literal);
	if (negcandidates != NULL) {
	  listsclauseslist *newneg = malloc(sizeof(listsclauseslist));
	  newneg->clauses = negcandidates;
	  newneg->next = first_neg;
	  first_neg = newneg;
	}
	aux = aux->next;
      }

      int size = 0;
    
      if (first_neg != NULL) {
	aux = chosen->right;
	while (aux != NULL) {
	  clauseslist *poscandidates = build_modal_candidates(m_sos,agent,modal_level,MPOSITIVE,-aux->literal);
	  if (poscandidates != NULL) {
	    size++;
	    listsclauseslist *newpos = malloc(sizeof(listsclauseslist));
	    newpos->clauses = poscandidates;
	    newpos->next = first_pos;
	    first_pos = newpos;
	  }
	  aux = aux->next;	
	}

	if (size >= chosen->size - 1) {
	  try_gen1(chosen,first_neg,first_pos);
	}
      }

      listsclauseslist *aux = first_neg;
      while (aux != NULL) {
	aux = aux->next;
	free(first_neg);
	first_neg = aux;
      }
      aux = first_pos;
      while (aux != NULL) {
	aux = aux->next;
	free(first_pos);
	first_pos = aux;
      }  
      first_neg = NULL;
      first_pos = NULL;
    }
  }
}

