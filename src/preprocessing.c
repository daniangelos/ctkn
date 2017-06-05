#include <stdio.h>
#include <pthread.h>
#include "uthash.h"
#include "tree.h"
#include "prover.h"
#include "symbol_table.h"
#include "clauses.h"

#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))

extern int mle;
extern int ml_ple;
extern int ple;
extern int unit;
extern int ml_prover;
extern int populate_usable;
extern int gen2;
extern int propagate_dia;

extern int modal_positive;
extern int modal_negative;
extern int strong_modal_positive;
extern int strong_modal_negative;
extern int numclause;
extern int numfsubsumed;
extern int numbsubsumed;
extern int nummle;
extern int numple;
extern int nummlple;
extern int numtautologies;

extern int numproofs;
extern int maxproof;


extern hml_pclauses *i_usable;
extern hml_pclauses *i_sos;
extern hml_pclauses *l_usable;
extern hml_pclauses *l_sos;

extern hml_mclauses *m_usable;
extern hml_mclauses *m_sos;

extern pthread_mutex_t mutexallclauses;

extern int size_clause (literalslist *l);
extern int max_lit_clause (literalslist *l);
extern int classify_clause (literalslist *l);
extern tclause *get_clause (int clause);

extern struct prop_node *propsid;

extern void insert_clause_set (tclause **clause, int type, int set);
extern void insert_clause_deleted(tclause *clause);
extern clauseslist *delete_clause_list(tclause *c, clauseslist *l);
extern void delete_clause_prop (hml_pclauses **set,tclause *c);
extern void delete_clause_modal (hml_mclauses **set, tclause *c);
extern void move_clause_propositional(tclause *c, hml_pclauses **set_out, hml_pclauses **set_in);
extern void self_subsumption (void);
extern void do_mres (hml_mclauses *set);
extern void do_gen2 (hml_mclauses *set);
extern void print_out (char *);
extern clauseslist *delete_clause_list(tclause *c, clauseslist *l);
extern void delete_clause_all(int number);
extern void propagate_unique_dia_ml (void);

extern int unit_resolution (hml_pclauses **set);

void populate(void) {
  hml_pclauses *aux, *auxhml;
  hmaxclauses *hmc, *hmcaux;
  hsizeclauses *hsc, *hscaux;

  HASH_ITER(hml,l_sos,aux,auxhml) {
    HASH_ITER(hmax,aux->max,hmc,hmcaux) {
	if ((populate_usable == MAX_LIT_NEGATIVE && hmc->max < 0) ||
	    (populate_usable == MAX_LIT_POSITIVE && hmc->max > 0) ||
	    (populate_usable == NON_NEGATIVE) ||
	    (populate_usable == NON_POSITIVE) ||
	    (populate_usable == NEGATIVE && hmc->max < 0) ||
	    (populate_usable == POSITIVE && hmc->max > 0)) {
	  HASH_ITER(hsize,hmc->size,hsc,hscaux) {
	    clauseslist *l = hsc->list;
	    while (l != NULL) {
	      tclause *clause = get_clause(l->clause);
	      l = l->next;
	      if (((populate_usable == NON_NEGATIVE) && (clause->class != NEGATIVEC)) ||
		  ((populate_usable == NON_POSITIVE) && (clause->class != POSITIVEC)) ||
		  ((populate_usable == NEGATIVE) && (clause->class == NEGATIVEC)) ||
		  ((populate_usable == POSITIVE) && (clause->class == POSITIVEC)) ||
		  (populate_usable == MAX_LIT_NEGATIVE) ||
		  (populate_usable == MAX_LIT_POSITIVE))
		{
		  move_clause_propositional(clause,&l_sos,&l_usable);
		}
	    }
	  }
	}
    }
  }
}


void delete_clause(tclause *clause) {
  if (clause != NULL) {
    if (clause->type == INITIAL) {
      delete_clause_prop(&i_usable,clause);
      delete_clause_prop(&i_sos,clause);
    }
    else if (clause->type == LITERAL) {
      delete_clause_prop(&l_usable,clause);
      delete_clause_prop(&l_sos,clause);
    }
    else {
      delete_clause_modal(&m_usable,clause);
      delete_clause_modal(&m_sos,clause);
    }
  }
}


tclause *create_new_modal_clause(tclause *clause, int prop, int rule) {

  int left;
  literalslist *right = malloc(sizeof(literalslist));
  
  if (prop == -clause->left)
    left = CFALSE;
  else left = clause->left;

  if (prop == clause->right->literal)
    right->literal = CTRUE;
  else right->literal = clause->right->literal;
  right->next = NULL;  

  clauseslist *parents = malloc(sizeof(clauseslist));
  parents->clause = clause->number;
  parents->next = NULL;
  literalslist *literals = malloc(sizeof(literal_list));
  literals->literal = prop;
  literals->next = NULL;
  justification *just = malloc(sizeof(justification));
  just->rule = rule;
  just->parents = parents;
  just->literals = literals;

  tclause *new = malloc(sizeof(tclause));
  new->number = numclause++;
  new->type = clause->type;
  new->modal_level = clause->modal_level;
  new->agent = clause->agent;
  new->propagated = 0;
  new->left = left;
  new->right = right;
  new->just = just;
  new->deleted = NULL;
  new->size = size_clause(right);
  new->max_literal = max_lit_clause(right);
  new->class = classify_clause(new->right);
  
  insert_clause_set(&new,new->type,SOS);

  clauseslist *parent = malloc(sizeof(clauseslist));
  parent->clause = new->number;
  parent->next = NULL;
  justification *deleted = malloc(sizeof(justification));
  deleted->rule = BACKSUBSUMED;
  deleted->parents = parent;
  deleted->literals = NULL;
  clause->deleted = deleted;
  numbsubsumed +=1;
  
  return clause;
}


void modal_level_ple (void) {
  prop_node *p;
  int try_ple = 1;
  int id = 0;
  while (numproofs < maxproof && try_ple) {
    try_ple = 0;
    for (p = propsid; p != NULL; p = p->hid.next) {
      hml_clauses *positive = p->positive;
      id = p->id;
      while (positive != NULL) {
	hml_clauses *negative;
	HASH_FIND(hml,p->negative,&(positive->ml),sizeof(int),negative);
	clausesid *clauses = positive->clauses;
	positive = positive->hml.next;
	if (negative == NULL) {
	  while (clauses != NULL) {
	    tclause *clause = get_clause(clauses->id);
	    clauses = clauses->hid.next;
	    if (clause != NULL) {
	      try_ple = 1;
	      if (clause->type == MPOSITIVE || clause->type == MNEGATIVE)
		clause = create_new_modal_clause(clause,id,MLPLE);
	      else {
		literalslist *literals = malloc(sizeof(literal_list));
		literals->literal = id;
		literals->next = NULL;
		justification *deleted = malloc(sizeof(justification));
		deleted->rule = MLPLE;
		deleted->parents = NULL;
		deleted->literals = literals;
		clause->deleted = deleted;
		nummlple++;
	      }
	    delete_clause(clause);
	    insert_clause_deleted(clause);
	    }
	  }
	}
      }
    }

    for (p = propsid; p != NULL; p = p->hid.next) {
      hml_clauses *negative = p->negative;
      id = -p->id;
      while (negative != NULL) {
	hml_clauses *positive;
	HASH_FIND(hml,p->positive,&(negative->ml),sizeof(int),positive);
	clausesid *clauses = negative->clauses;
	negative = negative->hml.next;
	if (positive == NULL) {
	  while (clauses != NULL) {
	    tclause *clause = get_clause(clauses->id);
	    clauses = clauses->hid.next;
	    if (clause != NULL) {
	      try_ple = 1;
	      if (clause->type == MPOSITIVE || clause->type == MNEGATIVE)
		clause = create_new_modal_clause(clause,id,MLPLE);
	      else {
		literalslist *literals = malloc(sizeof(literal_list));
		literals->literal = id;
		literals->next = NULL;
		justification *deleted = malloc(sizeof(justification));
		deleted->rule = MLPLE;
		deleted->parents = NULL;
		deleted->literals = literals;
		clause->deleted = deleted;
		nummlple++;
	      }
	    delete_clause(clause);
	    insert_clause_deleted(clause);
	    }
	  }
	}
      }
    }
  }
}

void pure_literal_elimination (void) {
  prop_node *p;
  int try_ple = 1;

  while (numproofs < maxproof && try_ple) {
    try_ple = 0;

    for (p = propsid; p != NULL; p = p->hid.next) {
      if ((p->occur_positive == 0 && p->occur_negative != 0) ||
	  (p->occur_positive != 0 && p->occur_negative == 0)) {
	try_ple = 1;
	int id;
	hml_clauses *aux;
	if (p->occur_negative) {
	  id = -p->id;
	  aux = p->negative;
	}
	else {
	  id = p->id;
	  aux = p->positive;
	}
	while (aux != NULL) {
	  clausesid *clauses = aux->clauses;
	  aux = aux->hml.next;
	  while (clauses != NULL) {
	    tclause *clause = get_clause(clauses->id);
	    clauses = clauses->hid.next;
	    if (clause != NULL) {
	      if (clause->type == MPOSITIVE || clause->type == MNEGATIVE)
		clause = create_new_modal_clause(clause,id,PLE);
	      else {
		literalslist *literals = malloc(sizeof(literal_list));
		literals->literal = id;
		literals->next = NULL;
		justification *deleted = malloc(sizeof(justification));
		deleted->rule = PLE;
		deleted->parents = NULL;
		deleted->literals = literals;
		clause->deleted = deleted;
		numple++;
	      }
	      delete_clause(clause);
	      insert_clause_deleted(clause);
	    }
	  }
	}
      }
    }
  }
}


int modal_level_elimination (void) {

  int try = 0;
  int internal_try = 1;
  
  hml_mclauses *aux = NULL, *auxtmp = NULL;
  hagentclauses *hag = NULL, * hagtmp = NULL;
  htypeclauses *htc = NULL, *htctmp = NULL;
  hmaxlitclauses *hmaxlit = NULL, *hmaxlittmp = NULL;

  while (internal_try) {
    internal_try = 0;
    HASH_ITER(hml,m_sos,aux,auxtmp) {
      HASH_ITER(hid,aux->id,hag,hagtmp) {
	htypeclauses *htcneg = NULL;
	htypeclauses *htcpos = NULL;
	if (hag->type->type == MPOSITIVE) {
	  htcneg = hag->type->htype.next;
	  htcpos = hag->type;
	}
	else {
	  htcneg = hag->type;
	  htcpos = hag->type->htype.next;
	}
	if (htcneg == NULL) {
	  //	  printf("\n Deleting");
	  try = 1;
	  internal_try = 1;

	  HASH_ITER(htype,htcpos,htc,htctmp) {
	    HASH_ITER(hmax,htc->lit,hmaxlit,hmaxlittmp) {
	      while (hmaxlit->list != NULL) {
		tclause *c  = get_clause(hmaxlit->list->clause);
		justification *deleted = malloc(sizeof(justification));
		deleted->rule = MLE;
		deleted->parents = NULL;
		deleted->literals = NULL;
		c->deleted = deleted;
		hmaxlit->list = delete_clause_list(c,hmaxlit->list);
		pthread_mutex_lock (&mutexallclauses);
		delete_clause_all(c->number);
		pthread_mutex_unlock (&mutexallclauses);
		insert_clause_deleted(c);
		nummle++;
	      }
	      HASH_DELETE(hmax,htc->lit,hmaxlit);
	      free(hmaxlit);
	      hmaxlit = NULL;
	    }
	    HASH_DELETE(htype,hag->type,htc);
	    free(htc);
	    htc = NULL;
	  }
	}
	if (hag->type == NULL) {
	  HASH_DELETE(hid,aux->id,hag);
	  free(hag);
	  hag = NULL;
	}
      }
      if (aux->id == NULL) {
	HASH_DELETE(hml,m_sos,aux);
	free(aux);
	aux = NULL;
      }
    }
  }
  return try;
}


void preprocessing (void) {

  int try = 1;
  while (numproofs < maxproof && try) {
    try = 0;
    if (propagate_dia == ON)
      propagate_unique_dia_ml();
    
    if (numproofs < maxproof && mle == ON) {
      try = modal_level_elimination();
    }
    if (numproofs < maxproof && ple == ON) {
      pure_literal_elimination();
      print_out("PLE");
    }
    if (numproofs < maxproof && ml_ple == ON) {
      modal_level_ple();
      print_out("ML_PLE");
    }
    if (l_sos != NULL && numproofs < maxproof && unit == ON) {
      int try2 = unit_resolution(&l_sos);
      try = MAX(try,try2);
      print_out("Unit Resolution");
    }
  }

  do_mres(m_sos);
  print_out("MRES");

  if (gen2 | (!modal_negative && !modal_positive && !strong_modal_positive &&!strong_modal_negative)) {
    do_gen2(m_sos);
    print_out("GEN2");
  }
  self_subsumption();
  print_out("Self Subsumption");

  if (populate_usable) {
    populate();
    print_out("Populated Usable");
  }
  print_out("Pre-processing");
}
