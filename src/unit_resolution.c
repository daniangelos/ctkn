#include <pthread.h>
#include "prover.h"
#include "symbol_table.h"
#include "clauses.h"

#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))

extern prop_node *find_prop (int id);
extern tclause *get_clause (int clause);
extern void insert_clause_set (tclause **clause, int type, int set);
extern int max_lit_clause (literalslist *l);
extern int classify_clause (literalslist *l);
extern void delete_clause (tclause *clause);
extern void insert_clause_deleted (tclause *clause);

extern literalslist *simplify_clause (literalslist *l);
extern int size_clause (literalslist *l);
extern clauseslist *build_modal_negative (hml_mclauses *set,int agent,int modal_level);
extern int check_repeated_prop (tclause *clause, hml_pclauses *set);

extern void move_clause_modal (tclause *c, hml_mclauses **set_out, hml_mclauses **set_in);
extern void move_clause_propositional (tclause *c, hml_pclauses **set_out, hml_pclauses **set_in);

extern void propagate_unique_dia_ml (void);
extern void propagate_unique_box_ml (void);

extern pthread_mutex_t mutexprops;
extern pthread_mutex_t mutexnumfsubsumed;
extern pthread_mutex_t mutexallclauses;
extern pthread_mutex_t mutexdeletedclauses;

extern hml_pclauses *l_sos;
extern hml_pclauses *l_usable;
extern hml_pclauses *i_sos;
extern hml_pclauses *i_usable;
extern hml_mclauses *m_sos;
extern hml_mclauses *m_usable;

extern int ml_prover;

extern int numclause;
extern int numfsubsumed;
extern int numbsubsumed;
extern int numtautologies;
extern int numproofs;
extern int maxproof;
extern int lhs_unit;
extern int propagate_box;
extern int propagate_dia;

int unit_gen = 0;

int resolve_unit_gen3(tclause *c1, tclause *c2) {
  int try = 0;

  if (c2->type == MPOSITIVE && c2->right->literal == -c1->right->literal) { // special case of GEN3
    clauseslist *candidates = build_modal_negative(m_sos,c2->agent,c2->modal_level);

    while (candidates != NULL) {
      try = 1;
      tclause *clause = get_clause(candidates->clause);

      tclause *resolvent = malloc(sizeof(tclause));
      resolvent->number = numclause++;
      resolvent->left = CTRUE;
      resolvent->type = LITERAL;
      resolvent->agent = 0;
	
      if (!ml_prover)
	resolvent->modal_level = 1;
      else resolvent->modal_level = c2->modal_level;
      
      resolvent->right = malloc(sizeof(literalslist));
      resolvent->right->literal = -clause->left;
      resolvent->right->next = malloc(sizeof(literalslist));
      resolvent->right->next->literal = -c2->left;
      resolvent->right->next->next = NULL;
      resolvent->right = simplify_clause(resolvent->right);

      clauseslist *parent = malloc(sizeof(clauseslist));
      parent->clause = clause->number;
      parent->next = malloc(sizeof(clauseslist));
      parent->next->clause = c2->number;
      parent->next->next = malloc(sizeof(clauseslist));
      parent->next->next->clause = c1->number;
      parent->next->next->next = NULL;
      
      literalslist *literals = malloc(sizeof(literalslist));
      literals->literal = clause->right->literal;
      literals->next = malloc(sizeof(literalslist));
      literals->next->literal = c2->right->literal;
      literals->next->next = NULL;
      
      justification *just = malloc(sizeof(justification));
      just->rule = UNITGEN3;
      just->parents = parent;
      just->literals = literals;
      resolvent->just = just;
      resolvent->deleted = NULL;

      resolvent->size = size_clause(resolvent->right);
      resolvent->max_literal =  max_lit_clause(resolvent->right);
      resolvent->class = classify_clause(resolvent->right);
      
      insert_clause_set(&resolvent,resolvent->type,SOS);
      
      clauseslist *aux = candidates;
      candidates = candidates->next;
      free(aux);
      unit_gen = 1;
    }      

    numbsubsumed += 1;
    clauseslist *parent2 = malloc(sizeof(clauseslist));
    parent2->clause = c1->number;
    parent2->next = NULL;
    justification *deleted = malloc(sizeof(justification));
    deleted->rule = BACKSUBSUMED;
    deleted->parents = parent2;
    deleted->literals = NULL;
    c2->deleted = deleted;
    delete_clause(c2);
    insert_clause_deleted(c2);

  }
  
  return try;
}

tclause *resolve_unit(tclause *c1, tclause *c2) {
  // c1 is always propositional clause and size one

  if (c2->type == INITIAL || c2->type == LITERAL) {
    literalslist *literals = c2->right;
    while (literals != NULL && literals->literal != -c1->right->literal) {
      literals = literals->next;
    }
    if (literals == NULL) // false positive
      return NULL;
    else {
      tclause *resolvent = malloc(sizeof(tclause));
      resolvent->number = numclause++;

      if (c2->type == INITIAL || c1->type == INITIAL) {
	resolvent->left = CSTART;
	resolvent->type = INITIAL;
      }
      else {
	resolvent->left = CTRUE;
	resolvent->type = LITERAL;
      }

      resolvent->modal_level = c2->modal_level;
      resolvent->agent = 0;
      resolvent->size = c2->size - 1;
      literalslist *aux = c2->right;
      literalslist *first = NULL;

      while (aux != NULL) {
	if (aux != literals){
	  literalslist *new = malloc(sizeof(literalslist));
	  new->literal = aux->literal;
	  new->next = first;
	  first = new;
	}
	aux = aux->next;
      }
      if (first == NULL) {
	literalslist *dis = malloc(sizeof(literalslist));
	dis->literal = CFALSE;
	dis->next = NULL;
	resolvent->right = dis;
      }
      else {
	resolvent->right = first;
      }

      resolvent->right = simplify_clause(resolvent->right);
      resolvent->max_literal = max_lit_clause(resolvent->right);
      resolvent->class = classify_clause(resolvent->right);
      return resolvent; 
    }
  }
  else if (c2->type == MNEGATIVE && c2->right->literal == -c1->right->literal && c1->type == LITERAL) { // special case of GEN1

    tclause *resolvent = malloc(sizeof(tclause));
    resolvent->number = numclause++;
    resolvent->size = 1;
    resolvent->type = LITERAL;
    resolvent->left = CTRUE;
    resolvent->agent = 0;
    resolvent->propagated = 0;
    
    if (!ml_prover)
      resolvent->modal_level = 1;
    else resolvent->modal_level = c2->modal_level;
    resolvent->right = malloc(sizeof(literalslist));
    resolvent->right->literal = -c2->left;
    resolvent->right->next = NULL;
    
    resolvent->size = 1;
    resolvent->max_literal =  max_lit_clause(resolvent->right);
    resolvent->class = classify_clause(resolvent->right);
    return resolvent;
  }
  return NULL;
}

int try_unit (int clausenumber) {
  int try = 0;
  hml_clauses *clauses;
  clausesid *candidates = NULL;
  prop_node *p;
  tclause *aux = get_clause(clausenumber);
  if (aux != NULL) {
    int id = aux->right->literal;
    if (id != CTRUE || id != CFALSE)
      {
	if (id < 0) {
	  id = -id;
	  p = find_prop(id);
	  HASH_FIND(hml,p->positive,&(aux->modal_level),sizeof(int),clauses);
	  if (clauses != NULL)
	    candidates = clauses->clauses;
	}
	else {
	  p = find_prop(id);
	  HASH_FIND(hml,p->negative,&(aux->modal_level),sizeof(int),clauses);
	  if (clauses != NULL)
	    candidates = clauses->clauses;
	}
	while (candidates != NULL) {
	  tclause *newclause = get_clause(candidates->id);
	  candidates = candidates->hid.next;
	  if ((newclause->modal_level == aux->modal_level &&
	       (!ml_prover || newclause->type == LITERAL || newclause->type == INITIAL)) ||
	      (ml_prover && newclause->modal_level == aux->modal_level - 1 &&
	       (newclause->type == MPOSITIVE || newclause->type == MNEGATIVE))) {
	    if (newclause->deleted == NULL && newclause->number != clausenumber) {
	      if (newclause->type == MPOSITIVE) {
		try = resolve_unit_gen3(aux,newclause);
	      }
	      else {
		tclause *resolvent = resolve_unit(aux,newclause);
		if (resolvent != NULL) {
		  try = 1;
		  clauseslist *parent = malloc(sizeof(clauseslist));
		  parent->clause = aux->number;
		  parent->next = malloc(sizeof(clauseslist));
		  parent->next->clause = newclause->number;
		  parent->next->next = NULL;
		  literalslist *literals = malloc(sizeof(literalslist));
		  literals->literal = p->id;
		  literals->next = NULL;
		  parent->next->next = NULL;
		  justification *just = malloc(sizeof(justification));
		  if (newclause->type == MNEGATIVE) {
		    just->rule = UNITGEN1;
		    unit_gen = 1;
		  }
		  else
		    just->rule = UNIT;
		  just->parents = parent;
		  just->literals = literals;
		  resolvent->just = just;
		  resolvent->deleted = NULL;
		  insert_clause_set(&resolvent,resolvent->type,SOS);

		  if (just->rule == UNITGEN1 || resolvent->type == newclause->type) { // if resolvent has a different type, then the parent is not subsumed
		    numbsubsumed += 1;
		    clauseslist *parent2 = malloc(sizeof(clauseslist));
		    parent2->clause = resolvent->number;
		    parent2->next = NULL;
		    justification *deleted = malloc(sizeof(justification));
		    deleted->rule = BACKSUBSUMED;
		    deleted->parents = parent2;
		    deleted->literals = NULL;
		    newclause->deleted = deleted;
		    delete_clause(newclause);
		    insert_clause_deleted(newclause);
		  }
		}
	      }
	    }
	  }

	  if (lhs_unit &&
	      newclause->deleted == NULL &&
	      newclause->modal_level == aux->modal_level &&
	      (newclause->type == MPOSITIVE || newclause->type == MNEGATIVE) &&
	      (newclause->left == aux->right->literal)) {

	    try = 1;
	    
	    tclause *resolvent = malloc(sizeof(tclause));
	    resolvent->number = numclause++;
	    resolvent->left = CTRUE;
	    resolvent->type = newclause->type;
	    resolvent->agent = newclause->agent;
	
	    if (!ml_prover)
	      resolvent->modal_level = 1;
	    else resolvent->modal_level = newclause->modal_level;
      
	    resolvent->right = malloc(sizeof(literalslist));
	    resolvent->right->literal = newclause->right->literal;
	    resolvent->right->next = NULL;

	    clauseslist *parent = malloc(sizeof(clauseslist));
	    parent->clause = aux->number;
	    parent->next = malloc(sizeof(clauseslist));
	    parent->next->clause = newclause->number;
	    parent->next->next = NULL;

	    literalslist *literals = malloc(sizeof(literalslist));
	    literals->literal = aux->right->literal;
	    literals->next = NULL;
      
	    justification *just = malloc(sizeof(justification));
	    just->rule = LHSUNIT;
	    just->parents = parent;
	    just->literals = literals;
	    resolvent->just = just;
	    resolvent->deleted = NULL;

	    resolvent->size = size_clause(resolvent->right);
	    resolvent->max_literal =  max_lit_clause(resolvent->right);
	    resolvent->class = classify_clause(resolvent->right);
      
	    insert_clause_set(&resolvent,resolvent->type,SOS);

	    numbsubsumed += 1;
	    clauseslist *parent2 = malloc(sizeof(clauseslist));
	    parent2->clause = resolvent->number;
	    parent2->next = NULL;
	    justification *deleted = malloc(sizeof(justification));
	    deleted->rule = BACKSUBSUMED;
	    deleted->parents = parent2;
	    deleted->literals = NULL;
	    newclause->deleted = deleted;
	    delete_clause(newclause);
	    insert_clause_deleted(newclause);
	  }	   
	}
      }
  }
  return try;
}

clauseslist *build_unit_candidates (clauseslist *initial, clauseslist *add) {
  clauseslist *first = NULL;
  clauseslist *aux = initial;

  while (aux != NULL) {
    clauseslist *new = malloc(sizeof(clauseslist));
    new->clause = aux->clause;
    new->next = first;
    first = new;
    aux = aux->next;
  }

  aux = add;
  while (aux != NULL) {
    clauseslist *new = malloc(sizeof(clauseslist));
    new->clause = aux->clause;
    new->next = first;
    first = new;
    aux = aux->next;
  }
  
  return first;
}

int unit_resolution (hml_pclauses **set) {

  hml_pclauses *hmlp = NULL;
  hmaxclauses *hmc = NULL;
  hsizeclauses *hsc = NULL;

  int try = 0;
  int sizeone = 1;
  clauseslist *candidates = NULL;
  
  hmlp = *set;

  pthread_mutex_lock(&mutexprops);
  for (hmlp = *set; hmlp != NULL; hmlp = hmlp->hml.next)
    for (hmc=hmlp->max; hmc != NULL; hmc = hmc->hmax.next) {
      HASH_FIND(hsize,hmc->size,&(sizeone),sizeof(int),hsc);
      if (hsc != NULL)
	candidates = build_unit_candidates(candidates,hsc->list);
    }
  pthread_mutex_unlock(&mutexprops);
  
  while (numproofs < maxproof && candidates != NULL) {

    tclause *c = get_clause(candidates->clause);

    if (c != NULL) {
      int repeated = 0;

      if (c->type == LITERAL) 
	repeated = check_repeated_prop(c, l_usable);
      else if (c->type == INITIAL)
	repeated = check_repeated_prop(c, i_usable);

      if (!repeated) {
	int new_try = try_unit(candidates->clause);
	try = MAX(try,new_try);
      
	if (c != NULL) {
	  if (c->type == LITERAL)
	    move_clause_propositional(c,&l_sos,&l_usable);
	  else
	    move_clause_propositional(c,&i_sos,&i_usable);
	}
      }
      else {
	pthread_mutex_lock (&mutexnumfsubsumed);
	numfsubsumed += 1;
	pthread_mutex_unlock (&mutexnumfsubsumed);
	clauseslist *parent = malloc(sizeof(clauseslist));
	parent->clause = repeated;
	parent->next = NULL;
	justification *deleted = malloc(sizeof(justification));
	deleted->rule = REPEATED;
	deleted->parents = parent;
	deleted->literals = NULL;
	c->deleted = deleted;
	delete_clause(c);
	pthread_mutex_lock (&mutexdeletedclauses);
	insert_clause_deleted(c);
	pthread_mutex_unlock (&mutexdeletedclauses);
      }
    }
    clauseslist *aux = candidates;
    candidates = candidates->next;
    free(aux);
  }

  if (unit_gen) {
    if (propagate_dia)
      propagate_unique_dia_ml();
    if (propagate_box)
      propagate_unique_box_ml();
    unit_gen = 0;
  }
     
  return try;
}
