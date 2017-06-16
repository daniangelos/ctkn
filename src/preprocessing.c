#include <stdio.h>
#include <pthread.h>
#include <string.h>
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

extern struct agent_node *agentsid;
extern struct prop_node *propsid;

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
extern literalslist *simplify_clause (literalslist *l);
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
extern void delete_clause_all(int number);
extern void propagate_unique_dia_ml (void);

extern int unit_resolution (hml_pclauses **set);
extern prop_node *insert_pos_node (char *name);



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
	      tclause *clause = get_clause(l->clause_number);
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
  parents->clause_number = clause->number;
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
  new->subtype = clause->subtype;
  new->numdiamond = clause->numdiamond;
  new->modal_level = clause->modal_level;
  new->agent = clause->agent;
  new->propagated = 0;
  new->left = left;
  new->right = right;
  new->just = just;
  new->deleted = NULL;
  new->size = size_clause(right);
  new->max_literal = max_lit_clause(right);
  new->min_literal = right->literal;
  new->class = classify_clause(new->right);
  
  insert_clause_set(&new,new->type,SOS);

  clauseslist *parent = malloc(sizeof(clauseslist));
  parent->clause_number = new->number;
  parent->next = NULL;
  justification *deleted = malloc(sizeof(justification));
  deleted->rule = BACKSUBSUMED;
  deleted->parents = parent;
  deleted->literals = NULL;
  clause->deleted = deleted;
  numbsubsumed +=1;
  
  return clause;
}


/*int modal_level_ple (void) {
  prop_node *p;
  int try_ple = 1;
  int try = 0;
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
	      try = 1;
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
	      try = 1;
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
  return try;
}
*/

int pure_literal_elimination (void) {
  prop_node *p, *auxp;
  int try_ple = 1;
  int try = 0;

  while (numproofs < maxproof && try_ple) {
    try_ple = 0;
    HASH_ITER(hid,propsid,p,auxp) {
      if (p->id != CTRUE && p->id != CFALSE && p->id != CSTART && (
	  (p->occur_positive == 0 && p->occur_negative != 0) ||
	  (p->occur_positive != 0 && p->occur_negative == 0))) {
	try_ple = 1;
	try = 1;
	int id;
	hml_clauses *aux = NULL,*auxtmp = NULL;
	if (p->occur_negative) {
	  id = -p->id;
	}
	else {
	  id = p->id;
	}
	HASH_ITER(hml,p->clauses,aux,auxtmp) {
	  clausesid *clauses = NULL;
	  if (aux->positive == NULL)
	    clauses = aux->negative;
	  else clauses = aux->positive;
	    
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
  return try;
}

int modal_level_ple (void) {
  int try_ple = 1;
  int try = 0;
  int id = 0;
  
  while (numproofs < maxproof && try_ple) {
    try_ple = 0;
    prop_node *p = NULL, *ptmp = NULL;
    HASH_ITER(hid,propsid,p,ptmp) {
      hml_clauses *clauses = NULL, *clausestmp = NULL;
      clausesid *working = NULL;
      HASH_ITER(hml,p->clauses,clauses,clausestmp) {
	if (clauses->positive != NULL && clauses->negative == NULL) {
	  working = clauses->positive;
	  id = p->id;
	}
	else if (clauses->positive == NULL && clauses->negative != NULL) {
	  working = clauses->negative;
	  id = -(p->id);
	}
	clausesid *auxw = NULL, *auxwtmp = NULL;      
	HASH_ITER(hid,working,auxw,auxwtmp) {
	  if (auxw != NULL) {
	    tclause *clause = get_clause(auxw->id);
	    if (clause != NULL) {
	      try_ple = 1;
	      try = 1;
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
  return try;
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
		tclause *c  = get_clause(hmaxlit->list->clause_number);
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


tclause *create_pos_clause(int type, int subtype, tclause *c, int left, int right) {
  tclause *new = malloc(sizeof(tclause));
  new->number = numclause++;
  new->type = type;
  new->subtype = subtype;
  new->numdiamond  = c->numdiamond;
  new->agent = c->agent;
  new->modal_level = c->modal_level;
  new->propagated = 0;
  if (type == MNEGATIVE) {
    new->left = left;
  }
  else {
    new->left = -left;
  }
  new->right = malloc(sizeof(literalslist));
  new->right->literal = right;
  new->right->next = NULL;
  new->right = simplify_clause(new->right);
  new->size = size_clause(new->right);
  new->max_literal = max_lit_clause(new->right);
  new->min_literal = new->right->literal;
  new->class = classify_clause(new->right);
  
  justification *just = malloc(sizeof(justification));
  just->rule = DEFINITION;
  just->parents = malloc(sizeof(clauseslist));
  just->parents->clause_number = c->number;
  just->parents->clause_pointer = c;
  just->parents->next = NULL;
  just->literals = NULL;
  new->just = just;
  new->deleted = NULL;
  return new;
}

tclause *create_4_clause(tclause *c,int left, int right) {//parent, left, right of new modal clause
  tclause *new = malloc(sizeof(tclause));
  new->number = numclause++;
  new->type = MPOSITIVE;
  new->subtype = c->subtype; // DEFINITIONS SHOULD BE ALWAYS AVAILABLE???
  new->numdiamond = 1;
  new->agent = c->agent;
  new->modal_level = c->modal_level;
  new->propagated = 0;
  new->left = left;
  new->right = malloc(sizeof(literalslist));
  new->right->literal = right;
  new->right->next = NULL;
  new->right = simplify_clause(new->right);
  new->size = size_clause(new->right);
  new->max_literal = max_lit_clause(new->right);
  new->min_literal = new->right->literal;
  new->class = classify_clause(new->right);
  
  justification *just = malloc(sizeof(justification));
  just->rule = FOUR;
  just->parents = malloc(sizeof(clauseslist));
  just->parents->clause_number = c->number;
  just->parents->clause_pointer = c;
  just->parents->next = NULL;
  just->literals = NULL;
  new->just = just;
  new->deleted = NULL;
  return new;
}

tclause *create_t_clause(tclause *c) {
  tclause *new = malloc(sizeof(tclause));
  new->number = numclause++;
  new->type = LITERAL;
  new->subtype = c->subtype; // DEFINITIONS SHOULD BE ALWAYS AVAILABLE???
  new->numdiamond = 1;
  new->agent = 0;
  new->modal_level = c->modal_level;
  new->propagated = 0;
  new->left = CTRUE;
  new->right = malloc(sizeof(literalslist));
  new->right->literal = -c->left;
  new->right->next = malloc(sizeof(literalslist));
  new->right->next->literal = c->right->literal;
  new->right->next->next = NULL;
  new->right = simplify_clause(new->right);
  new->size = size_clause(new->right);
  new->max_literal = max_lit_clause(new->right);
  new->min_literal = new->right->literal;
  new->class = classify_clause(new->right);
  
  justification *just = malloc(sizeof(justification));
  just->rule = T;
  just->parents = malloc(sizeof(clauseslist));
  just->parents->clause_number = c->number;
  just->parents->clause_pointer = c;
  just->parents->next = NULL;
  just->literals = NULL;
  new->just = just;
  new->deleted = NULL;
  return new;
}

int create_pos_literal(int lit) {
  char *s = NULL;
  prop_node *p;
  if (lit < 0) {
    lit = -lit;
    HASH_FIND(hid,propsid,&lit,sizeof(int),p);
    int len = snprintf(NULL, 0, "_def_n_%s",p->name) + 1;
    s = (char *) malloc(len);
    len = snprintf(s, len,"_def_n_%s",p->name);
  }
  else {
    HASH_FIND(hid,propsid,&lit,sizeof(int),p);
    int len = snprintf(NULL, 0, "_def_%s",p->name) + 1;
    s = (char *) malloc(len);
    len = snprintf(s, len,"_def_%s",p->name);
  }
  
  prop_node *new = insert_pos_node(s);
  return new->id;
}

void preprocess_axioms(void) {
  agent_node *a;
  clauseslist *newclauses = NULL;
  for (a = agentsid; a != NULL; a = a->hid.next) {
    if (a->four || a->t) { // five is not implemented yet
      // iterate over the set of modal clauses generating the relevant literals and clauses
      hml_mclauses *aux = m_sos;
      hagentclauses *hag = NULL;
      htypeclauses *htc = NULL;
      hmaxlitclauses *hmaxlit = NULL;
  
      for (aux=m_sos; aux != NULL; aux=aux->hml.next)
	for (hag=aux->id; hag != NULL; hag=hag->hid.next)
	  for (htc=hag->type; htc != NULL; htc=htc->htype.next) {
	    if (htc->type == MPOSITIVE) {
	      for (hmaxlit = htc->lit; hmaxlit != NULL; hmaxlit=hmaxlit->hmax.next) {
		clauseslist *l = hmaxlit->list;
		while (l != NULL) {
		  tclause *clause = get_clause(l->clause_number);
		  int lit = clause->right->literal;
		  if (a->t) {
		    tclause *new_definition_t = create_t_clause(clause);
		    clauseslist *new = malloc(sizeof(clauseslist));
		    new->clause_number = new_definition_t->number;
		    new->clause_pointer = new_definition_t;
		    new->next = newclauses;
		    newclauses = new;
		  }
		  if (a->four) {
		    int pos_lit = create_pos_literal(-lit);
		    tclause *new_definition_dia = create_pos_clause(MNEGATIVE,BOX,clause,pos_lit,-lit);
		    tclause *new_definition_box = create_pos_clause(MPOSITIVE,BOX,clause,pos_lit,lit);
		    clauseslist *new1 = malloc(sizeof(clauseslist));
		    new1->clause_number = new_definition_dia->number;
		    new1->clause_pointer = new_definition_dia;
		    new1->next = newclauses;
		    newclauses = new1;
		    clauseslist *new2 = malloc(sizeof(clauseslist));
		    new2->clause_number = new_definition_box->number;
		    new2->clause_pointer = new_definition_box;
		    new2->next = newclauses;
		    newclauses = new2;
		    tclause *new_four_1 = create_4_clause(clause,clause->left,-pos_lit); //parent, left, right of new modal clause
		    clauseslist *new3 = malloc(sizeof(clauseslist));
		    new3->clause_number = new_four_1->number;
		    new3->clause_pointer = new_four_1;
		    new3->next = newclauses;
		    newclauses = new3;
		    tclause *new_four_2 = create_4_clause(clause,-pos_lit,-pos_lit);
		    clauseslist *new4 = malloc(sizeof(clauseslist));
		    new4->clause_number = new_four_2->number;
		    new4->clause_pointer = new_four_2;
		    new4->next = newclauses;
		    newclauses = new4;
		    /* note this is needed for completeness, even if t is not an axiom */
		    tclause *new_definition_t_pos = create_t_clause(new_definition_box);
		    clauseslist *new5 = malloc(sizeof(clauseslist));
		    new5->clause_number = new_definition_t_pos->number;
		    new5->clause_pointer = new_definition_t_pos;
		    new5->next = newclauses;
		    newclauses = new5;
		    if (a->t) {
		      tclause *new_four_1_t = create_t_clause(new_four_1);
		      clauseslist *new6 = malloc(sizeof(clauseslist));
		      new6->clause_number = new_four_1_t->number;
		      new6->clause_pointer = new_four_1_t;
		      new6->next = newclauses;
		      newclauses = new6;
		      /*tclause *new_four_2_t = create_t_clause(new_four_2);
		      clauseslist *new7 = malloc(sizeof(clauseslist));
		      new7->clause_number = new_four_2_t->number;
		      new7->clause_pointer = new_four_2_t;
		      new7->next = newclauses;
		      newclauses = new7; */
		    }
		  }
		  l = l->next;
		}
	      }
	    }
	  }
    }
  }
  while (newclauses != NULL) {
    //    printf("\n newclauses->clause_number: %d",newclauses->clause_number);
    //    print_clause(newclauses->clause_pointer);
    insert_clause_set(&(newclauses->clause_pointer),newclauses->clause_pointer->type,SOS);
    clauseslist *tmp = newclauses;
    newclauses = newclauses->next;
    free(tmp);
  }
  print_out("Processing Axioms");
}


void preprocessing (void) {
  int try = 1;
  int try2 = 0;
  while (numproofs < maxproof && try) {
  
    try = 0;
    if (propagate_dia == ON)
      propagate_unique_dia_ml();
    
    if (numproofs < maxproof && mle == ON) {
      try = modal_level_elimination();
    }
    if (numproofs < maxproof && ple == ON) {
      try2 = pure_literal_elimination();
      try = MAX(try,try2);
      print_out("PLE");
    }
    if (numproofs < maxproof && ml_ple == ON) {
      try2 = modal_level_ple();
      try = MAX(try,try2);
      print_out("ML_PLE");
    }
    if (l_sos != NULL && numproofs < maxproof && unit == ON) {
      try2 = unit_resolution(&l_sos);
      try = MAX(try,try2);
      print_out("Unit Resolution");
    }
  }

  do_mres(m_sos);
  print_out("MRES");
    
  if (gen2 | (!modal_negative && !modal_positive && !strong_modal_positive && !strong_modal_negative)) {
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
