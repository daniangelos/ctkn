#include <pthread.h>
#include "prover.h"
#include "uthash.h"
#include "tree.h"
#include "symbol_table.h"
#include "clauses.h"

extern int improved_snf_plus;

extern int ml_prover;
extern int modal_negative;
extern int strong_modal_negative;
extern int numclause;
extern int newtemp;

extern hml_mclauses *m_usable;
extern hml_mclauses *m_sos;

extern int numprops;

extern void print_sos (void);
extern void delete_clause_all (int number);
extern tclause *get_clause (int clause);
extern prop_node *find_prop(int p);
extern int rename_formula(tnode *formula, int type, int set, int subtype, int modal_level);
extern void add_definition(int id, tnode *formula, int set, int subtype, int modal_level);
extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);
extern void insert_clause_modal (tclause **clause, hml_mclauses **set);
extern clauseslist *delete_clause_list(tclause *c, clauseslist *l);
extern prop_node *insert_pnew_node (int id, int type);

extern int check_minimal(tclause *clause, int modal_level);

typedef struct clauseslistsnfminus {
  tclause *clause;
  struct clauseslistsnfminus *next;
} clauseslistsnfminus;


/* Scans the modal formulae doing the rewriting and renaming when needed */


void free_clauses_set_m_snf_minus (hml_mclauses **set) {
  hml_mclauses *aux, *auxtmp;
  hagentclauses *hag, *hagtmp;
  htypeclauses *htc, *htctmp;
  hmaxlitclauses *hmaxlit, *hmaxlittmp;

  aux = *set;

  HASH_ITER(hml,*set,aux,auxtmp) {
    HASH_ITER(hid,aux->id,hag,hagtmp) {
      HASH_ITER(htype,hag->type,htc,htctmp) {
	HASH_ITER(hmax,htc->lit,hmaxlit,hmaxlittmp) {
	  if ((hmaxlit->max != CTRUE && hmaxlit->max != CFALSE) && (strong_modal_negative || modal_negative)) {
	    clauseslist *list = hmaxlit->list;
	    while (list != NULL) {
	      tclause *clause = get_clause(list->clause_number);
	      list = list->next;
	      if (clause->deleted != NULL) {
		hmaxlit->list = delete_clause_list(clause,hmaxlit->list);
		delete_clause_all(clause->number);
	      }
	    }
	  }
	  if (hmaxlit->list == NULL) {
	    HASH_DELETE(hmax,htc->lit,hmaxlit);
	    free(hmaxlit);
	    hmaxlit = NULL;
	  }
	}
	if (htc->lit == NULL) {
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
    if (aux == NULL) {
      HASH_DELETE(hml,*set,aux);
      free(aux);
      aux = NULL;
    }
  }
}


void snf_minus_by_set (int set, hml_mclauses **modal_set) {

  hml_mclauses *aux;
  hagentclauses *hag = NULL;
  htypeclauses *htc = NULL;
  hmaxlitclauses *hmaxlit = NULL;

  clauseslistsnfminus *newclauses = NULL;
  
  for (aux=*modal_set; aux != NULL; aux=aux->hml.next)
      for (hag=aux->id; hag != NULL; hag=hag->hid.next)
	for (htc=hag->type; htc != NULL; htc=htc->htype.next)
	  for (hmaxlit = htc->lit; hmaxlit != NULL; hmaxlit=hmaxlit->hmax.next) {
	    if ((hmaxlit->max != CTRUE && hmaxlit->max != CFALSE) && (strong_modal_negative || (modal_negative && hmaxlit->max > 0))) {
	      clauseslist *l = hmaxlit->list;
	      while (l != NULL) {
		tclause *clause = get_clause(l->clause_number);

		int minimal = 0;
		if (hmaxlit->max < 0 && improved_snf_plus) {
		  minimal = check_minimal(clause,clause->modal_level);
		}

		if (!minimal) {
		  int ml;
		  if (ml_prover) {
		    ml = clause->modal_level + 1;
		  }
		  else ml = clause->modal_level;
		
		  tnode *new_right = NULL;
		  if (strong_modal_negative || (modal_negative && clause->max_literal > 0)) {
		    new_right = create_tnode(PROP,clause->max_literal,ml,NULL,NULL,NULL);
		    if (clause->max_literal < 0) {
		      new_right->id = -new_right->id;
		      tnode *not = create_tnode(NEGATION,NEGATION,ml,new_right,NULL,NULL);
		      new_right = not;
		    }
		  }

		  /* Renaming the left-hand side */
		
		  int id_minus_right;

		  if (new_right != NULL) {
		    prop_node *p = insert_pnew_node(newtemp++,HIGH);
		    id_minus_right = -p->id;
		    int subtype;
		    if (clause->type == MPOSITIVE)
		      subtype = BOX;
		    else subtype = DIAMOND;
		    add_definition(id_minus_right,new_right,set,subtype,ml);
		  }
		  else id_minus_right = clause->max_literal;
		
		  tnode *new_left = create_tnode(PROP,clause->left,clause->modal_level,NULL,NULL,NULL);
		  if (clause->left < 0) {
		    new_left->id = -new_left->id;
		  }
		  else {
		    tnode *not = create_tnode(NEGATION,NEGATION,ml,new_left,NULL,NULL);
		    new_left = not;
		  }

		  prop_node *p = insert_pnew_node(newtemp++,HIGH);
		  int id_minus_left = p->id;
		  add_definition(id_minus_left,new_left,set,clause->subtype,clause->modal_level);
		
		  tclause *newclause = malloc(sizeof(tclause));

		  newclause->number = numclause++;
		  newclause->type = clause->type;
		  newclause->subtype = clause->subtype;
		  newclause->size = clause->size;
		  newclause->modal_level = clause->modal_level;
		  newclause->max_literal = id_minus_right;
		  newclause->min_literal = id_minus_right;
		  newclause->agent = clause->agent;
		  newclause->class = clause->class;
		  newclause->propagated = 0;
		  newclause->left = -id_minus_left;
		  newclause->right = malloc(sizeof(literalslist));
		  newclause->right->literal = id_minus_right;
		  newclause->right->next = NULL;
		  newclause->just = malloc(sizeof(justification));
		  newclause->just->rule = SNF_MINUS;
		  clauseslist *parent = malloc(sizeof(clauseslist));
		  parent->clause_number = clause->number;
		  parent->next = NULL;	  
		  newclause->just->parents = parent;
		  newclause->just->literals = NULL;
		  newclause->deleted = NULL;

		  clauseslist *parent_deleted = malloc(sizeof(clauseslist));
		  parent_deleted->clause_number = newclause->number;
		  parent_deleted->next = NULL;
      
		  literalslist *literals = malloc(sizeof(literalslist));
		  literals->literal = clause->right->literal;
		  literals->next = NULL;

		  justification *deleted = malloc(sizeof(justification));
		  deleted->rule = SNF_MINUS;
		  deleted->parents = parent_deleted;
		  deleted->literals = literals;
		  
		  clause->deleted = deleted;

		  clauseslistsnfminus *auxclauses = malloc(sizeof(clauseslistsnfminus));
		  auxclauses->clause = newclause;
		  auxclauses->next = newclauses;
		  newclauses = auxclauses;
		}
		l = l->next;
	      }
	    }
	  }
  
  free_clauses_set_m_snf_minus(&(*modal_set));

  while (newclauses != NULL) {
    insert_clause_modal(&(newclauses->clause),&(*modal_set));
    clauseslistsnfminus *auxclauses = newclauses->next;
    free(newclauses);
    newclauses = auxclauses;
  }

}

void snf_minus(void) {
  snf_minus_by_set(USABLE,&m_usable);
  snf_minus_by_set(SOS,&m_sos);
}
