#include <pthread.h>
#include "prover.h"
#include "uthash.h"
#include "tree.h"
#include "symbol_table.h"
#include "clauses.h"

extern int improved_snf_plus;

extern int ml_prover;
extern int modal_positive;
extern int strong_modal_positive;
extern int numclause;

extern hml_mclauses *m_usable;
extern hml_mclauses *m_sos;

extern int numprops;

extern void print_sos (void);
extern void delete_clause_all (int number);
extern tclause *get_clause (int clause);
extern prop_node *find_prop(int p);
extern int rename_formula(tnode *formula, int type, int set, int modal_level);
extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);
extern void insert_clause_modal (tclause **clause, hml_mclauses **set);
extern clauseslist *delete_clause_list(tclause *c, clauseslist *l);

typedef struct clauseslistsnfplus {
  tclause *clause;
  struct clauseslistsnfplus *next;
} clauseslistsnfplus;


/* Scans the modal formulae doing the rewriting and renaming when needed */

int check_minimal(tclause *clause, int modal_level) {
  int literal = clause->right->literal;
  if (literal < 0) {
    literal = -literal;
  }

  prop_node *p = find_prop(literal);
  int minimal = 1;
  modal_level = modal_level + 1;

  hml_clauses *clausesaux = NULL;

  HASH_FIND(hml,p->positive,&(modal_level),sizeof(int),clausesaux);

  int numliteral = 0;
  if (clausesaux != NULL) {
    clausesid *clauseslist = clausesaux->clauses;
    while (minimal && clauseslist != NULL) {
      tclause *newclause = get_clause(clauseslist->id);
      if (newclause->type == MNEGATIVE || newclause->type == MPOSITIVE) {
	int newliteral = newclause->left;
	if (newliteral < 0)
	  newliteral = -newliteral;
	if (literal == newliteral)
	  minimal = 0;
	  }
      else if (newclause->type == LITERAL) {
	numliteral++;
	literalslist *right = newclause->right;
	while (minimal && right != NULL) {
	  int newliteral = right->literal;
	  if (right->literal < 0)
	    newliteral = -newliteral;
	  if (newliteral < literal)
	    minimal = 0;
	  right = right->next;
	}
      }
      clauseslist = clauseslist->hid.next;
    }
  }


  HASH_FIND(hml,p->negative,&(modal_level),sizeof(int),clausesaux);
  
  if (minimal && clausesaux != NULL) {
    clausesid *clauseslist = clausesaux->clauses;
    while (minimal && clauseslist != NULL) {
      tclause *newclause = get_clause(clauseslist->id);
      if (newclause->type == MNEGATIVE || newclause->type == MPOSITIVE) {
	int newliteral = newclause->left;
	if (newliteral < 0)
	  newliteral = -newliteral;
	if (literal == newliteral)
	  minimal = 0;
	  }
      else if (newclause->type == LITERAL) {
	numliteral++;
	literalslist *right = newclause->right;
	while (minimal && right != NULL) {
	  int newliteral = right->literal;
	  if (right->literal < 0)
	    newliteral = -newliteral;
	  if (newliteral < literal)
	    minimal = 0;
	  right = right->next;
	}
      }
      clauseslist = clauseslist->hid.next;
    }
  }

  if (numliteral > 0)
    minimal = 0;

  return minimal;
}


void free_clauses_set_m_snf_plus (hml_mclauses **set) {
  hml_mclauses *aux, *auxtmp;
  hagentclauses *hag, *hagtmp;
  htypeclauses *htc, *htctmp;
  hmaxlitclauses *hmaxlit, *hmaxlittmp;

  aux = *set;

  HASH_ITER(hml,*set,aux,auxtmp) {
    HASH_ITER(hid,aux->id,hag,hagtmp) {
      HASH_ITER(htype,hag->type,htc,htctmp) {
	HASH_ITER(hmax,htc->lit,hmaxlit,hmaxlittmp) {
	  if ((hmaxlit->max != CTRUE && hmaxlit->max != CFALSE) && (strong_modal_positive || (modal_positive && hmaxlit->max < 0))) {
	    clauseslist *list = hmaxlit->list;
	    while (list != NULL) {
	      tclause *clause = get_clause(list->clause);
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



void snf_plus_by_set (int set, hml_mclauses **modal_set) {

  hml_mclauses *aux;
  hagentclauses *hag = NULL;
  htypeclauses *htc = NULL;
  hmaxlitclauses *hmaxlit = NULL;

  clauseslistsnfplus *newclauses = NULL;
  
  for (aux=*modal_set; aux != NULL; aux=aux->hml.next)
      for (hag=aux->id; hag != NULL; hag=hag->hid.next)
	for (htc=hag->type; htc != NULL; htc=htc->htype.next)
	  for (hmaxlit = htc->lit; hmaxlit != NULL; hmaxlit=hmaxlit->hmax.next) {
	    if ((hmaxlit->max != CTRUE && hmaxlit->max != CFALSE) && (strong_modal_positive || (modal_positive && hmaxlit->max < 0))) {
	      clauseslist *l = hmaxlit->list;
	      while (l != NULL) {
		tclause *clause = get_clause(l->clause);

		int minimal = 0;
		if (hmaxlit->max > 0 && improved_snf_plus) {
		  minimal = check_minimal(clause,clause->modal_level);
		}

		if (!minimal) {
		  int ml;
		  if (ml_prover) {
		    ml = clause->modal_level + 1;
		  }
		  else ml = clause->modal_level;
		
		  tnode *new = create_tnode(PROP,clause->max_literal,ml,NULL,NULL,NULL);
		  if (clause->max_literal < 0) {
		    new->id = -new->id;
		    tnode *not = create_tnode(NEGATION,NEGATION,ml,new,NULL,NULL);
		    new = not;
		  }
			
		  int id_plus = rename_formula(new,HIGH,set,ml);
		  tclause *newclause = malloc(sizeof(tclause));

		  newclause->number = numclause++;
		  newclause->type = clause->type;
		  newclause->size = clause->size;
		  newclause->modal_level = clause->modal_level;
		  newclause->max_literal = id_plus;
		  newclause->agent = clause->agent;
		  newclause->class = clause->class;
		  newclause->left = clause->left;
		  newclause->propagated = 0;
		  newclause->right = malloc(sizeof(literalslist));
		  newclause->right->literal = id_plus;
		  newclause->right->next = NULL;
		  newclause->just = malloc(sizeof(justification));
		  newclause->just->rule = SNF_PLUS;
		  clauseslist *parent = malloc(sizeof(clauseslist));
		  parent->clause = clause->number;
		  parent->next = NULL;	  
		  newclause->just->parents = parent;
		  newclause->just->literals = NULL;
		  newclause->deleted = NULL;

		  clauseslist *parent_deleted = malloc(sizeof(clauseslist));
		  parent_deleted->clause = newclause->number;
		  parent_deleted->next = NULL;
		  
		  literalslist *literals = malloc(sizeof(literalslist));
		  literals->literal = clause->right->literal;
		  literals->next = NULL;

		  justification *deleted = malloc(sizeof(justification));
		  deleted->rule = SNF_PLUS;
		  deleted->parents = parent_deleted;
		  deleted->literals = literals;

		  clause->deleted = deleted;

		  clauseslistsnfplus *auxclauses = malloc(sizeof(clauseslistsnfplus));
		  auxclauses->clause = newclause;
		  auxclauses->next = newclauses;
		  newclauses = auxclauses;
		}
		l = l->next;	
	      }
	    }
	  }
  
  free_clauses_set_m_snf_plus(&(*modal_set));

  while (newclauses != NULL) {
    insert_clause_modal(&(newclauses->clause),&(*modal_set));
    clauseslistsnfplus *auxclauses = newclauses->next;
    free(newclauses);
    newclauses = auxclauses;
  }

}

void snf_plus(void) {
  snf_plus_by_set(USABLE,&m_usable);
  snf_plus_by_set(SOS,&m_sos);
}
