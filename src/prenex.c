#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "prover.h"
#include "uthash.h"
#include "symbol_table.h"
#include "tree.h"

#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))
#define MIN(X, Y) (((X) < (Y)) ? (X) : (Y))

extern agent_node *find_agent(int id);
extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);

extern tnode *create_dia_tnode(int id, int mdepth, tnode *subf);
extern int is_literal (tnode *t);
extern int is_diamond(tnode *t);
extern int is_box(tnode *t);
extern void sort_formulalist(formulalist **l);

extern unsigned int hash_tree (tnode *t);
extern unsigned int hash_list (formulalist *l);

extern int formulasize;

tnode *simplify (tnode *s) {
  if ((is_box(s) && is_box(s) == is_box(s->left)) ||          // box box i p = box i p
      (is_box(s) && is_box(s)  == is_diamond(s->left)) ||     // box dia i p = dia i p
      (is_diamond(s) && is_diamond(s) == is_diamond(s->left)) ||  // dia dia p = dia p
      (is_diamond(s) && is_diamond(s) == is_box(s->left))) {      // dia box p = box p
    tnode *tmp;
    tmp = s;
    s = s->left;
    free(tmp);
    formulasize -= 1;
    return simplify(s);
  }
  return s;
}
    

tnode *get_prenex(tnode *s) {

  if (s == NULL)
    return NULL;
  else switch (s->type) {
    case SETC:
      {
	s->right = get_prenex(s->right);
	if (s->right != NULL)
	  s->mdepth = MAX(s->left->mdepth,s->right->mdepth);
	else s->mdepth = s->left->mdepth;
	return s;
      }
      break;
    case SETF: 
      {
	s->left = get_prenex(s->left);
	s->right = get_prenex(s->right);
	if (s->right != NULL)
	  s->mdepth = MAX(s->left->mdepth,s->right->mdepth);
	else s->mdepth = s->left->mdepth;
	return s;
      }
      break;
    case CONSTANT:
    case PROP:
      return s;
      break;
    case BOX:
    case DIAMOND:
      {
	s->left = get_prenex(s->left);
	s->value_number = hash_tree(s);
	agent_node *a = find_agent(s->id);
	if (a->five == 1 && a->four == 1)
	  return simplify(s);
	else return s;
      }
	break;
    case NEGATION:
      {
	if (is_literal(s))
	  return s;
	else printf("\n Error. Prenex. Negation.");
      }
      break;
    case CONJUNCTION:
      {
	sort_formulalist(&(s->list));
	formulalist *aux = s->list;
	while (aux != NULL) { 
	  aux->formula = get_prenex(aux->formula);
	  if (aux->formula->type == CONJUNCTION) {
	    if (aux->formula->list == NULL) {
	      aux->formula->type = CONSTANT;
	      aux->formula->id = CTRUE;
	      aux->formula->left = NULL;
	      aux->formula->right = NULL;
	      aux->formula->list = NULL;
	      aux->formula->value_number = hash_tree(aux->formula);
	    }
	    else {
	      formulalist *aux2 = aux->formula->list;
	      formulalist *aux3 = aux->formula->list;
	      while (aux3->next != NULL) {
		aux3 = aux3->next;
	      }
	      aux3->next = aux->next;
	      aux->formula = aux2->formula;
	      aux->next = aux2->next;
	      free(aux2);
	      aux = aux3;
	    }
	  }
	  aux = aux->next;
	}

	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	
	aux = s->list;
	while (aux != NULL && is_literal(aux->formula))
	  aux = aux->next;
	
	int id1;

	while (aux != NULL && (id1 = is_box(aux->formula))) {
	  formulalist *first = aux;
	  formulalist *last = aux;
	  int id2;
	  while (last->next != NULL && (id2 = is_box(last->next->formula)) && id1 == id2) {
	    last = last->next;
	  }

	  if (first != last) {
	    formulalist *newfirst = malloc(sizeof(formulalist));
	    newfirst->formula = first->formula;
	    newfirst->mdepth = first->mdepth;
	    newfirst->value_number = first->value_number;
	    newfirst->next = first->next;
	    
	    formulalist *aux = newfirst;
	    
	    while (aux != last->next) {
	      tnode *auxnode = aux->formula;
	      aux->formula = aux->formula->left;
	      aux->mdepth = aux->mdepth-1;
	      aux = aux->next;
	      free(auxnode);
	    }

	    
	    first->next = last->next;
	    last->next = NULL;
	    
	    tnode *and = create_tnode(CONJUNCTION,CONJUNCTION,first->mdepth-1,NULL,NULL,newfirst);
	    and = get_prenex(and);
	    tnode *box = create_tnode(BOX,id1,first->mdepth,and,NULL,NULL);

	    first->formula = box;
  
	  }
	  aux = aux->next;
	}

	if (s->list->next == NULL) {
	  s->type = s->list->formula->type;
	  s->id = s->list->formula->id;
	  s->value_number = s->list->formula->value_number;
	  s->mdepth = s->list->formula->mdepth;
	  s->left = s->list->formula->left;
	  free(s->list);
	  s->list = NULL;
	}
	
	if (s->list != NULL) {
	  sort_formulalist(&(s->list));
	  s->list->value_number = hash_list(s->list);
	}
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case DISJUNCTION:
      {
	sort_formulalist(&(s->list));
	formulalist *aux = s->list;
	while (aux != NULL) { 
	  aux->formula = get_prenex(aux->formula);
	  if (aux->formula->type == DISJUNCTION) {
	    if (aux->formula->list == NULL) {
	      aux->formula->type = CONSTANT;
	      aux->formula->id = CFALSE;
	      aux->formula->left = NULL;
	      aux->formula->right = NULL;
	      aux->formula->list = NULL;
	      aux->formula->value_number = hash_tree(aux->formula);
	    }
	    else {
	      formulalist *aux2 = aux->formula->list;
	      formulalist *aux3 = aux->formula->list;
	      while (aux3->next != NULL) {
		aux3 = aux3->next;
	      }
	      aux3->next = aux->next;
	      aux->formula = aux2->formula;
	      aux->next = aux2->next;
	      free(aux2);
	      aux = aux3;
	    }
	  }
	  aux = aux->next;
	}

	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);

	aux = s->list;
	while (aux != NULL && (is_literal(aux->formula) || is_box(aux->formula)))
	  aux = aux->next;
	
	int id1;
	
	while (aux != NULL && (id1 = is_diamond(aux->formula))) {
	  formulalist *first = aux;
	  formulalist *last = aux;
	  int id2;
	  while (last->next != NULL && (id2 = is_diamond(last->next->formula)) && id1 == id2) {
	    last = last->next;
	  }

	  if (first != last) {
	    formulalist *newfirst = malloc(sizeof(formulalist));
	    newfirst->formula = first->formula;
	    newfirst->value_number = first->value_number;
	    newfirst->mdepth = first->mdepth;
	    newfirst->next = first->next;
	    
	    formulalist *aux = newfirst;
	    
	    while (aux != last->next) {
	      tnode *auxnode = aux->formula;
	      aux->formula = aux->formula->left;
	      aux->mdepth = aux->mdepth-1;
	      aux = aux->next;
	      free(auxnode);
	    }

	    first->next = last->next;
	    last->next = NULL;
	    
	    tnode *or = create_tnode(DISJUNCTION,DISJUNCTION,first->mdepth-1,NULL,NULL,newfirst);
	    or = get_prenex(or);
	    tnode *diamond = create_tnode(DIAMOND,id1,first->mdepth,or,NULL,NULL);
	    
	    first->formula = diamond;
	  }
	  aux = aux->next;
	}

	if (s->list->next == NULL) {
	  s->type = s->list->formula->type;
	  s->id = s->list->formula->id;
	  s->mdepth = s->list->formula->mdepth;
	  s->left = s->list->formula->left;
	  s->value_number = s->list->formula->value_number;
	  free(s->list);
	  s->list = NULL;
	}
	if (s->list != NULL) {
	  sort_formulalist(&(s->list));
	  s->list->value_number = hash_list(s->list);
	}
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    default:
      printf("We have a problem, Houston. In prenex. \n");
    }
  return s;
}
