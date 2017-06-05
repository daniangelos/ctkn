#include <stdlib.h>
#include <stdio.h>
#include "prover.h"
#include "tree.h"

extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);

extern tnode *copy_tree(tnode *s);
extern formulalist *tree_to_list(int type, tnode *left, tnode *right);

extern unsigned int hash_tree (tnode *t);
extern unsigned int hash_list (formulalist *l);
extern void sort_formulalist(formulalist **l);

extern int formulasize;

tnode *get_bnf(tnode *s) {
  if (s == NULL)
    return NULL;
  else switch (s->type) {
    case SETC:
      {
	s->right = get_bnf(s->right);
	return s;
      }
      break;
    case SETF: 
      {
	s->left = get_bnf(s->left);
	s->right = get_bnf(s->right);
	return s;
      }
      break;
    case CONSTANT:
    case PROP:
      return s;
      break;
    case BOX:
      {
	s->left = get_bnf(s->left);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case DIAMOND:
      {
	tnode *neg = create_tnode(NEGATION,NEGATION,s->left->mdepth,s->left,NULL,NULL);
	tnode *box = create_tnode(BOX,s->id,s->mdepth,neg,NULL,NULL);
	s->type = NEGATION;
	s->id = NEGATION;
	s->left = box;
	s->left = get_bnf(s->left);
	s->value_number = hash_tree(s);
	formulasize = formulasize + 2;
	return s;
      }
      break;
    case NEGATION:
      {
	if (s->left != NULL) {
	  if (s->left->type == NEGATION) { // simplifies double negations
	    tnode *aux = s->left->left;
	    free(s->left);
	    free(s);
	    s = aux;
	    formulasize = formulasize - 2;
	  }
	  else if (s->left->type == CONSTANT) {
	    s->type = CONSTANT;
	    if (s->left->id == CTRUE)
	      s->id = CFALSE;
	    else s->id = CTRUE;
	    free(s->left);
	    s->left = NULL;
	    s->value_number = hash_tree(s);
	    formulasize = formulasize - 1;
	  }
	  else if (s->left->type == BOX) {
	    s->left = get_bnf(s->left);
	    s->value_number = hash_tree(s);
	  }
	  else if (s->left->type == DIAMOND) {
	    tnode *not = create_tnode(NEGATION,NEGATION,s->left->left->mdepth,s->left->left,NULL,NULL);
	    s->left->type = BOX;
	    s->left->left = not;
	    tnode *aux = get_bnf(s->left);
	    free(s);
	    s = aux;
	    /* size doesn't change */
	  }
	  else if (s->left->type == DISJUNCTION) { // neg (p or q) = neg p or neg q
	    s->type = CONJUNCTION;
	    s->id = CONJUNCTION;
	    formulalist *aux = s->left->list;
	    formulasize = formulasize - 1;
	    while (aux != NULL) {
	      aux->formula = create_tnode(NEGATION,NEGATION,s->mdepth,aux->formula,NULL,NULL);
	      aux->formula = get_bnf(aux->formula);
	      formulasize = formulasize + 1;
	      aux = aux->next;
	    }
	    s->list = s->left->list;
	    free(s->left);
	    s->left = NULL;
	    sort_formulalist(&(s->list));
	    s->list->value_number = hash_list(s->list);
	    s->value_number = hash_tree(s);
	  }
	  else if (s->left->type == CONJUNCTION) { // neg (p and q) = neg p and neg q
	    s->type = DISJUNCTION;
	    s->id = DISJUNCTION;
	    formulalist *aux = s->left->list;
	    formulasize = formulasize - 1;
	    while (aux != NULL) {
	      aux->formula = create_tnode(NEGATION,NEGATION,s->mdepth,aux->formula,NULL,NULL);
	      aux->formula = get_bnf(aux->formula);
	      formulasize = formulasize + 1;
	      aux = aux->next;
	    }
	    s->list = s->left->list;
	    free(s->left);
	    s->left = NULL;
	    sort_formulalist(&(s->list));
	    s->list->value_number = hash_list(s->list);
	    s->value_number = hash_tree(s);
	  }
	  else s->left = get_bnf(s->left);
	}
	return s;
      }
      break;
    case CONJUNCTION:
      {
	formulalist *aux = s->list;
	while (aux != NULL) {
	  aux->formula = get_bnf(aux->formula);
	  if (aux->formula->type == CONJUNCTION) {
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
	  aux = aux->next;
	}
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case DISJUNCTION:
      {
	formulalist *aux = s->list;
	while (aux != NULL) {
	  aux->formula = get_bnf(aux->formula);
	  if (aux->formula->type == DISJUNCTION) {
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
	  aux = aux->next;
	}
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    default:
      printf("We have a problem, Houston. In BNF.\n");
    }
  return s;
}

