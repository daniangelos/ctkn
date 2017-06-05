#include <stdlib.h>
#include <stdio.h>
#include "prover.h"
#include "tree.h"

extern int numsimp;
extern int formulasize;

extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);

extern tnode *free_tree (tnode *s);
extern formulalist *free_formulalist(formulalist *s);
extern void sort_formulalist(formulalist **l);

extern int size_tree(tnode *s);
extern int size_list(formulalist *s);

extern formulalist *simplify_and (formulalist *list);
extern formulalist *simplify_or (formulalist *list);

extern unsigned int hash_tree (tnode *t);
extern unsigned int hash_list (formulalist *l);

tnode *get_bnfsimp (tnode *s) {
  if (s == NULL)
    return s;
  else switch (s->type) {
    case SETC:
      {
	s->right = get_bnfsimp(s->right);
	return s;
      }
      break;
    case SETF: 
      {
	s->left = get_bnfsimp(s->left);
	s->right = get_bnfsimp(s->right);
	return s;
      }
      break;
    case NEGATION:
       {
	 if (s->left->type == NEGATION) { // simplifies double negations
	   tnode *aux = s;
	   s = s->left->left;
	   free(aux);
	   s = get_bnfsimp(s);
	  }
	 else if (s->left->type == CONSTANT && s->left->id != CSTART) {
	   int constant;
	   if (s->left->id == CTRUE)
	     constant = CFALSE;
	   else if (s->left->id ==  CFALSE)
	     constant = CTRUE;
	   s->type = CONSTANT;
	   s->id = constant;
	   free(s->left);
	   s->left = NULL;
	   s->value_number = hash_tree(s);
	 }
	 else s->left = get_bnfsimp(s->left);
	 return s;
       }
       break;
    case CONSTANT:
    case PROP:
      return s;
      break;
    case BOX:
      {
	s->left = get_bnfsimp(s->left);
	if (s->left->type == CONSTANT && s->left->id == CTRUE) {
	  s->type = CONSTANT;
	  s->id = CTRUE;
	  free(s->left);
	  s->left = NULL;
	  s->value_number = hash_tree(s);
	  numsimp++;
	  //	  printf("\n box true");
	  formulasize = formulasize - 2;
	}
	return s;
      }
      break;
    case DIAMOND: // there shouldn't be diamonds here anymore
      {
	tnode *neg = create_tnode(NEGATION,NEGATION,s->left->mdepth,s->left,NULL,NULL);
	tnode *box = create_tnode(BOX,s->id,s->mdepth,neg, NULL,NULL);
	s->type = NEGATION;
	s->id = NEGATION;
	s->left = get_bnfsimp(box);
	s->value_number = hash_tree(s);
	return s;
      }
      break;
    case DISJUNCTION:
      {
	sort_formulalist(&(s->list));
	formulalist *aux = s->list;
	while (aux != NULL) {
          aux->formula = get_bnfsimp(aux->formula);
	  if (aux->formula->type == CONSTANT && aux->formula->id == CTRUE) {
	    s->type = CONSTANT;
	    s->id = CTRUE;
	    s->list = free_formulalist(s->list);
	    s->list = NULL;
	    numsimp++;
	    //printf("\n OR true");
	    return s;
	  }
	  else aux = aux->next;
	}

	aux = s->list;
	int flag = 0;
	while (aux != NULL) {
	  if (aux->formula->type == DISJUNCTION) {
	    flag = 1;
	    formulalist *aux2 = aux->formula->list;
	    formulalist *aux3 = aux->formula->list;
	    while (aux3->next != NULL) {
	      aux3 = aux3->next;
	    }
	    aux3->next = aux->next;
	    aux->formula = aux2->formula;
	    aux->next = aux2->next;
	    free(aux2);
	    aux = aux3; // moves to the end of the list in formula then goes to the next
	  }
	  aux = aux->next;
	}

	if (flag) {
	  sort_formulalist(&(s->list));
	  s->list->value_number = hash_list(s->list);
	  s->value_number = hash_tree(s);
	}
	s->list = simplify_or(s->list);


	if (s->list == NULL) {
	  tnode *new = malloc(sizeof(tnode));
	  new->type = CONSTANT;
	  new->id = CFALSE;
	  new->left = NULL;
	  new->right = NULL;
	  new->list = NULL;
	  new->value_number = hash_tree(new);
	  s = new;
	}
	else if (s->list->next == NULL) {
	  tnode *aux = s->list->formula;
	  s->type = aux->type;
	  s->id = aux->id;
	  s->value_number = aux->value_number;
	  s->mdepth = aux->mdepth;
	  s->left = aux->left;
	  s-> right= aux->right;
	  s->list = aux->list;
	  free(aux);
	  numsimp++;
	  //printf("\n flattening disjunction");
	  formulasize = formulasize - 1;
	}
	return s;
      }
      break;
    case CONJUNCTION:
      {
	sort_formulalist(&(s->list));
	formulalist *aux = s->list;

	while (aux != NULL) {
          aux->formula = get_bnfsimp(aux->formula);
	  if (aux->formula->type == CONSTANT && aux->formula->id == CFALSE) {
	    s->type = CONSTANT;
	    s->id = CFALSE;
	    s->list = free_formulalist(s->list);
	    s->list = NULL;
	    numsimp++;
	    //printf("\n AND false");
	    return s;
	  }
	  aux = aux->next;
	}

	aux = s->list;
	int flag = 0;
	while (aux != NULL) {
	  if (aux->formula->type == CONJUNCTION) {
	    flag = 1;
	    formulalist *aux2 = aux->formula->list;
	    formulalist *aux3 = aux->formula->list;
	    while (aux3->next != NULL) {
	      aux3 = aux3->next;
	    }
	    aux3->next = aux->next;
	    aux->formula = aux2->formula;
	    aux->next = aux2->next;
	    free(aux2);
	    numsimp++;
	    aux = aux3;
	  }
	  aux = aux->next;
	}

	if (flag) {
	  sort_formulalist(&(s->list));
	  s->list->value_number = hash_list(s->list);
	  s->value_number = hash_tree(s);
	}
	s->list = simplify_and(s->list);

	if (s->list == NULL) {
	  tnode *new = malloc(sizeof(tnode));
	  new->type = CONSTANT;
	  new->id = CTRUE;
	  new->left = NULL;
	  new->right = NULL;
	  new->list = NULL;
	  new->value_number = hash_tree(new);
	  s = new;
	}
	else if (s->list->next == NULL) {
	  tnode *aux = s->list->formula;
	  s->type = aux->type;
	  s->id = aux->id;
	  s->value_number = aux->value_number;
	  s->mdepth = aux->mdepth;
	  s->left = aux->left;
	  s-> right= aux->right;
	  s->list = aux->list;
	  free(aux);
	  numsimp++;
	  //printf("\n flattening conjunction");
	  formulasize = formulasize - 1;
	}
	return s;
      }
      break;
    default:
      return s;
    }
}


