#include <stdio.h>
#include "tree.h"
#include "symbol_table.h"
#include "prover.h"

int emlple = 0;

extern void print_tree(tnode *t);
extern tnode *get_small_cnf(tnode *t);
extern tnode *copy_tree(tnode *t);
extern formulalist *tree_to_list(int type, tnode *left, tnode *right);
extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);
extern unsigned int hash_tree (tnode *t);
extern unsigned int hash_list (formulalist *l);
extern void sort_formulalist(formulalist **l);
extern formulalist *free_formulalist(formulalist *l);
extern tnode *free_tree(tnode *l);

extern int formulasize;
extern int size_tree (tnode *root);

extern int prenex;
extern int antiprenex;
extern int cnf;
extern int small_cnf;
extern int nnfsimp;
extern int bnfsimp;
extern int early_ple;
extern int early_mlple;
extern int numearlyple;
extern int numearlymlple;
extern int numsimp;
extern int linearise;

extern void print_out (char *);

extern tnode *get_prenex (tnode *s);
extern tnode *get_antiprenex (tnode *s);
extern tnode *get_propagate(tnode *s);
extern tnode *get_nnf (tnode *s, int stat);
extern tnode *get_nnfsimp (tnode *s);
extern tnode *get_bnf (tnode *s);
extern tnode *get_bnfsimp (tnode *s);

extern void free_pnode(prop_node *p);
extern prop_node *find_prop (int id);

extern tnode *init_eple (tnode *s, int sign);
extern tnode *get_eple (tnode *s);
extern void finish_eple (void);

extern struct prop_node *propsid;

tnode *eliminate_double_implications(tnode *s, int polarity) {
  if (s != NULL) {
    s->polarity = polarity;
    if (s->type == DOUBLEIMP) {
      if (polarity > 0) { // (p iff q) = (p then q) and (q then p)
	tnode *left = copy_tree(s->left);
	tnode *right = copy_tree(s->right);
	tnode *ifpart = create_tnode(IMPLICATION,IMPLICATION,s->mdepth,s->left,s->right,NULL);
	tnode *onlyifpart = create_tnode(IMPLICATION,IMPLICATION,s->mdepth,right,left,NULL);	
	s->type = CONJUNCTION;
	s->id = CONJUNCTION;
	s->list = tree_to_list(CONJUNCTION,ifpart,onlyifpart);
	s->left = NULL;
	s->right = NULL;
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	s = eliminate_double_implications(s,polarity);
      }
      else { // (p iff q) = (p & q) | (~p & ~q)
	tnode *newleft = copy_tree(s->left);
	tnode *newright = copy_tree(s->right);
	formulalist *leftlist = tree_to_list(CONJUNCTION,s->left,s->right);
	tnode *left = create_tnode(CONJUNCTION,CONJUNCTION,s->mdepth,NULL,NULL,leftlist);
	tnode *notleft = create_tnode(NEGATION,NEGATION,s->mdepth,newleft,NULL,NULL);
	tnode *notright = create_tnode(NEGATION,NEGATION,s->mdepth,newright,NULL,NULL);
	formulalist *rightlist = tree_to_list(CONJUNCTION,notleft,notright);
	tnode *right = create_tnode(CONJUNCTION,CONJUNCTION,s->mdepth,NULL,NULL,rightlist);

	s->type = DISJUNCTION;
	s->id = DISJUNCTION;
	s->left = NULL;
	s->right = NULL;
	s->list = tree_to_list(DISJUNCTION,left,right);
	sort_formulalist(&(s->list));
	s->list->value_number = hash_list(s->list);
	s->value_number = hash_tree(s);
	s = eliminate_double_implications(s,polarity);
      }
    }
    else {
      if (s->type == NEGATION || s->type == IMPLICATION)
	s->left = eliminate_double_implications(s->left,-polarity);
      else
	s->left = eliminate_double_implications(s->left,polarity);
      s->right = eliminate_double_implications(s->right,polarity);
      formulalist *aux = s->list;
      while (aux != NULL) {
	aux->formula = eliminate_double_implications(aux->formula,polarity);
	aux = aux->next;
      }
    }
  }
  return s;
}

formulalist *distribute(formulalist * l) {
  if (l == NULL)
    return l;
  else if (l->next != NULL) {
    l->next = distribute(l->next);
    tnode *aux = l->formula;
    formulalist *conjunction = NULL;
    if (l->formula->distribute == 1) {
      if (l->next->formula->distribute == 1) {
	formulalist *auxr = l->next->formula->list;
	while (auxr != NULL) {
	  if (aux->type == CONJUNCTION) {
	    formulalist *auxl = aux->list;
	    while (auxl != NULL) {
	      tnode *newleft = copy_tree(auxl->formula);
	      tnode *newright = copy_tree(auxr->formula);
	      formulalist *newl = tree_to_list(DISJUNCTION,newleft,newright);
	      tnode *dis = create_tnode(DISJUNCTION,DISJUNCTION,newl->mdepth,NULL,NULL,newl);
	      formulalist *tmp = malloc(sizeof(formulalist));
	      tmp->formula = dis;
	      tmp->next = conjunction;
	      conjunction = tmp;
	      auxl = auxl->next;
	    }
	  }
	  else {
	    tnode *newleft = copy_tree(aux);
	    tnode *newright = copy_tree(auxr->formula);
	    formulalist *newl = tree_to_list(DISJUNCTION,newleft,newright);
	    tnode *dis = create_tnode(DISJUNCTION,DISJUNCTION,newl->mdepth,NULL,NULL,newl);
	    formulalist *tmp = malloc(sizeof(formulalist));
	    tmp->formula = dis;
	    tmp->next = conjunction;
	    conjunction = tmp;
	  }
	  auxr = auxr->next;
	}
      }
    }
    if (conjunction != NULL) {
      tnode *conj = create_tnode(CONJUNCTION,CONJUNCTION,conjunction->mdepth,NULL,NULL,conjunction);
      formulalist *list = malloc(sizeof(formulalist));
      list->formula = conj;
      list->next = NULL;
      return list;
    }
  }
  return l;
}

tnode *get_cnf(tnode *t) {
  if (t == NULL) {
    return t;
  }
  else {
    switch (t->type) {
    case SETC:
      {
	t->right = get_cnf(t->right);
	return t;
      }
      break;
    case SETF: 
      {
	t->left = get_cnf(t->left);
	t->right = get_cnf(t->right);
	return t;
      }
      break;
    case LITERAL:
    case CONSTANT:
    case NEGATION:
      {
	return t;
      }
      break;
    case BOX:
    case DIAMOND:
      {
	t->left = get_cnf(t->left);
	return t;
      }
      break;
    case CONJUNCTION:
      {
	formulalist *aux = t->list;
	while (aux != NULL) {
	  aux->formula = get_cnf(aux->formula);
	  aux = aux->next;
	}
	
	sort_formulalist(&(t->list));
	t->list->value_number = hash_list(t->list);
	t->value_number = hash_tree(t);
	
	if (t->list->next == NULL) {
	  tnode *auxt = t->list->formula;
	  t->type = auxt->type;
	  t->id = auxt->id;
	  t->value_number = auxt->value_number;
	  t->mdepth = auxt->mdepth;
	  t->left = auxt->left;
	  t-> right= auxt->right;
	  t->list = auxt->list;
	  free(auxt);
	}
      }
      break;
    case DISJUNCTION:
      {
	formulalist *aux = t->list;
	while (aux != NULL) {
	  aux->formula = get_cnf(aux->formula);
	  aux = aux->next;
	}
	t->list = distribute(t->list);
	sort_formulalist(&(t->list));
	t->list->value_number = hash_list(t->list);
	if (t->list->formula->type == DISJUNCTION) {
	  t->type = CONJUNCTION;
	  t->value_number = hash_tree(t);
	  t = get_cnf(t);
	}
	if (t->list->next == NULL) {
	  tnode *auxt = t->list->formula;
	  t->type = auxt->type;
	  t->id = auxt->id;
	  t->value_number = auxt->value_number;
	  t->mdepth = auxt->mdepth;
	  t->left = auxt->left;
	  t-> right= auxt->right;
	  t->list = auxt->list;
	  free(auxt);
	}
	return t;
      }
    default:
      return t;
      break;
    }
  }
  return t;
}


tnode *calculate_polarity (tnode *s, int sign, int ml) {
  if (s == NULL)
    return s;
  
  s->polarity = sign;
  s->mlevel = ml;
  
  if (s->type == PROP) {
    prop_node *p = find_prop(s->id);
    if (sign > 0) {
      p->occur_positive++;
      hml_clauses *clauses;
      HASH_FIND(hml,p->positive,&ml,sizeof(int),clauses);
      if (clauses == NULL) {
	hml_clauses *new = malloc(sizeof(*new));
	new->ml = ml;
	new->occur_positive = 1;
	new->occur_negative = 0;
	new->clauses = NULL;
	HASH_ADD(hml,p->positive,ml,sizeof(int),new);
	clauses = new;
      }
      else
	clauses->occur_positive++;
    }
    else {
      p->occur_negative++;
      hml_clauses *clauses;
      HASH_FIND(hml,p->negative,&ml,sizeof(int),clauses);
      if (clauses == NULL) {
	hml_clauses *new = malloc(sizeof(*new));
	new->ml = ml;
	new->occur_positive = 0;
	new->occur_negative = 1;
	new->clauses = NULL;
	HASH_ADD(hml,p->negative,ml,sizeof(int),new);
	clauses = new;
      }
      else
	clauses->occur_negative++;
    }
  }
  else if (s->type == SETF || s->type == SETC) {
    s->left = calculate_polarity(s->left,sign,ml);
    s->right = calculate_polarity(s->right,sign,ml);
  }
  else if (s->type == BOX || s->type == DIAMOND) {
    s->left = calculate_polarity(s->left,sign,ml+1);
    s->right = calculate_polarity(s->right,sign,ml+1);
  }
  else if (s->type == NEGATION || s->type == IMPLICATION) {
    s->left = calculate_polarity(s->left,-sign,ml);
    s->right = calculate_polarity(s->right,sign,ml); 
  }
  else if (s->type == DOUBLEIMP) {
    s->left = calculate_polarity(s->left,sign,ml);
    s->right = calculate_polarity(s->right,sign,ml);
    s->left = calculate_polarity(s->left,-sign,ml); // I need this in order to get the right count on the occurrences of literals
    s->right = calculate_polarity(s->right,-sign,ml); // but I am not sure this is helping with linearisation. Probably not.
  }
  else { // it is a conjunction or a disjunction
    formulalist *aux = s->list;
    while (aux != NULL) {
      aux->formula = calculate_polarity(aux->formula,sign,ml);
      aux = aux->next;
    }
  }
  return s;
}

/*

int get_eple (void) {
  int done = 0;
  prop_node *p;
  
  for (p = propsid; p != NULL; p = p->hid.next) {
    if (p->occur_positive == 0 && p->occur_negative != 0) {
      done = 1;
      numearlyple++;
      literal_list *aux = p->neg_ple;
      while (aux != NULL) {
	p->occur_negative--;
	aux->literal->type = CONSTANT;
	aux->literal->id = CFALSE;
	literal_list *tmp = aux->next;
	free(aux);
	aux = tmp;
      }
      p->neg_ple = NULL;
    }
    else if (p->occur_positive != 0 && p->occur_negative == 0) {
      done = 1;
      numearlyple++;
      literal_list *aux = p->pos_ple;
      while (aux != NULL) {
	p->occur_positive--;
	aux->literal->type = CONSTANT;
	aux->literal->id = CTRUE;
	literal_list *tmp = aux->next;
	free(aux);
	aux = tmp;
      }
      p->pos_ple = NULL;
    }
  }
  return done;
}

*/


tnode *get_eple (tnode *s) {

  if (s == NULL)
    return s;
  if (s->type == PROP) {
    prop_node *p = find_prop(s->id);
    if (p->occur_positive == 0) {
      numearlyple++;
      s->type = CONSTANT;
      s->id = CFALSE;
    }
    else if (p->occur_negative == 0) {
      numearlyple++;
      s->type = CONSTANT;
      s->id = CTRUE;
    }
  }
  s->left = get_eple(s->left);
  s->right = get_eple(s->right);
  formulalist *aux = s->list;
  while (aux != NULL) {
    aux->formula = get_eple(aux->formula);
    aux = aux->next;
  }
  return s;
}

/* Implements early modal level pure literal elimination */

tnode *get_emlple (tnode *s) { 

  if (s == NULL)
    return s;
  if (s->type == PROP) {
    prop_node *p = find_prop(s->id);
    hml_clauses *clauses;
    if (s->polarity == 1) { //it is a positive literal, just check if there is a negative one at the same level
      HASH_FIND(hml,p->negative,&(s->mlevel),sizeof(int),clauses);
      if (clauses == NULL) {
	printf("\n Eliminating %s at ml %d",p->name,s->mlevel);
	numearlymlple++;
	emlple = 1;
	s->type = CONSTANT;
	s->id = CTRUE;
      }
    }
    else if (s->polarity == -1) {
      HASH_FIND(hml,p->positive,&(s->mlevel),sizeof(int),clauses);
      if (clauses == NULL) {
	printf("\n Eliminating ~%s at ml %d",p->name,s->mlevel);
	numearlymlple++;
	emlple = 1;
	s->type = CONSTANT;
	s->id = CFALSE;
      }
    }
  }
  s->left = get_emlple(s->left);
  s->right = get_emlple(s->right);
  formulalist *aux = s->list;
  while (aux != NULL) {
    aux->formula = get_emlple(aux->formula);
    aux = aux->next;
  }
  return s;
}


tnode *get_emlple2 (tnode *s) { 

  if (s != NULL) {
    if (s->left != NULL) {
      s->left = get_emlple2(s->left);
      if (s->type == BOX && s->left->type == CONSTANT && s->left->id == CTRUE) {
	s->id = CTRUE;
	s->type = CONSTANT;
	s->left = free_tree(s->left);
	numsimp++;
	//	printf("\n E_ML_PLE Truth Propagation, box true");
      }
      else if (s->type == DIAMOND && s->left->type == CONSTANT && s->left->id == CFALSE) {
	s->id = CFALSE;
	s->type = CONSTANT;
	s->left = free_tree(s->left);
	numsimp++;
	//printf("\n E_ML_PLE Truth Propagation, dia false");
      }
      else if (s->type == NEGATION && s->left->type == CONSTANT) {
	s->id = -s->left->id;
	s->type = CONSTANT;
	s->left = free_tree(s->left);
	numsimp++;
	//printf("\n E_ML_PLE Truth Propagation, neg const");
      }
      return s;
    }
    if (s->right != NULL) {
      s->right = get_emlple2(s->right);
    }
    if (s->list != NULL) {
      formulalist *aux = s->list;
      while (aux != NULL) {
	aux->formula = get_emlple2(aux->formula);
	if (aux->formula->type == CONSTANT &&
	    ((s->type == CONJUNCTION && aux->formula->id == CFALSE) ||
	     (s->type == DISJUNCTION && aux->formula->id == CTRUE))) {
	  if (s->type == CONJUNCTION && aux->formula->id == CFALSE)
	    s->id = CFALSE;
	  if (s->type == DISJUNCTION && aux->formula->id == CTRUE)
	    s->id = CTRUE;
	  s->type = CONSTANT;
	  s->list = free_formulalist(s->list);
	  s->list = NULL;
	  numsimp++;
	  //printf("\n E_ML_PLE Truth Propagation, disjunction, conjunction");
	  return s;
	}
	else aux = aux->next;
      }
    }
    if (s->type == PROP) {
      prop_node *p = find_prop(s->id);
      hml_clauses *clauses;
      if (s->polarity == 1) { //it is a positive literal, just check if there is a negative one at the same level
	HASH_FIND(hml,p->negative,&(s->mlevel),sizeof(int),clauses);
	if (clauses == NULL) {
	  //printf("\n Eliminating %s at ml %d",p->name,s->mlevel);
	  numearlymlple++;
	  emlple = 1;
	  s->type = CONSTANT;
	  s->id = CTRUE;
	}
      }
      else if (s->polarity == -1) {
	HASH_FIND(hml,p->positive,&(s->mlevel),sizeof(int),clauses);
	if (clauses == NULL) {
	  //printf("\n Eliminating ~%s at ml %d",p->name,s->mlevel);
	  numearlymlple++;
	  emlple = 1;
	  s->type = CONSTANT;
	  s->id = CFALSE;
	}
      }
    }
  }
  return s;
}

void finish_eple (void) {
  prop_node *p,*tmpp;
  
  HASH_ITER(hid,propsid,p,tmpp) {

    hml_clauses *clauses, *auxclauses;
    HASH_ITER(hml,p->positive,clauses,auxclauses) {
      HASH_DELETE(hml,p->positive,clauses);
      free(clauses);
    }
    HASH_ITER(hml,p->negative,clauses,auxclauses) {
      HASH_DELETE(hml,p->negative,clauses);
      free(clauses);
    }
    if (p->id != CFALSE && p->id != CTRUE && (p->occur_positive == 0 || p->occur_negative == 0)) {
      HASH_DELETE(hid,propsid,p);
      free_pnode(p);
    }
    else {
      p->occur_positive = 0;
      p->occur_negative = 0; 
    }
  }
}

tnode *input_simplification (tnode *root) {

  if (bnfsimp == ON) {
    root = get_bnf(root);
    print_out("BNF");
    int oldsimp;
    do {
      oldsimp = numsimp;
      root = get_bnfsimp(root);
      print_out("BNF Simplification");
      //	printf("\n Simplification steps: %d", numsimp - oldsimp);
    } while (numsimp > oldsimp);
    root = get_nnf(root,1);
    print_out("NNF");
  }
  if (nnfsimp == ON) {
    int oldsimp;
    do {
      oldsimp = numsimp;
      root = get_nnfsimp(root);
      print_out("NNF Simplification");
    } while (numsimp > oldsimp);
  }
  return root;
}


tnode *input_preprocessing(tnode *root) {

  if (linearise) {
    root = eliminate_double_implications(root,1);
  }
  
  root = get_nnf(root,1);
  print_out("NNF");

  root = input_simplification(root);

  if (early_ple == ON) {
    root = calculate_polarity(root,1,0); // the root is of positive polarity
    root = get_eple(root);
    finish_eple();
    print_out("Early PLE");
    root = input_simplification(root);
  }
  
  if (early_mlple == ON) {
    int oldnumearlymlple;

    do {
      oldnumearlymlple =  numearlymlple;
      emlple = 0;
      root = calculate_polarity(root,1,0); // the root is of positive polarity
      root = get_emlple2(root);
      finish_eple();
      print_out("Early ML_PLE");
      //      printf("\n Literals eliminated: %d",numearlymlple-oldnumearlymlple);
      if (nnfsimp || bnfsimp || (emlple && (numearlymlple-oldnumearlymlple > 20))) {
      	root = input_simplification(root);
      }
    } while (emlple != 0);
  }

  if (prenex == ON) {
    root=get_prenex(root);      
    print_out("Prenex");
    root = input_simplification(root);
    if (antiprenex > prenex) {
      root=get_antiprenex(root);
      print_out("Antiprenex");
      root = input_simplification(root);
    }
  }
  else if (antiprenex == ON) {
    root=get_antiprenex(root);
    print_out("Antiprenex");
    root = input_simplification(root);
    if (prenex > antiprenex) {
      root=get_prenex(root);
      print_out("Prenex");
      root = input_simplification(root);
    }
  }
	
  if (cnf == ON) {
	root = get_cnf(root);
	print_out("CNF");
	root = input_simplification(root);
  }
  else if (small_cnf == ON) {
    root = get_small_cnf(root);
    print_out("Small CNF");
    root = input_simplification(root);
  }
  
  formulasize = size_tree(root);
  return root;
}
