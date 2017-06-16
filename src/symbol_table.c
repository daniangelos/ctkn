#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "uthash.h"
#include "symbol_table.h"
#include "prover.h"
#include "tree.h"

extern int global;
extern int numprops;
extern int newtemp;
extern int numagents;
extern struct prop_node *propsname;
extern struct prop_node *propsid;
extern struct agent_node *agentsname; 
extern struct agent_node *agentsid; 

extern void print_out(char *);

void insert_clause_p_node (prop_node *p, int modal_level, int polarity, int idclause) {
  hml_clauses *clauses;
  clausesid *idclauses, *c;
  if (global == ON)
    modal_level = 1;
  HASH_FIND(hml,p->clauses,&modal_level,sizeof(int),clauses);
  if (clauses == NULL) {
    hml_clauses *new = malloc(sizeof(*new));
    new->ml = modal_level;
      new->occur_positive = 0;
      new->occur_negative = 0;
      new->positive = NULL;
      new->negative = NULL;
      HASH_ADD(hml,p->clauses,ml,sizeof(int),new);
      clauses = new;
  }
  if (polarity == POSITIVEP) {
    clauses->occur_positive++;
    HASH_FIND(hid,clauses->positive,&idclause,sizeof(int),c);
    if (c == NULL) {
      clausesid *new = malloc(sizeof(*new));
      new->id = idclause;
      HASH_ADD(hid,clauses->positive,id,sizeof(int),new);
    }
  }
  else {
    clauses->occur_negative++;
    HASH_FIND(hid,clauses->negative,&idclause,sizeof(int),c);
    if (c == NULL) {
      clausesid *new = malloc(sizeof(*new));
      new->id = idclause;
      HASH_ADD(hid,clauses->negative,id,sizeof(int),new);
    }
  }
}

void delete_clause_p_node (prop_node *p, int type, int modal_level, int idclause) {
  hml_clauses *clauses;
  clausesid *c;

  if (global == ON)
    modal_level = 1;
  if (type == POSITIVEP) {
    HASH_FIND(hml,p->clauses,&modal_level,sizeof(int),clauses);
    if (clauses != NULL) {
      HASH_FIND(hid,clauses->positive,&idclause,sizeof(int),c);
      if (c != NULL) {
	clauses->occur_positive--;
	HASH_DELETE(hid,clauses->positive,c);
	free(c);
	c = NULL;
	if (clauses == NULL) {
	  p->occur_positive = 0;
	  HASH_DELETE(hml,p->clauses,clauses);
	  free(clauses);
	  clauses = NULL;
	}
      }
    }
  }
  else {
    HASH_FIND(hml,p->clauses,&modal_level,sizeof(int),clauses);
    if (clauses != NULL) {
      HASH_FIND(hid,clauses->negative,&idclause,sizeof(int),c);
      if (c != NULL) {
	clauses->occur_negative--;
	HASH_DELETE(hid,clauses->negative,c);
	free(c);
	c = NULL;
	if (clauses == NULL) {
	  p->occur_negative = 0;
	  HASH_DELETE(hml,p->clauses,clauses);
	  free(clauses);
	  clauses = NULL;
	}
      }
    }
  }
}


void delete_clause_p_nodes (int modal_level, int idclause) {
  hml_clauses *clauses;
  clausesid *c;
  prop_node *p;

  for (p = propsid; p != NULL; p = p->hid.next) {
    HASH_FIND(hml,p->clauses,&modal_level,sizeof(int),clauses);
    if (clauses != NULL) {
      HASH_FIND(hid,clauses->positive,&idclause,sizeof(int),c);
      if (c != NULL) {
	clauses->occur_positive--;
	HASH_DELETE(hid,clauses->positive,c);
	free(c);
	c = NULL;
	if (clauses == NULL) {
	  HASH_DELETE(hml,p->clauses,clauses);
	  free(clauses);
	  clauses = NULL;
	}
      }
      else {
	HASH_FIND(hid,clauses->negative,&idclause,sizeof(int),c);
	if (c != NULL) {
	  clauses->occur_negative--;
	  HASH_DELETE(hid,clauses->negative,c);
	  free(c);
	  c = NULL;
	  if (clauses == NULL) {
	    HASH_DELETE(hml,p->clauses,clauses);
	    free(clauses);
	    clauses = NULL;
	  }
	}
      }
    }
  }
}


prop_node *create_p_node (char* name, int id) {
  prop_node *new = (prop_node *) malloc(sizeof(prop_node));
  new->name = name;
  new->id = id;
  new->occur = 1;
  new->occur_positive = 0;
  new->occur_negative = 0;
  new->positions = NULL;
  new->hmlpropsposition = NULL;
  new->clauses = NULL;
  return new;
}

agent_node *create_a_node (char* name, int id){
  agent_node *new = (agent_node *) malloc(sizeof(agent_node));
  new->name = name;
  new->id = id;
  new->occur = 1;
  new->five = 0;
  new->four = 0;
  new->t = 0;
  return new;
}

/* Creation of a node for new propositional symbols */
/* Type is needed here so that we can get a nice ordering */

prop_node *insert_pnew_node (int id, int type) {
  prop_node *p = NULL;
  if (id != numprops) {
    int len = snprintf(NULL, 0, "_t%d",id-numprops) + 1;
    char *s = (char *) malloc(len);
    len = snprintf(s, len, "_t%d",id-numprops);
    if (type == HIGH) 
      p = create_p_node(s,MAX_INT - id);
    else if (type == LOW)
      p = create_p_node(s,id);
    HASH_ADD(hid,propsid,id,sizeof(int),p);  
  }
  else { // this is for the new initial propositional symbol
    HASH_FIND(hid,propsid,&id,sizeof(int),p);
    if (p == NULL) {
      int len = snprintf(NULL, 0, "_t%d",0) + 1;
      char *s = (char *) malloc(len); 
      len = snprintf(s, len, "_t%d",0);
      p = create_p_node(s,MAX_INT - id);
      HASH_ADD(hid,propsid,id,sizeof(int),p);
    }
  }

  p->value_number = p->hid.hashv;
  return p;
}


prop_node *insert_pos_node (char *name) {
  int id;
  prop_node *p;
  HASH_FIND_STR(propsname,name,p);
  if (p) {
    //    id = p->id;
    p->occur++;
    free(name);
  }
  else {
    id = MAX_INT - newtemp++;
    p = create_p_node(name,id);
    HASH_ADD_KEYPTR(hh,propsname,p->name,strlen(p->name),p);
    HASH_ADD(hid,propsid,id,sizeof(int),p);
    p->value_number = p->hid.hashv;
  }

  return p;
}


/* Creation of a node for a propositional symbol occurring in the input */

prop_node *insert_p_node (char *name) {
  int id;
  prop_node *p;
  HASH_FIND_STR(propsname,name,p);
  if (p) {
    //id = p->id;
    p->occur++;
    free(name);
  }
  else {
    id = MAX_INT - numprops++;
    p = create_p_node(name,id);
    HASH_ADD_KEYPTR(hh,propsname,p->name,strlen(p->name),p);
    HASH_ADD(hid,propsid,id,sizeof(int),p);
    p->value_number = p->hid.hashv;
  }
  return p;
}



prop_node *insert_p_position(prop_node *p, tnode *position) {

  if (position != NULL) {
    hptr_nodes *positions = NULL;
    HASH_FIND(hptr,p->positions,&position,sizeof(tnode*),positions);
    //HASH_FIND_PTR(p->positions,&position,positions);
    if (positions == NULL) {
      hptr_nodes *new = malloc(sizeof(*new));
      new->node = position;
      new->deleted = 0;
      HASH_ADD(hptr,p->positions,node,sizeof(tnode*),new);
    }
  }
  return p;
}

/*tnode *remove_p_position(tnode *t) {
  prop_node *p = find_prop(t->id);
  if (p != NULL) {
    literal_list *aux = p->position;
    if (aux != NULL) {
      if (aux->literal == t) {
	p->position = p->position->next;
	free(aux);
      }
      else {
	int in = 0;
	while (!in && aux->next != NULL) {
	  if (aux->next->literal == t) {
	    literal_list *aux2 = aux->next;
	    aux->next = aux->next->next;
	    free(aux2);
	  }
	  else aux = aux->next;
	}
      }
    }
  }
}
*/

agent_node *insert_a_node (char *name) {
  int id;
  agent_node *a;
  HASH_FIND_STR(agentsname,name,a);
  if (a) {
    a->occur++;
    //id = a->id;
    free(name);
  }
  else {
    id = numagents++;
    a = create_a_node(name,id);
    HASH_ADD_KEYPTR(hh,agentsname,a->name,strlen(a->name),a);
    HASH_ADD(hid,agentsid,id,sizeof(int),a);
  }
  return a;
}

int sort_p_by_id (struct prop_node *a, struct prop_node *b) {
  if (a->id == b->id) return 0;
  return (a->id < b->id) ? -1 : 1;
}

int sort_p_by_name(struct prop_node *a, struct prop_node *b) {
  return strcmp(a->name,b->name);
}


int sort_a_by_id(struct agent_node *a, struct agent_node *b) {
  if (a->id == b->id) return 0;
  return (a->id < b->id) ? -1 : 1;
}

int sort_a_by_name(struct agent_node *a, struct agent_node *b) {
  return strcmp(a->name,b->name);
}

void print_positions (hptr_nodes *positions);

void print_symbols_tables(void) {

  agent_node *a;
  prop_node *p;

  for (a = agentsid; a != NULL; a = a->hid.next) {
    printf("\n Modal Operator: %s, id = %d, occurrences = %d, five = %d, four = %d, t = %d", a->name,a->id,a->occur,a->five,a->four,a->t);
  }
 
  for (p = propsid; p != NULL; p = p->hid.next) {
    printf("\n Propositional Symbol: %s, id = %d, vn = %u, occurrences = %d, positive = %d, negative = %d", p->name,p->id,p->value_number,p->occur,p->occur_positive,p->occur_negative);

    print_positions(p->positions);
    
    hml_props *auxml = NULL, *tmpaux = NULL;
    HASH_ITER(hml,p->hmlpropsposition,auxml,tmpaux) {
      printf("\n Modal Level %d, positive %d, negative %d:", auxml->ml, auxml->ml_occur_positive,auxml->ml_occur_negative);
      literal_list *auxpos = auxml->positive;
      printf("\n Positive occurrences: ");
      while (auxpos != NULL) {
	printf("%p ",auxpos->literal);
	auxpos = auxpos->next;
      }
      auxpos = auxml->negative;
      printf("\n Negative occurrences: ");
      while (auxpos != NULL) {
	printf("%p ",auxpos->literal);
	auxpos = auxpos->next;
      }
    }
    

    hml_clauses *aux = p->clauses;
    if (aux != NULL) {
      printf("\n Modal level %d, positive = %d, negative = %d:",aux->ml, aux->occur_positive, aux->occur_negative);
      printf("\n Clauses Positive: ");
      clausesid *aux2= aux->positive;
	while (aux2 != NULL) {
	  printf(" %d",aux2->id);
	  if (aux2->hid.next != NULL)
	    printf(", ");
	  aux2 = aux2->hid.next;
	}
	printf("\n Clauses Negative: ");    
	aux2 = aux->negative;
	
	while (aux2 != NULL) {
	  printf(" %d",aux2->id);
	  if (aux2->hid.next != NULL)
	    printf(", ");
	  aux2 = aux2->hid.next;
	}
	printf("\n");
	aux = aux->hml.next;
    }
  }
}



agent_node *find_agent (int id) {
  agent_node *a;
  HASH_FIND(hid,agentsid,&id,sizeof(int),a);
  return a;
}

void print_agent (int id) {
  agent_node *a;
  HASH_FIND(hid,agentsid,&id,sizeof(int),a);
  printf("%s",a->name);
}

prop_node *find_prop (int id) {
  prop_node *p;
  HASH_FIND(hid,propsid,&id,sizeof(int),p);
  return p;
}

void print_prop (int id) {
  prop_node *p;
  if (id < 0)
    id = -id;
  HASH_FIND(hid,propsid,&id,sizeof(int),p);
  if (p != NULL)
    printf("%s",p->name);
  else printf("problem");
}

void print_positions (hptr_nodes *positions) {
  hptr_nodes *aux = NULL, *auxtmp = NULL;
  if (positions != NULL) {
    printf("\n Positions (new):");
    HASH_ITER(hptr,positions,aux,auxtmp){
      if (!aux->deleted) 
	printf(" %p",aux->node);
      else
	printf(" %p (del)",aux->node);
    }
  }
}

hml_props *clean_p_positions(hml_props *mlpositions) {
  hml_props *aux = NULL, *auxtmp = NULL;
  HASH_ITER(hml,mlpositions,aux,auxtmp){
    literal_list *auxlist = aux->positive;
    while (auxlist != NULL) {
      literal_list *auxlist2 = auxlist;
      auxlist = auxlist->next;
      free(auxlist2);
    }
    auxlist = aux->negative;
    while (auxlist != NULL) {
      literal_list *auxlist2 = auxlist;
      auxlist = auxlist->next;
      free(auxlist2);
    }
    HASH_DELETE(hml,mlpositions,aux);
    free(aux);
  }
  return mlpositions;
}

hptr_nodes *clean_c_positions(hptr_nodes *positions) {
  hptr_nodes *aux = NULL, *auxtmp = NULL;
  HASH_ITER(hptr,positions,aux,auxtmp){
    HASH_DELETE(hptr,positions,aux);
    free(aux);
  }
  return positions;
}

void clean_positions(void) {
  prop_node *aux = NULL, *auxtmp = NULL;
  HASH_ITER(hid,propsid,aux,auxtmp){
    if (aux->id == CTRUE || aux->id == CFALSE || aux->id == CSTART)
	aux->positions = clean_c_positions(aux->positions);
    else {
      aux->occur_positive = 0;
      aux->occur_negative = 0;
      aux->hmlpropsposition = clean_p_positions(aux->hmlpropsposition);
    }
  }
}


int find_p_position(tnode *position) {
  if (position->type != CONSTANT)
    return 0;
  prop_node *p = find_prop(position->id);
  if (p == NULL)
    return 0;
  hptr_nodes *aux = NULL;
  HASH_FIND(hptr,p->positions,&position,sizeof(tnode*),aux);
  if (aux == NULL)
    return 0;
  return 1;
}

int compare_positions(hptr_nodes *p1, hptr_nodes *p2) {
  if (p1->node == NULL)
    return 0;
  else if (p2->node != NULL)
    return p1->node->mlevel < p2->node->mlevel;
  else return 0;
}

hptr_nodes *sort_positions(hptr_nodes *positions) {
  HASH_SRT(hptr,positions,compare_positions);
  return positions;
}

void clear_hashes (void) {
  HASH_CLEAR(hh,propsname);
  HASH_CLEAR(hh,agentsname);
}


void free_clausesid(clausesid *clauses) {
  clausesid *clause, *tmp;
  HASH_ITER(hid,clauses,clause,tmp) {
    HASH_DELETE(hid,clauses,clause);
    free(clause);
  }
}

void free_hml_clauses (hml_clauses *hclauses) {
  hml_clauses *clauses, *tmp;

  HASH_ITER(hml,hclauses,clauses,tmp) {
    if (clauses != NULL) {
      free_clausesid(clauses->positive);
      free_clausesid(clauses->negative);
      HASH_DELETE(hml,hclauses,clauses);
      free(clauses);
      clauses = NULL;
    }
  }
}

prop_node *free_pnode(prop_node *p) {
  if (p != NULL) {
    if (p->name != NULL)
      free(p->name);
    free_hml_clauses(p->clauses);
    free(p);
    p = NULL;
  }
  return p;
}

void free_anode(agent_node *a) {
  if (a != NULL) {
    if (a->name != NULL)
      free(a->name);
    free(a);
  }
}

void clear_all (void) {
  prop_node *p,*tmpp;
  
  HASH_ITER(hid,propsid,p,tmpp) {
    HASH_DELETE(hid,propsid,p);
    p=free_pnode(p);
  }

  HASH_CLEAR(hid,propsid);
  free(propsid);
  propsid = NULL;

  agent_node *a,*tmpa;
  
  HASH_ITER(hid,agentsid,a,tmpa) {
    HASH_DELETE(hid,agentsid,a);
    if (a != NULL)
      free_anode(a);
  }

  HASH_CLEAR(hid,agentsid);
  free(agentsid);
  agentsid = NULL;

}

void symbol_table_init(void) {

  prop_node *p;
  int id;

  id = CTRUE;
  int len = snprintf(NULL, 0, "_true") + 1;
  char *s1 = (char *) malloc(len); 
  len = snprintf(s1, len, "_true");
  p = create_p_node(s1,id);
  HASH_ADD(hid,propsid,id,sizeof(int),p);
  p->value_number = p->hid.hashv;
  p->occur = 0;
  p->positions = NULL;
  
  id = CFALSE;
  len = snprintf(NULL, 0, "_false") + 1;
  char *s2 = (char *) malloc(len); 
  len = snprintf(s2, len, "_false");
  p = create_p_node(s2,id);
  HASH_ADD(hid,propsid,id,sizeof(int),p);
  p->value_number = p->hid.hashv;
  p->occur = 0;
  p->positions = NULL;
  
  id = CSTART;
  len = snprintf(NULL, 0, "_start") + 1;
  char *s3 = (char *) malloc(len); 
  len = snprintf(s3, len, "_start");
  p = create_p_node(s3,id);
  HASH_ADD(hid,propsid,id,sizeof(int),p);
  p->value_number = p->hid.hashv;
  p->occur = 0;
  p->positions = NULL;
}
