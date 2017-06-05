#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "uthash.h"
#include "symbol_table.h"
#include "prover.h"
              
extern int numprops;
extern int numagents;
extern struct prop_node *propsname;
extern struct prop_node *propsid;
extern struct agent_node *agentsname; 
extern struct agent_node *agentsid; 

void insert_clause_p_node (prop_node *p, int modal_level, int polarity, int idclause) {
  hml_clauses *clauses;
  clausesid *c;
  if (polarity == POSITIVEP) {
    HASH_FIND(hml,p->positive,&modal_level,sizeof(int),clauses);
    if (clauses == NULL) {
      hml_clauses *new = malloc(sizeof(*new));
      new->ml = modal_level;
      new->occur_positive = 1;
      new->occur_negative = 0;
      new->clauses = NULL;
      HASH_ADD(hml,p->positive,ml,sizeof(int),new);
      clauses = new;
    }
    else clauses->occur_positive++;
  }
  else {
    HASH_FIND(hml,p->negative,&modal_level,sizeof(int),clauses);
    if (clauses == NULL) {
      hml_clauses *new = malloc(sizeof(*new));
      new->ml = modal_level;
      new->occur_positive = 0;
      new->occur_negative = 1;
      new->clauses = NULL;
      HASH_ADD(hml,p->negative,ml,sizeof(int),new);
      clauses = new;
    }
    else clauses->occur_negative++;
  }
  HASH_FIND(hid,clauses->clauses,&idclause,sizeof(int),c);
  if (c == NULL) {
    clausesid *new = malloc(sizeof(*new));
    new->id = idclause;
    HASH_ADD(hid,clauses->clauses,id,sizeof(int),new);
  }
}

void delete_clause_p_node (prop_node *p, int type, int modal_level, int idclause) {
  hml_clauses *clauses;
  clausesid *c;

  if (type == POSITIVEP) {
    HASH_FIND(hml,p->positive,&modal_level,sizeof(int),clauses);
    if (clauses != NULL) {
      HASH_FIND(hid,clauses->clauses,&idclause,sizeof(int),c);
      if (c != NULL) {
	clauses->occur_positive--;
	HASH_DELETE(hid,clauses->clauses,c);
	free(c);
	c = NULL;
	if (clauses->clauses == NULL) {
	  HASH_DELETE(hml,p->positive,clauses);
	  free(clauses);
	  clauses = NULL;
	}
      }
    }
  }
  else {
    HASH_FIND(hml,p->negative,&modal_level,sizeof(int),clauses);
    if (clauses != NULL) {
      HASH_FIND(hid,clauses->clauses,&idclause,sizeof(int),c);
      if (c != NULL) {
	clauses->occur_negative--;
	HASH_DELETE(hid,clauses->clauses,c);
	free(c);
	c = NULL;
	if (clauses->clauses == NULL) {
	  HASH_DELETE(hml,p->negative,clauses);
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
    HASH_FIND(hml,p->positive,&modal_level,sizeof(int),clauses);
    if (clauses != NULL) {
      HASH_FIND(hid,clauses->clauses,&idclause,sizeof(int),c);
      if (c != NULL) {
	clauses->occur_positive--;
	HASH_DELETE(hid,clauses->clauses,c);
	free(c);
	c = NULL;
	if (clauses->clauses == NULL) {
	  HASH_DELETE(hml,p->positive,clauses);
	  free(clauses);
	  clauses = NULL;
	}
      }
    }
    else {
      HASH_FIND(hml,p->negative,&modal_level,sizeof(int),clauses);
      if (clauses != NULL) {
	HASH_FIND(hid,clauses->clauses,&idclause,sizeof(int),c);
	if (c != NULL) {
	  clauses->occur_negative--;
	  HASH_DELETE(hid,clauses->clauses,c);
	  free(c);
	  c = NULL;
	  if (clauses->clauses == NULL) {
	    HASH_DELETE(hml,p->negative,clauses);
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
  new->pos_ple = NULL;
  new->neg_ple = NULL;
  new->positive = NULL;
  new->negative = NULL;
  return new;
}

agent_node *create_a_node (char* name, int id){
  agent_node *new = (agent_node *) malloc(sizeof(agent_node));
  new->name = name;
  new->id = id;
  new->occur = 1;
  new->five = 0;
  new->four = 0;
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

/* Creation of a node for a propositional symbol occurring in the input */

prop_node *insert_p_node (char *name) {
  int id;
  prop_node *p;
  HASH_FIND_STR(propsname,name,p);
  if (p) {
    id = p->id;
    p->occur++;
    free(name);
  }
  else {
    id = MAX_INT - numprops++;
    p = create_p_node(name,id);
    HASH_ADD_KEYPTR(hh,propsname,p->name,strlen(p->name),p);
    HASH_ADD(hid,propsid,id,sizeof(int),p);  
  }
  p->value_number = p->hid.hashv;
  return p;
}

agent_node *insert_a_node (char *name) {
  int id;
  agent_node *a;
  HASH_FIND_STR(agentsname,name,a);
  if (a) {
    a->occur++;
    id = a->id;
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

void print_symbols_tables(void) {

  agent_node *a;
  prop_node *p;

  for (a = agentsid; a != NULL; a = a->hid.next) {
    printf("\n Modal Operator: %s, id = %d, occurrences = %d, five = %d, four = %d", a->name,a->id,a->occur,a->five,a->four);
  }
 
  for (p = propsid; p != NULL; p = p->hid.next) {
    printf("\n Propositional Symbol: %s, id = %d, vn = %u, occurrences = %d, positive = %d, negative = %d", p->name,p->id,p->value_number,p->occur,p->occur_positive,p->occur_negative);
    
    printf("\n Clauses Positive: ");
    hml_clauses *aux = p->positive;
    
    while (aux != NULL) {
      printf("\n Modal level %d, positive = %d, negative = %d\n Clauses: ",aux->ml, aux->occur_positive, aux->occur_negative);
     
      clausesid *aux2= aux->clauses;
      while (aux2 != NULL) {
	printf(" %d",aux2->id);
	if (aux2->hid.next != NULL)
	  printf(", ");
	aux2 = aux2->hid.next;
      }
      printf("\n");
      aux = aux->hml.next;
    }
  
    printf("\n Clauses Negative: ");
    
    aux = p->negative;
    while (aux != NULL) {
      printf("\n Modal level %d, positive = %d, negative = %d\n Clauses: ",aux->ml, aux->occur_positive, aux->occur_negative);

      clausesid *aux2 = aux->clauses;
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

void free_hml_clauses (hml_clauses *clauses) {
  hml_clauses *tmpc1, *tmpc2;
  clausesid *tmpc3, *tmpc4;
  
  if (clauses != NULL) {
    HASH_ITER(hml,clauses,tmpc1,tmpc2) {
      HASH_ITER(hid,tmpc1->clauses,tmpc3,tmpc4) {
	HASH_DELETE(hid,tmpc1->clauses,tmpc3);
	free(tmpc3);
      }
      HASH_DELETE(hml,clauses,tmpc1);
      free(tmpc1);
    }
  }
}

void free_pnode(prop_node *p) {
  if (p != NULL) {
    if (p->name != NULL)
      free(p->name);
    free_hml_clauses(p->positive);
    free_hml_clauses(p->negative);
    free(p);
  }
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
    free_pnode(p);
  }

  HASH_CLEAR(hid,propsid);
  free(propsid);

  agent_node *a,*tmpa;
  
  HASH_ITER(hid,agentsid,a,tmpa) {
    HASH_DELETE(hid,agentsid,a);
    if (a != NULL)
      free_anode(a);
  }

  HASH_CLEAR(hid,agentsid);
  free(agentsid);

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
  
  id = CFALSE;
  len = snprintf(NULL, 0, "_false") + 1;
  char *s2 = (char *) malloc(len); 
  len = snprintf(s2, len, "_false");
  p = create_p_node(s2,id);
  HASH_ADD(hid,propsid,id,sizeof(int),p);
  p->value_number = p->hid.hashv;
  
  id = CSTART;
  len = snprintf(NULL, 0, "_start") + 1;
  char *s3 = (char *) malloc(len); 
  len = snprintf(s3, len, "_start");
  p = create_p_node(s3,id);
  HASH_ADD(hid,propsid,id,sizeof(int),p);
  p->value_number = p->hid.hashv;
}
