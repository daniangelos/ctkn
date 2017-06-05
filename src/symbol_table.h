#include <string.h>
#include <stdlib.h>  /* malloc */
#include "uthash.h"

#define MAX_INT 2147483646

// Polarity of propositional symbols

#define POSITIVEP    60
#define NEGATIVEP    61

// Classification of clauses

#define POSITIVEC     1
#define NEGATIVEC    -1
#define MIXEDC        0

// Ordering

#define HIGH  1
#define LOW   0

typedef struct literalslist {
  int literal;
  struct literalslist *next;
} literalslist;

typedef struct tclause {
  int number;
  int type;
  int size;
  int max_literal;
  int modal_level;
  int agent;
  int class;
  int left;
  int propagated;
  struct literalslist *right;
  struct justification *just;
  struct justification *deleted;
} tclause;


typedef struct clauseslist {
  int clause;
  struct clauseslist *next;
} clauseslist;

typedef struct justification {
  int rule;
  struct clauseslist *parents;
  struct literalslist *literals;
} justification;

typedef struct literal_list {
  struct tnode *literal;
  struct literal_list *next;
} literal_list;

typedef struct clausesid {
  int id;
  UT_hash_handle hid;
} clausesid;

typedef struct hml_clauses {
  int ml;
  int occur_positive;
  int occur_negative;
  clausesid *clauses;
  UT_hash_handle hml;
} hml_clauses;

typedef struct prop_node {
  char *name;
  int id;
  int occur;
  int occur_positive;
  int occur_negative;
  literal_list *pos_ple;
  literal_list *neg_ple;
  unsigned int value_number;
  hml_clauses *positive;
  hml_clauses *negative;
  UT_hash_handle hh;
  UT_hash_handle hid;
} prop_node;

typedef struct agent_node {
  char *name; //this is the concat of name and index of the modal operator
  int id;
  int occur;
  int five;
  int four;
  UT_hash_handle hh;
  UT_hash_handle hid;
} agent_node;

