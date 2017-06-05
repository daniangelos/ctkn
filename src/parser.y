/* 
 * Parser for modal formulae
*/

%error-verbose
 //%locations
%debug
%defines
%glr-parser
%expect 2
%pure-parser
%code requires {
#include "tree.h"
  
  extern tnode *root;
  extern tnode *create_tnode(int type, int id, int mdepth, tnode *left, tnode *right, formulalist *list);
  formulalist *tree_to_list(int type, tnode *left, tnode *right);
  
  char *getBoxName (char *);

  typedef struct axiom_list {
    int axiom;
    struct axiom_list *next;
  } axiom_list;

  typedef struct prop_list {
    char *prop;
    struct prop_list *next;
  } prop_list;

  void process_ordering(prop_list *props);
}


%{
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "prover.h"
#include "uthash.h"
#include "symbol_table.h"

  /* flex functions */

  extern int yylex () ;
  extern char *yytext;
  extern FILE *yyin;

  /* Max stack size for parsing */
  
#define YYMAXDEPTH 136854775807
    
  /* symbol table functions in symbol_table.c" */

#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))

  /* prototype for the error function */

  void yyerror (char const *s);
 
  /* global variables from tokenizer.l */

  extern int numtokens;
  extern int numlines;
  extern int numcolumns;

  /* global variables for parser.y */

  int numerrors = 0;  
  int numagents = 1;
  int numprops = 2; // 1 and -1 are reserved for CTRUE an CFALSE, 0 is reserved for CSTART
  int inputsize = 0;

  /* global variables for the prover */

  extern int configfile;
  extern int verbose;
  extern int print_deleted;
  extern int print_generated;
  extern int print_model;
  extern int print_proof;
  extern int ml_prover;
  extern int bnfsimp;
  extern int nnfsimp;
  extern int normal_renaming;
  extern int mild_renaming;             
  extern int strong_renaming;
  extern int modal_positive;
  extern int modal_negative;
  extern int conjunction_renaming;
  extern int strong_modal_positive;
  extern int strong_modal_negative;
  extern int improved_snf_plus;
  extern int prenex;
  extern int antiprenex;
  extern int cnf;
  extern int small_cnf;
  extern int unit;
  extern int lhs_unit;
  extern int ple;
  extern int mle;
  extern int early_ple;
  extern int early_mlple;
  extern int ml_ple;
  extern int propagate_box;
  extern int propagate_dia;
  extern int satmle;
  extern int literal_selection;
  extern int clause_selection;
  extern int forward_subsumption;
  extern int backward_subsumption;
  extern int sos_subsumption;
  extern int full_check_repeated;
  extern int maxproof;
  extern int global;
  extern int parallel_prover;
  extern int processors;
  extern int ires;
  extern int mres;
  extern int gen2;
  extern int populate_usable;

  extern prop_node *find_prop (int id);
  extern prop_node *create_p_node (char *name; int id;);
  extern agent_node *create_a_node (char *name; int id;);

  extern agent_node *insert_a_node (char *name);
  extern prop_node *insert_p_node (char *name);

  struct prop_node *propsname = NULL;
  struct prop_node *propsid = NULL;    /* important! initialize to NULL */
  struct agent_node *agentsname = NULL; 
  struct agent_node *agentsid = NULL;    
%}

%union{
  char *strValue;
  tnode *tnode;
  formulalist *formulalist;
  axiom_list *axiom_list;
  prop_list *prop_list;
}

%left TIFF 
%left TIMPLY 
%left TONLYIF 
%left TOR 
%left TAND
%right TNOT 
%right <strValue> TPOSSIBLE TNECESSARY
%right <strValue> TOBOX TODIA "modal operator delimiter (open)"
%left TCBOX TCDIA "modal operator delimiter (close)"

%token TIFF "double implication"
%token TIMPLY "implication"
%token TONLYIF "only if"
%token TOR "disjunction"
%token TAND "conjunction"
%token TNOT "negation"
%token TPOSSIBLE "diamond operator"
%token TNECESSARY "box operator"

%token <strValue> TNAME "identifier"
%token <strValue> TNUMBER "number"
%token <strValue> TSTART TTRUE TFALSE  "constant"

%token TSET "set option command"
%token TDOT "."
%token TCOMMA ","
%token TCLAUSES  "clauses"
%token TFORMULAS "formulas"
%token TSOS "sos"
%token TUSABLE "usable"
%token TEND "end of list"
%token TLPAREN "("
%token TRPAREN ")"

%type <strValue> modal_arg
%type <tnode> formula
%type <tnode> formulas
%type <tnode> clauses
%type <tnode> initial_clause
%type <tnode> literal_clause
%type <tnode> modal_clause
%type <tnode> disjunction_literals
%type <tnode> sets
%type <tnode> formulas_sets_tail
%type <tnode> clauses_sets_tail
%type <tnode> proposition
%type <tnode> literal

%type <axiom_list> axioms
%type <prop_list> propositions_list

%%

file : declarations sets
     {
       root = $2;
     }
     ;

declarations : // it can be empty
             | TSET TLPAREN option TRPAREN TDOT declarations
             | error TDOT declarations { numerrors++; }
             ;

option : TNAME
       {
	 if (!configfile) {
	   char *option = strdup($1);
	   // strategies that can be combined with others
	   if (!strcmp(option,"unit")) unit = ON;
	   else if (!strcmp(option,"lhs_unit")) {unit = ON; lhs_unit = ON;}
	   else if (!strcmp(option,"mlple")) ml_ple = ON;
	   else if (!strcmp(option,"ple")) ple = ON;
	   else if (!strcmp(option,"mle")) mle = ON;
	   else if (!strcmp(option,"satmle")) satmle = ON;
	   else if (!strcmp(option,"early_ple")) early_ple = ON;
	   else if (!strcmp(option,"early_mlple")) early_mlple = ON;
	   else if (!strcmp(option,"propbox")) propagate_box = ON;
	   else if (!strcmp(option,"propdia")) propagate_dia = ON;
	   // subsumption
	   else if (!strcmp(option,"forward")) forward_subsumption = ON;
	   else if (!strcmp(option,"backward")) backward_subsumption = ON;
	   else if (!strcmp(option,"sos_subsumption")) sos_subsumption = ON;
	   else if (!strcmp(option,"full_check_repeated")) full_check_repeated = ON;
	   // clause selection
	   else if (!strcmp(option,"newest")) clause_selection = NEWEST;
	   else if (!strcmp(option,"oldest")) clause_selection = OLDEST;
	   else if (!strcmp(option,"shortest")) clause_selection = SHORTEST;
	   else if (!strcmp(option,"smallest")) clause_selection = SMALLEST;
	   else if (!strcmp(option,"greatest")) clause_selection = GREATEST;
	   // literal selection
	   else if (!strcmp(option,"ordered")) literal_selection = ORDERED;
	   else if (!strcmp(option,"negative")) literal_selection = NEGATIVE;
	   else if (!strcmp(option,"positive")) literal_selection = POSITIVE;
	   else if (!strcmp(option,"negative_ordered")) literal_selection = NEGORDERED;
	   else if (!strcmp(option,"ordered_selection")) literal_selection = ORDSELECT;
	   // normal form
	   else if (!strcmp(option,"bnfsimp")) {bnfsimp = ON; nnfsimp = ON;}
	   else if (!strcmp(option,"nnfsimp")) nnfsimp = ON;
	   else if (!strcmp(option,"normal_renaming")) {normal_renaming = ON; mild_renaming = OFF; strong_renaming = OFF;}
	   else if (!strcmp(option,"limited_reuse_renaming")) {normal_renaming = OFF; mild_renaming = ON; strong_renaming = OFF;}
	   else if (!strcmp(option,"extensive_reuse_renaming")) {normal_renaming = OFF; mild_renaming = OFF; strong_renaming = ON;}
	   else if (!strcmp(option,"conjunct_renaming")) conjunction_renaming = ON;
	   else if (!strcmp(option,"snf+")) modal_positive = ON;
	   else if (!strcmp(option,"snf-")) modal_negative = ON;
	   else if (!strcmp(option,"snf++")) strong_modal_positive = ON;
	   else if (!strcmp(option,"snf--")) strong_modal_negative = ON;
	   else if (!strcmp(option,"improved_extended_snf")) improved_snf_plus = ON;
	   else if (!strcmp(option,"prenex")) prenex = antiprenex + 1;
	   else if (!strcmp(option,"antiprenex")) antiprenex = prenex + 1;
	   else if (!strcmp(option,"cnf")) cnf = ON;
	   else if (!strcmp(option,"small_cnf")) small_cnf = ON;
	   // inference rules
	   else if (!strcmp(option,"ires")) ires = ON;
	   else if (!strcmp(option,"mres")) mres = ON;
	   else if (!strcmp(option,"gen2")) gen2 = ON;
	   // prover modes
	   else if (!strcmp(option,"global")) global = ON;
	   else if (!strcmp(option,"local")) ml_prover = ON;
	   // printing options
	   else if (!strcmp(option,"print_deleted")) print_deleted = ON;
	   else if (!strcmp(option,"print_proofs")) print_proof = ON;
	   else if (!strcmp(option,"print_generated")) print_generated = ON;
	   else if (!strcmp(option,"print_model")) print_model = ON;
	   else {
	     yyerror(option);
	     numerrors++;
	   }
	   free(option);
	 }
	 free($1);

       }
       | TNAME TCOMMA TNUMBER
       {
       	 if (!configfile) {
	   char *option = strdup($1);
	   if (!strcmp(option,"verbosity")) verbose = atoi($3);
	   else if (!strcmp(option,"maxproof")) maxproof = atoi($3);
	   else if (!strcmp(option,"parallel")) {parallel_prover = ON; processors = atoi($3);}
	   free(option);
	 }
	 free($1);
	 free($3);
       }
       | TNAME TCOMMA propositions_list
       {
	 if (!configfile) {
	   char *option = strdup($1);
	   if (!strcmp(option,"order")) {
	     process_ordering($3);
	   }
	   else if (!strcmp(option,"populate_usable")) {
	     prop_list *populate = $3;
	     if (!strcmp(populate->prop,"non_negative")) 
	       populate_usable = NON_NEGATIVE;
	     else if (!strcmp(populate->prop,"non_positive"))
	       populate_usable = NON_POSITIVE;
	     if (!strcmp(populate->prop,"negative")) 
	       populate_usable = NEGATIVE;
	     else if (!strcmp(populate->prop,"positive"))
	       populate_usable = POSITIVE;
	     else if (!strcmp(populate->prop,"max_lit_positive"))
	       populate_usable = MAX_LIT_POSITIVE;
	     else if (!strcmp(populate->prop,"max_lit_negative"))
	       populate_usable = MAX_LIT_NEGATIVE;
	     free($3);
	   }
	 free($1);
	 free(option);
	 }
       }
       | TNECESSARY modal_arg TCOMMA axioms
       {
	 if (!configfile) {
	   agent_node *a;
	   char *pname, *index;
	   pname = strdup($1);
	   if ($2 != NULL) {index = strdup($2);} else index=NULL;
	   char * s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	   sprintf(s, "%s %s", pname, index);
	   a = insert_a_node(s);
	   a->occur -= 1;

	   axiom_list *l = $4;
	 
	   while (l != NULL) {
	     if (l->axiom == FIVE)
	       a->five = 1;
	     else if (l->axiom == FOUR)
	       a->four = 1;
	     l = l->next;
	   }
	   free($1);
	   if (index != NULL) free($2);
	 }
       }
       | TNECESSARY TCOMMA axioms
       {
	 if (!configfile) {
	   agent_node *a;
	   char *pname;
	   pname = strdup($1);
	   a = insert_a_node(pname);
	   a->occur -= 1;
	 
	   axiom_list *l = $3;
	 
	   while (l !=NULL) {  
	     if (l->axiom == FIVE)
	       a->five = 1;
	     else if (l->axiom == FOUR)
	       a->four = 1;
	     l = l->next;
	   }
	   free($1);
	 }
       }
       | error {numerrors++;}
       ;

axioms : {$$=NULL;}
       | TNAME
       {
	 if (!configfile) {
	   char *name;
	   axiom_list *a = malloc(sizeof(axiom_list));
	   name = strdup($1);
	   if (!strcmp(name,"five"))
	     a->axiom = FIVE;
	   else if (!strcmp(name,"four"))
	     a->axiom = FOUR;
	   else a->axiom = 0;
	   a->next = NULL;
	   $$ = a;
	   free($1);
	 }
       }
       | TNAME TCOMMA axioms {
	 if (!configfile) {
	   char *name;
	   axiom_list *a = malloc(sizeof(axiom_list));
	   name = strdup($1);
	   if (!strcmp(name,"five"))
	     a->axiom = FIVE;
	   else if (!strcmp(name,"four"))
	     a->axiom = FOUR;
	   else a->axiom = 0;
	   a->next = $3;
	   $$ = a;
	   free($1);
	 }
      }
      ;

sets : {$$ = NULL;}
     | TSOS TLPAREN TFORMULAS TRPAREN TDOT formulas_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=SOS;
	 $$->mdepth = $6->mdepth;
       }
     }
     | TUSABLE TLPAREN TFORMULAS TRPAREN TDOT formulas_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=USABLE;
	 $$->mdepth = $6->mdepth;
       }
     }
     | TSOS TLPAREN TCLAUSES TRPAREN TDOT clauses_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=SOS;
	 $$->mdepth = $6->mdepth;
       }
     }
     | TUSABLE TLPAREN TCLAUSES TRPAREN TDOT clauses_sets_tail
     {
       $$ = $6;
       if ($$ != NULL) {
	 $$->id=USABLE;
	 $$->mdepth = $6->mdepth;
       }
     }
     ;

formulas_sets_tail : formulas TEND TDOT sets
                  {      
		    int mdepth;
		    if ($4 != NULL)
		      mdepth = MAX($1->mdepth,$4->mdepth);
		    else
		      mdepth=$1->mdepth;
		    tnode *new = create_tnode(SETF,SETF,mdepth,$1,$4,NULL);
		    $$ = new;
		   }
                  ;

clauses_sets_tail : clauses TEND TDOT sets
                  {
		    int mdepth;
		    if ($4 != NULL)
		      mdepth = MAX($1->mdepth,$4->mdepth);
		    else
		      mdepth=$1->mdepth;
		    tnode *new = create_tnode(SETC,SETC,mdepth,$1,$4,NULL);
		    $$ = new;
		  }
                  ;

clauses : {$$ = NULL;}
        | initial_clause TDOT clauses
	{
	  if ($3 != NULL) {
	    int mdepth = MAX($1->mdepth,$3->mdepth);
	    formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	    $$ = new;
	  }
	  else $$ = $1;
	}
	| literal_clause TDOT clauses
	{
	  if ($3 != NULL) {
	    int mdepth = MAX($1->mdepth,$3->mdepth);
	    formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	    $$ = new;
	  }
	  else $$ = $1;
	}
	| modal_clause TDOT clauses
	{
	  if ($3 != NULL) {
	    int mdepth = MAX($1->mdepth,$3->mdepth);
	    formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	    $$ = new;
	  }
	  else $$ = $1;
	}
        | error TDOT clauses {numerrors++;}
        ;

initial_clause : TSTART TIMPLY disjunction_literals
                 {
		   inputsize += 2;
	           tnode *newst = create_tnode(CONSTANT,CSTART,0,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,CONJUNCTION,$3->mdepth,newst,$3,NULL);
		   $$ = new;
                 }
                 ;

literal_clause : TTRUE TIMPLY disjunction_literals %prec TIMPLY
                 {
		   inputsize += 2;
	           tnode *newconst = create_tnode(CONSTANT,CTRUE,0,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,IMPLICATION,$3->mdepth,newconst,$3,NULL);
		   $$ = new;
                 }
                 | disjunction_literals
		 {
	           tnode *newconst = create_tnode(CONSTANT,CTRUE,0,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,IMPLICATION,$1->mdepth,newconst,$1,NULL);
		   $$ = new;
		 }
                 ;

// It looks awful, but I have tried to factor this and I get an ambiguous grammar.

modal_clause : literal TIMPLY TNECESSARY modal_arg literal
               {
		inputsize += 2;
	        agent_node *a;
                char *pname, *index;
                pname = strdup($3);
                if ($4 !=NULL) {index = strdup($4);} else index=NULL;
                char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	        sprintf(s, "%s %s", pname, index);
	        a=insert_a_node(s);
	        tnode *new = create_tnode(BOX,a->id,$5->mdepth+1,$5,NULL,NULL);
		int md = MAX($5->mdepth+1,$1->mdepth);
		tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		$$ = newimp;
		free($3);
		if (index != NULL) free($4);
	       }
               | literal TIMPLY TNECESSARY literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname;
		 pname = strdup($3);
		 a=insert_a_node(pname);
		 tnode *new = create_tnode(BOX,a->id,$4->mdepth+1,$4,NULL,NULL);
		 int md = MAX($4->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
		 free($3);
	       }
               | literal TIMPLY TOBOX modal_arg TCBOX literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *index;
		 if ($4 !=NULL) {index = strdup($4);} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
		 sprintf(s, "box %s", index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(BOX,a->id,$6->mdepth+1,$6,NULL,NULL);
		 int md = MAX($6->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
		 if (index != NULL) free($4);
	       }
               | literal TIMPLY TOBOX TCBOX literal
	       {
		 inputsize += 2;
		 agent_node *a;
		 char * s = malloc(snprintf(NULL, 0, "box") + 1);
		 sprintf(s, "box");	  
		 a=insert_a_node(s);
		 tnode *new = create_tnode(BOX,a->id,$5->mdepth+1,$5,NULL,NULL);
		 int md = MAX($5->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
	       }
               | literal TIMPLY TPOSSIBLE modal_arg literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname, *index;
		 pname = getBoxName(strdup($3));
		 if ($4 !=NULL) {index = strdup($4);} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
		 sprintf(s, "%s %s", pname, index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,$5->mdepth + 1,$5,NULL,NULL);
		 int md = MAX($5->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
		 free($3);
		 if (index != NULL) free($4);
	       }
               | literal TIMPLY TPOSSIBLE literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname;
		 pname = getBoxName(strdup($3));
		 a = insert_a_node(pname);
		 tnode *new = create_tnode(DIAMOND,a->id,$4->mdepth + 1,$4,NULL,NULL);
		 int md = MAX($4->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
		 free($3);
	       }
               | literal TIMPLY TODIA modal_arg TCDIA literal
	       { 
		 inputsize += 2;
		 agent_node *a;
		 char *index;
		 if ($4 !=NULL) {index = strdup($4);} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
		 sprintf(s, "box %s", index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,$6->mdepth+1,$6,NULL,NULL);
		 int md = MAX($6->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
		 if (index != NULL) free($4);
	       }
               | literal TIMPLY TODIA TCDIA literal
	       {
		 inputsize += 2;
		 agent_node *a;
		 char * s = malloc(snprintf(NULL, 0, "box") + 1);
		 sprintf(s, "box");	  
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,$5->mdepth+1,$5,NULL,NULL);
		 int md = MAX($5->mdepth+1,$1->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,$1,new,NULL);
		 $$ = newimp;
	       }
	       ;

disjunction_literals : {$$ = NULL;}
                     | literal TOR disjunction_literals
		     {
		       inputsize += 1;
		       if ($3 != NULL) {
                         int mdepth = MAX($1->mdepth,$3->mdepth);
			 formulalist *list = tree_to_list(DISJUNCTION,$1,$3);
			 tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,mdepth,NULL,NULL,list);
			 $$ = new;
		       }
		       else $$ =$1;
		     }
                     | literal 
		     {
		       formulalist *list = tree_to_list(DISJUNCTION,$1,NULL);
		       tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,$1->mdepth,NULL,NULL,list);
		       $$ = new;
		     }
                     | TLPAREN disjunction_literals TRPAREN
		     {
		       formulalist *list = tree_to_list(DISJUNCTION,$2,NULL);
		       tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,$2->mdepth,NULL,NULL,list);
		       $$ = new;
		     }
                     ;

literal : proposition {$$ = $1;}
        | TNOT literal 
        {
	  inputsize += 1;
	  tnode *new = create_tnode(NEGATION,NEGATION,$2->mdepth,$2,NULL,NULL);
	  $$ = new;
        }
        

formulas : {$$ = NULL;}
         | formula TDOT formulas
	 {
	   if ($3 != NULL) {
	     int mdepth = MAX($1->mdepth,$3->mdepth);
	     formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	     tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	     $$ = new;
	   }
	   else $$ = $1;
	 }
	 | error TDOT formulas {numerrors++;}
         ;

formula : formula TIFF formula 
          { // double-implications are not treated as abbreviations.
            // I would have a dag if I didn't want to copy the whole tree. 
            // and I don't want to deal with polarity at this point. 
	    // I am postponing whatever is to be done to when I need to put the formula into NNF.
	  inputsize += 1;
	  int mdepth = MAX($1->mdepth,$3->mdepth);
	  tnode *new = create_tnode(DOUBLEIMP,DOUBLEIMP,mdepth,$1,$3,NULL);
	  $$ = new;
        }
        | formula TIMPLY formula
        {
	  inputsize += 1;
	  int mdepth = MAX($1->mdepth,$3->mdepth);
	  tnode *new = create_tnode(IMPLICATION,IMPLICATION,mdepth,$1,$3,NULL);
	  $$ = new;
        }
        | formula TONLYIF formula
        {
	  inputsize += 1;
	  int mdepth = MAX($1->mdepth,$3->mdepth);
	  tnode *new = create_tnode(IMPLICATION,IMPLICATION,mdepth,$3,$1,NULL);
	  $$ = new;
        }
        | formula TOR formula
        {
	  inputsize += 1;
	  int mdepth = MAX($1->mdepth,$3->mdepth);
	  formulalist *newlist = tree_to_list(DISJUNCTION,$1,$3);
	  tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,mdepth,NULL,NULL,newlist);
	  $$ = new;
        }
        | formula TAND formula
        {
	  inputsize += 1;
	  int mdepth = MAX($1->mdepth,$3->mdepth);
	  formulalist *newlist = tree_to_list(CONJUNCTION,$1,$3);
	  tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	  $$ = new;
        }
        | TNOT formula 
        {
	  // I was eliminating double negations here, but that changes the counting of the input formula. 
	  inputsize += 1;
          tnode *new = create_tnode(NEGATION,NEGATION,$2->mdepth,$2,NULL,NULL);
	  $$ = new;
	}
        | TOBOX modal_arg TCBOX formula
	{ 
	  inputsize += 1;
	  agent_node *a;
          char *index;
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char * s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
	  sprintf(s, "box %s", index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(BOX,a->id,$4->mdepth+1,$4,NULL,NULL);
	  $$ = new;
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
	}
        | TNECESSARY modal_arg formula 
        { 
	  inputsize += 1;
	  agent_node *a;
          char *pname, *index;
          pname = strdup($1);
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char * s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	  sprintf(s, "%s %s", pname, index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(BOX,a->id,$3->mdepth+1,$3,NULL,NULL);
	  $$ = new;
	  free($1);
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
        }
	| TOBOX TCBOX formula
	{ 
	  inputsize += 1;
	  agent_node *a;
	  char * s = malloc(snprintf(NULL, 0, "box") + 1);
	  sprintf(s, "box");	  
	  a=insert_a_node(s);
          tnode *new = create_tnode(BOX,a->id,$3->mdepth+1,$3,NULL,NULL);
	  $$ = new;
        }
        | TNECESSARY formula
        { 
	  inputsize += 1;
	  agent_node *a;
          char *pname;
          pname = strdup($1);
	  a=insert_a_node(pname);
          tnode *new = create_tnode(BOX,a->id,$2->mdepth+1,$2,NULL,NULL);
	  $$ = new;
	  free($1);
        }
        | TODIA modal_arg TCDIA formula
	{ 
	  inputsize += 1;
	  agent_node *a;
          char *index;
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
	  sprintf(s, "box %s", index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(DIAMOND,a->id,$4->mdepth+1,$4,NULL,NULL);
	  $$ = new;
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
	}
        | TPOSSIBLE modal_arg formula
        { 
	  inputsize += 1; // the modal_args count as zero (as part of the operator);
	  agent_node *a;
          char *pname, *index;
          pname = getBoxName(strdup($1));
          if ($2 !=NULL) {index = strdup($2);} else index=NULL;
          char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	  sprintf(s, "%s %s", pname, index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(DIAMOND,a->id,$3->mdepth + 1,$3,NULL,NULL);
	  $$ = new;
	  free($1);
	  if (index != NULL) {
	    free(index);
	    free($2);
	  }
        }
        | TODIA TCDIA formula
	{ 
	  inputsize += 1;
	  agent_node *a;
	  char * s = malloc(snprintf(NULL, 0, "box") + 1);
	  sprintf(s, "box");	  
	  a=insert_a_node(s);
          tnode *new = create_tnode(DIAMOND,a->id,$3->mdepth+1,$3,NULL,NULL);
	  $$ = new;
        }
        | TPOSSIBLE formula
        { 
	  inputsize += 1;
	  agent_node *a;
          char *pname;
          pname = getBoxName(strdup($1));
	  a = insert_a_node(pname);
	  tnode *new = create_tnode(DIAMOND,a->id,$2->mdepth + 1,$2,NULL,NULL);
	  $$ = new;
	  free($1);
	}
        | TLPAREN formula TRPAREN
        {
	  $$ = $2;
	}
        | proposition
	{ 
	  $$ = $1;
        }
        ;

propositions_list: TNAME
                 {
		   char *prop = strdup($1);
		   prop_list *new = malloc(sizeof(prop_list));
		   new->prop = prop;
		   new->next = NULL;
		   free($1);
		   $$ = new;
		 }  
                 | TNAME TCOMMA propositions_list
                 {
		   char *prop = strdup($1);
		   prop_list *new = malloc(sizeof(prop_list));
		   new->prop = prop;
		   new->next = $3;
		   free($1);
		   $$ = new;
		 }
                 ;

modal_arg : TNUMBER 
          | TNAME
          ;

proposition: TNAME
           {
	     inputsize += 1;
             prop_node *p;
             char *pname = strdup($1);

	     char *s = malloc(snprintf(NULL, 0, "%s", pname) + 1);
	     sprintf(s, "%s", pname);
	     
	     p = insert_p_node(s);
	     tnode *new = create_tnode(PROP,p->id,0,NULL,NULL,NULL);
	     $$ = new;
	     free(pname);
	     free($1);
	   }
           | TSTART
	   {
	     inputsize += 1;
	     // prop_node *p = find_prop(CSTART);
	     tnode *new = create_tnode(CONSTANT,CSTART,0,NULL,NULL,NULL);
	     $$  = new;
	   }
           | TTRUE
	   {
	     inputsize += 1;
	     //prop_node *p = find_prop(CTRUE);
	     tnode *new = create_tnode(CONSTANT,CTRUE,0,NULL,NULL,NULL);
	     $$  = new;
	   }
           | TFALSE
	   {
	     inputsize += 1;
	     //	     prop_node *p = find_prop(CFALSE);
	     tnode *new = create_tnode(CONSTANT,CFALSE,0,NULL,NULL,NULL);
	     $$ = new;
	   } 
           ;

%%


char *getBoxName(char *diamond) {

  //NECESSARY   "L"|(?i:box)|(?i:nec)|(?i:necessary)|(?i:k)
  //POSSIBLE    "M"|(?i:dia)|(?i:pos)|(?i:diamond)|(?i:possible)
  char *s = NULL;

  if (!strcmp(diamond,"m")) {
     s = (char *) malloc(2);
     snprintf(s, 2, "%s","l");
  }
  else if (!strcmp(diamond,"dia") || !strcmp(diamond,"diamond")) {
    s = (char *) malloc(4);
    snprintf(s, 4, "%s","box");
  }
  else if (!strcmp(diamond,"possible")) {
    s = (char *) malloc(10);
    snprintf(s, 4, "%s","necessary");
  }
  free(diamond);
  return s;
}

void yyerror (char const *s) {
  fprintf (stderr, "\n Error: %s, line %d, column %d\n",s,numlines,numcolumns);
}

void process_ordering(prop_list *props) {
  while(props != NULL) {
    if (strcmp(props->prop,"start") && strcmp(props->prop,"true") && strcmp(props->prop,"false")) {
      insert_p_node(props->prop);
    }
    // not freeing the name because it is used in the symbol table.
    prop_list *aux;
    aux = props;
    props = props->next;
    free(aux); 
  }
}

