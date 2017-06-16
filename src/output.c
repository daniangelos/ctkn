#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "prover.h"
#include "uthash.h"
#include "tree.h"
#include "symbol_table.h"
#include "clauses.h"

extern int print_tree (tnode *r);
extern void print_agent (int id);
extern void print_prop (int id);
extern void print_clauses(void);
extern void print_symbols_tables(void);


/* variables from prover */

extern tnode *root; 

extern int newtemp;
extern int numclause;
extern int numtautologies;
extern int numfsubsumed;
extern int numbsubsumed;
extern int numple;
extern int nummle;
extern int nummlple;
extern int numearlyple;
extern int numearlymlple;
extern int numsimp;
extern int numpropagateunique;
extern int numctepropagated;
extern int verbose;
extern int time_stamp;
extern int mdepth;
extern int cycles;
extern int numsat;

/* variables from tokenizer.l */

extern int numtokens;
extern int numlines;
extern int numcolumns;

/* variables from parser.y */

extern int numerrors;
extern int numagents;
extern int numprops;
extern int inputsize;
extern int formulasize;
extern int snfclausesize;

extern hclauses *proofs;

void print_literal(int lit) {
  if (lit == CFALSE)
     printf("false");
  else if (lit == CSTART)
    printf("start");
  else if (lit == CTRUE)
     printf("true");
  else if (lit < 0) {
    printf("~");
    print_prop(lit);
  }
  else print_prop(lit);
}

void print_disjunction(literalslist *s) {
  while (s != NULL) {
    print_literal(s->literal);
    if (s->next != NULL)
      printf(" | ");
    s=s->next;
  }
}

void print_parents (clauseslist *parents) {
  while (parents != NULL) {
    printf(", ");
    printf("%d",parents->clause_number);
    parents = parents->next;
  }
}

void print_literals (literalslist *literals) {
  while (literals != NULL) {
    printf(", ");
    print_literal(literals->literal);
    literals = literals->next;
  }
}
    


void print_justification (justification *just) {
  if (just != NULL) {
    printf(" [ ");
    if (just != NULL)
      switch (just->rule) {
      case GIVEN: printf("Given");
	break;
      case FOUR: printf("Axiom 4");
	break;
      case FIVE: printf("Axiom 5");
	break;
      case T: printf("Axiom T");
	break;
      case DEFINITION: printf("Definition Clause");
	break;
      case SNF: printf("SNF");
	break;
      case SNF_PLUS: printf("SNF++");
	break;
      case SNF_MINUS: printf("SNF--");
	break;
      case TAUTOLOGY: printf("Tautology");
	break;
      case PLE: printf("Pure Literal Elimination");
	break;
      case MLPLE: printf("Modal Level Pure Literal Elimination");
	break;
      case BACKSUBSUMED: printf("Backward Subsumption");
	break;
      case FORWARD_SUBSUMES: printf("Forward Subsumption");
	break;
      case FORWARD_SUBSUMED: printf("Forward Subsumption");
	break;
      case SUBSUMED: printf("Subsumption");
	break;
      case REPEATED: printf("Repeated");
	break;
      case RETIRED: printf("Retired");
	break;
      case UNIT: printf("Unit Resolution");
	break;
      case LHSUNIT: printf("LHS Unit Resolution");
	break;
      case UNITGEN1: printf("GEN1 Unit Resolution");
	break;
      case UNITGEN3: printf("GEN3 Unit Resolution");
	break;
      case LRES: printf("LRES");
	break;
      case MRES: printf("MRES");
	break;
      case GEN1: printf("GEN1");
	break;
      case GEN2: printf("GEN2");
	break;
      case GEN3: printf("GEN3");
	break;
      case IRES1: printf("IRES1");
	break;
      case IRES2: printf("IRES2");
	break;
      case SAT: printf("SAT last ML");
	break;
      case PROPUNIQUEDIA: printf("Unique Diamond Propagation");
	break;
      case PROPUNIQUEBOX: printf("Unique Box Propagation");
	break;	
      case MLE: printf("MLE");
	break;
      case SIMP: printf("Simplification");
	break;
      case BOXFALSE: printf("MRES Box False");
	break;
      default :
	printf("Justification not found");
	break;
      }
    print_parents(just->parents);
    print_literals(just->literals);
    printf(" ]");
  }
}

void print_clause(tclause *clause) {
  printf("\n (%d,%d) [%d,%d].",clause->subtype,clause->numdiamond,clause->number,clause->modal_level);
  if (clause->type == INITIAL)
    printf("start");
  else if (clause->type == LITERAL)
    printf("true");
  else print_literal(clause->left);
  printf(" => ");
  if (clause->type == MNEGATIVE) {
    printf("~");
    print_agent(clause->agent);
    printf("~ ");
  }
  else if (clause->type == MPOSITIVE) {
    print_agent(clause->agent);
    printf(" ");
  }
  print_disjunction(clause->right);
  printf("\t");
  print_justification(clause->just);
  print_justification(clause->deleted);
  printf(" Max lit: %d.",clause->max_literal);
  printf(" Min lit: %d.",clause->min_literal);
}

void print_short(int cycle) {
  printf("\n\n Statistics:\n");
  printf("\n Number of errors: %d", numerrors);
  printf("\n Size of formula (original): %d", inputsize);
  printf("\n Size of formula (after processing input): %d", formulasize);
  printf("\n Size of formula (after SNF): %d", snfclausesize);
  printf("\n Number of propositional symbols (original): %d", numprops-2);
  printf("\n Number of modal operators: %d", numagents-1);
  printf("\n Modal depth: %d", mdepth);
  printf("\n Occurrences of pure literals removed by early PLE: %d", numearlyple);
  printf("\n Occurrences of pure literals removed by early ML_PLE: %d", numearlymlple);
  printf("\n Number of constants propagated: %d",numctepropagated);
  printf("\n Number of simplification steps: %d", numsimp);
  if (newtemp > 0) 
    printf("\n Number of propositional symbols (after translation): %d", newtemp-2);
  printf("\n Number of tautologies removed: %d", numtautologies);
  printf("\n Number of forward subsumed clauses removed: %d", numfsubsumed);
  printf("\n Number of backward subsumed clauses removed: %d", numbsubsumed);
  printf("\n Number of clauses removed by PLE: %d", numple);
  printf("\n Number of clauses removed by MLE: %d", nummle);
  printf("\n Number of clauses removed by ML_PLE: %d", nummlple);
  printf("\n Number of clauses removed by SAT: %d",numsat);
  printf("\n Number of propagated clauses: %d",numpropagateunique);
  printf("\n Number of cycles: %d", cycles);
  printf("\n Number of clauses (generated): %d", numclause - 1);
  printf("\n Number of clauses (kept): %d\n", (numclause - 1) - (numtautologies + numfsubsumed + numbsubsumed + numple + nummle + nummlple));
}


void print_out (char *phase) {
  switch (verbose) {
  case 6:  {
    if (numerrors == 0) {
      printf("\n Starting %s",phase);
      printf("\n Syntactic Tree:\n");
      print_tree(root);
    }
  }
  case 5: {
    printf("\n Symbol Table:\n");
    print_symbols_tables();
  }
  case 4: {
    print_clauses();
  }
  case 3: {
    print_short(0);
  }
  case 2: {
    printf("\n Finished %s",phase);
    if (time_stamp) {
      time_t t;
      time(&t);
      char *s = ctime(&t);
      s[strlen(s) - 1] = '\0';
      printf(" %s",s);
    }
  }
  case 1: {
  }
  default:
    break;
  }
}


