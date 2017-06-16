/* Options for the prover */

#define ON  1
#define OFF 0

/* Clause selection options */

#define SHORTEST 0
#define NEWEST   1
#define OLDEST   2
#define SMALLEST 3
#define GREATEST 4

/* Level selection options */

#define NONE 0
#define ASCENDING 1
#define DESCENDING 2
#define SHUFFLE 3

/* Literal selection options */

#define ORDERED      0
#define NEGATIVE     1
#define POSITIVE     2
#define SATURATE     3
#define NEGORDERED   4
#define ORDSELECT    5

/* Pre-processing options */

#define NON_NEGATIVE 400
#define NON_POSITIVE 401
#define MAX_LIT_POSITIVE 402
#define MAX_LIT_NEGATIVE 403

/* Logic Symbols */

#define PROP        0
#define BOX         1
#define DIAMOND     2
#define NEGATION    3
#define CONJUNCTION 4
#define DISJUNCTION 5
#define IMPLICATION 6
#define DOUBLEIMP   7
#define CONSTANT    8

/* Axioms */

#define AXIOM       20
#define FOUR        21
#define FIVE        22
#define T           23
#define DEFINITION  24

// Constants

#define CSTART      0
#define CTRUE       1
#define CFALSE     -1

// Sets

#define SETF       -30
#define SETC       -31
#define SOS        -40
#define USABLE     -41

// Clauses

#define INITIAL    -50
#define LITERAL    -51
#define MNEGATIVE  -52
#define MPOSITIVE  -53

// Inference Rules and other justifications

#define PLE          100 // Pure Literal Elimination
#define BACKSUBSUMED 101 // Back Subsumption
#define SUBSUMED     102 // Subsumption
#define UNIT         103 // Unit Resolution
#define REPEATED     104
#define LHSUNIT      105 // Unit Resolution on the left hand side of modal clauses
#define UNITGEN1     106 // Unit Resolution on the right hand side of negative modal clauses
#define UNITGEN3     107 // Unit Resolution on the right hand side of positive modal clauses
#define RETIRED      108 // Modal clause is moved to modal usable
#define SNF          200 // From transformation
#define GIVEN        201 // As given by user
#define TAUTOLOGY    202 
#define MRES         203
#define GEN1         204
#define GEN2         205
#define GEN3         206
#define LRES         207
#define IRES1        208
#define IRES2        209
#define MLPLE        210
#define SNF_PLUS     211
#define SNF_MINUS    212
#define SAT          213
#define MLE          214
#define PROPUNIQUEDIA   215
#define PROPUNIQUEBOX   216
#define SIMP         217
#define BOXFALSE     218
#define FORWARD_SUBSUMES     302 // Subsumption
#define FORWARD_SUBSUMED     303 // Subsumption


