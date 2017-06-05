/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Skeleton implementation for Bison GLR parsers in C

   Copyright (C) 2002-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C GLR parser skeleton written by Paul Hilfinger.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "glr.c"

/* Pure parsers.  */
#define YYPURE 1






/* First part of user declarations.  */
#line 35 "parser.y" /* glr.c:240  */

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

#line 155 "parser.tab.c" /* glr.c:240  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

#include "parser.tab.h"

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* Default (constant) value used for initialization for null
   right-hand sides.  Unlike the standard yacc.c template, here we set
   the default value of $$ to a zeroed-out value.  Since the default
   value is undefined, this behavior is technically correct.  */
static YYSTYPE yyval_default;

/* Copy the second part of user declarations.  */

#line 183 "parser.tab.c" /* glr.c:263  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YYFREE
# define YYFREE free
#endif
#ifndef YYMALLOC
# define YYMALLOC malloc
#endif
#ifndef YYREALLOC
# define YYREALLOC realloc
#endif

#define YYSIZEMAX ((size_t) -1)

#ifdef __cplusplus
   typedef bool yybool;
#else
   typedef unsigned char yybool;
#endif
#define yytrue 1
#define yyfalse 0

#ifndef YYSETJMP
# include <setjmp.h>
# define YYJMP_BUF jmp_buf
# define YYSETJMP(Env) setjmp (Env)
/* Pacify clang.  */
# define YYLONGJMP(Env, Val) (longjmp (Env, Val), YYASSERT (0))
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#ifndef YYASSERT
# define YYASSERT(Condition) ((void) ((Condition) || (abort (), 0)))
#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  7
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   236

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  32
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  19
/* YYNRULES -- Number of rules.  */
#define YYNRULES  70
/* YYNRULES -- Number of states.  */
#define YYNSTATES  158
/* YYMAXRHS -- Maximum number of symbols on right-hand side of rule.  */
#define YYMAXRHS 6
/* YYMAXLEFT -- Maximum number of symbols to the left of a handle
   accessed by $0, $-1, etc., in any rule.  */
#define YYMAXLEFT 0

/* YYTRANSLATE(X) -- Bison symbol number corresponding to X.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   286

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const unsigned char yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31
};

#if YYDEBUG
/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const unsigned short int yyrline[] =
{
       0,   197,   197,   203,   204,   205,   208,   277,   289,   316,
     341,   362,   365,   366,   382,   399,   400,   408,   416,   424,
     434,   446,   458,   459,   469,   479,   489,   492,   501,   508,
     518,   535,   548,   563,   575,   592,   605,   620,   634,   635,
     646,   652,   660,   661,   669,   670,   680,   683,   693,   700,
     707,   715,   723,   730,   746,   764,   774,   785,   801,   819,
     829,   840,   844,   850,   859,   870,   871,   874,   889,   896,
     903
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "\"double implication\"",
  "\"implication\"", "\"only if\"", "\"disjunction\"", "\"conjunction\"",
  "\"negation\"", "\"diamond operator\"", "\"box operator\"", "TOBOX",
  "TODIA", "\"modal operator delimiter (open)\"", "TCBOX", "TCDIA",
  "\"modal operator delimiter (close)\"", "\"identifier\"", "\"number\"",
  "TSTART", "TTRUE", "\"constant\"", "\"set option command\"", "\".\"",
  "\",\"", "\"clauses\"", "\"formulas\"", "\"sos\"", "\"usable\"",
  "\"end of list\"", "\"(\"", "\")\"", "$accept", "file", "declarations",
  "option", "axioms", "sets", "formulas_sets_tail", "clauses_sets_tail",
  "clauses", "initial_clause", "literal_clause", "modal_clause",
  "disjunction_literals", "literal", "formulas", "formula",
  "propositions_list", "modal_arg", "proposition", YY_NULLPTR
};
#endif

#define YYPACT_NINF -106
#define YYTABLE_NINF -68

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const short int yypact[] =
{
     133,   -21,    -3,    36,   -11,   133,    27,  -106,    23,    37,
    -106,  -106,  -106,    61,    53,    60,    20,    76,  -106,  -106,
      77,    84,   134,    87,    81,    92,    95,    97,   111,  -106,
      77,   118,  -106,  -106,   133,   135,   159,   160,   163,    77,
    -106,   164,  -106,   124,   110,   124,   110,  -106,  -106,   172,
      39,  -106,   212,   215,  -106,   129,  -106,   175,   197,   198,
     199,  -106,    35,  -106,   201,   168,   154,   154,   183,    65,
    -106,  -106,   168,  -106,   194,   187,  -106,  -106,  -106,   124,
    -106,   129,   129,   195,   219,   204,   124,   124,   124,   158,
     129,   110,  -106,     7,  -106,   168,  -106,   168,   168,   214,
     168,   216,    93,   206,   168,   168,   168,   168,   168,   110,
    -106,  -106,  -106,  -106,   -11,  -106,  -106,  -106,   188,   188,
     185,   200,  -106,  -106,  -106,  -106,  -106,   168,  -106,   168,
    -106,   -11,   207,    82,   150,   223,  -106,  -106,  -106,  -106,
      39,  -106,    39,    39,   218,    39,   220,  -106,  -106,  -106,
    -106,  -106,  -106,    39,  -106,    39,  -106,  -106
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const unsigned char yydefact[] =
{
       0,     0,     0,     0,    15,     0,     0,     1,     0,     0,
       2,     5,    11,     0,     6,     0,     0,     0,    66,    65,
      12,     0,     0,     0,     0,     0,     0,     0,    13,    10,
      12,    63,     7,     8,     0,     0,     0,     0,     0,    12,
       9,     0,     4,     0,     0,     0,     0,    14,    64,     0,
       0,    67,    68,    69,    70,    38,    18,     0,     0,     0,
       0,    29,    40,    42,     0,     0,     0,     0,     0,     0,
      68,    69,     0,    16,     0,     0,    62,    19,    17,     0,
      43,    38,    38,     0,    40,     0,     0,     0,     0,     0,
      38,     0,    52,    66,    60,     0,    56,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      26,    27,    28,    41,    15,    23,    24,    25,     0,     0,
       0,     0,    39,    46,    58,    54,    55,     0,    59,     0,
      61,    15,    47,    48,    49,    50,    51,    45,    21,    35,
       0,    31,     0,     0,     0,     0,     0,    53,    57,    20,
      34,    30,    33,     0,    37,     0,    32,    36
};

  /* YYPGOTO[NTERM-NUM].  */
static const short int yypgoto[] =
{
    -106,  -106,    -1,  -106,   -24,  -105,   190,   189,   -37,  -106,
    -106,  -106,   -47,   -50,   -84,     9,   192,   -48,   -43
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const signed char yydefgoto[] =
{
      -1,     3,     4,    15,    29,    10,    73,    56,    57,    58,
      59,    60,    61,    62,    74,    75,    33,    21,    63
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const short int yytable[] =
{
      80,    76,     5,    76,    11,    84,    40,   123,    83,   138,
     -67,   -67,   -67,   -67,   -67,    47,     8,     9,    95,    97,
      99,   101,    76,    76,    76,   137,   149,     6,    12,    76,
     -67,    84,    84,    42,   111,   112,     7,    13,   -67,    89,
      84,    90,   110,   122,    14,    24,    25,    50,    76,   115,
     116,   117,    76,    16,    76,    76,    51,    76,    70,    71,
      54,    76,    76,    76,    76,    76,    76,    17,   139,   141,
     140,   142,   144,   146,    92,    94,    96,    22,    18,    19,
     100,   102,    18,    19,    76,    20,    76,   106,   107,   108,
     150,    23,   151,   152,    28,   154,   104,   105,   106,   107,
     108,    26,    27,   156,   124,   157,   125,   126,    30,   128,
      34,    64,    35,   132,   133,   134,   135,   136,    65,    66,
      67,    68,    69,    36,   130,    49,    37,    51,    38,    70,
      71,    54,    50,    -3,     1,    39,   147,    50,   148,   -44,
      72,    51,    41,    52,    53,    54,    51,   -38,    70,    71,
      54,    31,    32,   -22,    55,     2,   107,   108,    43,    55,
      -3,    -3,    65,    66,    67,    68,    69,   118,   119,   120,
     121,    93,    19,    70,    71,    54,    65,    66,    67,    68,
      69,    31,    44,    45,    72,    51,    46,    70,    71,    54,
     104,   105,   106,   107,   108,    79,    50,    98,    72,   143,
      18,    19,    18,    19,    85,    93,    19,    70,    71,    54,
     109,   105,   106,   107,   108,   145,    81,    18,    19,    82,
      86,    87,    88,   103,    91,    90,   113,   114,   127,   131,
     108,   129,   153,    48,    77,   155,    78
};

static const unsigned char yycheck[] =
{
      50,    44,    23,    46,     5,    55,    30,    91,    55,   114,
       3,     4,     5,     6,     7,    39,    27,    28,    66,    67,
      68,    69,    65,    66,    67,   109,   131,    30,     1,    72,
      23,    81,    82,    34,    81,    82,     0,    10,    31,     4,
      90,     6,    79,    90,    17,    25,    26,     8,    91,    86,
      87,    88,    95,    30,    97,    98,    17,   100,    19,    20,
      21,   104,   105,   106,   107,   108,   109,    30,   118,   119,
     118,   119,   120,   121,    65,    66,    67,    24,    17,    18,
      15,    72,    17,    18,   127,    24,   129,     5,     6,     7,
     140,    31,   142,   143,    17,   145,     3,     4,     5,     6,
       7,    25,    26,   153,    95,   155,    97,    98,    24,   100,
      23,     1,    31,   104,   105,   106,   107,   108,     8,     9,
      10,    11,    12,    31,    31,     1,    31,    17,    31,    19,
      20,    21,     8,     0,     1,    24,   127,     8,   129,    29,
      30,    17,    24,    19,    20,    21,    17,    23,    19,    20,
      21,    17,    18,    29,    30,    22,     6,     7,    23,    30,
      27,    28,     8,     9,    10,    11,    12,     9,    10,    11,
      12,    17,    18,    19,    20,    21,     8,     9,    10,    11,
      12,    17,    23,    23,    30,    17,    23,    19,    20,    21,
       3,     4,     5,     6,     7,    23,     8,    14,    30,    14,
      17,    18,    17,    18,    29,    17,    18,    19,    20,    21,
      23,     4,     5,     6,     7,    15,     4,    17,    18,     4,
      23,    23,    23,    29,    23,     6,    31,    23,    14,    23,
       7,    15,    14,    41,    45,    15,    46
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const unsigned char yystos[] =
{
       0,     1,    22,    33,    34,    23,    30,     0,    27,    28,
      37,    34,     1,    10,    17,    35,    30,    30,    17,    18,
      24,    49,    24,    31,    25,    26,    25,    26,    17,    36,
      24,    17,    18,    48,    23,    31,    31,    31,    31,    24,
      36,    24,    34,    23,    23,    23,    23,    36,    48,     1,
       8,    17,    19,    20,    21,    30,    39,    40,    41,    42,
      43,    44,    45,    50,     1,     8,     9,    10,    11,    12,
      19,    20,    30,    38,    46,    47,    50,    39,    38,    23,
      45,     4,     4,    44,    45,    29,    23,    23,    23,     4,
       6,    23,    47,    17,    47,    49,    47,    49,    14,    49,
      15,    49,    47,    29,     3,     4,     5,     6,     7,    23,
      40,    44,    44,    31,    23,    40,    40,    40,     9,    10,
      11,    12,    44,    46,    47,    47,    47,    14,    47,    15,
      31,    23,    47,    47,    47,    47,    47,    46,    37,    45,
      49,    45,    49,    14,    49,    15,    49,    47,    47,    37,
      45,    45,    45,    14,    45,    15,    45,    45
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const unsigned char yyr1[] =
{
       0,    32,    33,    34,    34,    34,    35,    35,    35,    35,
      35,    35,    36,    36,    36,    37,    37,    37,    37,    37,
      38,    39,    40,    40,    40,    40,    40,    41,    42,    42,
      43,    43,    43,    43,    43,    43,    43,    43,    44,    44,
      44,    44,    45,    45,    46,    46,    46,    47,    47,    47,
      47,    47,    47,    47,    47,    47,    47,    47,    47,    47,
      47,    47,    47,    48,    48,    49,    49,    50,    50,    50,
      50
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const unsigned char yyr2[] =
{
       0,     2,     2,     0,     6,     3,     1,     3,     3,     4,
       3,     1,     0,     1,     3,     0,     6,     6,     6,     6,
       4,     4,     0,     3,     3,     3,     3,     3,     3,     1,
       5,     4,     6,     5,     5,     4,     6,     5,     0,     3,
       1,     3,     1,     2,     0,     3,     3,     3,     3,     3,
       3,     3,     2,     4,     3,     3,     2,     4,     3,     3,
       2,     3,     1,     1,     3,     1,     1,     1,     1,     1,
       1
};


/* YYDPREC[RULE-NUM] -- Dynamic precedence of rule #RULE-NUM (0 if none).  */
static const unsigned char yydprec[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0
};

/* YYMERGER[RULE-NUM] -- Index of merging function for rule #RULE-NUM.  */
static const unsigned char yymerger[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0
};

/* YYIMMEDIATE[RULE-NUM] -- True iff rule #RULE-NUM is not to be deferred, as
   in the case of predicates.  */
static const yybool yyimmediate[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0
};

/* YYCONFLP[YYPACT[STATE-NUM]] -- Pointer into YYCONFL of start of
   list of conflicting reductions corresponding to action entry for
   state STATE-NUM in yytable.  0 means no conflicts.  The list in
   yyconfl is terminated by a rule number of 0.  */
static const unsigned char yyconflp[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     1,     0,     0,     3,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0
};

/* YYCONFL[I] -- lists of conflicting rule numbers, each terminated by
   0, pointed into by YYCONFLP.  */
static const short int yyconfl[] =
{
       0,    68,     0,    69,     0
};

/* Error token number */
#define YYTERROR 1




#undef yynerrs
#define yynerrs (yystackp->yyerrcnt)
#undef yychar
#define yychar (yystackp->yyrawchar)
#undef yylval
#define yylval (yystackp->yyval)
#undef yylloc
#define yylloc (yystackp->yyloc)


static const int YYEOF = 0;
static const int YYEMPTY = -2;

typedef enum { yyok, yyaccept, yyabort, yyerr } YYRESULTTAG;

#define YYCHK(YYE)                              \
  do {                                          \
    YYRESULTTAG yychk_flag = YYE;               \
    if (yychk_flag != yyok)                     \
      return yychk_flag;                        \
  } while (0)

#if YYDEBUG

# ifndef YYFPRINTF
#  define YYFPRINTF fprintf
# endif

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YYDPRINTF(Args)                        \
  do {                                          \
    if (yydebug)                                \
      YYFPRINTF Args;                           \
  } while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                  \
  do {                                                                  \
    if (yydebug)                                                        \
      {                                                                 \
        YYFPRINTF (stderr, "%s ", Title);                               \
        yy_symbol_print (stderr, Type, Value);        \
        YYFPRINTF (stderr, "\n");                                       \
      }                                                                 \
  } while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;

struct yyGLRStack;
static void yypstack (struct yyGLRStack* yystackp, size_t yyk)
  YY_ATTRIBUTE_UNUSED;
static void yypdumpstack (struct yyGLRStack* yystackp)
  YY_ATTRIBUTE_UNUSED;

#else /* !YYDEBUG */

# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)

#endif /* !YYDEBUG */

/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < YYMAXDEPTH * sizeof (GLRStackItem)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif

/* Minimum number of free items on the stack allowed after an
   allocation.  This is to allow allocation and initialization
   to be completed by functions that call yyexpandGLRStack before the
   stack is expanded, thus insuring that all necessary pointers get
   properly redirected to new data.  */
#define YYHEADROOM 2

#ifndef YYSTACKEXPANDABLE
#  define YYSTACKEXPANDABLE 1
#endif

#if YYSTACKEXPANDABLE
# define YY_RESERVE_GLRSTACK(Yystack)                   \
  do {                                                  \
    if (Yystack->yyspaceLeft < YYHEADROOM)              \
      yyexpandGLRStack (Yystack);                       \
  } while (0)
#else
# define YY_RESERVE_GLRSTACK(Yystack)                   \
  do {                                                  \
    if (Yystack->yyspaceLeft < YYHEADROOM)              \
      yyMemoryExhausted (Yystack);                      \
  } while (0)
#endif


#if YYERROR_VERBOSE

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static size_t
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      size_t yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return strlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

#endif /* !YYERROR_VERBOSE */

/** State numbers, as in LALR(1) machine */
typedef int yyStateNum;

/** Rule numbers, as in LALR(1) machine */
typedef int yyRuleNum;

/** Grammar symbol */
typedef int yySymbol;

/** Item references, as in LALR(1) machine */
typedef short int yyItemNum;

typedef struct yyGLRState yyGLRState;
typedef struct yyGLRStateSet yyGLRStateSet;
typedef struct yySemanticOption yySemanticOption;
typedef union yyGLRStackItem yyGLRStackItem;
typedef struct yyGLRStack yyGLRStack;

struct yyGLRState {
  /** Type tag: always true.  */
  yybool yyisState;
  /** Type tag for yysemantics.  If true, yysval applies, otherwise
   *  yyfirstVal applies.  */
  yybool yyresolved;
  /** Number of corresponding LALR(1) machine state.  */
  yyStateNum yylrState;
  /** Preceding state in this stack */
  yyGLRState* yypred;
  /** Source position of the last token produced by my symbol */
  size_t yyposn;
  union {
    /** First in a chain of alternative reductions producing the
     *  non-terminal corresponding to this state, threaded through
     *  yynext.  */
    yySemanticOption* yyfirstVal;
    /** Semantic value for this state.  */
    YYSTYPE yysval;
  } yysemantics;
};

struct yyGLRStateSet {
  yyGLRState** yystates;
  /** During nondeterministic operation, yylookaheadNeeds tracks which
   *  stacks have actually needed the current lookahead.  During deterministic
   *  operation, yylookaheadNeeds[0] is not maintained since it would merely
   *  duplicate yychar != YYEMPTY.  */
  yybool* yylookaheadNeeds;
  size_t yysize, yycapacity;
};

struct yySemanticOption {
  /** Type tag: always false.  */
  yybool yyisState;
  /** Rule number for this reduction */
  yyRuleNum yyrule;
  /** The last RHS state in the list of states to be reduced.  */
  yyGLRState* yystate;
  /** The lookahead for this reduction.  */
  int yyrawchar;
  YYSTYPE yyval;
  /** Next sibling in chain of options.  To facilitate merging,
   *  options are chained in decreasing order by address.  */
  yySemanticOption* yynext;
};

/** Type of the items in the GLR stack.  The yyisState field
 *  indicates which item of the union is valid.  */
union yyGLRStackItem {
  yyGLRState yystate;
  yySemanticOption yyoption;
};

struct yyGLRStack {
  int yyerrState;


  int yyerrcnt;
  int yyrawchar;
  YYSTYPE yyval;

  YYJMP_BUF yyexception_buffer;
  yyGLRStackItem* yyitems;
  yyGLRStackItem* yynextFree;
  size_t yyspaceLeft;
  yyGLRState* yysplitPoint;
  yyGLRState* yylastDeleted;
  yyGLRStateSet yytops;
};

#if YYSTACKEXPANDABLE
static void yyexpandGLRStack (yyGLRStack* yystackp);
#endif

static _Noreturn void
yyFail (yyGLRStack* yystackp, const char* yymsg)
{
  if (yymsg != YY_NULLPTR)
    yyerror (yymsg);
  YYLONGJMP (yystackp->yyexception_buffer, 1);
}

static _Noreturn void
yyMemoryExhausted (yyGLRStack* yystackp)
{
  YYLONGJMP (yystackp->yyexception_buffer, 2);
}

#if YYDEBUG || YYERROR_VERBOSE
/** A printable representation of TOKEN.  */
static inline const char*
yytokenName (yySymbol yytoken)
{
  if (yytoken == YYEMPTY)
    return "";

  return yytname[yytoken];
}
#endif

/** Fill in YYVSP[YYLOW1 .. YYLOW0-1] from the chain of states starting
 *  at YYVSP[YYLOW0].yystate.yypred.  Leaves YYVSP[YYLOW1].yystate.yypred
 *  containing the pointer to the next state in the chain.  */
static void yyfillin (yyGLRStackItem *, int, int) YY_ATTRIBUTE_UNUSED;
static void
yyfillin (yyGLRStackItem *yyvsp, int yylow0, int yylow1)
{
  int i;
  yyGLRState *s = yyvsp[yylow0].yystate.yypred;
  for (i = yylow0-1; i >= yylow1; i -= 1)
    {
#if YYDEBUG
      yyvsp[i].yystate.yylrState = s->yylrState;
#endif
      yyvsp[i].yystate.yyresolved = s->yyresolved;
      if (s->yyresolved)
        yyvsp[i].yystate.yysemantics.yysval = s->yysemantics.yysval;
      else
        /* The effect of using yysval or yyloc (in an immediate rule) is
         * undefined.  */
        yyvsp[i].yystate.yysemantics.yyfirstVal = YY_NULLPTR;
      s = yyvsp[i].yystate.yypred = s->yypred;
    }
}

/* Do nothing if YYNORMAL or if *YYLOW <= YYLOW1.  Otherwise, fill in
 * YYVSP[YYLOW1 .. *YYLOW-1] as in yyfillin and set *YYLOW = YYLOW1.
 * For convenience, always return YYLOW1.  */
static inline int yyfill (yyGLRStackItem *, int *, int, yybool)
     YY_ATTRIBUTE_UNUSED;
static inline int
yyfill (yyGLRStackItem *yyvsp, int *yylow, int yylow1, yybool yynormal)
{
  if (!yynormal && yylow1 < *yylow)
    {
      yyfillin (yyvsp, *yylow, yylow1);
      *yylow = yylow1;
    }
  return yylow1;
}

/** Perform user action for rule number YYN, with RHS length YYRHSLEN,
 *  and top stack item YYVSP.  YYLVALP points to place to put semantic
 *  value ($$), and yylocp points to place for location information
 *  (@$).  Returns yyok for normal return, yyaccept for YYACCEPT,
 *  yyerr for YYERROR, yyabort for YYABORT.  */
static YYRESULTTAG
yyuserAction (yyRuleNum yyn, size_t yyrhslen, yyGLRStackItem* yyvsp,
              yyGLRStack* yystackp,
              YYSTYPE* yyvalp)
{
  yybool yynormal YY_ATTRIBUTE_UNUSED = (yystackp->yysplitPoint == YY_NULLPTR);
  int yylow;
  YYUSE (yyvalp);
  YYUSE (yyrhslen);
# undef yyerrok
# define yyerrok (yystackp->yyerrState = 0)
# undef YYACCEPT
# define YYACCEPT return yyaccept
# undef YYABORT
# define YYABORT return yyabort
# undef YYERROR
# define YYERROR return yyerrok, yyerr
# undef YYRECOVERING
# define YYRECOVERING() (yystackp->yyerrState != 0)
# undef yyclearin
# define yyclearin (yychar = YYEMPTY)
# undef YYFILL
# define YYFILL(N) yyfill (yyvsp, &yylow, N, yynormal)
# undef YYBACKUP
# define YYBACKUP(Token, Value)                                              \
  return yyerror (YY_("syntax error: cannot back up")),     \
         yyerrok, yyerr

  yylow = 1;
  if (yyrhslen == 0)
    *yyvalp = yyval_default;
  else
    *yyvalp = yyvsp[YYFILL (1-yyrhslen)].yystate.yysemantics.yysval;
  switch (yyn)
    {
        case 2:
#line 198 "parser.y" /* glr.c:816  */
    {
       root = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);
     }
#line 1053 "parser.tab.c" /* glr.c:816  */
    break;

  case 5:
#line 205 "parser.y" /* glr.c:816  */
    { numerrors++; }
#line 1059 "parser.tab.c" /* glr.c:816  */
    break;

  case 6:
#line 209 "parser.y" /* glr.c:816  */
    {
	 if (!configfile) {
	   char *option = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
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
	 free((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));

       }
#line 1132 "parser.tab.c" /* glr.c:816  */
    break;

  case 7:
#line 278 "parser.y" /* glr.c:816  */
    {
       	 if (!configfile) {
	   char *option = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	   if (!strcmp(option,"verbosity")) verbose = atoi((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
	   else if (!strcmp(option,"maxproof")) maxproof = atoi((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
	   else if (!strcmp(option,"parallel")) {parallel_prover = ON; processors = atoi((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));}
	   free(option);
	 }
	 free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	 free((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
       }
#line 1148 "parser.tab.c" /* glr.c:816  */
    break;

  case 8:
#line 290 "parser.y" /* glr.c:816  */
    {
	 if (!configfile) {
	   char *option = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	   if (!strcmp(option,"order")) {
	     process_ordering((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.prop_list));
	   }
	   else if (!strcmp(option,"populate_usable")) {
	     prop_list *populate = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.prop_list);
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
	     free((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.prop_list));
	   }
	 free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	 free(option);
	 }
       }
#line 1179 "parser.tab.c" /* glr.c:816  */
    break;

  case 9:
#line 317 "parser.y" /* glr.c:816  */
    {
	 if (!configfile) {
	   agent_node *a;
	   char *pname, *index;
	   pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.strValue));
	   if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue) != NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));} else index=NULL;
	   char * s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	   sprintf(s, "%s %s", pname, index);
	   a = insert_a_node(s);
	   a->occur -= 1;

	   axiom_list *l = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.axiom_list);
	 
	   while (l != NULL) {
	     if (l->axiom == FIVE)
	       a->five = 1;
	     else if (l->axiom == FOUR)
	       a->four = 1;
	     l = l->next;
	   }
	   free((((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.strValue));
	   if (index != NULL) free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	 }
       }
#line 1208 "parser.tab.c" /* glr.c:816  */
    break;

  case 10:
#line 342 "parser.y" /* glr.c:816  */
    {
	 if (!configfile) {
	   agent_node *a;
	   char *pname;
	   pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	   a = insert_a_node(pname);
	   a->occur -= 1;
	 
	   axiom_list *l = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.axiom_list);
	 
	   while (l !=NULL) {  
	     if (l->axiom == FIVE)
	       a->five = 1;
	     else if (l->axiom == FOUR)
	       a->four = 1;
	     l = l->next;
	   }
	   free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	 }
       }
#line 1233 "parser.tab.c" /* glr.c:816  */
    break;

  case 11:
#line 362 "parser.y" /* glr.c:816  */
    {numerrors++;}
#line 1239 "parser.tab.c" /* glr.c:816  */
    break;

  case 12:
#line 365 "parser.y" /* glr.c:816  */
    {((*yyvalp).axiom_list)=NULL;}
#line 1245 "parser.tab.c" /* glr.c:816  */
    break;

  case 13:
#line 367 "parser.y" /* glr.c:816  */
    {
	 if (!configfile) {
	   char *name;
	   axiom_list *a = malloc(sizeof(axiom_list));
	   name = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
	   if (!strcmp(name,"five"))
	     a->axiom = FIVE;
	   else if (!strcmp(name,"four"))
	     a->axiom = FOUR;
	   else a->axiom = 0;
	   a->next = NULL;
	   ((*yyvalp).axiom_list) = a;
	   free((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
	 }
       }
#line 1265 "parser.tab.c" /* glr.c:816  */
    break;

  case 14:
#line 382 "parser.y" /* glr.c:816  */
    {
	 if (!configfile) {
	   char *name;
	   axiom_list *a = malloc(sizeof(axiom_list));
	   name = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	   if (!strcmp(name,"five"))
	     a->axiom = FIVE;
	   else if (!strcmp(name,"four"))
	     a->axiom = FOUR;
	   else a->axiom = 0;
	   a->next = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.axiom_list);
	   ((*yyvalp).axiom_list) = a;
	   free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	 }
      }
#line 1285 "parser.tab.c" /* glr.c:816  */
    break;

  case 15:
#line 399 "parser.y" /* glr.c:816  */
    {((*yyvalp).tnode) = NULL;}
#line 1291 "parser.tab.c" /* glr.c:816  */
    break;

  case 16:
#line 401 "parser.y" /* glr.c:816  */
    {
       ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);
       if (((*yyvalp).tnode) != NULL) {
	 ((*yyvalp).tnode)->id=SOS;
	 ((*yyvalp).tnode)->mdepth = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth;
       }
     }
#line 1303 "parser.tab.c" /* glr.c:816  */
    break;

  case 17:
#line 409 "parser.y" /* glr.c:816  */
    {
       ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);
       if (((*yyvalp).tnode) != NULL) {
	 ((*yyvalp).tnode)->id=USABLE;
	 ((*yyvalp).tnode)->mdepth = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth;
       }
     }
#line 1315 "parser.tab.c" /* glr.c:816  */
    break;

  case 18:
#line 417 "parser.y" /* glr.c:816  */
    {
       ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);
       if (((*yyvalp).tnode) != NULL) {
	 ((*yyvalp).tnode)->id=SOS;
	 ((*yyvalp).tnode)->mdepth = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth;
       }
     }
#line 1327 "parser.tab.c" /* glr.c:816  */
    break;

  case 19:
#line 425 "parser.y" /* glr.c:816  */
    {
       ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);
       if (((*yyvalp).tnode) != NULL) {
	 ((*yyvalp).tnode)->id=USABLE;
	 ((*yyvalp).tnode)->mdepth = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth;
       }
     }
#line 1339 "parser.tab.c" /* glr.c:816  */
    break;

  case 20:
#line 435 "parser.y" /* glr.c:816  */
    {      
		    int mdepth;
		    if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL)
		      mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
		    else
		      mdepth=(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode)->mdepth;
		    tnode *new = create_tnode(SETF,SETF,mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
		    ((*yyvalp).tnode) = new;
		   }
#line 1353 "parser.tab.c" /* glr.c:816  */
    break;

  case 21:
#line 447 "parser.y" /* glr.c:816  */
    {
		    int mdepth;
		    if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL)
		      mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
		    else
		      mdepth=(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode)->mdepth;
		    tnode *new = create_tnode(SETC,SETC,mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
		    ((*yyvalp).tnode) = new;
		  }
#line 1367 "parser.tab.c" /* glr.c:816  */
    break;

  case 22:
#line 458 "parser.y" /* glr.c:816  */
    {((*yyvalp).tnode) = NULL;}
#line 1373 "parser.tab.c" /* glr.c:816  */
    break;

  case 23:
#line 460 "parser.y" /* glr.c:816  */
    {
	  if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL) {
	    int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	    formulalist *newlist = tree_to_list(CONJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	    ((*yyvalp).tnode) = new;
	  }
	  else ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode);
	}
#line 1387 "parser.tab.c" /* glr.c:816  */
    break;

  case 24:
#line 470 "parser.y" /* glr.c:816  */
    {
	  if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL) {
	    int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	    formulalist *newlist = tree_to_list(CONJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	    ((*yyvalp).tnode) = new;
	  }
	  else ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode);
	}
#line 1401 "parser.tab.c" /* glr.c:816  */
    break;

  case 25:
#line 480 "parser.y" /* glr.c:816  */
    {
	  if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL) {
	    int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	    formulalist *newlist = tree_to_list(CONJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
	    tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	    ((*yyvalp).tnode) = new;
	  }
	  else ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode);
	}
#line 1415 "parser.tab.c" /* glr.c:816  */
    break;

  case 26:
#line 489 "parser.y" /* glr.c:816  */
    {numerrors++;}
#line 1421 "parser.tab.c" /* glr.c:816  */
    break;

  case 27:
#line 493 "parser.y" /* glr.c:816  */
    {
		   inputsize += 2;
	           tnode *newst = create_tnode(CONSTANT,CSTART,0,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,CONJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth,newst,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
		   ((*yyvalp).tnode) = new;
                 }
#line 1432 "parser.tab.c" /* glr.c:816  */
    break;

  case 28:
#line 502 "parser.y" /* glr.c:816  */
    {
		   inputsize += 2;
	           tnode *newconst = create_tnode(CONSTANT,CTRUE,0,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,IMPLICATION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth,newconst,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
		   ((*yyvalp).tnode) = new;
                 }
#line 1443 "parser.tab.c" /* glr.c:816  */
    break;

  case 29:
#line 509 "parser.y" /* glr.c:816  */
    {
	           tnode *newconst = create_tnode(CONSTANT,CTRUE,0,NULL,NULL,NULL);
		   tnode *new = create_tnode(IMPLICATION,IMPLICATION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth,newconst,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
		   ((*yyvalp).tnode) = new;
		 }
#line 1453 "parser.tab.c" /* glr.c:816  */
    break;

  case 30:
#line 519 "parser.y" /* glr.c:816  */
    {
		inputsize += 2;
	        agent_node *a;
                char *pname, *index;
                pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
                if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));} else index=NULL;
                char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	        sprintf(s, "%s %s", pname, index);
	        a=insert_a_node(s);
	        tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode)->mdepth);
		tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode),new,NULL);
		((*yyvalp).tnode) = newimp;
		free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
		if (index != NULL) free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	       }
#line 1474 "parser.tab.c" /* glr.c:816  */
    break;

  case 31:
#line 536 "parser.y" /* glr.c:816  */
    { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname;
		 pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
		 a=insert_a_node(pname);
		 tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
		 free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	       }
#line 1491 "parser.tab.c" /* glr.c:816  */
    break;

  case 32:
#line 549 "parser.y" /* glr.c:816  */
    { 
		 inputsize += 2;
		 agent_node *a;
		 char *index;
		 if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
		 sprintf(s, "box %s", index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
		 if (index != NULL) free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	       }
#line 1510 "parser.tab.c" /* glr.c:816  */
    break;

  case 33:
#line 564 "parser.y" /* glr.c:816  */
    {
		 inputsize += 2;
		 agent_node *a;
		 char * s = malloc(snprintf(NULL, 0, "box") + 1);
		 sprintf(s, "box");	  
		 a=insert_a_node(s);
		 tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
	       }
#line 1526 "parser.tab.c" /* glr.c:816  */
    break;

  case 34:
#line 576 "parser.y" /* glr.c:816  */
    { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname, *index;
		 pname = getBoxName(strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue)));
		 if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
		 sprintf(s, "%s %s", pname, index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth + 1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
		 free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
		 if (index != NULL) free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	       }
#line 1547 "parser.tab.c" /* glr.c:816  */
    break;

  case 35:
#line 593 "parser.y" /* glr.c:816  */
    { 
		 inputsize += 2;
		 agent_node *a;
		 char *pname;
		 pname = getBoxName(strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue)));
		 a = insert_a_node(pname);
		 tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth + 1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
		 free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	       }
#line 1564 "parser.tab.c" /* glr.c:816  */
    break;

  case 36:
#line 606 "parser.y" /* glr.c:816  */
    { 
		 inputsize += 2;
		 agent_node *a;
		 char *index;
		 if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));} else index=NULL;
		 char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
		 sprintf(s, "box %s", index);
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
		 if (index != NULL) free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	       }
#line 1583 "parser.tab.c" /* glr.c:816  */
    break;

  case 37:
#line 621 "parser.y" /* glr.c:816  */
    {
		 inputsize += 2;
		 agent_node *a;
		 char * s = malloc(snprintf(NULL, 0, "box") + 1);
		 sprintf(s, "box");	  
		 a=insert_a_node(s);
		 tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
		 int md = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode)->mdepth);
		 tnode *newimp = create_tnode(IMPLICATION,IMPLICATION,md,(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval.tnode),new,NULL);
		 ((*yyvalp).tnode) = newimp;
	       }
#line 1599 "parser.tab.c" /* glr.c:816  */
    break;

  case 38:
#line 634 "parser.y" /* glr.c:816  */
    {((*yyvalp).tnode) = NULL;}
#line 1605 "parser.tab.c" /* glr.c:816  */
    break;

  case 39:
#line 636 "parser.y" /* glr.c:816  */
    {
		       inputsize += 1;
		       if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL) {
                         int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
			 formulalist *list = tree_to_list(DISJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
			 tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,mdepth,NULL,NULL,list);
			 ((*yyvalp).tnode) = new;
		       }
		       else ((*yyvalp).tnode) =(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode);
		     }
#line 1620 "parser.tab.c" /* glr.c:816  */
    break;

  case 40:
#line 647 "parser.y" /* glr.c:816  */
    {
		       formulalist *list = tree_to_list(DISJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
		       tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth,NULL,NULL,list);
		       ((*yyvalp).tnode) = new;
		     }
#line 1630 "parser.tab.c" /* glr.c:816  */
    break;

  case 41:
#line 653 "parser.y" /* glr.c:816  */
    {
		       formulalist *list = tree_to_list(DISJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.tnode),NULL);
		       tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.tnode)->mdepth,NULL,NULL,list);
		       ((*yyvalp).tnode) = new;
		     }
#line 1640 "parser.tab.c" /* glr.c:816  */
    break;

  case 42:
#line 660 "parser.y" /* glr.c:816  */
    {((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);}
#line 1646 "parser.tab.c" /* glr.c:816  */
    break;

  case 43:
#line 662 "parser.y" /* glr.c:816  */
    {
	  inputsize += 1;
	  tnode *new = create_tnode(NEGATION,NEGATION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
        }
#line 1656 "parser.tab.c" /* glr.c:816  */
    break;

  case 44:
#line 669 "parser.y" /* glr.c:816  */
    {((*yyvalp).tnode) = NULL;}
#line 1662 "parser.tab.c" /* glr.c:816  */
    break;

  case 45:
#line 671 "parser.y" /* glr.c:816  */
    {
	   if ((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode) != NULL) {
	     int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	     formulalist *newlist = tree_to_list(CONJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
	     tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	     ((*yyvalp).tnode) = new;
	   }
	   else ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode);
	 }
#line 1676 "parser.tab.c" /* glr.c:816  */
    break;

  case 46:
#line 680 "parser.y" /* glr.c:816  */
    {numerrors++;}
#line 1682 "parser.tab.c" /* glr.c:816  */
    break;

  case 47:
#line 684 "parser.y" /* glr.c:816  */
    { // double-implications are not treated as abbreviations.
            // I would have a dag if I didn't want to copy the whole tree. 
            // and I don't want to deal with polarity at this point. 
	    // I am postponing whatever is to be done to when I need to put the formula into NNF.
	  inputsize += 1;
	  int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	  tnode *new = create_tnode(DOUBLEIMP,DOUBLEIMP,mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
	  ((*yyvalp).tnode) = new;
        }
#line 1696 "parser.tab.c" /* glr.c:816  */
    break;

  case 48:
#line 694 "parser.y" /* glr.c:816  */
    {
	  inputsize += 1;
	  int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	  tnode *new = create_tnode(IMPLICATION,IMPLICATION,mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL);
	  ((*yyvalp).tnode) = new;
        }
#line 1707 "parser.tab.c" /* glr.c:816  */
    break;

  case 49:
#line 701 "parser.y" /* glr.c:816  */
    {
	  inputsize += 1;
	  int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	  tnode *new = create_tnode(IMPLICATION,IMPLICATION,mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),NULL);
	  ((*yyvalp).tnode) = new;
        }
#line 1718 "parser.tab.c" /* glr.c:816  */
    break;

  case 50:
#line 708 "parser.y" /* glr.c:816  */
    {
	  inputsize += 1;
	  int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	  formulalist *newlist = tree_to_list(DISJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
	  tnode *new = create_tnode(DISJUNCTION,DISJUNCTION,mdepth,NULL,NULL,newlist);
	  ((*yyvalp).tnode) = new;
        }
#line 1730 "parser.tab.c" /* glr.c:816  */
    break;

  case 51:
#line 716 "parser.y" /* glr.c:816  */
    {
	  inputsize += 1;
	  int mdepth = MAX((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth);
	  formulalist *newlist = tree_to_list(CONJUNCTION,(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.tnode),(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode));
	  tnode *new = create_tnode(CONJUNCTION,CONJUNCTION,mdepth,NULL,NULL,newlist);
	  ((*yyvalp).tnode) = new;
        }
#line 1742 "parser.tab.c" /* glr.c:816  */
    break;

  case 52:
#line 724 "parser.y" /* glr.c:816  */
    {
	  // I was eliminating double negations here, but that changes the counting of the input formula. 
	  inputsize += 1;
          tnode *new = create_tnode(NEGATION,NEGATION,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	}
#line 1753 "parser.tab.c" /* glr.c:816  */
    break;

  case 53:
#line 731 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
          char *index;
          if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));} else index=NULL;
          char * s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
	  sprintf(s, "box %s", index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	  if (index != NULL) {
	    free(index);
	    free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	  }
	}
#line 1773 "parser.tab.c" /* glr.c:816  */
    break;

  case 54:
#line 747 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
          char *pname, *index;
          pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
          if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));} else index=NULL;
          char * s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	  sprintf(s, "%s %s", pname, index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	  free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	  if (index != NULL) {
	    free(index);
	    free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	  }
        }
#line 1795 "parser.tab.c" /* glr.c:816  */
    break;

  case 55:
#line 765 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
	  char * s = malloc(snprintf(NULL, 0, "box") + 1);
	  sprintf(s, "box");	  
	  a=insert_a_node(s);
          tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
        }
#line 1809 "parser.tab.c" /* glr.c:816  */
    break;

  case 56:
#line 775 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
          char *pname;
          pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	  a=insert_a_node(pname);
          tnode *new = create_tnode(BOX,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	  free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
        }
#line 1824 "parser.tab.c" /* glr.c:816  */
    break;

  case 57:
#line 786 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
          char *index;
          if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));} else index=NULL;
          char *s = malloc(snprintf(NULL, 0, "box %s", index) + 1);
	  sprintf(s, "box %s", index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	  if (index != NULL) {
	    free(index);
	    free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	  }
	}
#line 1844 "parser.tab.c" /* glr.c:816  */
    break;

  case 58:
#line 802 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1; // the modal_args count as zero (as part of the operator);
	  agent_node *a;
          char *pname, *index;
          pname = getBoxName(strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue)));
          if ((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue) !=NULL) {index = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));} else index=NULL;
          char *s = malloc(snprintf(NULL, 0, "%s %s", pname, index) + 1);
	  sprintf(s, "%s %s", pname, index);
	  a=insert_a_node(s);
	  tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth + 1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	  free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
	  if (index != NULL) {
	    free(index);
	    free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	  }
        }
#line 1866 "parser.tab.c" /* glr.c:816  */
    break;

  case 59:
#line 820 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
	  char * s = malloc(snprintf(NULL, 0, "box") + 1);
	  sprintf(s, "box");	  
	  a=insert_a_node(s);
          tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth+1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
        }
#line 1880 "parser.tab.c" /* glr.c:816  */
    break;

  case 60:
#line 830 "parser.y" /* glr.c:816  */
    { 
	  inputsize += 1;
	  agent_node *a;
          char *pname;
          pname = getBoxName(strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue)));
	  a = insert_a_node(pname);
	  tnode *new = create_tnode(DIAMOND,a->id,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode)->mdepth + 1,(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode),NULL,NULL);
	  ((*yyvalp).tnode) = new;
	  free((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.strValue));
	}
#line 1895 "parser.tab.c" /* glr.c:816  */
    break;

  case 61:
#line 841 "parser.y" /* glr.c:816  */
    {
	  ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval.tnode);
	}
#line 1903 "parser.tab.c" /* glr.c:816  */
    break;

  case 62:
#line 845 "parser.y" /* glr.c:816  */
    { 
	  ((*yyvalp).tnode) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.tnode);
        }
#line 1911 "parser.tab.c" /* glr.c:816  */
    break;

  case 63:
#line 851 "parser.y" /* glr.c:816  */
    {
		   char *prop = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
		   prop_list *new = malloc(sizeof(prop_list));
		   new->prop = prop;
		   new->next = NULL;
		   free((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
		   ((*yyvalp).prop_list) = new;
		 }
#line 1924 "parser.tab.c" /* glr.c:816  */
    break;

  case 64:
#line 860 "parser.y" /* glr.c:816  */
    {
		   char *prop = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
		   prop_list *new = malloc(sizeof(prop_list));
		   new->prop = prop;
		   new->next = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.prop_list);
		   free((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval.strValue));
		   ((*yyvalp).prop_list) = new;
		 }
#line 1937 "parser.tab.c" /* glr.c:816  */
    break;

  case 67:
#line 875 "parser.y" /* glr.c:816  */
    {
	     inputsize += 1;
             prop_node *p;
             char *pname = strdup((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));

	     char *s = malloc(snprintf(NULL, 0, "%s", pname) + 1);
	     sprintf(s, "%s", pname);
	     
	     p = insert_p_node(s);
	     tnode *new = create_tnode(PROP,p->id,0,NULL,NULL,NULL);
	     ((*yyvalp).tnode) = new;
	     free(pname);
	     free((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval.strValue));
	   }
#line 1956 "parser.tab.c" /* glr.c:816  */
    break;

  case 68:
#line 890 "parser.y" /* glr.c:816  */
    {
	     inputsize += 1;
	     // prop_node *p = find_prop(CSTART);
	     tnode *new = create_tnode(CONSTANT,CSTART,0,NULL,NULL,NULL);
	     ((*yyvalp).tnode)  = new;
	   }
#line 1967 "parser.tab.c" /* glr.c:816  */
    break;

  case 69:
#line 897 "parser.y" /* glr.c:816  */
    {
	     inputsize += 1;
	     //prop_node *p = find_prop(CTRUE);
	     tnode *new = create_tnode(CONSTANT,CTRUE,0,NULL,NULL,NULL);
	     ((*yyvalp).tnode)  = new;
	   }
#line 1978 "parser.tab.c" /* glr.c:816  */
    break;

  case 70:
#line 904 "parser.y" /* glr.c:816  */
    {
	     inputsize += 1;
	     //	     prop_node *p = find_prop(CFALSE);
	     tnode *new = create_tnode(CONSTANT,CFALSE,0,NULL,NULL,NULL);
	     ((*yyvalp).tnode) = new;
	   }
#line 1989 "parser.tab.c" /* glr.c:816  */
    break;


#line 1993 "parser.tab.c" /* glr.c:816  */
      default: break;
    }

  return yyok;
# undef yyerrok
# undef YYABORT
# undef YYACCEPT
# undef YYERROR
# undef YYBACKUP
# undef yyclearin
# undef YYRECOVERING
}


static void
yyuserMerge (int yyn, YYSTYPE* yy0, YYSTYPE* yy1)
{
  YYUSE (yy0);
  YYUSE (yy1);

  switch (yyn)
    {

      default: break;
    }
}

                              /* Bison grammar-table manipulation.  */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}

/** Number of symbols composing the right hand side of rule #RULE.  */
static inline int
yyrhsLength (yyRuleNum yyrule)
{
  return yyr2[yyrule];
}

static void
yydestroyGLRState (char const *yymsg, yyGLRState *yys)
{
  if (yys->yyresolved)
    yydestruct (yymsg, yystos[yys->yylrState],
                &yys->yysemantics.yysval);
  else
    {
#if YYDEBUG
      if (yydebug)
        {
          if (yys->yysemantics.yyfirstVal)
            YYFPRINTF (stderr, "%s unresolved", yymsg);
          else
            YYFPRINTF (stderr, "%s incomplete", yymsg);
          YY_SYMBOL_PRINT ("", yystos[yys->yylrState], YY_NULLPTR, &yys->yyloc);
        }
#endif

      if (yys->yysemantics.yyfirstVal)
        {
          yySemanticOption *yyoption = yys->yysemantics.yyfirstVal;
          yyGLRState *yyrh;
          int yyn;
          for (yyrh = yyoption->yystate, yyn = yyrhsLength (yyoption->yyrule);
               yyn > 0;
               yyrh = yyrh->yypred, yyn -= 1)
            yydestroyGLRState (yymsg, yyrh);
        }
    }
}

/** Left-hand-side symbol for rule #YYRULE.  */
static inline yySymbol
yylhsNonterm (yyRuleNum yyrule)
{
  return yyr1[yyrule];
}

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-106)))

/** True iff LR state YYSTATE has only a default reduction (regardless
 *  of token).  */
static inline yybool
yyisDefaultedState (yyStateNum yystate)
{
  return yypact_value_is_default (yypact[yystate]);
}

/** The default reduction for YYSTATE, assuming it has one.  */
static inline yyRuleNum
yydefaultAction (yyStateNum yystate)
{
  return yydefact[yystate];
}

#define yytable_value_is_error(Yytable_value) \
  0

/** Set *YYACTION to the action to take in YYSTATE on seeing YYTOKEN.
 *  Result R means
 *    R < 0:  Reduce on rule -R.
 *    R = 0:  Error.
 *    R > 0:  Shift to state R.
 *  Set *YYCONFLICTS to a pointer into yyconfl to a 0-terminated list
 *  of conflicting reductions.
 */
static inline void
yygetLRActions (yyStateNum yystate, int yytoken,
                int* yyaction, const short int** yyconflicts)
{
  int yyindex = yypact[yystate] + yytoken;
  if (yypact_value_is_default (yypact[yystate])
      || yyindex < 0 || YYLAST < yyindex || yycheck[yyindex] != yytoken)
    {
      *yyaction = -yydefact[yystate];
      *yyconflicts = yyconfl;
    }
  else if (! yytable_value_is_error (yytable[yyindex]))
    {
      *yyaction = yytable[yyindex];
      *yyconflicts = yyconfl + yyconflp[yyindex];
    }
  else
    {
      *yyaction = 0;
      *yyconflicts = yyconfl + yyconflp[yyindex];
    }
}

/** Compute post-reduction state.
 * \param yystate   the current state
 * \param yysym     the nonterminal to push on the stack
 */
static inline yyStateNum
yyLRgotoState (yyStateNum yystate, yySymbol yysym)
{
  int yyr = yypgoto[yysym - YYNTOKENS] + yystate;
  if (0 <= yyr && yyr <= YYLAST && yycheck[yyr] == yystate)
    return yytable[yyr];
  else
    return yydefgoto[yysym - YYNTOKENS];
}

static inline yybool
yyisShiftAction (int yyaction)
{
  return 0 < yyaction;
}

static inline yybool
yyisErrorAction (int yyaction)
{
  return yyaction == 0;
}

                                /* GLRStates */

/** Return a fresh GLRStackItem in YYSTACKP.  The item is an LR state
 *  if YYISSTATE, and otherwise a semantic option.  Callers should call
 *  YY_RESERVE_GLRSTACK afterwards to make sure there is sufficient
 *  headroom.  */

static inline yyGLRStackItem*
yynewGLRStackItem (yyGLRStack* yystackp, yybool yyisState)
{
  yyGLRStackItem* yynewItem = yystackp->yynextFree;
  yystackp->yyspaceLeft -= 1;
  yystackp->yynextFree += 1;
  yynewItem->yystate.yyisState = yyisState;
  return yynewItem;
}

/** Add a new semantic action that will execute the action for rule
 *  YYRULE on the semantic values in YYRHS to the list of
 *  alternative actions for YYSTATE.  Assumes that YYRHS comes from
 *  stack #YYK of *YYSTACKP. */
static void
yyaddDeferredAction (yyGLRStack* yystackp, size_t yyk, yyGLRState* yystate,
                     yyGLRState* yyrhs, yyRuleNum yyrule)
{
  yySemanticOption* yynewOption =
    &yynewGLRStackItem (yystackp, yyfalse)->yyoption;
  YYASSERT (!yynewOption->yyisState);
  yynewOption->yystate = yyrhs;
  yynewOption->yyrule = yyrule;
  if (yystackp->yytops.yylookaheadNeeds[yyk])
    {
      yynewOption->yyrawchar = yychar;
      yynewOption->yyval = yylval;
    }
  else
    yynewOption->yyrawchar = YYEMPTY;
  yynewOption->yynext = yystate->yysemantics.yyfirstVal;
  yystate->yysemantics.yyfirstVal = yynewOption;

  YY_RESERVE_GLRSTACK (yystackp);
}

                                /* GLRStacks */

/** Initialize YYSET to a singleton set containing an empty stack.  */
static yybool
yyinitStateSet (yyGLRStateSet* yyset)
{
  yyset->yysize = 1;
  yyset->yycapacity = 16;
  yyset->yystates = (yyGLRState**) YYMALLOC (16 * sizeof yyset->yystates[0]);
  if (! yyset->yystates)
    return yyfalse;
  yyset->yystates[0] = YY_NULLPTR;
  yyset->yylookaheadNeeds =
    (yybool*) YYMALLOC (16 * sizeof yyset->yylookaheadNeeds[0]);
  if (! yyset->yylookaheadNeeds)
    {
      YYFREE (yyset->yystates);
      return yyfalse;
    }
  return yytrue;
}

static void yyfreeStateSet (yyGLRStateSet* yyset)
{
  YYFREE (yyset->yystates);
  YYFREE (yyset->yylookaheadNeeds);
}

/** Initialize *YYSTACKP to a single empty stack, with total maximum
 *  capacity for all stacks of YYSIZE.  */
static yybool
yyinitGLRStack (yyGLRStack* yystackp, size_t yysize)
{
  yystackp->yyerrState = 0;
  yynerrs = 0;
  yystackp->yyspaceLeft = yysize;
  yystackp->yyitems =
    (yyGLRStackItem*) YYMALLOC (yysize * sizeof yystackp->yynextFree[0]);
  if (!yystackp->yyitems)
    return yyfalse;
  yystackp->yynextFree = yystackp->yyitems;
  yystackp->yysplitPoint = YY_NULLPTR;
  yystackp->yylastDeleted = YY_NULLPTR;
  return yyinitStateSet (&yystackp->yytops);
}


#if YYSTACKEXPANDABLE
# define YYRELOC(YYFROMITEMS,YYTOITEMS,YYX,YYTYPE) \
  &((YYTOITEMS) - ((YYFROMITEMS) - (yyGLRStackItem*) (YYX)))->YYTYPE

/** If *YYSTACKP is expandable, extend it.  WARNING: Pointers into the
    stack from outside should be considered invalid after this call.
    We always expand when there are 1 or fewer items left AFTER an
    allocation, so that we can avoid having external pointers exist
    across an allocation.  */
static void
yyexpandGLRStack (yyGLRStack* yystackp)
{
  yyGLRStackItem* yynewItems;
  yyGLRStackItem* yyp0, *yyp1;
  size_t yynewSize;
  size_t yyn;
  size_t yysize = yystackp->yynextFree - yystackp->yyitems;
  if (YYMAXDEPTH - YYHEADROOM < yysize)
    yyMemoryExhausted (yystackp);
  yynewSize = 2*yysize;
  if (YYMAXDEPTH < yynewSize)
    yynewSize = YYMAXDEPTH;
  yynewItems = (yyGLRStackItem*) YYMALLOC (yynewSize * sizeof yynewItems[0]);
  if (! yynewItems)
    yyMemoryExhausted (yystackp);
  for (yyp0 = yystackp->yyitems, yyp1 = yynewItems, yyn = yysize;
       0 < yyn;
       yyn -= 1, yyp0 += 1, yyp1 += 1)
    {
      *yyp1 = *yyp0;
      if (*(yybool *) yyp0)
        {
          yyGLRState* yys0 = &yyp0->yystate;
          yyGLRState* yys1 = &yyp1->yystate;
          if (yys0->yypred != YY_NULLPTR)
            yys1->yypred =
              YYRELOC (yyp0, yyp1, yys0->yypred, yystate);
          if (! yys0->yyresolved && yys0->yysemantics.yyfirstVal != YY_NULLPTR)
            yys1->yysemantics.yyfirstVal =
              YYRELOC (yyp0, yyp1, yys0->yysemantics.yyfirstVal, yyoption);
        }
      else
        {
          yySemanticOption* yyv0 = &yyp0->yyoption;
          yySemanticOption* yyv1 = &yyp1->yyoption;
          if (yyv0->yystate != YY_NULLPTR)
            yyv1->yystate = YYRELOC (yyp0, yyp1, yyv0->yystate, yystate);
          if (yyv0->yynext != YY_NULLPTR)
            yyv1->yynext = YYRELOC (yyp0, yyp1, yyv0->yynext, yyoption);
        }
    }
  if (yystackp->yysplitPoint != YY_NULLPTR)
    yystackp->yysplitPoint = YYRELOC (yystackp->yyitems, yynewItems,
                                      yystackp->yysplitPoint, yystate);

  for (yyn = 0; yyn < yystackp->yytops.yysize; yyn += 1)
    if (yystackp->yytops.yystates[yyn] != YY_NULLPTR)
      yystackp->yytops.yystates[yyn] =
        YYRELOC (yystackp->yyitems, yynewItems,
                 yystackp->yytops.yystates[yyn], yystate);
  YYFREE (yystackp->yyitems);
  yystackp->yyitems = yynewItems;
  yystackp->yynextFree = yynewItems + yysize;
  yystackp->yyspaceLeft = yynewSize - yysize;
}
#endif

static void
yyfreeGLRStack (yyGLRStack* yystackp)
{
  YYFREE (yystackp->yyitems);
  yyfreeStateSet (&yystackp->yytops);
}

/** Assuming that YYS is a GLRState somewhere on *YYSTACKP, update the
 *  splitpoint of *YYSTACKP, if needed, so that it is at least as deep as
 *  YYS.  */
static inline void
yyupdateSplit (yyGLRStack* yystackp, yyGLRState* yys)
{
  if (yystackp->yysplitPoint != YY_NULLPTR && yystackp->yysplitPoint > yys)
    yystackp->yysplitPoint = yys;
}

/** Invalidate stack #YYK in *YYSTACKP.  */
static inline void
yymarkStackDeleted (yyGLRStack* yystackp, size_t yyk)
{
  if (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
    yystackp->yylastDeleted = yystackp->yytops.yystates[yyk];
  yystackp->yytops.yystates[yyk] = YY_NULLPTR;
}

/** Undelete the last stack in *YYSTACKP that was marked as deleted.  Can
    only be done once after a deletion, and only when all other stacks have
    been deleted.  */
static void
yyundeleteLastStack (yyGLRStack* yystackp)
{
  if (yystackp->yylastDeleted == YY_NULLPTR || yystackp->yytops.yysize != 0)
    return;
  yystackp->yytops.yystates[0] = yystackp->yylastDeleted;
  yystackp->yytops.yysize = 1;
  YYDPRINTF ((stderr, "Restoring last deleted stack as stack #0.\n"));
  yystackp->yylastDeleted = YY_NULLPTR;
}

static inline void
yyremoveDeletes (yyGLRStack* yystackp)
{
  size_t yyi, yyj;
  yyi = yyj = 0;
  while (yyj < yystackp->yytops.yysize)
    {
      if (yystackp->yytops.yystates[yyi] == YY_NULLPTR)
        {
          if (yyi == yyj)
            {
              YYDPRINTF ((stderr, "Removing dead stacks.\n"));
            }
          yystackp->yytops.yysize -= 1;
        }
      else
        {
          yystackp->yytops.yystates[yyj] = yystackp->yytops.yystates[yyi];
          /* In the current implementation, it's unnecessary to copy
             yystackp->yytops.yylookaheadNeeds[yyi] since, after
             yyremoveDeletes returns, the parser immediately either enters
             deterministic operation or shifts a token.  However, it doesn't
             hurt, and the code might evolve to need it.  */
          yystackp->yytops.yylookaheadNeeds[yyj] =
            yystackp->yytops.yylookaheadNeeds[yyi];
          if (yyj != yyi)
            {
              YYDPRINTF ((stderr, "Rename stack %lu -> %lu.\n",
                          (unsigned long int) yyi, (unsigned long int) yyj));
            }
          yyj += 1;
        }
      yyi += 1;
    }
}

/** Shift to a new state on stack #YYK of *YYSTACKP, corresponding to LR
 * state YYLRSTATE, at input position YYPOSN, with (resolved) semantic
 * value *YYVALP and source location *YYLOCP.  */
static inline void
yyglrShift (yyGLRStack* yystackp, size_t yyk, yyStateNum yylrState,
            size_t yyposn,
            YYSTYPE* yyvalp)
{
  yyGLRState* yynewState = &yynewGLRStackItem (yystackp, yytrue)->yystate;

  yynewState->yylrState = yylrState;
  yynewState->yyposn = yyposn;
  yynewState->yyresolved = yytrue;
  yynewState->yypred = yystackp->yytops.yystates[yyk];
  yynewState->yysemantics.yysval = *yyvalp;
  yystackp->yytops.yystates[yyk] = yynewState;

  YY_RESERVE_GLRSTACK (yystackp);
}

/** Shift stack #YYK of *YYSTACKP, to a new state corresponding to LR
 *  state YYLRSTATE, at input position YYPOSN, with the (unresolved)
 *  semantic value of YYRHS under the action for YYRULE.  */
static inline void
yyglrShiftDefer (yyGLRStack* yystackp, size_t yyk, yyStateNum yylrState,
                 size_t yyposn, yyGLRState* yyrhs, yyRuleNum yyrule)
{
  yyGLRState* yynewState = &yynewGLRStackItem (yystackp, yytrue)->yystate;
  YYASSERT (yynewState->yyisState);

  yynewState->yylrState = yylrState;
  yynewState->yyposn = yyposn;
  yynewState->yyresolved = yyfalse;
  yynewState->yypred = yystackp->yytops.yystates[yyk];
  yynewState->yysemantics.yyfirstVal = YY_NULLPTR;
  yystackp->yytops.yystates[yyk] = yynewState;

  /* Invokes YY_RESERVE_GLRSTACK.  */
  yyaddDeferredAction (yystackp, yyk, yynewState, yyrhs, yyrule);
}

#if !YYDEBUG
# define YY_REDUCE_PRINT(Args)
#else
# define YY_REDUCE_PRINT(Args)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print Args;               \
} while (0)

/*----------------------------------------------------------------------.
| Report that stack #YYK of *YYSTACKP is going to be reduced by YYRULE. |
`----------------------------------------------------------------------*/

static inline void
yy_reduce_print (int yynormal, yyGLRStackItem* yyvsp, size_t yyk,
                 yyRuleNum yyrule)
{
  int yynrhs = yyrhsLength (yyrule);
  int yyi;
  YYFPRINTF (stderr, "Reducing stack %lu by rule %d (line %lu):\n",
             (unsigned long int) yyk, yyrule - 1,
             (unsigned long int) yyrline[yyrule]);
  if (! yynormal)
    yyfillin (yyvsp, 1, -yynrhs);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyvsp[yyi - yynrhs + 1].yystate.yylrState],
                       &yyvsp[yyi - yynrhs + 1].yystate.yysemantics.yysval
                                              );
      if (!yyvsp[yyi - yynrhs + 1].yystate.yyresolved)
        YYFPRINTF (stderr, " (unresolved)");
      YYFPRINTF (stderr, "\n");
    }
}
#endif

/** Pop the symbols consumed by reduction #YYRULE from the top of stack
 *  #YYK of *YYSTACKP, and perform the appropriate semantic action on their
 *  semantic values.  Assumes that all ambiguities in semantic values
 *  have been previously resolved.  Set *YYVALP to the resulting value,
 *  and *YYLOCP to the computed location (if any).  Return value is as
 *  for userAction.  */
static inline YYRESULTTAG
yydoAction (yyGLRStack* yystackp, size_t yyk, yyRuleNum yyrule,
            YYSTYPE* yyvalp)
{
  int yynrhs = yyrhsLength (yyrule);

  if (yystackp->yysplitPoint == YY_NULLPTR)
    {
      /* Standard special case: single stack.  */
      yyGLRStackItem* yyrhs = (yyGLRStackItem*) yystackp->yytops.yystates[yyk];
      YYASSERT (yyk == 0);
      yystackp->yynextFree -= yynrhs;
      yystackp->yyspaceLeft += yynrhs;
      yystackp->yytops.yystates[0] = & yystackp->yynextFree[-1].yystate;
      YY_REDUCE_PRINT ((1, yyrhs, yyk, yyrule));
      return yyuserAction (yyrule, yynrhs, yyrhs, yystackp,
                           yyvalp);
    }
  else
    {
      int yyi;
      yyGLRState* yys;
      yyGLRStackItem yyrhsVals[YYMAXRHS + YYMAXLEFT + 1];
      yys = yyrhsVals[YYMAXRHS + YYMAXLEFT].yystate.yypred
        = yystackp->yytops.yystates[yyk];
      for (yyi = 0; yyi < yynrhs; yyi += 1)
        {
          yys = yys->yypred;
          YYASSERT (yys);
        }
      yyupdateSplit (yystackp, yys);
      yystackp->yytops.yystates[yyk] = yys;
      YY_REDUCE_PRINT ((0, yyrhsVals + YYMAXRHS + YYMAXLEFT - 1, yyk, yyrule));
      return yyuserAction (yyrule, yynrhs, yyrhsVals + YYMAXRHS + YYMAXLEFT - 1,
                           yystackp, yyvalp);
    }
}

/** Pop items off stack #YYK of *YYSTACKP according to grammar rule YYRULE,
 *  and push back on the resulting nonterminal symbol.  Perform the
 *  semantic action associated with YYRULE and store its value with the
 *  newly pushed state, if YYFORCEEVAL or if *YYSTACKP is currently
 *  unambiguous.  Otherwise, store the deferred semantic action with
 *  the new state.  If the new state would have an identical input
 *  position, LR state, and predecessor to an existing state on the stack,
 *  it is identified with that existing state, eliminating stack #YYK from
 *  *YYSTACKP.  In this case, the semantic value is
 *  added to the options for the existing state's semantic value.
 */
static inline YYRESULTTAG
yyglrReduce (yyGLRStack* yystackp, size_t yyk, yyRuleNum yyrule,
             yybool yyforceEval)
{
  size_t yyposn = yystackp->yytops.yystates[yyk]->yyposn;

  if (yyforceEval || yystackp->yysplitPoint == YY_NULLPTR)
    {
      YYSTYPE yysval;

      YYRESULTTAG yyflag = yydoAction (yystackp, yyk, yyrule, &yysval);
      if (yyflag == yyerr && yystackp->yysplitPoint != YY_NULLPTR)
        {
          YYDPRINTF ((stderr, "Parse on stack %lu rejected by rule #%d.\n",
                     (unsigned long int) yyk, yyrule - 1));
        }
      if (yyflag != yyok)
        return yyflag;
      YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyrule], &yysval, &yyloc);
      yyglrShift (yystackp, yyk,
                  yyLRgotoState (yystackp->yytops.yystates[yyk]->yylrState,
                                 yylhsNonterm (yyrule)),
                  yyposn, &yysval);
    }
  else
    {
      size_t yyi;
      int yyn;
      yyGLRState* yys, *yys0 = yystackp->yytops.yystates[yyk];
      yyStateNum yynewLRState;

      for (yys = yystackp->yytops.yystates[yyk], yyn = yyrhsLength (yyrule);
           0 < yyn; yyn -= 1)
        {
          yys = yys->yypred;
          YYASSERT (yys);
        }
      yyupdateSplit (yystackp, yys);
      yynewLRState = yyLRgotoState (yys->yylrState, yylhsNonterm (yyrule));
      YYDPRINTF ((stderr,
                  "Reduced stack %lu by rule #%d; action deferred.  "
                  "Now in state %d.\n",
                  (unsigned long int) yyk, yyrule - 1, yynewLRState));
      for (yyi = 0; yyi < yystackp->yytops.yysize; yyi += 1)
        if (yyi != yyk && yystackp->yytops.yystates[yyi] != YY_NULLPTR)
          {
            yyGLRState *yysplit = yystackp->yysplitPoint;
            yyGLRState *yyp = yystackp->yytops.yystates[yyi];
            while (yyp != yys && yyp != yysplit && yyp->yyposn >= yyposn)
              {
                if (yyp->yylrState == yynewLRState && yyp->yypred == yys)
                  {
                    yyaddDeferredAction (yystackp, yyk, yyp, yys0, yyrule);
                    yymarkStackDeleted (yystackp, yyk);
                    YYDPRINTF ((stderr, "Merging stack %lu into stack %lu.\n",
                                (unsigned long int) yyk,
                                (unsigned long int) yyi));
                    return yyok;
                  }
                yyp = yyp->yypred;
              }
          }
      yystackp->yytops.yystates[yyk] = yys;
      yyglrShiftDefer (yystackp, yyk, yynewLRState, yyposn, yys0, yyrule);
    }
  return yyok;
}

static size_t
yysplitStack (yyGLRStack* yystackp, size_t yyk)
{
  if (yystackp->yysplitPoint == YY_NULLPTR)
    {
      YYASSERT (yyk == 0);
      yystackp->yysplitPoint = yystackp->yytops.yystates[yyk];
    }
  if (yystackp->yytops.yysize >= yystackp->yytops.yycapacity)
    {
      yyGLRState** yynewStates;
      yybool* yynewLookaheadNeeds;

      yynewStates = YY_NULLPTR;

      if (yystackp->yytops.yycapacity
          > (YYSIZEMAX / (2 * sizeof yynewStates[0])))
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yycapacity *= 2;

      yynewStates =
        (yyGLRState**) YYREALLOC (yystackp->yytops.yystates,
                                  (yystackp->yytops.yycapacity
                                   * sizeof yynewStates[0]));
      if (yynewStates == YY_NULLPTR)
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yystates = yynewStates;

      yynewLookaheadNeeds =
        (yybool*) YYREALLOC (yystackp->yytops.yylookaheadNeeds,
                             (yystackp->yytops.yycapacity
                              * sizeof yynewLookaheadNeeds[0]));
      if (yynewLookaheadNeeds == YY_NULLPTR)
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yylookaheadNeeds = yynewLookaheadNeeds;
    }
  yystackp->yytops.yystates[yystackp->yytops.yysize]
    = yystackp->yytops.yystates[yyk];
  yystackp->yytops.yylookaheadNeeds[yystackp->yytops.yysize]
    = yystackp->yytops.yylookaheadNeeds[yyk];
  yystackp->yytops.yysize += 1;
  return yystackp->yytops.yysize-1;
}

/** True iff YYY0 and YYY1 represent identical options at the top level.
 *  That is, they represent the same rule applied to RHS symbols
 *  that produce the same terminal symbols.  */
static yybool
yyidenticalOptions (yySemanticOption* yyy0, yySemanticOption* yyy1)
{
  if (yyy0->yyrule == yyy1->yyrule)
    {
      yyGLRState *yys0, *yys1;
      int yyn;
      for (yys0 = yyy0->yystate, yys1 = yyy1->yystate,
           yyn = yyrhsLength (yyy0->yyrule);
           yyn > 0;
           yys0 = yys0->yypred, yys1 = yys1->yypred, yyn -= 1)
        if (yys0->yyposn != yys1->yyposn)
          return yyfalse;
      return yytrue;
    }
  else
    return yyfalse;
}

/** Assuming identicalOptions (YYY0,YYY1), destructively merge the
 *  alternative semantic values for the RHS-symbols of YYY1 and YYY0.  */
static void
yymergeOptionSets (yySemanticOption* yyy0, yySemanticOption* yyy1)
{
  yyGLRState *yys0, *yys1;
  int yyn;
  for (yys0 = yyy0->yystate, yys1 = yyy1->yystate,
       yyn = yyrhsLength (yyy0->yyrule);
       yyn > 0;
       yys0 = yys0->yypred, yys1 = yys1->yypred, yyn -= 1)
    {
      if (yys0 == yys1)
        break;
      else if (yys0->yyresolved)
        {
          yys1->yyresolved = yytrue;
          yys1->yysemantics.yysval = yys0->yysemantics.yysval;
        }
      else if (yys1->yyresolved)
        {
          yys0->yyresolved = yytrue;
          yys0->yysemantics.yysval = yys1->yysemantics.yysval;
        }
      else
        {
          yySemanticOption** yyz0p = &yys0->yysemantics.yyfirstVal;
          yySemanticOption* yyz1 = yys1->yysemantics.yyfirstVal;
          while (yytrue)
            {
              if (yyz1 == *yyz0p || yyz1 == YY_NULLPTR)
                break;
              else if (*yyz0p == YY_NULLPTR)
                {
                  *yyz0p = yyz1;
                  break;
                }
              else if (*yyz0p < yyz1)
                {
                  yySemanticOption* yyz = *yyz0p;
                  *yyz0p = yyz1;
                  yyz1 = yyz1->yynext;
                  (*yyz0p)->yynext = yyz;
                }
              yyz0p = &(*yyz0p)->yynext;
            }
          yys1->yysemantics.yyfirstVal = yys0->yysemantics.yyfirstVal;
        }
    }
}

/** Y0 and Y1 represent two possible actions to take in a given
 *  parsing state; return 0 if no combination is possible,
 *  1 if user-mergeable, 2 if Y0 is preferred, 3 if Y1 is preferred.  */
static int
yypreference (yySemanticOption* y0, yySemanticOption* y1)
{
  yyRuleNum r0 = y0->yyrule, r1 = y1->yyrule;
  int p0 = yydprec[r0], p1 = yydprec[r1];

  if (p0 == p1)
    {
      if (yymerger[r0] == 0 || yymerger[r0] != yymerger[r1])
        return 0;
      else
        return 1;
    }
  if (p0 == 0 || p1 == 0)
    return 0;
  if (p0 < p1)
    return 3;
  if (p1 < p0)
    return 2;
  return 0;
}

static YYRESULTTAG yyresolveValue (yyGLRState* yys,
                                   yyGLRStack* yystackp);


/** Resolve the previous YYN states starting at and including state YYS
 *  on *YYSTACKP. If result != yyok, some states may have been left
 *  unresolved possibly with empty semantic option chains.  Regardless
 *  of whether result = yyok, each state has been left with consistent
 *  data so that yydestroyGLRState can be invoked if necessary.  */
static YYRESULTTAG
yyresolveStates (yyGLRState* yys, int yyn,
                 yyGLRStack* yystackp)
{
  if (0 < yyn)
    {
      YYASSERT (yys->yypred);
      YYCHK (yyresolveStates (yys->yypred, yyn-1, yystackp));
      if (! yys->yyresolved)
        YYCHK (yyresolveValue (yys, yystackp));
    }
  return yyok;
}

/** Resolve the states for the RHS of YYOPT on *YYSTACKP, perform its
 *  user action, and return the semantic value and location in *YYVALP
 *  and *YYLOCP.  Regardless of whether result = yyok, all RHS states
 *  have been destroyed (assuming the user action destroys all RHS
 *  semantic values if invoked).  */
static YYRESULTTAG
yyresolveAction (yySemanticOption* yyopt, yyGLRStack* yystackp,
                 YYSTYPE* yyvalp)
{
  yyGLRStackItem yyrhsVals[YYMAXRHS + YYMAXLEFT + 1];
  int yynrhs = yyrhsLength (yyopt->yyrule);
  YYRESULTTAG yyflag =
    yyresolveStates (yyopt->yystate, yynrhs, yystackp);
  if (yyflag != yyok)
    {
      yyGLRState *yys;
      for (yys = yyopt->yystate; yynrhs > 0; yys = yys->yypred, yynrhs -= 1)
        yydestroyGLRState ("Cleanup: popping", yys);
      return yyflag;
    }

  yyrhsVals[YYMAXRHS + YYMAXLEFT].yystate.yypred = yyopt->yystate;
  {
    int yychar_current = yychar;
    YYSTYPE yylval_current = yylval;
    yychar = yyopt->yyrawchar;
    yylval = yyopt->yyval;
    yyflag = yyuserAction (yyopt->yyrule, yynrhs,
                           yyrhsVals + YYMAXRHS + YYMAXLEFT - 1,
                           yystackp, yyvalp);
    yychar = yychar_current;
    yylval = yylval_current;
  }
  return yyflag;
}

#if YYDEBUG
static void
yyreportTree (yySemanticOption* yyx, int yyindent)
{
  int yynrhs = yyrhsLength (yyx->yyrule);
  int yyi;
  yyGLRState* yys;
  yyGLRState* yystates[1 + YYMAXRHS];
  yyGLRState yyleftmost_state;

  for (yyi = yynrhs, yys = yyx->yystate; 0 < yyi; yyi -= 1, yys = yys->yypred)
    yystates[yyi] = yys;
  if (yys == YY_NULLPTR)
    {
      yyleftmost_state.yyposn = 0;
      yystates[0] = &yyleftmost_state;
    }
  else
    yystates[0] = yys;

  if (yyx->yystate->yyposn < yys->yyposn + 1)
    YYFPRINTF (stderr, "%*s%s -> <Rule %d, empty>\n",
               yyindent, "", yytokenName (yylhsNonterm (yyx->yyrule)),
               yyx->yyrule - 1);
  else
    YYFPRINTF (stderr, "%*s%s -> <Rule %d, tokens %lu .. %lu>\n",
               yyindent, "", yytokenName (yylhsNonterm (yyx->yyrule)),
               yyx->yyrule - 1, (unsigned long int) (yys->yyposn + 1),
               (unsigned long int) yyx->yystate->yyposn);
  for (yyi = 1; yyi <= yynrhs; yyi += 1)
    {
      if (yystates[yyi]->yyresolved)
        {
          if (yystates[yyi-1]->yyposn+1 > yystates[yyi]->yyposn)
            YYFPRINTF (stderr, "%*s%s <empty>\n", yyindent+2, "",
                       yytokenName (yystos[yystates[yyi]->yylrState]));
          else
            YYFPRINTF (stderr, "%*s%s <tokens %lu .. %lu>\n", yyindent+2, "",
                       yytokenName (yystos[yystates[yyi]->yylrState]),
                       (unsigned long int) (yystates[yyi-1]->yyposn + 1),
                       (unsigned long int) yystates[yyi]->yyposn);
        }
      else
        yyreportTree (yystates[yyi]->yysemantics.yyfirstVal, yyindent+2);
    }
}
#endif

static YYRESULTTAG
yyreportAmbiguity (yySemanticOption* yyx0,
                   yySemanticOption* yyx1)
{
  YYUSE (yyx0);
  YYUSE (yyx1);

#if YYDEBUG
  YYFPRINTF (stderr, "Ambiguity detected.\n");
  YYFPRINTF (stderr, "Option 1,\n");
  yyreportTree (yyx0, 2);
  YYFPRINTF (stderr, "\nOption 2,\n");
  yyreportTree (yyx1, 2);
  YYFPRINTF (stderr, "\n");
#endif

  yyerror (YY_("syntax is ambiguous"));
  return yyabort;
}

/** Resolve the ambiguity represented in state YYS in *YYSTACKP,
 *  perform the indicated actions, and set the semantic value of YYS.
 *  If result != yyok, the chain of semantic options in YYS has been
 *  cleared instead or it has been left unmodified except that
 *  redundant options may have been removed.  Regardless of whether
 *  result = yyok, YYS has been left with consistent data so that
 *  yydestroyGLRState can be invoked if necessary.  */
static YYRESULTTAG
yyresolveValue (yyGLRState* yys, yyGLRStack* yystackp)
{
  yySemanticOption* yyoptionList = yys->yysemantics.yyfirstVal;
  yySemanticOption* yybest = yyoptionList;
  yySemanticOption** yypp;
  yybool yymerge = yyfalse;
  YYSTYPE yysval;
  YYRESULTTAG yyflag;

  for (yypp = &yyoptionList->yynext; *yypp != YY_NULLPTR; )
    {
      yySemanticOption* yyp = *yypp;

      if (yyidenticalOptions (yybest, yyp))
        {
          yymergeOptionSets (yybest, yyp);
          *yypp = yyp->yynext;
        }
      else
        {
          switch (yypreference (yybest, yyp))
            {
            case 0:
              return yyreportAmbiguity (yybest, yyp);
              break;
            case 1:
              yymerge = yytrue;
              break;
            case 2:
              break;
            case 3:
              yybest = yyp;
              yymerge = yyfalse;
              break;
            default:
              /* This cannot happen so it is not worth a YYASSERT (yyfalse),
                 but some compilers complain if the default case is
                 omitted.  */
              break;
            }
          yypp = &yyp->yynext;
        }
    }

  if (yymerge)
    {
      yySemanticOption* yyp;
      int yyprec = yydprec[yybest->yyrule];
      yyflag = yyresolveAction (yybest, yystackp, &yysval);
      if (yyflag == yyok)
        for (yyp = yybest->yynext; yyp != YY_NULLPTR; yyp = yyp->yynext)
          {
            if (yyprec == yydprec[yyp->yyrule])
              {
                YYSTYPE yysval_other;
                yyflag = yyresolveAction (yyp, yystackp, &yysval_other);
                if (yyflag != yyok)
                  {
                    yydestruct ("Cleanup: discarding incompletely merged value for",
                                yystos[yys->yylrState],
                                &yysval);
                    break;
                  }
                yyuserMerge (yymerger[yyp->yyrule], &yysval, &yysval_other);
              }
          }
    }
  else
    yyflag = yyresolveAction (yybest, yystackp, &yysval);

  if (yyflag == yyok)
    {
      yys->yyresolved = yytrue;
      yys->yysemantics.yysval = yysval;
    }
  else
    yys->yysemantics.yyfirstVal = YY_NULLPTR;
  return yyflag;
}

static YYRESULTTAG
yyresolveStack (yyGLRStack* yystackp)
{
  if (yystackp->yysplitPoint != YY_NULLPTR)
    {
      yyGLRState* yys;
      int yyn;

      for (yyn = 0, yys = yystackp->yytops.yystates[0];
           yys != yystackp->yysplitPoint;
           yys = yys->yypred, yyn += 1)
        continue;
      YYCHK (yyresolveStates (yystackp->yytops.yystates[0], yyn, yystackp
                             ));
    }
  return yyok;
}

static void
yycompressStack (yyGLRStack* yystackp)
{
  yyGLRState* yyp, *yyq, *yyr;

  if (yystackp->yytops.yysize != 1 || yystackp->yysplitPoint == YY_NULLPTR)
    return;

  for (yyp = yystackp->yytops.yystates[0], yyq = yyp->yypred, yyr = YY_NULLPTR;
       yyp != yystackp->yysplitPoint;
       yyr = yyp, yyp = yyq, yyq = yyp->yypred)
    yyp->yypred = yyr;

  yystackp->yyspaceLeft += yystackp->yynextFree - yystackp->yyitems;
  yystackp->yynextFree = ((yyGLRStackItem*) yystackp->yysplitPoint) + 1;
  yystackp->yyspaceLeft -= yystackp->yynextFree - yystackp->yyitems;
  yystackp->yysplitPoint = YY_NULLPTR;
  yystackp->yylastDeleted = YY_NULLPTR;

  while (yyr != YY_NULLPTR)
    {
      yystackp->yynextFree->yystate = *yyr;
      yyr = yyr->yypred;
      yystackp->yynextFree->yystate.yypred = &yystackp->yynextFree[-1].yystate;
      yystackp->yytops.yystates[0] = &yystackp->yynextFree->yystate;
      yystackp->yynextFree += 1;
      yystackp->yyspaceLeft -= 1;
    }
}

static YYRESULTTAG
yyprocessOneStack (yyGLRStack* yystackp, size_t yyk,
                   size_t yyposn)
{
  while (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
    {
      yyStateNum yystate = yystackp->yytops.yystates[yyk]->yylrState;
      YYDPRINTF ((stderr, "Stack %lu Entering state %d\n",
                  (unsigned long int) yyk, yystate));

      YYASSERT (yystate != YYFINAL);

      if (yyisDefaultedState (yystate))
        {
          YYRESULTTAG yyflag;
          yyRuleNum yyrule = yydefaultAction (yystate);
          if (yyrule == 0)
            {
              YYDPRINTF ((stderr, "Stack %lu dies.\n",
                          (unsigned long int) yyk));
              yymarkStackDeleted (yystackp, yyk);
              return yyok;
            }
          yyflag = yyglrReduce (yystackp, yyk, yyrule, yyimmediate[yyrule]);
          if (yyflag == yyerr)
            {
              YYDPRINTF ((stderr,
                          "Stack %lu dies "
                          "(predicate failure or explicit user error).\n",
                          (unsigned long int) yyk));
              yymarkStackDeleted (yystackp, yyk);
              return yyok;
            }
          if (yyflag != yyok)
            return yyflag;
        }
      else
        {
          yySymbol yytoken;
          int yyaction;
          const short int* yyconflicts;

          yystackp->yytops.yylookaheadNeeds[yyk] = yytrue;
          if (yychar == YYEMPTY)
            {
              YYDPRINTF ((stderr, "Reading a token: "));
              yychar = yylex (&yylval);
            }

          if (yychar <= YYEOF)
            {
              yychar = yytoken = YYEOF;
              YYDPRINTF ((stderr, "Now at end of input.\n"));
            }
          else
            {
              yytoken = YYTRANSLATE (yychar);
              YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
            }

          yygetLRActions (yystate, yytoken, &yyaction, &yyconflicts);

          while (*yyconflicts != 0)
            {
              YYRESULTTAG yyflag;
              size_t yynewStack = yysplitStack (yystackp, yyk);
              YYDPRINTF ((stderr, "Splitting off stack %lu from %lu.\n",
                          (unsigned long int) yynewStack,
                          (unsigned long int) yyk));
              yyflag = yyglrReduce (yystackp, yynewStack,
                                    *yyconflicts,
                                    yyimmediate[*yyconflicts]);
              if (yyflag == yyok)
                YYCHK (yyprocessOneStack (yystackp, yynewStack,
                                          yyposn));
              else if (yyflag == yyerr)
                {
                  YYDPRINTF ((stderr, "Stack %lu dies.\n",
                              (unsigned long int) yynewStack));
                  yymarkStackDeleted (yystackp, yynewStack);
                }
              else
                return yyflag;
              yyconflicts += 1;
            }

          if (yyisShiftAction (yyaction))
            break;
          else if (yyisErrorAction (yyaction))
            {
              YYDPRINTF ((stderr, "Stack %lu dies.\n",
                          (unsigned long int) yyk));
              yymarkStackDeleted (yystackp, yyk);
              break;
            }
          else
            {
              YYRESULTTAG yyflag = yyglrReduce (yystackp, yyk, -yyaction,
                                                yyimmediate[-yyaction]);
              if (yyflag == yyerr)
                {
                  YYDPRINTF ((stderr,
                              "Stack %lu dies "
                              "(predicate failure or explicit user error).\n",
                              (unsigned long int) yyk));
                  yymarkStackDeleted (yystackp, yyk);
                  break;
                }
              else if (yyflag != yyok)
                return yyflag;
            }
        }
    }
  return yyok;
}

static void
yyreportSyntaxError (yyGLRStack* yystackp)
{
  if (yystackp->yyerrState != 0)
    return;
#if ! YYERROR_VERBOSE
  yyerror (YY_("syntax error"));
#else
  {
  yySymbol yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);
  size_t yysize0 = yytnamerr (YY_NULLPTR, yytokenName (yytoken));
  size_t yysize = yysize0;
  yybool yysize_overflow = yyfalse;
  char* yymsg = YY_NULLPTR;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected").  */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[yystackp->yytops.yystates[0]->yylrState];
      yyarg[yycount++] = yytokenName (yytoken);
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for this
             state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;
          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytokenName (yyx);
                {
                  size_t yysz = yysize + yytnamerr (YY_NULLPTR, yytokenName (yyx));
                  yysize_overflow |= yysz < yysize;
                  yysize = yysz;
                }
              }
        }
    }

  switch (yycount)
    {
#define YYCASE_(N, S)                   \
      case N:                           \
        yyformat = S;                   \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  {
    size_t yysz = yysize + strlen (yyformat);
    yysize_overflow |= yysz < yysize;
    yysize = yysz;
  }

  if (!yysize_overflow)
    yymsg = (char *) YYMALLOC (yysize);

  if (yymsg)
    {
      char *yyp = yymsg;
      int yyi = 0;
      while ((*yyp = *yyformat))
        {
          if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
            {
              yyp += yytnamerr (yyp, yyarg[yyi++]);
              yyformat += 2;
            }
          else
            {
              yyp++;
              yyformat++;
            }
        }
      yyerror (yymsg);
      YYFREE (yymsg);
    }
  else
    {
      yyerror (YY_("syntax error"));
      yyMemoryExhausted (yystackp);
    }
  }
#endif /* YYERROR_VERBOSE */
  yynerrs += 1;
}

/* Recover from a syntax error on *YYSTACKP, assuming that *YYSTACKP->YYTOKENP,
   yylval, and yylloc are the syntactic category, semantic value, and location
   of the lookahead.  */
static void
yyrecoverSyntaxError (yyGLRStack* yystackp)
{
  size_t yyk;
  int yyj;

  if (yystackp->yyerrState == 3)
    /* We just shifted the error token and (perhaps) took some
       reductions.  Skip tokens until we can proceed.  */
    while (yytrue)
      {
        yySymbol yytoken;
        if (yychar == YYEOF)
          yyFail (yystackp, YY_NULLPTR);
        if (yychar != YYEMPTY)
          {
            yytoken = YYTRANSLATE (yychar);
            yydestruct ("Error: discarding",
                        yytoken, &yylval);
          }
        YYDPRINTF ((stderr, "Reading a token: "));
        yychar = yylex (&yylval);
        if (yychar <= YYEOF)
          {
            yychar = yytoken = YYEOF;
            YYDPRINTF ((stderr, "Now at end of input.\n"));
          }
        else
          {
            yytoken = YYTRANSLATE (yychar);
            YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
          }
        yyj = yypact[yystackp->yytops.yystates[0]->yylrState];
        if (yypact_value_is_default (yyj))
          return;
        yyj += yytoken;
        if (yyj < 0 || YYLAST < yyj || yycheck[yyj] != yytoken)
          {
            if (yydefact[yystackp->yytops.yystates[0]->yylrState] != 0)
              return;
          }
        else if (! yytable_value_is_error (yytable[yyj]))
          return;
      }

  /* Reduce to one stack.  */
  for (yyk = 0; yyk < yystackp->yytops.yysize; yyk += 1)
    if (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
      break;
  if (yyk >= yystackp->yytops.yysize)
    yyFail (yystackp, YY_NULLPTR);
  for (yyk += 1; yyk < yystackp->yytops.yysize; yyk += 1)
    yymarkStackDeleted (yystackp, yyk);
  yyremoveDeletes (yystackp);
  yycompressStack (yystackp);

  /* Now pop stack until we find a state that shifts the error token.  */
  yystackp->yyerrState = 3;
  while (yystackp->yytops.yystates[0] != YY_NULLPTR)
    {
      yyGLRState *yys = yystackp->yytops.yystates[0];
      yyj = yypact[yys->yylrState];
      if (! yypact_value_is_default (yyj))
        {
          yyj += YYTERROR;
          if (0 <= yyj && yyj <= YYLAST && yycheck[yyj] == YYTERROR
              && yyisShiftAction (yytable[yyj]))
            {
              /* Shift the error token.  */
              YY_SYMBOL_PRINT ("Shifting", yystos[yytable[yyj]],
                               &yylval, &yyerrloc);
              yyglrShift (yystackp, 0, yytable[yyj],
                          yys->yyposn, &yylval);
              yys = yystackp->yytops.yystates[0];
              break;
            }
        }
      if (yys->yypred != YY_NULLPTR)
        yydestroyGLRState ("Error: popping", yys);
      yystackp->yytops.yystates[0] = yys->yypred;
      yystackp->yynextFree -= 1;
      yystackp->yyspaceLeft += 1;
    }
  if (yystackp->yytops.yystates[0] == YY_NULLPTR)
    yyFail (yystackp, YY_NULLPTR);
}

#define YYCHK1(YYE)                                                          \
  do {                                                                       \
    switch (YYE) {                                                           \
    case yyok:                                                               \
      break;                                                                 \
    case yyabort:                                                            \
      goto yyabortlab;                                                       \
    case yyaccept:                                                           \
      goto yyacceptlab;                                                      \
    case yyerr:                                                              \
      goto yyuser_error;                                                     \
    default:                                                                 \
      goto yybuglab;                                                         \
    }                                                                        \
  } while (0)

/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
  int yyresult;
  yyGLRStack yystack;
  yyGLRStack* const yystackp = &yystack;
  size_t yyposn;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY;
  yylval = yyval_default;

  if (! yyinitGLRStack (yystackp, YYINITDEPTH))
    goto yyexhaustedlab;
  switch (YYSETJMP (yystack.yyexception_buffer))
    {
    case 0: break;
    case 1: goto yyabortlab;
    case 2: goto yyexhaustedlab;
    default: goto yybuglab;
    }
  yyglrShift (&yystack, 0, 0, 0, &yylval);
  yyposn = 0;

  while (yytrue)
    {
      /* For efficiency, we have two loops, the first of which is
         specialized to deterministic operation (single stack, no
         potential ambiguity).  */
      /* Standard mode */
      while (yytrue)
        {
          yyRuleNum yyrule;
          int yyaction;
          const short int* yyconflicts;

          yyStateNum yystate = yystack.yytops.yystates[0]->yylrState;
          YYDPRINTF ((stderr, "Entering state %d\n", yystate));
          if (yystate == YYFINAL)
            goto yyacceptlab;
          if (yyisDefaultedState (yystate))
            {
              yyrule = yydefaultAction (yystate);
              if (yyrule == 0)
                {

                  yyreportSyntaxError (&yystack);
                  goto yyuser_error;
                }
              YYCHK1 (yyglrReduce (&yystack, 0, yyrule, yytrue));
            }
          else
            {
              yySymbol yytoken;
              if (yychar == YYEMPTY)
                {
                  YYDPRINTF ((stderr, "Reading a token: "));
                  yychar = yylex (&yylval);
                }

              if (yychar <= YYEOF)
                {
                  yychar = yytoken = YYEOF;
                  YYDPRINTF ((stderr, "Now at end of input.\n"));
                }
              else
                {
                  yytoken = YYTRANSLATE (yychar);
                  YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
                }

              yygetLRActions (yystate, yytoken, &yyaction, &yyconflicts);
              if (*yyconflicts != 0)
                break;
              if (yyisShiftAction (yyaction))
                {
                  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
                  yychar = YYEMPTY;
                  yyposn += 1;
                  yyglrShift (&yystack, 0, yyaction, yyposn, &yylval);
                  if (0 < yystack.yyerrState)
                    yystack.yyerrState -= 1;
                }
              else if (yyisErrorAction (yyaction))
                {

                  yyreportSyntaxError (&yystack);
                  goto yyuser_error;
                }
              else
                YYCHK1 (yyglrReduce (&yystack, 0, -yyaction, yytrue));
            }
        }

      while (yytrue)
        {
          yySymbol yytoken_to_shift;
          size_t yys;

          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            yystackp->yytops.yylookaheadNeeds[yys] = yychar != YYEMPTY;

          /* yyprocessOneStack returns one of three things:

              - An error flag.  If the caller is yyprocessOneStack, it
                immediately returns as well.  When the caller is finally
                yyparse, it jumps to an error label via YYCHK1.

              - yyok, but yyprocessOneStack has invoked yymarkStackDeleted
                (&yystack, yys), which sets the top state of yys to NULL.  Thus,
                yyparse's following invocation of yyremoveDeletes will remove
                the stack.

              - yyok, when ready to shift a token.

             Except in the first case, yyparse will invoke yyremoveDeletes and
             then shift the next token onto all remaining stacks.  This
             synchronization of the shift (that is, after all preceding
             reductions on all stacks) helps prevent double destructor calls
             on yylval in the event of memory exhaustion.  */

          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            YYCHK1 (yyprocessOneStack (&yystack, yys, yyposn));
          yyremoveDeletes (&yystack);
          if (yystack.yytops.yysize == 0)
            {
              yyundeleteLastStack (&yystack);
              if (yystack.yytops.yysize == 0)
                yyFail (&yystack, YY_("syntax error"));
              YYCHK1 (yyresolveStack (&yystack));
              YYDPRINTF ((stderr, "Returning to deterministic operation.\n"));

              yyreportSyntaxError (&yystack);
              goto yyuser_error;
            }

          /* If any yyglrShift call fails, it will fail after shifting.  Thus,
             a copy of yylval will already be on stack 0 in the event of a
             failure in the following loop.  Thus, yychar is set to YYEMPTY
             before the loop to make sure the user destructor for yylval isn't
             called twice.  */
          yytoken_to_shift = YYTRANSLATE (yychar);
          yychar = YYEMPTY;
          yyposn += 1;
          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            {
              int yyaction;
              const short int* yyconflicts;
              yyStateNum yystate = yystack.yytops.yystates[yys]->yylrState;
              yygetLRActions (yystate, yytoken_to_shift, &yyaction,
                              &yyconflicts);
              /* Note that yyconflicts were handled by yyprocessOneStack.  */
              YYDPRINTF ((stderr, "On stack %lu, ", (unsigned long int) yys));
              YY_SYMBOL_PRINT ("shifting", yytoken_to_shift, &yylval, &yylloc);
              yyglrShift (&yystack, yys, yyaction, yyposn,
                          &yylval);
              YYDPRINTF ((stderr, "Stack %lu now in state #%d\n",
                          (unsigned long int) yys,
                          yystack.yytops.yystates[yys]->yylrState));
            }

          if (yystack.yytops.yysize == 1)
            {
              YYCHK1 (yyresolveStack (&yystack));
              YYDPRINTF ((stderr, "Returning to deterministic operation.\n"));
              yycompressStack (&yystack);
              break;
            }
        }
      continue;
    yyuser_error:
      yyrecoverSyntaxError (&yystack);
      yyposn = yystack.yytops.yystates[0]->yyposn;
    }

 yyacceptlab:
  yyresult = 0;
  goto yyreturn;

 yybuglab:
  YYASSERT (yyfalse);
  goto yyabortlab;

 yyabortlab:
  yyresult = 1;
  goto yyreturn;

 yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturn;

 yyreturn:
  if (yychar != YYEMPTY)
    yydestruct ("Cleanup: discarding lookahead",
                YYTRANSLATE (yychar), &yylval);

  /* If the stack is well-formed, pop the stack until it is empty,
     destroying its entries as we go.  But free the stack regardless
     of whether it is well-formed.  */
  if (yystack.yyitems)
    {
      yyGLRState** yystates = yystack.yytops.yystates;
      if (yystates)
        {
          size_t yysize = yystack.yytops.yysize;
          size_t yyk;
          for (yyk = 0; yyk < yysize; yyk += 1)
            if (yystates[yyk])
              {
                while (yystates[yyk])
                  {
                    yyGLRState *yys = yystates[yyk];
                  if (yys->yypred != YY_NULLPTR)
                      yydestroyGLRState ("Cleanup: popping", yys);
                    yystates[yyk] = yys->yypred;
                    yystack.yynextFree -= 1;
                    yystack.yyspaceLeft += 1;
                  }
                break;
              }
        }
      yyfreeGLRStack (&yystack);
    }

  return yyresult;
}

/* DEBUGGING ONLY */
#if YYDEBUG
static void
yy_yypstack (yyGLRState* yys)
{
  if (yys->yypred)
    {
      yy_yypstack (yys->yypred);
      YYFPRINTF (stderr, " -> ");
    }
  YYFPRINTF (stderr, "%d@%lu", yys->yylrState,
             (unsigned long int) yys->yyposn);
}

static void
yypstates (yyGLRState* yyst)
{
  if (yyst == YY_NULLPTR)
    YYFPRINTF (stderr, "<null>");
  else
    yy_yypstack (yyst);
  YYFPRINTF (stderr, "\n");
}

static void
yypstack (yyGLRStack* yystackp, size_t yyk)
{
  yypstates (yystackp->yytops.yystates[yyk]);
}

#define YYINDEX(YYX)                                                         \
    ((YYX) == YY_NULLPTR ? -1 : (yyGLRStackItem*) (YYX) - yystackp->yyitems)


static void
yypdumpstack (yyGLRStack* yystackp)
{
  yyGLRStackItem* yyp;
  size_t yyi;
  for (yyp = yystackp->yyitems; yyp < yystackp->yynextFree; yyp += 1)
    {
      YYFPRINTF (stderr, "%3lu. ",
                 (unsigned long int) (yyp - yystackp->yyitems));
      if (*(yybool *) yyp)
        {
          YYASSERT (yyp->yystate.yyisState);
          YYASSERT (yyp->yyoption.yyisState);
          YYFPRINTF (stderr, "Res: %d, LR State: %d, posn: %lu, pred: %ld",
                     yyp->yystate.yyresolved, yyp->yystate.yylrState,
                     (unsigned long int) yyp->yystate.yyposn,
                     (long int) YYINDEX (yyp->yystate.yypred));
          if (! yyp->yystate.yyresolved)
            YYFPRINTF (stderr, ", firstVal: %ld",
                       (long int) YYINDEX (yyp->yystate
                                             .yysemantics.yyfirstVal));
        }
      else
        {
          YYASSERT (!yyp->yystate.yyisState);
          YYASSERT (!yyp->yyoption.yyisState);
          YYFPRINTF (stderr, "Option. rule: %d, state: %ld, next: %ld",
                     yyp->yyoption.yyrule - 1,
                     (long int) YYINDEX (yyp->yyoption.yystate),
                     (long int) YYINDEX (yyp->yyoption.yynext));
        }
      YYFPRINTF (stderr, "\n");
    }
  YYFPRINTF (stderr, "Tops:");
  for (yyi = 0; yyi < yystackp->yytops.yysize; yyi += 1)
    YYFPRINTF (stderr, "%lu: %ld; ", (unsigned long int) yyi,
               (long int) YYINDEX (yystackp->yytops.yystates[yyi]));
  YYFPRINTF (stderr, "\n");
}
#endif

#undef yylval
#undef yychar
#undef yynerrs



#line 912 "parser.y" /* glr.c:2584  */



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

