typedef struct pair_t pair_t;
typedef struct tbranch tbranch;

typedef struct tbranch{
    unsigned int id;
    int closed;
    int ml; /* modal level */
    int agent;
    int tliterals;
    //int litmin;
    //int litmax;
    struct literalshash *literals;
}tbranch;

typedef struct brancheslist{
    tbranch *branch;
    struct brancheslist *next;
}brancheslist;

typedef struct hidbranches{
    unsigned int id;
    tbranch *branch;
    UT_hash_handle hid;
}hidbranches;

typedef struct hmaxbranches {
    int max;
    hidbranches *branches;
    UT_hash_handle hmax;
}hmaxbranches;

typedef struct hminbranches {
    int min;
    hmaxbranches *litmax;
    UT_hash_handle hmin;
}hminbranches;

typedef struct hagbranches{
    int agent;
    //hminbranches *litmin;
    hidbranches *branches;
    UT_hash_handle hag;
}hagbranches;

typedef struct hmlbranches{
    int ml;
    hagbranches *agent;
    UT_hash_handle hml;
}hmlbranches;

typedef struct literalshash{
    int literal;
    UT_hash_handle hh;
}literalshash;
    

typedef struct headlist {
    int head;
    literalshash *literals;
    UT_hash_handle hh;
}headlist;

typedef struct htype{
    int type;
    headlist* heads;
    UT_hash_handle htp;
}htype;

typedef struct hagent{
    int ag;
    htype *types;
    UT_hash_handle hag;
}hagent;

typedef struct hmlliterals{
    int ml;
    hagent *agents;
    UT_hash_handle hml;
}hmlliterals;

