typedef struct pair_t pair_t;
typedef struct world_t world_t;
typedef struct tbranch tbranch;

typedef struct tbranch{
    unsigned int id;
    int closed;
    int ml; /* modal level */
    int agent;
    int tliterals;
    //pair_t *modallit;
    //int litmin;
    //int litmax;
    //struct literalslist *literals;
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
    

struct world_t {
	unsigned int id;
	unsigned int ml;
	struct literalslist* literals;
	struct pair_t* positives;
	struct pair_t* negatives;
};

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

typedef struct hmlliterals{
    int ml;
    htype *types;
    UT_hash_handle hml;
}hmlliterals;

