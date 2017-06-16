#include <stdio.h>
#include "symbol_table.h"
#include "model.h"
#include "clauses.h"
#include "prover.h"

extern hml_pclauses *l_usable;
extern hml_pclauses *l_sos;
extern tclause *get_clause(int clause);
extern void print_literal(int lit);
extern void delete_literalslist(literalshash** list);
/*extern void print_tableaux(tableaux_t* tableaux);*/
extern void print_clause(tclause *clause);
void add_pclause(tclause* clause);
void add_mclause(tclause* clause, int agent, int type);
void expandmodallevels();
void appendliterals(literalshash **original, literalshash *append);
int satnextlevel(literalshash **neg, literalshash *pos, hmlbranches *level);
int try_modalliteral(tclause* clause);
void add_pos_mclause(tclause* clause);
void branch_pclauses(hml_pclauses *pclauses);
void branch_mclauses(hml_mclauses *mclauses);
void create_empty_ml(int modal_level, int literal, int agent);

int add_literal(int literal, literalshash** list, int* tliterals);
int try_literal(int literal, literalshash* list);
void copy_literals(literalshash** list, literalshash* copy);

void add_branch(tbranch *branch);
void add_brancheslist(tbranch **branch, brancheslist **list);
int literalslist_cmp(struct literalshash *l1, struct literalshash *l2);
int find_duplicated_branch(hidbranches *lbranches, tbranch *branch);
void delete_branch(tbranch **branch);
void delete_branch_hash(tbranch *branch);
void destroy_hash();
void destroy_literalshash(literalshash **users);
void print_literalslist(literalshash *list);
void print_branch();
void print_modalliterals();

int tag = 0;
int id_branch = 0;
int total_branches = 0;
int modal_levels[1000];
extern int id_world;

hmlbranches *mlbranches = NULL;
hmlliterals *mlliterals = NULL;

void branch_pclauses(hml_pclauses *pclauses){
    hml_pclauses *hlc = NULL;
    hmaxclauses *hmc = NULL;
    hsizeclauses *hsc = NULL;  
    tclause *clause = NULL;

    for(hlc=pclauses; hlc != NULL; hlc=hlc->hml.next){
        for (hmc=hlc->max; hmc != NULL; hmc=hmc->hmax.next){
            for (hsc=hmc->size; hsc != NULL; hsc=hsc->hsize.next) {
                clauseslist *l = hsc->list;
                while (l != NULL) {
                    clause = get_clause(l->clause_number);
                    /*print_clause(clause);*/
                    /*printf("\n");*/
                    add_pclause(clause);
                    /*print_branch();*/
                    /*getchar();*/
                    if(mlbranches == NULL) return;
                    l = l->next;
                }
            }
        }
    }
}

void branch_mclauses(hml_mclauses *mclauses){
    if(mclauses == NULL) return;

    hml_mclauses *maux;
    hagentclauses *hag = NULL;
    htypeclauses *htc = NULL;
    hmaxlitclauses *hmaxlit = NULL;
    htypeclauses *pos;
    htypeclauses *neg;
    tclause *clause;
    int ml;
    int agent;


    for (maux=mclauses; maux != NULL; maux=maux->hml.next){
        for(hag = maux->id; hag != NULL; hag=hag->hid.next) {
            agent = hag->id;
            htc = hag->type; 
            if(htc->type == MNEGATIVE) {
                pos = htc->htype.next;
                neg = htc;
            }
            else if(htc->type == MPOSITIVE){
                pos = htc;
                neg = htc->htype.next;
            }

            if(pos != NULL){
                for(hmaxlit = pos->lit; hmaxlit != NULL; hmaxlit = hmaxlit->hmax.next) {
                    clauseslist *l = hmaxlit->list;
                    while(l != NULL) {
                        clause = get_clause(l->clause_number);
                        add_mclause(clause, agent, MPOSITIVE);
                        l = l->next;
                    }
                }
            }

            if(neg != NULL){
                for(hmaxlit = neg->lit; hmaxlit != NULL; hmaxlit = hmaxlit->hmax.next) {
                    clauseslist *l = hmaxlit->list;
                    while(l != NULL) {
                        clause = get_clause(l->clause_number);
                        /*print_literal(clause->right->literal);*/
                        /*getchar();*/
                        add_mclause(clause, agent, MNEGATIVE);
                        /*print_branch();*/
                        l = l->next;
                    }
                }
            }
        }
    }
    /*print_branch();*/

}

tbranch *create_branch(int ml, int agent){
    tbranch *branch = malloc(sizeof(tbranch)); 
    branch->id = id_branch++;
    branch->closed = 0;
    branch->ml = ml;
    branch->agent = agent;
    branch->literals = NULL;
    branch->tliterals = 0;
    /*branch->modallit = NULL;*/
    return branch;
}

void add_pclause(tclause* clause){
    literalslist* literals;
    literals = clause->right;
    int modal_level = clause->modal_level;
    int agent = clause->agent;
    tbranch *branch;

    //BRANCH EMPTY, CREATE INITIAL WORLDS
    if(mlbranches == NULL) {
        while(literals != NULL){
            branch = create_branch(clause->modal_level, agent);
            add_literal(literals->literal, &(branch->literals), 
                    &(branch->tliterals));
            add_branch(branch);
            literals = literals->next;
        }
        return;
    }

    //LITERALS NEEDED TO BE INSERTED IN EXISTING BRANCHES
    hmlbranches *mlaux;
    hagbranches *agaux;
    hidbranches *idaux;
    brancheslist *add;
    add = NULL;
    int tliterals;

    HASH_FIND(hml, mlbranches, &(modal_level), sizeof(int), mlaux);
    if(mlaux == NULL){
INSERT: while(literals != NULL){
            branch = create_branch(clause->modal_level, agent);
            add_literal(literals->literal, &(branch->literals),
                    &(branch->tliterals));
            add_branch(branch);
            literals = literals->next;
        }
        return;
    }

    HASH_FIND(hag, mlaux->agent, &(agent), sizeof(int), agaux);
    if(agaux == NULL) goto INSERT;

    literalslist* l;
    for(idaux=agaux->branches; idaux!=NULL; idaux=idaux->hid.next){
        branch = idaux->branch;
        l = literals;
        while(l->next != NULL){
            if(try_literal(l->literal, branch->literals) == 0){
                tliterals = branch->tliterals;
                literalshash *provlist = NULL;
                copy_literals(&provlist, branch->literals);
                add_literal(l->literal, &provlist, &tliterals);
                tbranch *newbranch = create_branch(modal_level, agent);
                newbranch->literals = provlist;
                newbranch->tliterals = tliterals;
                //ADD BRANCH TO QUEUE
                add_brancheslist(&newbranch, &add);
            }
            l = l->next;
        }
        if(try_literal(l->literal, branch->literals) < 0){
            delete_branch(&branch); 
        }
        else{
            add_literal(l->literal, &(branch->literals), &(branch->tliterals));
            int a = find_duplicated_branch(agaux->branches, branch);
            if(a){
                delete_branch(&branch);
            }
        }
    }
    while(add != NULL){
        add_branch(add->branch);
        add = add->next;
    }
}

void add_mclause(tclause *clause, int agent, int type){
    hmlliterals *ml = NULL;
    hagent *ag = NULL;
    htype *t = NULL;
    headlist *l = NULL;
    
    int modal_level = clause->modal_level;
    int mliteral = clause->left;

    HASH_FIND(hml, mlliterals, &modal_level, sizeof(int), ml);
    if(ml == NULL){
        ml = malloc(sizeof(hmlliterals));
        ml->ml = modal_level;
        ml->agents = NULL;
        HASH_ADD(hml, mlliterals, ml, sizeof(int), ml); 
    }
    HASH_FIND(hag, ml->agents, &agent, sizeof(int), ag);
    if(ag == NULL){
        ag = malloc(sizeof(hagent));
        ag->ag = agent;
        ag->types = NULL;
        HASH_ADD(hag, ml->agents, ag, sizeof(int), ag);
    }
    HASH_FIND(htp, ag->types, &type, sizeof(int), t);
    if(t == NULL){
        t = malloc(sizeof(htype));
        t->type = type;
        t->heads = NULL;
        HASH_ADD(htp, ag->types, type, sizeof(int), t);
    }
    HASH_FIND_INT(t->heads, &mliteral, l);
    if(l == NULL){
        l = malloc(sizeof(headlist));
        l->head = mliteral;
        l->literals = NULL;
        HASH_ADD_INT(t->heads, head, l);
    }
    add_literal(clause->right->literal, &(l->literals), NULL);
}

/*void expandmodallevels(){*/
    /*hmlliterals *mlit = NULL;*/
    /*htype *hlit = NULL;*/
    /*headlist *positives = NULL;*/
    /*headlist *pos = NULL;*/
    /*headlist *negatives = NULL;*/
    /*headlist *neg = NULL;*/
    /*literalshash *literals = NULL;*/
    /*literalshash *mustsat_pos = NULL;*/
    /*literalshash *mustsat_neg = NULL;*/
    /*hmlbranches *mlaux = NULL;*/
    /*hmlbranches *mltmp = NULL;*/
    /*hmlbranches *mlpre = NULL;*/
    /*hagbranches *agaux = NULL;*/
    /*hagbranches *agtmp = NULL;*/
    /*hidbranches *idaux = NULL;*/
    /*hidbranches *idtmp = NULL;*/
    /*tbranch *branch = NULL;*/
    /*int ml;*/
    /*int head;*/
    /*int tag;*/
    /*int try;*/
    /*int levelok = 1;*/

    /*HASH_ITER(hml, mlbranches, mlaux, mltmp){*/
        /*// get the modal literals for the corresponding modal level:*/
        /*ml = mlaux->ml - 1;*/
        /*[>printf("%d: ", ml);<]*/
        /*HASH_FIND(hml, mlliterals, &ml, sizeof(int), mlit);*/
        /*if(mlit == NULL) continue;*/
        /*hlit = mlit->types;*/
        /*if(hlit->type == MNEGATIVE){*/
            /*neg = hlit->heads;*/
            /*if(hlit->htp.next != NULL){*/
                /*hlit = hlit->htp.next;*/
                /*pos = hlit->heads;*/
            /*}*/
        /*}*/
        /*else{*/
            /*pos = hlit->heads;*/
            /*if(hlit->htp.next != NULL){*/
                /*hlit = hlit->htp.next;*/
                /*neg = hlit->heads;*/
            /*}*/
        /*}*/
        /*[>printf("%d: ", mlaux->ml);<]*/
        /*mlpre = mlaux->hml.next;*/
        /*// try to satisfy the modal literals in some branch:*/
        /*HASH_ITER(hag, mlpre->agent, agaux, agtmp){*/
            /*HASH_ITER(hid, agaux->branches, idaux, idtmp){*/
                /*branch = idaux->branch;*/
                /*[>printf("[%d] ", branch->id);<]*/

                /*for(negatives = neg; negatives != NULL; negatives = negatives->hh.next){*/
                    /*head = negatives->head;*/
                    /*[>print_literal(head); printf(" => ");<]*/
                    /*[>print_literalslist(branch->literals);<]*/
                    /*[>getchar();<]*/
                    /*// try to insert the negation of head*/
                    /*if(!try_literal(-head, branch->literals)) continue; // if ok then next head*/
                    /*appendliterals(&mustsat_neg, negatives->literals);*/
                /*}*/
                /*if(mustsat_neg == NULL) continue; // */
                /*[>print_literalslist(mustsat_neg);<]*/
                /*// else get the positive literals:*/
                /*for(positives = pos; positives != NULL; positives = positives->hh.next){*/
                    /*head = positives->head;*/
                    /*// try to insert the negation of head*/
                    /*if(!try_literal(-head, branch->literals)) continue; // if ok then next head*/
                    /*appendliterals(&mustsat_pos, positives->literals);*/
                /*}*/
                /*[>print_literalslist(mustsat_pos);<]*/
                /*if(!satnextlevel(&mustsat_neg, mustsat_pos, mlaux)){*/
                    /*HASH_DELETE(hid, agaux->branches, idaux);*/
                    /*free(idaux);*/
                    /*idaux = NULL;*/
                /*}*/
                /*destroy_literalshash(&mustsat_neg);*/
                /*destroy_literalshash(&mustsat_pos);*/
            /*}*/
            /*if(agaux->branches == NULL){*/
                /*HASH_DELETE(hag, mlpre->agent, agaux);*/
                /*free(agaux);*/
                /*agaux = NULL;*/
            /*}*/
        /*}*/
        /*[>printf("Finishing expansion on level %d\n",mlpre->ml);<]*/
        /*[>print_branch();<]*/
        /*[>getchar();<]*/
        /*if(mlpre->agent == NULL){*/
            /*HASH_DELETE(hml, mlbranches, mlpre);*/
            /*free(mlpre);*/
            /*mlpre = NULL;*/
        /*}*/
    /*}*/
/*}*/

void destroy_literalshash(literalshash **users) {
    literalshash *current_user, *tmp;

    HASH_ITER(hh, *users, current_user, tmp) {
        HASH_DEL(*users,current_user);  /* delete; users advances to next */
        free(current_user);            /* optional- if you want to free  */
        current_user = NULL;
    }
    *users = NULL;
}

int satnextlevel(literalshash **neg, literalshash *pos, hmlbranches *level){
    hagbranches *agents = NULL;
    hidbranches *ids = NULL;
    hidbranches *aux = NULL;
    tbranch *branch = NULL;
    literalshash *dia = NULL;
    literalshash *tmp = NULL;
    literalshash *box = NULL;
    int _pos;

    /*printf("%d", level->ml);getchar();*/
    for(agents = level->agent; agents != NULL; agents = agents->hag.next){
        /*for(ids = agents->branches; ids != NULL; ids = ids->hid.next){*/
        HASH_ITER(hid, agents->branches, ids, aux){
            branch = ids->branch;
            _pos = 1;
            for(box = pos; box != NULL; box = box->hh.next){
                if(try_literal(box->literal, branch->literals)) {
                    _pos = 0;
                    /*HASH_DELETE(hid,agents->branches, ids);*/
                    /*free(ids);*/
                    /*ids = NULL;*/
                    break;
                }
            }
            if(!_pos) continue;
            HASH_ITER(hh, *neg, dia, tmp){
                if(try_literal(dia->literal, branch->literals) == 0){
                    HASH_DEL(*neg, dia);
                    free(dia);
                    dia = NULL;
                }
            }
        }
    }
    if(*neg != NULL) return 0;
    return 1;
}

void appendliterals(literalshash **original, literalshash *append){
    literalshash *aux;
    literalshash *a = NULL;
    int literal;
    for(aux = append; aux != NULL; aux = aux->hh.next){
        a = malloc(sizeof(literalshash));
        literal = a->literal = aux->literal;
        HASH_ADD_INT(*original, literal, a);
    }
}

int try_modalliteral(tclause *clause){
    hmlbranches *ml = NULL;
    hagbranches *ag = NULL;
    hidbranches *bid = NULL;
    tbranch *branch = NULL;
    int modal_level = clause->modal_level + 1;
    int agent = clause->agent;

    int mliteral = clause->right->literal;

    HASH_FIND(hml, mlbranches, &modal_level, sizeof(int), ml);
    if(ml == NULL){
        if(!modal_levels[modal_level]) create_empty_ml(modal_level, mliteral,agent);
        else destroy_hash();
        return 0;
    }
    for(ag = ml->agent; ag != NULL; ag = ag->hag.next){
        for(bid = ag->branches; bid != NULL; bid = bid->hid.next){
            branch = bid->branch;
            if(try_literal(mliteral, branch->literals) == 0) return 0;
        }
    }
    return 1;
} 

void add_pos_mclause(tclause *clause){
} 

void create_empty_ml(int modal_level, int literal, int agent){
    tbranch *branch = NULL;
    branch = create_branch(modal_level, agent);
    add_literal(literal, &(branch->literals), &(branch->tliterals));
    add_branch(branch);
}

int try_literal(int literal, literalshash* list){
    if(list == NULL) return 0;
    literalshash *a;
    int minus = -literal;

    HASH_FIND_INT(list, &minus, a);
    if(a != NULL) return -1;

    return 0;
}

int lit_srt(literalshash *a, literalshash *b){
    if(a->literal < b->literal) return (a-b);
    if(a->literal > b->literal) return (a-b);
    return 0;
}

int add_literal(int literal, literalshash** list, int* tliterals){
    literalshash *a = NULL;
    int minus = -literal;

    HASH_FIND_INT(*list, &minus, a);
    if(a != NULL) return -1;

    HASH_FIND_INT(*list, &literal, a);
    if(a != NULL) return 0;

    a = malloc(sizeof(literalshash));
    a->literal = literal;
    HASH_ADD_INT(*list, literal, a);
    if(tliterals != NULL) (*tliterals)++;

    /*HASH_SORT(*list, lit_srt);*/

    return 0;
}

void add_brancheslist(tbranch **branch, brancheslist **list){
    if(*list == NULL){
        *list = malloc(sizeof(brancheslist));
        (*list)->next = NULL;
	(*list)->branch = *branch;
    }
    else {
      brancheslist *aux = *list;
      while(aux->next != NULL) aux = aux->next;
      aux->next = malloc(sizeof(brancheslist));
      aux = aux->next;
      aux->branch = *branch;
      aux->next = NULL;
    }
    return;
}

void copy_literals(literalshash** list, literalshash* copy) {
    literalshash* a; // iterator of list
    if(copy == NULL) {*list = NULL; return; }
    if(*list != NULL) {
        delete_literalslist(list);
    }
    *list = NULL;

    for(a = copy; a != NULL; a = a->hh.next){
        add_literal(a->literal, list, NULL);
    }
}

int literalslist_cmp(struct literalshash *l1, struct literalshash *l2){
    literalshash *a1, *a2;

    for(a1 = l1; a1 != NULL; a1 = a1->hh.next){
        HASH_FIND_INT(l2, &(a1->literal), a2);
        if(a2 == NULL) return 0;
    }
    return 1;
}

int find_duplicated_branch(hidbranches *lbranches, tbranch *branch){
    hidbranches *aux;
    struct literalshash *literals;

    for(aux = lbranches; aux!=NULL; aux = aux->hid.next){
        literals = aux->branch->literals;
        if((branch->tliterals == aux->branch->tliterals) &&
            (literalslist_cmp(literals, branch->literals) && 
                    aux->branch->id != branch->id))
            return 1;
    }
    return 0;
}

void add_branch(tbranch *branch){
    hmlbranches *ml = NULL;
    hagbranches *agent = NULL;
    hidbranches *bid = NULL;

    HASH_FIND(hml, mlbranches, &(branch->ml), sizeof(int), ml);
    if(ml == NULL){
        ml = malloc(sizeof(hmlbranches));
        ml->ml = branch->ml;
        ml->agent = NULL;
        HASH_ADD(hml, mlbranches, ml, sizeof(int), ml);
        modal_levels[branch->ml] = 1;
        modal_levels[branch->ml+1] = 0;
    }
    HASH_FIND(hag, ml->agent, &(branch->agent), sizeof(int), agent);
    if(agent == NULL){
        agent = malloc(sizeof(hagbranches));
        agent->agent = branch->agent;
        agent->branches = NULL;
        HASH_ADD(hag, ml->agent, agent, sizeof(int), agent);
    }
    HASH_FIND(hid, agent->branches, &(branch->id), sizeof(int), bid);
    if(bid == NULL){
        int a = find_duplicated_branch(agent->branches, branch);
        if(a) return;
        bid = malloc(sizeof(hidbranches));
        bid->id = branch->id;
        bid->branch = branch;
        HASH_ADD(hid, agent->branches, id, sizeof(int), bid);
    }
    else printf("This id of branch already exists.\n");
}

tbranch *find_branch(tbranch *branch){
    hmlbranches *ml = NULL;
    hagbranches *agent = NULL;
    hidbranches *bid = NULL;

    HASH_FIND(hml, mlbranches, &(branch->ml), sizeof(int), ml);
    if(ml == NULL) return NULL;
    HASH_FIND(hag, ml->agent, &(branch->agent), sizeof(int), agent);
    if(agent == NULL) return NULL;
    HASH_FIND(hid, agent->branches, &(branch->id), sizeof(int), bid);
    if(bid != NULL){
        return bid->branch;
    }
    return NULL;
}

void delete_branch(tbranch **branch){
    delete_branch_hash(*branch);
    delete_literalslist(&(*branch)->literals);
    free(*branch);
    *branch = NULL;
}

void delete_branch_hash(tbranch *branch){
    hmlbranches *ml = NULL;
    hagbranches *agent = NULL;
    hidbranches *bid = NULL;

    HASH_FIND(hml, mlbranches, &(branch->ml), sizeof(int), ml);
    if(ml == NULL) {printf("No modal level found to be deleted.\n"); return;}
    HASH_FIND(hag, ml->agent, &(branch->agent), sizeof(int), agent);
    if(agent == NULL) {printf("No agent found to be deleted.\n"); return;}
    HASH_FIND(hid, agent->branches, &(branch->id), sizeof(int), bid);
    if(bid != NULL){
        /*printf("Deleting branch %d.\n", branch->id);*/
        HASH_DELETE(hid, agent->branches, bid);
        hidbranches *branches = agent->branches;
        if(branches != NULL) return;
        HASH_DELETE(hag, ml->agent, agent);
        hagbranches *agents = ml->agent;
        if(agents != NULL) return;
        HASH_DELETE(hml, mlbranches, ml);
    }
}

void destroy_hash(){
    hmlbranches *mlaux;
    hagbranches *agaux;
    hidbranches *idaux;
    tbranch *branch;

    for(mlaux = mlbranches; mlaux != NULL; mlaux = mlaux->hml.next)
        for(agaux = mlaux->agent; agaux != NULL; agaux = agaux->hag.next)
            for(idaux = agaux->branches; idaux != NULL; idaux = idaux->hid.next){
                branch = idaux->branch;
                delete_branch(&branch);
            }
    mlbranches = NULL;
}

void print_literalslist(literalshash *list){
    literalshash *a;
    for(a = list; a != NULL; a = a->hh.next){
        print_literal(a->literal);
        printf(" ");
    }
    printf("\n");
}

/*void print_pair(pair_t* modallist){*/
    /*pair_t* it;*/
    /*printf("\t Modal literals\n");*/
    /*for(it = modallist; it != NULL; it = it->hh.next){*/
        /*printf("\t");*/
        /*print_literal(it->head);*/
        /*printf(":\n");*/
        /*printf("\tPOS: ");*/
        /*print_literalslist(it->pos);*/
        /*printf("\n");*/
        /*printf("\tNEG: ");*/
        /*print_literalslist(it->neg);*/
        /*printf("\n");*/
    /*}*/
/*}*/

void print_branch(){
    // PRINT PROPOSITIONAL BRANCHES
    hmlbranches *mlaux; 
    hagbranches *agaux;
    hidbranches *idaux;
    tbranch *branch;

    for(mlaux = mlbranches; mlaux != NULL; mlaux = mlaux->hml.next)
        for(agaux = mlaux->agent; agaux != NULL; agaux = agaux->hag.next)
            for(idaux = agaux->branches; idaux != NULL; idaux = idaux->hid.next){
                branch = idaux->branch;
                printf("branch [%d] on %d modal level by agent %d with %d literals\n", branch->id, branch->ml, branch->agent, branch->tliterals);
                print_literalslist(branch->literals);
            }

    printf("\n");
    //PRINT MODAL LITERALS
    hmlliterals *mlit;
    hagent *hag;
    htype *hlit;
    headlist *headl;
    literalshash *literals;
    for(mlit = mlliterals; mlit != NULL; mlit = mlit->hml.next){
        for(hag = mlit->agents; hag != NULL; hag = hag->hag.next){
            printf("[%d,%d]: \n", hag->ag, mlit->ml);
            for(hlit = hag->types; hlit != NULL; hlit = hlit->htp.next){
                printf("\t");
                if(hlit->type == MPOSITIVE) printf("pos: \n");
                else if(hlit->type == MNEGATIVE) printf("neg: \n");
                for(headl = hlit->heads; headl != NULL; headl = headl->hh.next){
                    printf("\t");
                    print_literal(headl->head);
                    printf(" => ");
                    print_literalslist(headl->literals);
                }
            }
        }
    }
}

