#include <stdio.h>
#include "symbol_table.h"
#include "model.h"
#include "clauses.h"
#include "prover.h"

extern hml_pclauses *l_usable;
extern hml_pclauses *l_sos;
extern hml_mclauses *m_usable;
extern hml_mclauses *m_sos;

extern int numproofs;

extern void print_pclauses (hml_pclauses *set);
extern void print_mclauses (hml_mclauses *set);
extern void print_agent (int id);
extern void print_literal(int lit);
extern tclause *get_clause(int clause);

void instantiate_branch();
int id_world = 0;
int id_model = 0;
extern int total_branches;
extern int id_branch;
extern int print_model;

extern void branch_mclauses(hml_mclauses *m_clauses);
extern void branch_pclauses(hml_pclauses *p_clauses);
extern void print_branch();
extern void destroy_hash();
extern int add_literal(int literal, literalslist** list);
extern void expandmodallevels();
void print_pair(pair_t* pair);
int ml_sort(hml_mclauses *a, hml_mclauses *b);
int pl_sort(hml_pclauses *a, hml_pclauses *b);
int ml_branches(hmlbranches *a, hmlbranches *b);
int compare_clauses(clauseslist *left, clauseslist *right);
void generate_model();
/*void print_tableaux(tableaux_t* tableaux);*/

void delete_literalslist(literalshash** list);
extern void print_clauses();

extern hmlbranches *mlbranches;

void clausaltableau() {
    if(m_sos == NULL && m_usable == NULL &&
            l_sos == NULL && l_usable == NULL){
        return;
    }

    /* Sort the given sets of clauses by modal level
     * in decreasing order 
     */
    HASH_SRT(hml, m_sos, ml_sort);
    HASH_SRT(hml, m_usable, ml_sort);
    HASH_SRT(hml, l_sos, pl_sort);
    HASH_SRT(hml, l_usable, pl_sort);

    /* Show sorted clauses */
    if(print_model == ON){
        print_clauses(); 
        printf("\n");
    }

    /* Application of PROP and ELIM1 rules */
    branch_pclauses(l_sos);
    branch_pclauses(l_usable); 
    if(mlbranches == NULL){
        /*printf("Unsatisfiable\n");*/
        numproofs = 1;
        return;
    }

    /* Application of NEG, POS and ELIM1 rules */
    branch_mclauses(m_sos);
    branch_mclauses(m_usable);
    if(mlbranches == NULL){
        /*printf("Unsatisfiable\n");*/
        numproofs = 1;
        return;
    }

    /* Application of ELIM2 rule */
    /*expandmodallevels();*/
    hml_mclauses *maux;
    int ml = 1;
    HASH_FIND(hml, mlbranches, &(ml), sizeof(int), maux);
    if(maux == NULL){ 
        /*printf("Unsatisfiable\n");*/
        numproofs = 1;
        return;
    }
    else {
        if (print_model == ON) print_branch();
        generate_model();
        /*printf("Satisfiable\n");*/
    }
    destroy_hash();
}

/*void expand_modallevels(tableaux_t* tableaux){*/
    /*if(tableaux == NULL || tableaux->branch == NULL) return;*/
    /*branch_t* b_it;*/
    /*world_t* wi; // i-esim world*/
    /*pair_t *p_negatives, *p_positives;*/

    /*b_it = tableaux->branch;*/

    /*while(b_it != NULL){*/
        /*wi = b_it->world;*/
        /*p_negatives = wi->negatives;*/
        /*p_positives = wi->positives;*/
        /*if(p_negatives == NULL) goto POSITIVES;*/
        /*while(p_negatives != NULL){*/
            /*add_negativeagents(p_negatives, wi->ml + 1, b_it, &(tableaux->next));*/
            /*if(p_negatives->next == NULL) break;*/
            /*p_negatives = p_negatives->next;*/
        /*}*/
/*POSITIVES: if(p_positives == NULL) goto NEXT_IT;*/
           /*while(p_positives != NULL){*/
               /*add_positiveagents(p_positives, b_it, tableaux->next);*/
               /*if(p_positives->next == NULL) break;*/
               /*p_positives = p_positives->next;*/
           /*}*/
/*NEXT_IT: if(b_it->next_branch == NULL) break; */
        /*b_it = b_it->next_branch;*/
    /*}*/
    /*if(tableaux->next != NULL)*/
        /*tableaux->next->prev = tableaux;*/
/*}*/

/*void add_negativeagents(pair_t* negatives, int ml, branch_t* prev_level, tableaux_t** tableaux){*/
    /*if(negatives == NULL) return;*/
    /*literalslist* l_neg;*/
    /*world_t* w;*/
    /*branch_t* branch;*/

    /*if((*tableaux) == NULL) {*/
        /**tableaux = malloc(sizeof(tableaux_t));*/
        /*(*tableaux)->next = (*tableaux)->prev = NULL;*/
        /*(*tableaux)->ml = ml;*/
        /*(*tableaux)->branch = malloc(sizeof(branch_t));*/
        /*branch = (*tableaux)->branch;*/
        /*branch->id = id_branch++;*/
        /*branch->closed = 0;*/
        /*branch->ml = ml;*/
        /*branch->agent = negatives->agent;*/
        /*branch->next_level_t = 0;*/
        /*branch->next_branch = branch->prev_branch = NULL;*/
        /*branch->origin_level = prev_level;*/
        /*prev_level->next_level_t++;*/
        /*branch->next_level_t = 0;*/
    /*}*/
    /*else{*/
        /*branch = (*tableaux)->branch;*/
        /*while(branch->next_branch != NULL)*/
            /*branch = branch->next_branch;*/
        /*branch->next_branch = malloc(sizeof(branch_t));*/
        /*branch->next_branch->prev_branch = branch;*/
        /*branch = branch->next_branch;*/
        /*branch->id = id_branch++;*/
        /*branch->closed = 0;*/
        /*branch->ml = ml;*/
        /*branch->agent = negatives->agent;*/
        /*branch->next_level_t = 0;*/
        /*branch->next_branch = NULL;*/
        /*branch->origin_level = prev_level;*/
        /*prev_level->next_level_t++;*/
        /*branch->next_level_t = 0;*/
    /*}*/

    /*l_neg = negatives->literals;*/
    /*while(l_neg != NULL){*/
        /*branch->world = malloc(sizeof(world_t));*/
        /*w = branch->world;*/
        /*w->id = id_world++;*/
        /*w->ml = ml;*/
        /*w->literals = NULL;*/
        /*w->positives = w->negatives = NULL;*/
        /*add_literal(l_neg->literal, &(w->literals));*/
        /*w->positives = w->negatives = NULL;*/
        /*if(l_neg->next == NULL) break;*/
        /*l_neg = l_neg->next;*/

        /*branch->next_branch = malloc(sizeof(branch_t));*/
        /*branch->next_branch->prev_branch = branch;*/
        /*branch = branch->next_branch;*/
        /*branch->next_level_t = 0;*/
        /*branch->id = id_branch++;*/
        /*branch->closed = 0;*/
        /*branch->ml = ml;*/
        /*branch->agent = negatives->agent;*/
        /*branch->world = NULL;*/
        /*branch->next_branch = NULL;*/
        /*branch->origin_level = prev_level;*/
        /*prev_level->next_level_t++;*/
    /*}*/
/*}*/

/*void add_positiveagents(pair_t* positives, branch_t* branch, tableaux_t* tableaux){*/
    /*if(tableaux == NULL) return;*/
    /*literalslist* l_pos;*/
    /*branch_t* baux;*/
    /*branch_t* eliminate = NULL;*/
    /*int insert = 0;*/

    /*baux = tableaux->branch;*/
    /*l_pos = positives->literals;*/

    /*while(baux != NULL){*/
        /*if(baux->origin_level->id == branch->id){*/
            /*if(baux->agent == positives->agent){*/
                /*l_pos = positives->literals;*/
                /*while(l_pos != NULL){*/
                    /*// FAZER A VERIFICACAO DE INCONSISTENCIA*/
                    /*insert = add_literal(l_pos->literal, &(baux->world->literals));*/
                    /*eliminate = baux;*/
                    /*if(l_pos->next == NULL) break;*/
                    /*l_pos = l_pos->next;*/
                /*}*/
            /*}*/
        /*}*/
        /*if(baux->next_branch == NULL) break;*/
        /*baux = baux->next_branch;*/
        /*if(insert < 0){ */
            /*if(eliminate->prev_branch == NULL){*/
                /*tableaux->branch = eliminate->next_branch;*/
            /*}*/
            /*if(eliminate->origin_level->prev_branch == NULL)*/
                /*tableaux->prev->branch = eliminate->origin_level->next_branch;*/
            /*remove_branch(&(eliminate->origin_level));*/
            /*remove_branch(&eliminate);*/
        /*}*/
    /*}*/
    /*if(insert < 0){ */
        /*if(eliminate->prev_branch == NULL){*/
            /*tableaux->branch = eliminate->next_branch;*/
        /*}*/
        /*if(eliminate->origin_level->prev_branch == NULL)*/
            /*tableaux->prev->branch = eliminate->origin_level->next_branch;*/
        /*remove_branch(&(eliminate->origin_level));*/
        /*remove_branch(&eliminate);*/
    /*}*/
/*}*/

int ml_sort(hml_mclauses *a, hml_mclauses *b){
    if(a->ml > b->ml) return -1;
    else if (a->ml == b->ml) return 0;
    return 1;
}

int ml_branches(hmlbranches *a, hmlbranches *b){
    if(a->ml > b->ml) return -1;
    else if(a->ml == b->ml) return 0;
    return 1;
}

int pl_sort(hml_pclauses *a, hml_pclauses *b){
    if(a->ml > b->ml) return -1;
    else if (a->ml == b->ml) return 0;
    return 1;
}



void delete_literalslist(literalshash** list) {
    literalshash *current, *tmp;
    HASH_ITER(hh, *list, current, tmp){
        HASH_DEL(*list, current); 
        free(current);
    }
    return;
}
 
void generate_model(){}
