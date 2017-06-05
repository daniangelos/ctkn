#include<model.h>
#include<stdlib.h>
#include "symbol_table.h"
#include "model.h"
#include "clauses.h"
#include "prover.h"

void add_positiveagents(pair_t* positives, branch_t* branch, tableaux_t* tableaux){
    if(tableaux == NULL) return;
    literalslist* l_pos;
    branch_t* baux;
    branch_t* eliminate = NULL;

    baux = tableaux->branch;
    l_pos = positives->literals;

    while(baux != NULL){
        if(baux->origin_level->id == branch->id){
            if(baux->agent == positives->agent){
                l_pos = positives->literals;
                while(l_pos != NULL){
                    // FAZER A VERIFICACAO DE INCONSISTENCIA
                    insert = add_literal(l_pos->literal, &(baux->world->literals));
                    if(insert < 0){
                        eliminate = baux;
                        baux = baux->prev;
                        remove_branch(eliminate);
                    }
                    if(l_pos->next == NULL) break;
                    l_pos = l_pos->next;
                }
            }
        }
        if(baux->next_branch == NULL) break;
        baux = baux->next_branch;
    }
    
}
/*void add_positiveagents(pair_t* positives, branch_t* branch){*/
    /*// NOTHING TO DO IF BRANCH IS NULL*/
    /*if(branch == NULL) return;*/
    /*world_t* w = NULL;*/
    /*literalslist* l_pos;*/
    /*branch_t* baux;*/
    /*int insert;*/
    /*baux = branch;*/

    /*//FOR EACH WORLD IN THE LIST, INSERT ALL POSITIVE LITERALS*/
    /*while(baux != NULL){*/
        /*//VERIFICAR TAMBÉM SE PRECISA DO MODAL LEVEL*/
        /*if(baux->agent == positives->agent){*/
            /*l_pos = positives->literals;*/
            /*while(l_pos != NULL){*/
                /*// FAZER A VERIFICACAO DE INCONSISTENCIA*/
                /*insert = add_literal(l_pos->literal, &(baux->world->literals));*/
                /*if(l_pos->next == NULL) break;*/
                /*l_pos = l_pos->next;*/
            /*}*/
        /*}*/
        /*if(baux->next_branch == NULL) break;*/
        /*baux = baux->next_branch;*/
    /*}*/
/*}*/
