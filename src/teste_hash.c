#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include "symbol_table.h"
#include "uthash.h"
#include "model.h"


hmlbranches *mlbranches = NULL;

int literalslist_cmp(struct literalslist *l1, struct literalslist *l2){
    literalslist *aux1, *aux2;
    aux1 = l1;
    aux2 = l2;

    while(aux1 != NULL && aux2 != NULL && aux1->literal == aux2->literal){
        aux1 = aux1->next;
        aux2 = aux2->next;
    }
    if(aux1 == NULL && aux2 == NULL) return 1;
    return 0;
}

int find_duplicated_branch(hidbranches *lbranches, tbranch *branch){
    hidbranches *aux;
    struct literalslist *literals;
    for(aux = lbranches; aux!=NULL; aux = aux->hid.next){
        literals = aux->branch->literals;
        if(literalslist_cmp(literals, branch->literals))
            return 1;
    }
    return 0;
}

void add_branch(tbranch *branch){
    hmlbranches *ml = NULL;
    hagbranches *agent = NULL;
    /*hminbranches *bmin = NULL;*/
    /*hmaxbranches *bmax = NULL;*/
    hidbranches *bid = NULL;

    HASH_FIND(hml, mlbranches, &(branch->ml), sizeof(int), ml);
    if(ml == NULL){
        ml = malloc(sizeof(hmlbranches));
        ml->ml = branch->ml;
        ml->agent = NULL;
        HASH_ADD(hml, mlbranches, ml, sizeof(int), ml);
    }
    HASH_FIND(hag, ml->agent, &(branch->agent), sizeof(int), agent);
    if(agent == NULL){
        agent = malloc(sizeof(hagbranches));
        agent->agent = branch->agent;
        agent->branches = NULL;
        HASH_ADD(hag, ml->agent, agent, sizeof(int), agent);
    }
    /*HASH_FIND(hmin, agent->litmin, &(branch->litmin), sizeof(int), bmin); */
    /*if(bmin == NULL){*/
        /*bmin = malloc(sizeof(hminbranches));*/
        /*bmin->min = branch->litmin;*/
        /*bmin->litmax = NULL;*/
        /*HASH_ADD(hmin, agent->litmin, min, sizeof(int), bmin);*/
    /*}*/
    /*HASH_FIND(hmax, bmin->litmax, &(branch->litmax), sizeof(int), bmax);*/
    /*if(bmax == NULL){*/
        /*bmax = malloc(sizeof(hmaxbranches));*/
        /*bmax->max = branch->litmax;*/
        /*bmax->branches = NULL;*/
        /*HASH_ADD(hmax, bmin->litmax, max, sizeof(int), bmax);*/
    /*}*/
    HASH_FIND(hid, agent->branches, &(branch->id), sizeof(int), bid);
    if(bid == NULL){
        if(find_duplicated_branch(agent->branches, branch)) return;
        bid = malloc(sizeof(hidbranches));
        bid->id = branch->id;
        bid->branch = branch;
        HASH_ADD(hid, agent->branches, id, sizeof(int), bid);
    }
    else printf("This id of branch already exists.\n");
}

void print_literalslist(literalslist *list){
    while(list != NULL){
        /*print_literal(list->literal);*/
        printf("%d", list->literal);
        printf(" ");
        list = list->next;
    }
    printf("\n");
}

void print_branch(){
    hmlbranches *mlaux;
    hagbranches *agaux;
    hidbranches *idaux;
    tbranch *branch;

    for(mlaux = mlbranches; mlaux != NULL; mlaux = mlaux->hml.next)
        for(agaux = mlaux->agent; agaux != NULL; agaux = agaux->hag.next)
            for(idaux = agaux->branches; idaux != NULL; idaux = idaux->hid.next){
                branch = idaux->branch;
                printf("branch [%d] on %d modal level by agent %d\n",
                        branch->id, branch->ml, branch->agent);
                print_literalslist(branch->literals);
            }
}

void delete_branch(tbranch *branch){
    hmlbranches *ml = NULL;
    hagbranches *agent = NULL;
    hminbranches *bmin = NULL;
    hmaxbranches *bmax = NULL;
    hidbranches *bid = NULL;

    HASH_FIND(hml, mlbranches, &(branch->ml), sizeof(int), ml);
    if(ml == NULL) {printf("No modal level found to be deleted.\n"); return;}
    HASH_FIND(hag, ml->agent, &(branch->agent), sizeof(int), agent);
    if(agent == NULL) {printf("No agent found to be deleted.\n"); return;}
    /*HASH_FIND(hmin, agent->litmin, &(branch->litmin), sizeof(int), bmin); */
    /*if(bmin == NULL) {printf("No minimum literal found to be deleted.\n"); return;}*/
    /*HASH_FIND(hmax, bmin->litmax, &(branch->litmax), sizeof(int), bmax);*/
    /*if(bmax == NULL) {printf("No maximum literal found to be deleted.\n"); return;}*/
    HASH_FIND(hid, agent->branches, &(branch->id), sizeof(int), bid);
    if(bid != NULL){
        printf("Deleting branch %d.\n", branch->id);
        HASH_DELETE(hid, agent->branches, bid);
    }
}

tbranch *find_branch(tbranch *branch){
    hmlbranches *ml = NULL;
    hagbranches *agent = NULL;
    hminbranches *bmin = NULL;
    hmaxbranches *bmax = NULL;
    hidbranches *bid = NULL;

    HASH_FIND(hml, mlbranches, &(branch->ml), sizeof(int), ml);
    if(ml == NULL) return NULL;
    HASH_FIND(hag, ml->agent, &(branch->agent), sizeof(int), agent);
    if(agent == NULL) return NULL;
    /*HASH_FIND(hmin, agent->litmin, &(branch->litmin), sizeof(int), bmin); */
    /*if(bmin == NULL) return NULL;*/
    /*HASH_FIND(hmax, bmin->litmax, &(branch->litmax), sizeof(int), bmax);*/
    /*if(bmax == NULL) return NULL;*/
    HASH_FIND(hid, agent->branches, &(branch->id), sizeof(int), bid);
    if(bid != NULL){
        return bid->branch;
    }
}

void add_brancheslist(tbranch *branch, brancheslist **list){
    if(*list == NULL) *list = malloc(sizeof(brancheslist));
    brancheslist *aux = *list;
    while(aux->next != NULL) aux = aux->next;
    aux->next = malloc(sizeof(brancheslist));
    aux = aux->next;
    aux->branch = branch;
    aux->next = NULL;
    return;
}

void add_literal_(literalslist_ **list, int literal){
    literalslist_ *a;
    int minus = -literal;
    HASH_FIND_INT(*list, &minus,  a);
    if(a != NULL) {
        printf("Minus literal already in list\n"); 
        return;
    }
    HASH_FIND_INT(*list, &literal,  a);
    if(a != NULL) {
        printf("Literal already in list\n"); 
        return;
    }
    a = malloc(sizeof(literalslist_));
    a->literal = literal;
    HASH_ADD_INT(*list, literal, a);
}


int main(){

    literalslist_ *l1, *l2;
    l1 = NULL;
    l2 = NULL;
    add_literal_(&l1, 1);
    add_literal_(&l1, -1);
    add_literal_(&l2, 2);
    add_literal_(&l2, 3);
    add_literal_(&l2, -2);


    return 0;
}
