#include<stdio.h>
#include<stdlib.h>

typedef struct literalslist{
    int literal;
    struct literalslist* next;
}literalslist;

int add_literal(int literal, literalslist** list);
void print_list(literalslist* list);

int main(){
    literalslist* list = NULL;
    print_list(list);
    printf("retorno: %d\n", add_literal(-1, &list));
    print_list(list);
    printf("retorno: %d\n", add_literal(-3, &list));
    print_list(list);
    printf("retorno: %d\n", add_literal(-2, &list));
    print_list(list);
    printf("retorno: %d\n", add_literal(2, &list));
    print_list(list);
    printf("retorno: %d\n", add_literal(6, &list));
    print_list(list);
    printf("retorno: %d\n", add_literal(4, &list));
    print_list(list);
    printf("retorno: %d\n", add_literal(6, &list));
    print_list(list);

    return 0;
}

int add_literal(int literal, literalslist** list){
    if(*list == NULL){
        (*list) = malloc(sizeof(literalslist));
        (*list)->literal = literal;
        (*list)->next == NULL;
        return 0;
    }
    literalslist *aux, *prev;
    int tag = 0;
    aux = prev = *list;
    if(literal < aux->literal){
        literalslist* insert;
        insert = malloc(sizeof(literalslist));
        insert->literal = literal;
        insert->next = aux;
        (*list) = insert;
        tag = 1;
    }
    do{
        if(literal == -aux->literal) return -1;
        if(literal == aux->literal && literal <= 0) return 1;
        if(!tag && literal < aux->literal){
            literalslist* insert;
            insert = malloc(sizeof(literalslist));
            insert->literal = literal;
            insert->next = aux;
            prev->next = insert;
            tag = 1;
        }
        prev = aux;
        aux = aux->next;
        if(aux == NULL) break;
    }while(-literal <= aux->literal || literal <= -aux->literal);
    if(!tag && aux == NULL){
        if(prev->literal == literal) return 1;
        prev->next = malloc(sizeof(literalslist));
        aux = prev->next;
        aux->literal = literal;
        aux->next = NULL;
    }
    return 0;
}

void print_list(literalslist* list){
    if(list == NULL) {printf("Empty list\n"); return;}
    literalslist* aux;
    aux = list;
    printf("lista: ");
    while(aux != NULL){
        printf("%d ", aux->literal);
        aux = aux->next;
    }
    printf("\n");
    return;
}
