int add_literal(int literal, literalslist** list) {
    if(*list == NULL) {
        *list = malloc(sizeof(literalslist));
        (*list)->literal = literal;
        (*list)->next = NULL;
        return 0;
    }
    else{
        literalslist* aux;
        literalslist* prev;
        literalslist* save;
        int l_curr;
        aux = save = *list;
        l_curr = aux->literal;
        // IF AUX->LITERAL == LITERAL THEN TEST IF IT IS NEGATIVE
        // IF IT IS NEGATIVE, CHECK IF THE INSERTION WONT ADD
        // INCONSISTENCE TO THE BRANCH
        // IF IT IS NOT NEGATIVE, THEN RETURN
        if(l_curr == literal) goto TEST_NEG;
        if(l_curr == -literal) return -1;
        // IF THE FIRST LITERAL IS GREATER THEN THE LITERAL TO BE
        // INSERTED, THEN TEST IF IT IS NEGATIVE, IF IT IS, CHECK
        // IF THE INSERTION WONT ADD INCONSISTENCE TO THE BRANCH
        if(l_curr > literal){
TEST_NEG:   if(aux->literal < 0) {
				while(aux->next != NULL && -literal <= aux->literal){
                    if(aux->literal == -literal) {
                        return -1;
                    }
                    aux = aux->next;
                }
                if(aux->literal == -literal) return -1;
                aux = save;
            }
            if(aux->literal == literal) return 0;
            literalslist* new;
            new = malloc(sizeof(literalslist));
            new->literal = literal;
            new->next = aux;
            *list = new;
            return 0;
        }
        if (aux->next == NULL) goto INSERT;
        prev = aux;
        aux = aux->next;
        while(aux->next != NULL){
            if(aux->literal == literal) return 0;
            if(aux->literal == -literal) return -1;
            if(aux->literal < literal) {
                prev = aux;
                aux = aux->next;
            }
            else break;
        }
        if(aux->literal < 0){
            save = aux;
            while(aux->next !=NULL && -literal <= aux->literal) {
                if(aux->literal == -literal) {
                    return -1;
                }
                aux = aux->next;
            }
            if(aux->literal == -literal) return -1;
            aux = save;
        }
        if(aux->next == NULL && aux->literal < literal) {
INSERT:     aux->next = malloc(sizeof(literalslist));
            aux = aux->next;
            aux->literal = literal;
            aux->next = NULL;
            return 0;
        }
        literalslist* new;
        new = malloc(sizeof(literalslist));
        new->literal = literal;
        new->next = aux;
        prev->next = new;
        return 0;
    }
}

        for(i = total_branches/2; i<total_branches; i++) {
            if(!baux->dead) {
                /*[>[>mliterals = clause->right;<]<]*/
                copy_literals(&mliterals, clause->right);
                baux->dead = add_literal(clause->left, &mliterals);
                /*[>[>baux->world->literals = mliterals;<]<]*/
                baux->dead = add_literalslist(&(baux->world->literals), mliterals);
                if(type == MPOSITIVE) 
                    add_mliteral(clause->agent, clause->right, &(baux->world->positives));
                else
                    add_mliteral(clause->agent, clause->right, &(baux->world->negatives));
            }
            baux = baux->next;
        }
int add_literalslist(literalslist** list1, literalslist* list2) {
    literalslist* aux=NULL;
    if(list2 == NULL) return 0;
    if(*list1 == NULL) *list1 = malloc(sizeof(literalslist));
    int len, eq, add;
    len = 1;
    eq = 0;

    aux = list2;

    while(aux->next != NULL) {
        add = add_literal(aux->literal, list1);
        if(add < 0) return -1;
        if(add == 1) eq++;
        len++;
        aux = aux->next;
    }
    add = add_literal(aux->literal, list1);
    if(add<0) return -1;
    if(add==1) eq++;
    if(eq == len) return 1;

    return 0;
}

void add_mliteral(int agent, literalslist* mliterals, pair_t** list){
    pair_t* paux;
    literalslist* laux;
    /*int i =0;*/
    paux = *list;
    if(*list == NULL){
        *list = malloc(sizeof(pair_t));
        (*list)->agent = agent;
        /*(*list)->literals = mliterals;*/
        (*list)->literals = NULL;
        copy_literals(&((*list)->literals), mliterals);
    }
    else {
        laux = (*list)->literals;
        while(paux->agent != agent && paux->next != NULL)
            paux = paux->next;
        if(paux->agent != agent) {
            paux->next = malloc(sizeof(pair_t));
            paux = paux->next;
            paux->agent = agent;
            /*paux->literals = mliterals;*/
            paux->literals = NULL;
            copy_literals(&(paux->literals), mliterals);
        }
        else {
            if(laux == NULL) copy_literals(&laux, mliterals);
            else{
                while(laux->next != NULL) laux = laux->next;
                /*laux->next = mliterals;*/
                laux->next = NULL;
                copy_literals(&(laux->next), mliterals);
            }
        }
    }
}









