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
		aux = *list;
		save = aux;
		if(aux->literal == literal) goto TEST_POS;
		if(aux->literal == -literal) return -1;
		if(aux->literal > literal){
TEST_POS:	if(aux->literal < 0) {
				while(aux->next !=NULL) {
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
			while(aux->next !=NULL) {
				if(aux->literal == -literal) {
					return -1;
				}
				aux = aux->next;
			}
			if(aux->literal == -literal) return -1;
			aux = save;
		}
		if(aux->next == NULL && aux->literal < literal) {
INSERT:		aux->next = malloc(sizeof(literalslist));
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
	}
    return 0;
}
