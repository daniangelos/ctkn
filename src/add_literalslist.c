int add_literalslist(literalslist** list1, literalslist* list2) {
	literalslist* aux=NULL;
	if(list2 == NULL) return 0;
	if(*list1 == NULL) *list1 = malloc(sizeof(literalslist));

	aux = list2;

	while(aux->next != NULL) {
		if(add_literal(aux->literal, list1) < 0) return -1;
		aux = aux->next;
	}

	return 0;
}
