/* facility/src/string-set.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "boolean.h"
#include "string-set.h"

static int numMallocs = 0;
static int numFrees = 0;

void printStringSetMemMgrReport() {
	printf("  String sets: %d mallocs, %d frees", numMallocs, numFrees);

	if (numMallocs > numFrees) {
		printf(" : **** LEAKAGE ****");
	}

	printf("\n");
}

BOOL stringSetContains(STRING_SET * set, char * str) {

	for (; set != NULL; set = set->next) {

		if (!strcmp(set->str, str)) {
			return TRUE;
		}
	}

	return FALSE;
}

STRING_SET * addStringToSet(char * str, STRING_SET * set) {

	if (stringSetContains(set, str)) {
		/** return NULL; */
		return set;
	}

	STRING_SET * newSet = (STRING_SET * )malloc(sizeof(STRING_SET));

	++numMallocs;
	newSet->str = str;
	newSet->next = set;

	return newSet;
}

STRING_SET * unionOfStringSets(STRING_SET * set1, STRING_SET * set2) {

	for (; set2 != NULL; set2 = set2->next) {

		if (!stringSetContains(set1, set2->str)) {
			set1 = addStringToSet(set2->str, set1);
		}
	}

	return set1;
}

void freeStringSet(STRING_SET * set) {

	while (set != NULL) {
		STRING_SET * next = set->next;

		set->str = NULL;
		free(set);
		++numFrees;
		set = next;
	}
}

/* **** The End **** */
