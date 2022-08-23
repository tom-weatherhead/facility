/* facility/src/string-set.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "boolean.h"
#include "string-set.h"

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

/* **** The End **** */
