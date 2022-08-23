/* facility/src/de-bruijn.c */

/* See https://en.wikipedia.org/wiki/De_Bruijn_index */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "boolean.h"

#include "types.h"

typedef struct STRING_LIST_STRUCT {
	char * str;
	struct STRING_LIST_STRUCT * next;
} STRING_LIST;

int findIndexOfString(char * name, STRING_LIST * boundVariablesList) {
	int n = 1;

	for (; boundVariablesList != NULL; boundVariablesList = boundVariablesList->next) {

		if (!strcmp(name, boundVariablesList->str)) {
			return n;
		}

		++n;
	}

	return 0; /* I.e. the name was not found in the list */
}

BOOL stringListContains(STRING_LIST * stringList, char * name) {
	return findIndexOfString(name, stringList) > 0;
}

STRING_LIST * addStringToList(char * name, STRING_LIST * stringList) {

	/* if (name != NULL && strlen(name) >= maxStringValueLength - 1) {
		fprintf(stderr, "addStringToList() : The name '%s' is too long.\n", name);
		return NULL;
	} */

	STRING_LIST * newStringList = (STRING_LIST *)malloc(sizeof(STRING_LIST));

	newStringList->str = name;
	newStringList->next = stringList;

	return newStringList;
}

/* Initially, boundVariablesList will be NULL. */

static void printDeBruijnIndexLocal(LC_EXPR * expr, STRING_LIST * boundVariablesList) {
	int n = 0;
	STRING_LIST * newBoundVariablesList = NULL;

	switch (expr->type) {
		case lcExpressionType_Variable:
			n = findIndexOfString(expr->name, boundVariablesList);

			if (n > 0) {
				printf("%d", n);
			} else {
				printf("%s", expr->name);
			}

			break;

		case lcExpressionType_LambdaExpr:
			printf("λ");
			newBoundVariablesList = addStringToList(expr->name, boundVariablesList);
			printDeBruijnIndexLocal(expr->expr, newBoundVariablesList);
			newBoundVariablesList->next = NULL;
			free(newBoundVariablesList);
			newBoundVariablesList = NULL;
			break;

		case lcExpressionType_FunctionCall:
			printf("(");
			printDeBruijnIndexLocal(expr->expr, boundVariablesList);
			printf(" ");
			printDeBruijnIndexLocal(expr->expr2, boundVariablesList);
			printf(")");
			break;

		default:
			break;
	}
}

void printDeBruijnIndex(LC_EXPR * expr) {
	printDeBruijnIndexLocal(expr, NULL);
}

/* **** The End **** */
