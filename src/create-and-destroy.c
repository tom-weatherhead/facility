/* facility/src/create-and-destroy.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
/* #include <ctype.h> */
/* #include <assert.h> */

#include "boolean.h"

#include "types.h"
#include "memory-manager.h"

static int numMallocs = 0;
static int numFrees = 0;

void printCreateAndDestroyMemMgrReport() {
	printf("  Create and destroy: %d mallocs, %d frees", numMallocs, numFrees);

	if (numMallocs > numFrees) {
		printf(" : **** LEAKAGE ****");
	}

	printf("\n");
}

// **** Create and Free functions ****

static LC_EXPR * createExpr(int type, char * name, LC_EXPR * expr, LC_EXPR * expr2) {

	if (name != NULL && strlen(name) >= maxStringValueLength - 1) {
		fprintf(stderr, "createExpr() : The name '%s' is too long.\n", name);
		return NULL;
	}

	LC_EXPR * newExpr = (LC_EXPR *)malloc(sizeof(LC_EXPR));

	++numMallocs;
	newExpr->mark = 0;
	newExpr->type = type;
	memset(newExpr->name, 0, maxStringValueLength);

	if (name != NULL) {
		strcpy(newExpr->name, name);
	}

	newExpr->expr = expr;
	newExpr->expr2 = expr2;

	addItemToMemMgrRecords(newExpr);

	return newExpr;
}

LC_EXPR * createVariable(char * name) {
	return createExpr(lcExpressionType_Variable, name, NULL, NULL);
}

LC_EXPR * createLambdaExpr(char * argName, LC_EXPR * body) {
	return createExpr(lcExpressionType_LambdaExpr, argName, body, NULL);
}

LC_EXPR * createFunctionCall(LC_EXPR * expr, LC_EXPR * expr2) {
	return createExpr(lcExpressionType_FunctionCall, NULL, expr, expr2);
}

/* void freeExpr(LC_EXPR * expr) {
	memset(expr->name, 0, maxStringValueLength);

	/ * if (expr->expr != NULL) {
		freeExpr(expr->expr);
		expr->expr = NULL;
	}

	if (expr->expr2 != NULL) {
		freeExpr(expr->expr2);
		expr->expr2 = NULL;
	} * /

	/ * TODO? : Remove newExpr from memmgrRecords? Or just wait for garbage collection? * /

	expr->expr = NULL;
	expr->expr2 = NULL;
	free(expr);
	++numFrees;
} */

void incNumFreesInCreateAndDestroy() {
	++numFrees;
}

/* **** The End **** */
