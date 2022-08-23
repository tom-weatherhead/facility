/* facility/src/main.c */

/*
toString
* equals
X applySubstitution is only needed if unify() is implemented
* containsVariableNamed
* containsBoundVariableNamed
* containsUnboundVariableNamed
* substituteForUnboundVariable
getSetOfAllVariableNames
renameBoundVariable -> α-conversion
isBetaReducible
betaReduce
X deltaReduce
etaReduce -> Reduce λx.(f x) to f if x does not appear free in f.
X kappaReduce
isIsomorphicTo -> compare De Bruijn indices
*/

/*
void fn(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			break;

		case lcExpressionType_LambdaExpr:
			break;

		case lcExpressionType_FunctionCall:
			break;

		default:
			break;
	}

	return ;
}
*/

/* ThAW: Started on 2022-08-22 */

/* To compile and link: $ make */
/* To run: $ ./facility */
/* To remove all build products: $ make clean */

/* The grammar of the Lambda Calculus:
 * expression := variable
 *             | lambda-symbol variable dot expression		(function def'n)
 *             | (expression expression)					(function call)
 *
 * The lambda-symbol is λ
 */

/* From https://opendsa.cs.vt.edu/ODSA/Books/PL/html/Syntax.html :
 *
 * 	A complete BNF (Backus-Naur form) grammar for the lambda calculus:
 *
 *  < λexp > ::= < var >
 *           | λ < var > . < λexp >
 *           | ( < λexp > < λexp > )
 */

/* Glossary:
 * A 'redex' is a reducible expression
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
/* #include <ctype.h> */
/* #include <assert.h> */

#include "boolean.h"

#include "char-source.h"

/* Preprocessor defines */

/* const int maxStringValueLength = 8; */
#define maxStringValueLength 8

/* Forward declarations of some structs */

/* struct LC_EXPR_STRUCT; */

/* Type definitions */

/* typedef struct {
	char name[maxStringValueLength];
} LC_VAR;

typedef struct {
	LC_VAR * var;
	struct LC_EXPR_STRUCT * body;
} LC_FN_DEFN;

typedef struct {
	struct LC_EXPR_STRUCT * fn;
	struct LC_EXPR_STRUCT * arg; / * Every function takes exactly one arg * /
} LC_FN_CALL;

typedef struct LC_EXPR_STRUCT {
	int type;
	LC_VAR * var;
	LC_FN_DEFN * fnDefn; / * i.e. lambdaExpr * /
	LC_FN_CALL * fnCall;
} LC_EXPR; */

typedef struct LC_EXPR_STRUCT {
	/* int mark; */ /* For use by a mark-and-sweep garbage collector */
	int type;
	char name[maxStringValueLength]; /* Used for Variable and LambdaExpr */
	struct LC_EXPR_STRUCT * expr; /* Used for LambdaExpr and FunctionCall */
	struct LC_EXPR_STRUCT * expr2; /* Used for FunctionCall */
} LC_EXPR; /* A Lambda calculus expression */

/* Enums */

enum {
	/* lcExpressionType_Undefined, */
	lcExpressionType_Variable,
	lcExpressionType_LambdaExpr,
	lcExpressionType_FunctionCall
};

// **** Create and Free functions ****

/* LC_EXPR * createUndefinedExpression() {
	LC_EXPR * result = (LC_EXPR *)malloc(sizeof(LC_EXPR));

	result->type = lcExpressionType_Undefined;
	result->var = NULL;
	result->fnDefn = NULL; / * i.e. lambdaExpr * /
	result->fnCall = NULL;

	return result;
} */

// **** Create and Free Variable functions ****

LC_EXPR * createExpr(int type, char * name, LC_EXPR * expr, LC_EXPR * expr2) {

	if (name != NULL && strlen(name) >= maxStringValueLength - 1) {
		fprintf(stderr, "createExpr() : The name '%s' is too long.\n", name);
		return NULL;
	}

	LC_EXPR * newExpr = (LC_EXPR *)malloc(sizeof(LC_EXPR));

	newExpr->type = type;
	memset(newExpr->name, 0, maxStringValueLength);

	if (name != NULL) {
		strcpy(newExpr->name, name);
	}

	newExpr->expr = expr;
	newExpr->expr2 = expr2;

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

/* See https://en.wikipedia.org/wiki/De_Bruijn_index */

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

void printDeBruijnIndex(LC_EXPR * expr, STRING_LIST * boundVariablesList) {
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
			printDeBruijnIndex(expr->expr, newBoundVariablesList);
			newBoundVariablesList->next = NULL;
			free(newBoundVariablesList);
			newBoundVariablesList = NULL;
			break;

		case lcExpressionType_FunctionCall:
			printf("(");
			printDeBruijnIndex(expr->expr, boundVariablesList);
			printf(" ");
			printDeBruijnIndex(expr->expr2, boundVariablesList);
			printf(")");
			break;

		default:
			break;
	}
}

void freeExpr(LC_EXPR * expr) {
	memset(expr->name, 0, maxStringValueLength);

	if (expr->expr != NULL) {
		freeExpr(expr->expr);
		expr->expr = NULL;
	}

	if (expr->expr2 != NULL) {
		freeExpr(expr->expr2);
		expr->expr2 = NULL;
	}

	free(expr);
}

BOOL areEqual(LC_EXPR * expr1, LC_EXPR * expr2) {

	if (expr1->type != expr2->type) {
		return FALSE;
	}

	switch (expr1->type) {
		case lcExpressionType_Variable:
			return !strcmp(expr1->name, expr2->name) ? TRUE : FALSE;

		case lcExpressionType_LambdaExpr:
			return !strcmp(expr1->name, expr2->name) && areEqual(expr1->expr, expr2->expr);

		case lcExpressionType_FunctionCall:
			return areEqual(expr1->expr, expr2->expr) && areEqual(expr2->expr, expr2->expr2);

		default:
			break;
	}

	return FALSE;
}

BOOL containsVariableNamed(LC_EXPR * expr, char * varName) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			return !strcmp(expr->name, varName);

		case lcExpressionType_LambdaExpr:
			return !strcmp(expr->name, varName) || containsVariableNamed(expr->expr, varName);

		case lcExpressionType_FunctionCall:
			return containsVariableNamed(expr->expr, varName) || containsVariableNamed(expr->expr2, varName);

		default:
			break;
	}

	return FALSE;
}

BOOL containsBoundVariableNamed(LC_EXPR * expr, char * varName) {

	switch (expr->type) {
		case lcExpressionType_LambdaExpr:
			return !strcmp(expr->name, varName) || containsBoundVariableNamed(expr->expr, varName);

		case lcExpressionType_FunctionCall:
			return containsBoundVariableNamed(expr->expr, varName) || containsBoundVariableNamed(expr->expr2, varName);

		/* case lcExpressionType_Variable: */
		default:
			break;
	}

	return FALSE;
}

BOOL containsUnboundVariableNamed(LC_EXPR * expr, char * varName, STRING_LIST * boundVariableNames) {
	BOOL result = FALSE;
	STRING_LIST * newStringList = NULL;

	switch (expr->type) {
		case lcExpressionType_Variable:
			return !strcmp(expr->name, varName) && !stringListContains(boundVariableNames, varName);

		case lcExpressionType_LambdaExpr:
			/* This lambda expression binds the variable expr->name */
			/* Create the set: boundVariableNames union { expr->name } */

			if (!stringListContains(boundVariableNames, expr->name)) {
				newStringList = addStringToList(expr->name, boundVariableNames);
				boundVariableNames = newStringList;
			}

			result = containsUnboundVariableNamed(expr->expr, varName, boundVariableNames);

			/* If we allocated any memory by calling addStringToList() above, then free it now */

			if (newStringList != NULL) {
				newStringList->next = NULL;
				free(newStringList);
			}

			return result;

		case lcExpressionType_FunctionCall:
			return containsUnboundVariableNamed(expr->expr, varName, boundVariableNames) || containsUnboundVariableNamed(expr->expr2, varName, boundVariableNames);

		default:
			break;
	}

	return FALSE;
}

LC_EXPR * substituteForUnboundVariable(LC_EXPR * expr, char * varName, LC_EXPR * replacementExpr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			return !strcmp(expr->name, varName) ? replacementExpr : expr;

		case lcExpressionType_LambdaExpr:
			return !strcmp(expr->name, varName) ? expr : createLambdaExpr(expr->name, substituteForUnboundVariable(expr->expr, varName, replacementExpr));

		case lcExpressionType_FunctionCall:
			return createFunctionCall(substituteForUnboundVariable(expr->expr, varName, replacementExpr), substituteForUnboundVariable(expr->expr2, varName, replacementExpr));

		default:
			break;
	}

	return NULL;
}

/*
// α-conversion
renameBoundVariable(newName: string, oldName: string): ILCExpression; // Alpha-conversion

// β-reduction
isBetaReducible(): boolean;
betaReduce(options?: ILCBetaReductionOptions): ILCExpression;

// δ-reduction for extended Lambda calculus; e.g. ((+ 2) 3) δ-> 5
deltaReduce(): ILCExpression;

// η-reduction: Reduce λx.(f x) to f if x does not appear free in f.
etaReduce(): ILCExpression;

// κ-reduction is the reduction of the SKI combinators (?)
 */

/* TODO: Alpha-conversion α : renameBoundVariable() */
/* TODO: Beta-reduction β : */

/* export enum BetaReductionStrategy {
	CallByName,
	NormalOrder,
	CallByValue,
	ApplicativeOrder,
	HybridApplicativeOrder,
	HeadSpine,
	HybridNormalOrder,
	ThAWHackForYCombinator
} */

/* X TODO: Delta-reduction δ (reduction of constant arithmetic exprs) */
/* TODO: Eta-reduction η */
/* TODO? : Kappa-reduction κ */

/* LC_EXPR * reduce(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			/ * Return a clone of the expr so it can be freed separately * /
			return cloneExpr(expr->var);

		case lcExpressionType_LambdaExpr:
			return reduceLambdaExpression(expr->fnDefn);

		case lcExpressionType_FunctionCall:
			return reduceFunctionCall(expr->fnCall);

		default:
			return NULL;
	}
} */

LC_EXPR * parseExpression(CharSource * cs) {
	char dstBuf[maxStringValueLength];
	int c = getNextChar(cs);

	if (c == EOF) {
		return NULL;
	/*} else if (c == 'λ') { */ /* error: character too large for enclosing character literal type */
	} else if (c == '\\') {
		char argName[maxStringValueLength];

		if (getIdentifier(cs, argName, maxStringValueLength) == 0) {
			return NULL;
		}

		/* Consume . */

		if (getIdentifier(cs, dstBuf, maxStringValueLength) == 0 || strcmp(dstBuf, ".")) {
			fprintf(stderr, "parseExpression() : Error consuming '.'\n");
			return NULL;
		}

		LC_EXPR * expr = parseExpression(cs);

		return createLambdaExpr(argName, expr);
	} else if (c == '(') {
		LC_EXPR * expr = parseExpression(cs);
		LC_EXPR * expr2 = parseExpression(cs);

		/* Consume ) */

		if (getIdentifier(cs, dstBuf, maxStringValueLength) == 0 || strcmp(dstBuf, ")")) {
			fprintf(stderr, "parseExpression() : Error consuming ')'\n");
			return NULL;
		}

		return createFunctionCall(expr, expr2);
	} else {
		rewindOneChar(cs);

		if (getIdentifier(cs, dstBuf, maxStringValueLength) == 0) {
			return NULL;
		}

		return createVariable(dstBuf);
	}
}

LC_EXPR * parse(char * str) {
	printf("\nInput: '%s'\n", str);

	CharSource * cs = createCharSource(str);

	LC_EXPR * parseTree = parseExpression(cs);

	/* LC_EXPR * parseTree = parseExpression(cs, -1);

	LC_EXPR * reducedExpr = reduce(parseTree);

	printf("Output: ");
	printExpr(reducedExpr);

	freeExpression(reducedExpr);
	freeExpression(parseTree); */
	freeCharSource(cs);

	if (parseTree == NULL) {
		fprintf(stderr, "parse('%s') : parseExpression() returned NULL\n", str);
	} else {
		printf("Expr type = %d\nDeBruijn index: ", parseTree->type);
		printDeBruijnIndex(parseTree, NULL);
		printf("\n");
	}

	return parseTree;
}

/* void parseAndReduce(char * str) {
	printf("\nInput: '%s'\n", str);

	CharSource * cs = createCharSource(str);

	LC_EXPR * parseTree = parseExpression(cs, -1);

	LC_EXPR * reducedExpr = reduce(parseTree);

	printf("Output: ");
	printExpr(reducedExpr);

	freeExpression(reducedExpr);
	freeExpression(parseTree);
	freeCharSource(cs);
} */

void runTests() {
	printf("\nRunning tests...\n");

	/* parseAndReduce("x");
	parseAndReduce("(lambda (x) x)"); */ /* The identity function */

	/* parseAndReduce(""); */

	parse("x");
	parse("\\x.x");
	parse("(x y)");

	parse("\\x.\\y.x");
	parse("\\x.\\y.y");

	printf("\nDone.\n\n");
}

/* **** The Main MoFo **** */

int main(int argc, char * argv[]) {
	runTests();

	return 0; /* Zero (as a Unix exit code) means success. */
}

/* **** The End **** */
