/* facility/src/main.c */

/* ThAW: Started on 2022-08-22 */

/* To compile and link: $ make */
/* To run: $ ./facility */
/* To remove all build products: $ make clean */
/* To do all of the above: $ make clean && make && ./facility */

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

#include "types.h"

#include "char-source.h"
#include "de-bruijn.h"
#include "string-set.h"

// **** Memory manager functions ****

/* TODO: Memory manager version 2:

typedef struct MEMMGR_RECORD_STRUCT {
	void * ptr;
	struct MEMMGR_RECORD_STRUCT * next;
} MEMMGR_RECORD;
*/

typedef struct {
	void (*mark)(void * ptr);
	void (*unmark)(void * ptr);
	BOOL (*isMarked)(void * ptr);
	/* MEMMGR_RECORD * memmgrRecords; */
} MEMMGR;

void markExpr(void * ptr) {
	((LC_EXPR *)ptr)->mark = 1;
}

void unmarkExpr(void * ptr) {
	((LC_EXPR *)ptr)->mark = 0;
}

BOOL isExprMarked(void * ptr) {
	return ((LC_EXPR *)ptr)->mark != 0;
}

MEMMGR * createMemoryManager(void (*mark)(void * ptr), void (*unmark)(void * ptr), BOOL (*isMarked)(void * ptr)) {
	MEMMGR * mm = (MEMMGR *)malloc(sizeof(MEMMGR));

	mm->mark = mark;
	mm->unmark = unmark;
	mm->isMarked = isMarked;
	/* mm->memmgrRecords = NULL; */

	return mm;
}

MEMMGR * exprMemMgr = NULL;
MEMMGR * stringListMemMgr = NULL;
MEMMGR * stringSetMemMgr = NULL;

void initMemoryManagers() {
	exprMemMgr = createMemoryManager(markExpr, unmarkExpr, isExprMarked);
	/* stringListMemMgr = createMemoryManager(...);
	stringSetMemMgr = createMemoryManager(...); */
}

void terminateMemoryManagers() {
}

// **** Memory manager version 1 ****

typedef struct MEMMGR_RECORD_STRUCT {
	LC_EXPR * expr;
	struct MEMMGR_RECORD_STRUCT * next;
} MEMMGR_RECORD;

MEMMGR_RECORD * memmgrRecords = NULL;

int getNumMemMgrRecords() {
	int n = 0;
	MEMMGR_RECORD * mmRec = memmgrRecords;

	while (mmRec != NULL) {
		++n;
		mmRec = mmRec->next;
	}

	return n;
}

void clearMarks() {
	MEMMGR_RECORD * mmRec;

	for (mmRec = memmgrRecords; mmRec != NULL; mmRec = mmRec->next) {
		mmRec->expr->mark = 0;
	}
}

void setMarksInExprTree(LC_EXPR * expr) {
	/* Do this recursively */
	expr->mark = 1;

	if (expr->expr != NULL) {
		setMarksInExprTree(expr->expr);
	}

	if (expr->expr2 != NULL) {
		setMarksInExprTree(expr->expr2);
	}
}

void freeUnmarkedStructs() {
	MEMMGR_RECORD ** ppmmRec = &memmgrRecords;
	MEMMGR_RECORD * mmRec = *ppmmRec;

	while (mmRec != NULL) {

		if (mmRec->expr->mark == 0) {
			/* Free mmRec->expr. Do not free recursively. */
			mmRec->expr->expr = NULL;
			mmRec->expr->expr2 = NULL;
			free(mmRec->expr);
			mmRec->expr = NULL;

			/* Then free mmRec, preserving the integrity of the linked list */
			MEMMGR_RECORD * nextmmRec = mmRec->next;

			mmRec->expr = NULL;
			mmRec->next = NULL;
			free(mmRec);
			*ppmmRec = nextmmRec;
		} else {
			ppmmRec = &mmRec->next;
		}

		mmRec = *ppmmRec;
	}
}

void collectGarbage(LC_EXPR * exprTreesToMark[]) {
	int i;

	clearMarks();

	for (i = 0; exprTreesToMark[i] != NULL; ++i) {
		setMarksInExprTree(exprTreesToMark[i]);
	}

	freeUnmarkedStructs();
}

void freeAllStructs() {
	clearMarks();
	freeUnmarkedStructs();
}

// **** Create and Free functions ****

LC_EXPR * createExpr(int type, char * name, LC_EXPR * expr, LC_EXPR * expr2) {

	if (name != NULL && strlen(name) >= maxStringValueLength - 1) {
		fprintf(stderr, "createExpr() : The name '%s' is too long.\n", name);
		return NULL;
	}

	LC_EXPR * newExpr = (LC_EXPR *)malloc(sizeof(LC_EXPR));

	newExpr->mark = 0;
	newExpr->type = type;
	memset(newExpr->name, 0, maxStringValueLength);

	if (name != NULL) {
		strcpy(newExpr->name, name);
	}

	newExpr->expr = expr;
	newExpr->expr2 = expr2;

	/* TODO: Add newExpr to memmgrRecords */
	MEMMGR_RECORD * mmRec = (MEMMGR_RECORD *)malloc(sizeof(MEMMGR_RECORD));

	mmRec->expr = newExpr;
	mmRec->next = memmgrRecords;
	memmgrRecords = mmRec;

	return newExpr;
}

LC_EXPR * cloneExpr(LC_EXPR * expr) {
	return createExpr(expr->type, expr->name, expr->expr, expr->expr2);
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

void freeExpr(LC_EXPR * expr) {
	memset(expr->name, 0, maxStringValueLength);

	/* if (expr->expr != NULL) {
		freeExpr(expr->expr);
		expr->expr = NULL;
	}

	if (expr->expr2 != NULL) {
		freeExpr(expr->expr2);
		expr->expr2 = NULL;
	} */

	/* TODO? : Remove newExpr from memmgrRecords? Or just wait for garbage collection? */

	expr->expr = NULL;
	expr->expr2 = NULL;
	free(expr);
}

/* ---- */

BOOL areEqual(LC_EXPR * expr1, LC_EXPR * expr2) {

	if (expr1->type != expr2->type) {
		return FALSE;
	}

	switch (expr1->type) {
		case lcExpressionType_Variable:
			return !strcmp(expr1->name, expr2->name);

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

BOOL containsUnboundVariableNamed(LC_EXPR * expr, char * varName, STRING_SET * boundVariableNames) {
	BOOL result = FALSE;
	STRING_SET * newStringSet = NULL;

	switch (expr->type) {
		case lcExpressionType_Variable:
			return !strcmp(expr->name, varName) && !stringSetContains(boundVariableNames, varName);

		case lcExpressionType_LambdaExpr:
			/* This lambda expression binds the variable expr->name */
			/* Create the set: boundVariableNames union { expr->name } */

			if (!stringSetContains(boundVariableNames, expr->name)) {
				newStringSet = addStringToSet(expr->name, boundVariableNames);
				boundVariableNames = newStringSet;
			}

			result = containsUnboundVariableNamed(expr->expr, varName, boundVariableNames);

			/* If we allocated any memory by calling addStringToList() above, then free it now */

			if (newStringSet != NULL) {
				newStringSet->next = NULL;
				free(newStringSet);
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

STRING_SET * getSetOfAllVariableNames(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			return addStringToSet(expr->name, NULL);

		case lcExpressionType_LambdaExpr:
			return addStringToSet(expr->name, getSetOfAllVariableNames(expr->expr));

		case lcExpressionType_FunctionCall:
			return unionOfStringSets(getSetOfAllVariableNames(expr->expr), getSetOfAllVariableNames(expr->expr2));

		default:
			break;
	}

	return NULL;
}

LC_EXPR * renameBoundVariable(LC_EXPR * expr, char * newName, char * oldName) {
	/* Also known as α-conversion (alpha conversion) */

	switch (expr->type) {
		case lcExpressionType_Variable:
			return expr;

		case lcExpressionType_LambdaExpr:

			if (strcmp(expr->name, oldName)) {
				return createLambdaExpr(expr->name, renameBoundVariable(expr->expr, newName, oldName));
			}

			return createLambdaExpr(newName, substituteForUnboundVariable(expr->expr, oldName, createVariable(newName)));

		case lcExpressionType_FunctionCall:
			return createFunctionCall(renameBoundVariable(expr->expr, newName, oldName), renameBoundVariable(expr->expr2, newName, oldName));

		default:
			break;
	}

	return NULL;
}

BOOL isBetaReducible(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_LambdaExpr:
			return isBetaReducible(expr->expr);

		case lcExpressionType_FunctionCall:
			return expr->expr->type == lcExpressionType_LambdaExpr || isBetaReducible(expr->expr) || isBetaReducible(expr->expr2);

		default:
			break;
	}

	return FALSE;
}

LC_EXPR * betaReduce(LC_EXPR * expr, int maxDepth) {

	if (maxDepth <= 0) {
		return expr;
	}

	--maxDepth;

	switch (expr->type) {
		case lcExpressionType_Variable:
			return expr;

		case lcExpressionType_LambdaExpr:
			/*
			public override betaReduce(options: ILCBetaReductionOptions = {}): ILCExpression {
				if (typeof options.generateNewVariableName === 'undefined') {
					throw new Error(
						'lambda-expression.ts betaReduce() : options.generateNewVariableName is undefined'
					);
				}

				let maxDepth = ifDefinedThenElse(options.maxDepth, defaultMaxBetaReductionDepth);

				if (maxDepth <= 0) {
					return this;
					// throw new Error('lambda-expression.ts betaReduce() : maxDepth <= 0');
				}

				maxDepth--;

				const strategy = ifDefinedThenElse(options.strategy, defaultBetaReductionStrategy);
				const newOptions = {
					strategy,
					generateNewVariableName: options.generateNewVariableName,
					maxDepth
				};

				// 'redex' means 'reducible expression'.
				const redex = this.etaReduce();

				if (!isLCLambdaExpression(redex)) {
					return redex.betaReduce(newOptions);
				}

				switch (strategy) {
					case BetaReductionStrategy.CallByName:
						return redex;

					case BetaReductionStrategy.NormalOrder:
						return new LCLambdaExpression(redex.arg, redex.body.betaReduce(newOptions));

					case BetaReductionStrategy.CallByValue:
						return redex;
				}
			}
			*/
			return NULL;

		case lcExpressionType_FunctionCall:
			/*
			/// normal - leftmost outermost; the most popular reduction strategy

			private betaReduceNormalOrder(
				generateNewVariableName: () => string,
				maxDepth: number
			): ILCExpression {

				if (maxDepth <= 0) {
					return this;
					// throw new Error('call.ts : betaReduceNormalOrder() : maxDepth <= 0');
				}

				const options = {
					strategy: BetaReductionStrategy.NormalOrder,
					generateNewVariableName,
					maxDepth
				};

				// First, evaluate this.callee; if it does not evaluate to a LCLambdaExpression,
				// then return.
				const evaluatedCallee = this.callee.deltaReduce().betaReduce(options);

				if (!isLCLambdaExpression(evaluatedCallee)) {
					// The result is App(e1’’, nor e2),
					// where e1’’ = nor e1’ = ...
					// and e1’ = nor e1 = evaluatedCallee
					// and e1 = this.callee
					const result = new LCFunctionCall(
						evaluatedCallee.deltaReduce().betaReduce(options),
						// Note: Simply using 'this.arg' as the second argument fails.
						this.arg.deltaReduce().betaReduce(options)
					);

					return result;
				}

				// Next, substitute this.arg in for the arg in the evaluated callee.

				return this.betaReduceCore(evaluatedCallee, this.arg, generateNewVariableName)
					.deltaReduce()
					.betaReduce(options);
			}
			*/
			return NULL;

		default:
			break;
	}

	return NULL;
}

LC_EXPR * etaReduce(LC_EXPR * expr) {
	/* Reduce λx.(f x) to f if x does not appear free in f. */

	switch (expr->type) {
		case lcExpressionType_Variable:
			/* return expr; */

			return cloneExpr(expr);

			/* return createVariable(expr->name); */

		case lcExpressionType_LambdaExpr:

			if (expr->expr->type == lcExpressionType_FunctionCall && expr->expr->expr2->type == lcExpressionType_Variable && !strcmp(expr->expr->expr2->name, expr->name) && !containsUnboundVariableNamed(expr->expr->expr, expr->name, NULL)) {
				return etaReduce(expr->expr->expr);
			}

			return createLambdaExpr(expr->name, etaReduce(expr->expr));

		case lcExpressionType_FunctionCall:
			return createFunctionCall(etaReduce(expr->expr), etaReduce(expr->expr2));

		default:
			break;
	}

	return NULL;
}

BOOL areIsomorphic(LC_EXPR * expr1, LC_EXPR * expr2) {
	const int bufSize = 64;
	char buf1[bufSize];
	char buf2[bufSize];

	getDeBruijnIndex(expr1, buf1, bufSize);
	getDeBruijnIndex(expr2, buf2, bufSize);

	return strlen(buf1) > 0 && !strcmp(buf1, buf2);
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
	CharSource * cs = createCharSource(str);

	LC_EXPR * parseTree = parseExpression(cs);

	freeCharSource(cs);

	return parseTree;
}

void printExpr(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			printf("%s", expr->name);
			break;

		case lcExpressionType_LambdaExpr:
			printf("λ");
			printf("%s", expr->name);
			printf(".");
			printExpr(expr->expr);
			break;

		case lcExpressionType_FunctionCall:
			printf("(");
			printExpr(expr->expr);
			printf(" ");
			printExpr(expr->expr2);
			printf(")");
			break;

		default:
			break;
	}
}

void parseAndReduce(char * str) {
	printf("\nInput: '%s'\n", str);

	LC_EXPR * parseTree = parse(str);

	/* LC_EXPR * reducedExpr = reduce(parseTree);

	freeExpression(reducedExpr); */

	if (parseTree == NULL) {
		fprintf(stderr, "parse('%s') : parseExpression() returned NULL\n", str);
		return;
	}

	printf("Output: ");
	printExpr(parseTree);
	printf("\n");

	const int bufSize = 64;
	char buf[bufSize];

	getDeBruijnIndex(parseTree, buf, bufSize);

	printf("Expr type = %d\nDeBruijn index: %s\n", parseTree->type, buf);

	LC_EXPR * etaReduction = etaReduce(parseTree);

	printf("Eta reduction: ");
	printExpr(etaReduction);
	printf("\n");

	/* freeExpr(etaReduction);
	freeExpr(parseTree); */

	LC_EXPR * fff[] = { etaReduction, NULL };

	printf("1) NumMemMgrRecords: %d\n", getNumMemMgrRecords());
	collectGarbage(fff);
	printf("2) NumMemMgrRecords: %d\n", getNumMemMgrRecords());
	freeAllStructs();
	printf("3) NumMemMgrRecords: %d\n", getNumMemMgrRecords());
}

void runTests() {
	printf("\nRunning tests...\n");

	initMemoryManagers();

	/* parseAndReduce("x");
	parseAndReduce("(lambda (x) x)"); */ /* The identity function */

	/* parseAndReduce(""); */

	parseAndReduce("x");
	parseAndReduce("\\x.x");
	parseAndReduce("(x y)");

	parseAndReduce("\\x.\\y.x");
	parseAndReduce("\\x.\\y.y");

	/* Eta-reduction test: */
	parseAndReduce("\\f.\\x.(f x)"); /* -> \\f.f : Fails to reduce */
	parseAndReduce("\\x.(f x)"); /* -> f : Succeeds */

	terminateMemoryManagers();

	printf("\nDone.\n");
}

/* **** The Main MoFo **** */

int main(int argc, char * argv[]) {
	runTests();

	return 0; /* Zero (as a Unix exit code) means success. */
}

/* **** The End **** */
