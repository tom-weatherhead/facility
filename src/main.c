/* facility/src/main.c */

/* ThAW: Started on 2022-08-22 */

/* To compile and link: $ make */
/* To run tests: $ ./facility -t */
/* To remove all build products: $ make clean */
/* To do all of the above: $ make clean && make && ./facility -t */

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

typedef enum {
	brsCallByName,
	brsNormalOrder,
	brsCallByValue,
	brsApplicativeOrder,
	brsHybridApplicativeOrder,
	brsHeadSpine,
	brsHybridNormalOrder,
	brsThAWHackForYCombinator,
	brsDefault = brsNormalOrder
} BetaReductionStrategy;

static int numMallocs = 0;
static int numFrees = 0;

static int generatedVariableNumber = 0;

static LC_EXPR * betaReduce(LC_EXPR * expr, int maxDepth, BetaReductionStrategy strategy);
static LC_EXPR * etaReduce(LC_EXPR * expr);

// **** Memory manager functions ****

/* TODO: Memory manager version 2:

typedef struct MEMMGR_RECORD_STRUCT {
	void * ptr;
	struct MEMMGR_RECORD_STRUCT * next;
} MEMMGR_RECORD;

typedef struct {
	void (*mark)(void * ptr);
	void (*unmark)(void * ptr);
	BOOL (*isMarked)(void * ptr);
	/ * MEMMGR_RECORD * memmgrRecords; * /
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

	++numMallocs;
	mm->mark = mark;
	mm->unmark = unmark;
	mm->isMarked = isMarked;
	/ * mm->memmgrRecords = NULL; * /

	return mm;
}

MEMMGR * exprMemMgr = NULL;
MEMMGR * stringListMemMgr = NULL;
MEMMGR * stringSetMemMgr = NULL;

void initMemoryManagers() {
	exprMemMgr = createMemoryManager(markExpr, unmarkExpr, isExprMarked);
	/ * stringListMemMgr = createMemoryManager(...);
	stringSetMemMgr = createMemoryManager(...); * /
}
*/

void generateMemoryManagementReport() {
	printf("\nMemory management report:\n");
	printf("  Expressions: %d mallocs, %d frees", numMallocs, numFrees);

	if (numMallocs > numFrees) {
		printf(" : **** LEAKAGE ****");
	}

	printf("\n");
	printCharSourceMemMgrReport();
	printStringSetMemMgrReport();
	printStringListMemMgrReport();
}

/*
void terminateMemoryManagers() {

	if (exprMemMgr != NULL) {
		free(exprMemMgr);
		exprMemMgr = NULL;
		++numFrees;
	}

	generateMemoryManagementReport();
}
*/

// **** BEGIN Memory manager version 1 ****

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
			++numFrees;
			mmRec->expr = NULL;

			/* Then free mmRec, preserving the integrity of the linked list */
			MEMMGR_RECORD * nextmmRec = mmRec->next;

			mmRec->expr = NULL;
			mmRec->next = NULL;
			free(mmRec);
			++numFrees;
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

// **** END Memory manager version 1 ****

// **** Create and Free functions ****

LC_EXPR * createExpr(int type, char * name, LC_EXPR * expr, LC_EXPR * expr2) {

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

	/* TODO: Add newExpr to memmgrRecords */
	MEMMGR_RECORD * mmRec = (MEMMGR_RECORD *)malloc(sizeof(MEMMGR_RECORD));

	++numMallocs;
	mmRec->expr = newExpr;
	mmRec->next = memmgrRecords;
	memmgrRecords = mmRec;

	return newExpr;
}

/* LC_EXPR * cloneExpr(LC_EXPR * expr) {
	return createExpr(expr->type, expr->name, expr->expr, expr->expr2);
} */

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

/* Domain Object Model functions */

/* BOOL areEqual(LC_EXPR * expr1, LC_EXPR * expr2) {

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
} */

static BOOL containsBoundVariableNamed(LC_EXPR * expr, char * varName) {

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

static BOOL containsUnboundVariableNamed(LC_EXPR * expr, char * varName, STRING_SET * boundVariableNames) {
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
				freeStringSet(newStringSet);
			}

			return result;

		case lcExpressionType_FunctionCall:
			return containsUnboundVariableNamed(expr->expr, varName, boundVariableNames) || containsUnboundVariableNamed(expr->expr2, varName, boundVariableNames);

		default:
			break;
	}

	return FALSE;
}

static LC_EXPR * substituteForUnboundVariable(LC_EXPR * expr, char * varName, LC_EXPR * replacementExpr) {

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

static STRING_SET * getSetOfAllVariableNames(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			return addStringToSet(expr->name, NULL);

		case lcExpressionType_LambdaExpr:
			return addStringToSet(expr->name, getSetOfAllVariableNames(expr->expr));

		case lcExpressionType_FunctionCall:
			return unionOfStringSets(getSetOfAllVariableNames(expr->expr), getSetOfAllVariableNames(expr->expr2), TRUE);

		default:
			break;
	}

	return NULL;
}

static LC_EXPR * renameBoundVariable(LC_EXPR * expr, char * newName, char * oldName) {
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

/* BOOL isBetaReducible(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_LambdaExpr:
			return isBetaReducible(expr->expr);

		case lcExpressionType_FunctionCall:
			return expr->expr->type == lcExpressionType_LambdaExpr || isBetaReducible(expr->expr) || isBetaReducible(expr->expr2);

		default:
			break;
	}

	return FALSE;
} */

static void generateNewVariableName(char * buf, int bufSize) {
	memset(buf, 0, bufSize);
	++generatedVariableNumber;
	sprintf(buf, "v%d", generatedVariableNumber);
}

static LC_EXPR * betaReduceCore(LC_EXPR * lambdaExpression, LC_EXPR * arg) {
	/* Rename variables as necessary (α-conversion) */

	/* My idea for an algorithm:
	1) Build a set of all (unbound?) variables in the body;
	I.e. Create an array of the names of all unbound variables in arg: */

	STRING_SET * allVarNames = getSetOfAllVariableNames(arg);
	STRING_SET * allVarNamesUnboundInArg = NULL;
	STRING_SET * ss;

	for (ss = allVarNames; ss != NULL; ss = ss->next) {

		if (containsUnboundVariableNamed(arg, ss->str, NULL)) {
			allVarNamesUnboundInArg = addStringToSet(ss->str, allVarNamesUnboundInArg);
		}
	}

	freeStringSet(allVarNames);
	allVarNames = NULL;

	/*
	// 2) for each var v in the set:
	//   - If v occurs as a bound variable in the callee, then:
	//     - Generate a new variable name w that does not occur in the callee;
	//     - In the callee, replace all bound occurrences of v with w.

	// The variable renaming here prevents unbound variables in arg from
	// becoming unintentionally bound when the substitution (into the Lambda
	// expression's body) is performed.
	*/

	for (ss = allVarNamesUnboundInArg; ss != NULL; ss = ss->next) {

		if (containsBoundVariableNamed(lambdaExpression, ss->str)) {
			char buf[maxStringValueLength];

			generateNewVariableName(buf, maxStringValueLength);

			/* α-conversion happens here: */
			lambdaExpression = renameBoundVariable(lambdaExpression, buf, ss->str);
		}
	}

	freeStringSet(allVarNamesUnboundInArg);
	allVarNamesUnboundInArg = NULL;

	/* Substitution:
	Replace all unbound occurrences of Lambda expression's formal parameter
	(lambdaExpression.arg) in the Lambda expression's body
	(lambdaExpression.body) with an actual parameter (arg) : */

	return substituteForUnboundVariable(lambdaExpression->expr, lambdaExpression->name, arg);
}

/* static LC_EXPR * betaReduceFunctionCall_CallByName(LC_EXPR * expr, int maxDepth) {

	if (maxDepth <= 0) {
		return this;
		// throw new Error('call.ts : betaReduceCallByName() : maxDepth <= 0');
	}

	const options = {
		strategy: BetaReductionStrategy.CallByName,
		generateNewVariableName,
		maxDepth
	};

	// First, evaluate this.callee; if it does not evaluate to a LCLambdaExpression,
	// then return.
	const evaluatedCallee = this.callee.etaReduce().deltaReduce().betaReduce(options);

	if (!isLCLambdaExpression(evaluatedCallee)) {
		const result = new LCFunctionCall(
			evaluatedCallee,
			// Note: Simply using 'this.arg' as the second argument fails.
			this.arg.deltaReduce().betaReduce(options)
		);

		return result;
	}

	// case cbn e1 of
	// Lam (x, e) => cbn (subst e2 (Lam(x, e)))
	// x := evaluatedCallee.arg
	// e := evaluatedCallee.body

	// Next, substitute this.arg in for the arg in the evaluated callee.

	return this.betaReduceCore(evaluatedCallee, this.arg, generateNewVariableName)
		.deltaReduce()
		.betaReduce(options);
} */

static LC_EXPR * betaReduceFunctionCall_NormalOrder(LC_EXPR * expr, int maxDepth) {
	/* normal - leftmost outermost; the most popular reduction strategy */

	if (maxDepth <= 0) {
		return expr;
	}

	/* First, evaluate this.callee; if it does not evaluate
	to a LCLambdaExpression, then return. */
	/* TODO? : Should we replace expr->expr with etaReduce(expr->expr) here? */
	LC_EXPR * evaluatedCallee = betaReduce(expr->expr, maxDepth, brsNormalOrder);

	if (evaluatedCallee->type != lcExpressionType_LambdaExpr) {
		/* The result is App(e1’’, nor e2),
		where e1’’ = nor e1’ = ...
		and e1’ = nor e1 = evaluatedCallee
		and e1 = this.callee */

		return createFunctionCall(
			betaReduce(evaluatedCallee, maxDepth, brsNormalOrder),
			/* Note: Simply using 'this.arg' (i.e. expr->expr2) as
			the second argument fails. */
			betaReduce(expr->expr2, maxDepth, brsNormalOrder)
		);
	}

	/* Next, substitute this.arg (expr->expr2) in for the argument
	in the evaluated callee. */

	return betaReduce(
		betaReduceCore(evaluatedCallee, expr->expr2),
		maxDepth,
		brsNormalOrder
	);
}

/* static LC_EXPR * betaReduceFunctionCall_CallByValue(LC_EXPR * expr, int maxDepth) {

	if (maxDepth <= 0) {
		return this;
		// throw new Error('call.ts : betaReduceCallByValue() : maxDepth <= 0');
	}

	const options = {
		strategy: BetaReductionStrategy.CallByValue,
		generateNewVariableName,
		maxDepth
	};

	// First, evaluate this.callee; if it does not evaluate to a LCLambdaExpression,
	// then return.
	const evaluatedCallee = this.callee.deltaReduce().betaReduce(options);
	const evaluatedArg = this.arg.deltaReduce().betaReduce(options);

	if (!isLCLambdaExpression(evaluatedCallee)) {
		return new LCFunctionCall(evaluatedCallee, evaluatedArg);
	}

	// case cbv e1 of
	// Lam (x, e) => cbv (subst (cbv e2) (Lam(x, e)))
	// x := evaluatedCallee.arg
	// e := evaluatedCallee.body

	// Next, substitute evaluatedArg in for the arg in the evaluated callee.

	return this.betaReduceCore(evaluatedCallee, this.arg, generateNewVariableName)
		.deltaReduce()
		.betaReduce(options);
} */

static LC_EXPR * betaReduceFunctionCall_ThAWHackForYCombinator(LC_EXPR * expr, int maxDepth) {

	if (maxDepth <= 0) {
		return expr; // This is needed to prevent unbounded recursion.
		// throw new Error('call.ts : betaReduceThAWHackForYCombinator() : maxDepth <= 0');
	}

	/* const options = {
		strategy: BetaReductionStrategy.ThAWHackForYCombinator,
		generateNewVariableName,
		maxDepth
	}; */

	/* First, evaluate this.callee; if it does not evaluate
	to a LCLambdaExpression, then return. */
	LC_EXPR * evaluatedCallee = betaReduce(etaReduce(expr->expr), maxDepth, brsThAWHackForYCombinator);

	if (evaluatedCallee->type != lcExpressionType_LambdaExpr) {
		/* The result is App(e1’’, nor e2),
		where e1’’ = nor e1’ = ...
		and e1’ = nor e1 = evaluatedCallee
		and e1 = this.callee */

		return createFunctionCall(
			evaluatedCallee,
			/* Note: Simply using 'this.arg' (i.e. expr->expr2) as
			the second argument fails. */
			betaReduce(expr->expr2, maxDepth, brsThAWHackForYCombinator)
		);
	}

	/* Next, substitute this.arg (expr->expr2) in for the argument
	in the evaluated callee. */

	return betaReduce(
		betaReduceCore(evaluatedCallee, expr->expr2),
		maxDepth,
		brsThAWHackForYCombinator
	);
}

static LC_EXPR * betaReduce(LC_EXPR * expr, int maxDepth, BetaReductionStrategy strategy) {
	/* β-reduction (beta-reduction) : In the call (\\x.body arg), replace all
	free occurrences of x in body with arg. Rename free variables in arg where
	necessary to prevent them from becoming bound inside body. */

	/* BetaReductionStrategy strategy = brsDefault; */

	if (maxDepth <= 0) {
		return expr;
	}

	--maxDepth;

	expr = etaReduce(expr);

	switch (expr->type) {
		case lcExpressionType_Variable:
			return expr;

		case lcExpressionType_LambdaExpr:

			switch (strategy) {
				case brsCallByName:
				case brsCallByValue:
					return expr;

				default:
					return createLambdaExpr(expr->name, betaReduce(expr->expr, maxDepth, strategy));
			}

			break;

		case lcExpressionType_FunctionCall:

			switch (strategy) {
				case brsNormalOrder:
					return betaReduceFunctionCall_NormalOrder(expr, maxDepth);

				case brsThAWHackForYCombinator:
					return betaReduceFunctionCall_ThAWHackForYCombinator(expr, maxDepth);

				default:
					return NULL;
			}

			return NULL;

		default:
			break;
	}

	return NULL;
}

static LC_EXPR * etaReduce(LC_EXPR * expr) {
	/* η-reduction (eta-reduction) : Reduce λx.(f x) to f if x does not appear
	free in f. */

	switch (expr->type) {
		case lcExpressionType_Variable:
			return expr;

		case lcExpressionType_LambdaExpr:

			if (
				expr->expr->type == lcExpressionType_FunctionCall &&
				expr->expr->expr2->type == lcExpressionType_Variable &&
				!strcmp(expr->expr->expr2->name, expr->name) &&
				!containsUnboundVariableNamed(expr->expr->expr, expr->name, NULL)
			) {
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

/* BOOL areIsomorphic(LC_EXPR * expr1, LC_EXPR * expr2) {
	const int bufSize = 64;
	char buf1[bufSize];
	char buf2[bufSize];

	getDeBruijnIndex(expr1, buf1, bufSize);
	getDeBruijnIndex(expr2, buf2, bufSize);

	return strlen(buf1) > 0 && !strcmp(buf1, buf2);
} */

/*
- δ-reduction (delta-reduction) for extended Lambda calculus: the reduction of
constant arithmetic expressions; e.g. ((+ 2) 3) δ-> 5

- κ-reduction (kappa-reduction) is the reduction of the SKI combinators (?)
 */

static LC_EXPR * parseExpression(CharSource * cs) {
	char dstBuf[maxStringValueLength];
	int c = getNextChar(cs);

	if (c == EOF) {
		return NULL;
	/*} else if (c == 'λ') { */ /* error: character too large for enclosing character literal type */
	} else if (c == '\\') {

		if (getIdentifier(cs, dstBuf, maxStringValueLength) == 0) {
			return NULL;
		}

		if (!consumeStr(cs, ".")) {
			fprintf(stderr, "parseExpression() : Error consuming '.'\n");
			return NULL;
		}

		LC_EXPR * expr = parseExpression(cs);

		return createLambdaExpr(dstBuf, expr);
	} else if (c == '(') {
		LC_EXPR * expr = parseExpression(cs);
		LC_EXPR * expr2 = parseExpression(cs);

		if (!consumeStr(cs, ")")) {
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

static LC_EXPR * parse(char * str) {
	CharSource * cs = createCharSource(str);

	LC_EXPR * parseTree = parseExpression(cs);

	freeCharSource(cs);

	return parseTree;
}

static void printExpr(LC_EXPR * expr) {

	switch (expr->type) {
		case lcExpressionType_Variable:
			printf("%s", expr->name);
			break;

		case lcExpressionType_LambdaExpr:
			printf("λ%s.", expr->name);
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

static void parseAndReduceDelegate(char * str, BetaReductionStrategy strategy) {
	const int maxDepth = 50;

	printf("\nInput: '%s'\n", str);

	LC_EXPR * parseTree = parse(str);

	if (parseTree == NULL) {
		fprintf(stderr, "parse('%s') : parseExpression() returned NULL\n", str);
		return;
	}

	printf("Output: ");
	printExpr(parseTree);
	printf("\n");

	const int bufSize = 1024;
	char * buf = (char *)malloc(bufSize * sizeof(char));

	++numMallocs;
	getDeBruijnIndex(parseTree, buf, bufSize);

	printf("Expr type = %d\nDeBruijn index: %s\n", parseTree->type, buf);
	free(buf);
	++numFrees;

	LC_EXPR * reducedExpr = betaReduce(parseTree, maxDepth, strategy);

	LC_EXPR * stillInUse[] = { reducedExpr, NULL };

	printf("1) NumMemMgrRecords before GC: %d\n", getNumMemMgrRecords());
	collectGarbage(stillInUse);
	printf("2) NumMemMgrRecords after GC: %d\n", getNumMemMgrRecords());

	printf("reducedExpr: ");
	printExpr(reducedExpr);
	printf("\n");

	freeAllStructs();
	printf("3) NumMemMgrRecords final: %d\n", getNumMemMgrRecords());
}

static void parseAndReduce(char * str) {
	parseAndReduceDelegate(str, brsDefault);
}

static void parseAndReduceYCombinator(char * str) {
	parseAndReduceDelegate(str, brsThAWHackForYCombinator);
}

static void runYCombinatorTest1() {
	/* Y combinator test 1 */

	/* This test calculates 3 factorial using Church numerals
	and the Y combinator. */

	/* This Y combinator test succeeds via the CallByName strategy only... */
	/* or is it ThAWHackForYCombinator ? */

	/* const strG = 'λr.λn.if (= n 0) 1 (* n (r (- n 1)))'; */

	/* Rewrite strG as pure λ-calculus: */

	/* char * strTrue = "\\x.\\y.x"; */
	/* char * strFalse = "\\x.\\y.y"; */
	char * strIf = "\\b.\\x.\\y.((b x) y)";
	char * strOne = "\\f.\\x.(f x)";
	char * strThree= "\\f.\\x.(f (f (f x)))";
	/* char * strSix = "\\f.\\x.(f (f (f (f (f (f x))))))"; */
	char * strMult = "\\m.\\n.\\f.(m (n f))";
	char * strPredecessor = "\\n.\\f.\\x.(((n \\g.\\h.(h (g f))) \\u.x) \\u.u)";

	/* sprintf(strIsZero, "\\n.((n \\x.%s) %s)", strFalse, strTrue); */
	char * strIsZero = "\\n.((n \\z.\\x.\\y.y) \\x.\\y.x)";

	/* const strG = `λr.λn.(((${strIf} (${strIsZero} n)) ${strOne}) ((${strMult} n) (r (${strPredecessor} n))))`; */
	char * strG = (char *)malloc(512 * sizeof(char));

	++numMallocs;
	memset(strG, 0, 512 * sizeof(char));
	sprintf(strG, "\\r.\\n.(((%s (%s n)) %s) ((%s n) (r (%s n))))", strIf, strIsZero, strOne, strMult, strPredecessor);

	printf("strG is: %s\n", strG);
	printf("strlen(strG) is: %lu\n", strlen(strG)); /* -> 150 */

	/* const strYCombinator = 'λa.(λb.(a (b b)) λb.(a (b b)))'; */
	char * strYCombinator = "\\a.(\\b.(a (b b)) \\b.(a (b b)))";

	/* const expr = `((${strYCombinator} ${strG}) ${strThree})`; */
	char * expr = (char *)malloc(512 * sizeof(char));

	++numMallocs;
	memset(expr, 0, 512 * sizeof(char));
	sprintf(expr, "((%s %s) %s)", strYCombinator, strG, strThree);

	printf("expr is: %s\n", expr);
	printf("strlen(expr) is: %lu\n", strlen(expr)); /* -> 205 */

	parseAndReduceYCombinator(expr);
	/* Output: reducedExpr: λf.λx.(f (f (f (f (f (f x)))))) == 6 */
	/* The test passes! */

	free(expr);
	++numFrees;
	free(strG);
	++numFrees;
}

static void runTests() {
	printf("\nRunning tests...\n");

	/* initMemoryManagers(); */

	parseAndReduce("x");
	parseAndReduce("\\x.x");
	parseAndReduce("(x y)");

	parseAndReduce("\\x.\\y.x");
	parseAndReduce("\\x.\\y.y");

	/* Eta-reduction test: */
	parseAndReduce("\\f.\\x.(f x)"); /* -> \\f.f : Succeeds */
	parseAndReduce("\\x.(f x)"); /* -> f : Succeeds */

	/* LambdaCalculus beta-reduction test 1 from thaw-grammar */
	parseAndReduce("(\\x.x y)"); /* -> y : Succeeds */

	/* LambdaCalculus beta-reduction test 2 */
	parseAndReduce("(\\f.\\x.x g)"); /* -> \\x.x : Succeeds */

	/* LambdaCalculus beta-reduction test 3 */
	parseAndReduce("((\\f.\\x.x g) h)"); /* -> h : Succeeds */

	/* LambdaCalculus Church Numerals Successor Test 1 */
	/* const strSucc = 'λn.λf.λx.(f ((n f) x))'; The successor function */
	/* const strZero = 'λf.λx.x'; */
	/* Expected result: const strOne = 'λf.λx.(f x)'; */
	parseAndReduce("(\\n.\\f.\\x.(f ((n f) x)) \\f.\\x.x)"); /* succ(0) = 1 : Succeeds */
	parseAndReduce("(\\n.\\f.\\x.(f ((n f) x)) \\f.\\x.(f x))"); /* succ(1) = 2 : Succeeds */

	/* LambdaCalculus Church Numerals Predecessor Test 1 */
	/* const strPred = 'λn.λf.λx.(((n λg.λh.(h (g f))) λu.x) λu.u)'; */
	/* const strOne = 'λf.λx.(f x)'; */
	/* const strTwo = 'λf.λx.(f (f x))'; */
	/* const strThree = 'λf.λx.(f (f (f x)))'; */
	parseAndReduce("(\\n.\\f.\\x.(((n \\g.\\h.(h (g f))) \\u.x) \\u.u) \\f.\\x.(f x))"); /* pred(1) = 0 : Succeeds */
	parseAndReduce("(\\n.\\f.\\x.(((n \\g.\\h.(h (g f))) \\u.x) \\u.u) \\f.\\x.(f (f x)))"); /* pred(2) = 1 : Succeeds */
	parseAndReduce("(\\n.\\f.\\x.(((n \\g.\\h.(h (g f))) \\u.x) \\u.u) \\f.\\x.(f (f (f x))))"); /* pred(3) = 2 : Succeeds */

	/* TODO: */
	/* integerToChurchNumeral Test 1 */
	/* churchNumeralToInteger Test 1 */
	/* Church Numerals And Test 1 */
	/* Church Numerals Or Test 1 */
	/* Church Numerals Addition Test 1 */
	/* Church Numerals Addition Test 2 */
	/* Church Numerals Multiplication Test 1 */
	/* Church Numerals isZero Test 1 */

	/* Y combinator test 1 */
	runYCombinatorTest1();

	/* parseAndReduce("( )"); */

	/* terminateMemoryManagers(); */
	generateMemoryManagementReport();

	printf("\nDone.\n");
}

/* **** The Main MoFo **** */

int main(int argc, char * argv[]) {
	/* TODO: Implement an REPL (a read-evaluate-print loop) */
	/* TODO: Implement the execution of a script in a file */

	BOOL enableTests = FALSE;
	BOOL enableVersion = FALSE;
	int i;

	for (i = 1; i < argc; ++i) {
		/* printf("argv[%d] = %s\n", i, argv[i]); */

		if (!strcmp(argv[i], "-t")) {
			enableTests = TRUE;
		} else if (!strcmp(argv[i], "-v")) {
			enableVersion = TRUE;
		}
	}

	if (enableVersion) {
		printf("\nFacility version 0.0.0\n");
	} else if (enableTests) {
		runTests();
	}

	return 0; /* Zero (as a Unix exit code) means success. */
}

/* **** The End **** */
