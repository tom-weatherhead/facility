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
#include "create-and-destroy.h"

#include "beta-reduction.h"
#include "char-source.h"
#include "de-bruijn.h"
#include "string-set.h"
#include "memory-manager.h"

static int numMallocs = 0;
static int numFrees = 0;

// **** Memory manager functions ****

void generateMemoryManagementReport() {
	printf("\nMemory management report:\n");
	printf("  Main: %d mallocs, %d frees", numMallocs, numFrees);

	if (numMallocs > numFrees) {
		printf(" : **** LEAKAGE ****");
	}

	printf("\n");
	printMemMgrSelfReport();
	printCreateAndDestroyMemMgrReport();
	printCharSourceMemMgrReport();
	printStringSetMemMgrReport();
	printStringListMemMgrReport();
}

/* Domain Object Model functions */

/* Types of graph reduction: alpha-conversion, beta, eta, ...
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

void execScriptInFile(char * filename) {
	printf("\nTODO: Execute the script in the file '%s'\n", filename);
}

void readEvalPrintLoop() {
	printf("\nTODO: Implement readEvalPrintLoop()\n");
}

/* **** The Main MoFo **** */

int main(int argc, char * argv[]) {
	/* TODO: Implement an REPL (a read-evaluate-print loop) */
	/* TODO: Implement the execution of a script in a file */

	BOOL enableTests = FALSE;
	BOOL enableVersion = FALSE;
	char * filename = NULL;
	int i;

	for (i = 1; i < argc; ++i) {
		/* printf("argv[%d] = %s\n", i, argv[i]); */

		if (!strcmp(argv[i], "-t")) {
			enableTests = TRUE;
		} else if (!strcmp(argv[i], "-v")) {
			enableVersion = TRUE;
		} else if (filename == NULL && argv[i][0] != '-') {
			filename = argv[i];
		}
	}

	if (enableVersion) {
		printf("\nFacility version 0.0.0\n");
	} else if (enableTests) {
		runTests();
	} else if (filename != NULL) {
		execScriptInFile(filename);
	} else {
		readEvalPrintLoop();
	}

	return 0; /* Zero (as a Unix exit code) means success. */
}

/* **** The End **** */
