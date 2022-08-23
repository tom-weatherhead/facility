/* facility/src/main.c */

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

#include "types.h"

#include "char-source.h"
#include "de-bruijn.h"
#include "string-set.h"

/*
toString
* equals
X applySubstitution is only needed if unify() is implemented
* containsVariableNamed
* containsBoundVariableNamed
* containsUnboundVariableNamed
* substituteForUnboundVariable
* getSetOfAllVariableNames
* renameBoundVariable -> α-conversion
* isBetaReducible
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

// **** Create and Free functions ****

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

LC_EXPR * betaReduce(LC_EXPR * expr) {

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
			return expr;

		case lcExpressionType_LambdaExpr:
			/*
			if (
				isLCFunctionCall(this.body) &&
				isLCVariable(this.body.arg) &&
				this.body.arg.name === this.arg.name &&
				!this.body.callee.containsUnboundVariableNamed(this.arg.name, createSet<string>())
			) {
				return this.body.callee.etaReduce();
			}

			return this;
			*/
			return NULL;

		case lcExpressionType_FunctionCall:
			return createFunctionCall(etaReduce(expr->expr), etaReduce(expr->expr2));

		default:
			break;
	}

	return NULL;
}

BOOL isIsomorphicTo(LC_EXPR * expr) {

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

	return FALSE;
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
		printDeBruijnIndex(parseTree);
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
