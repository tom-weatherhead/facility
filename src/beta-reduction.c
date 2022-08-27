/* facility/src/beta-reduction.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
/* #include <ctype.h> */
/* #include <assert.h> */

#include "boolean.h"

#include "types.h"

#include "beta-reduction.h"
#include "string-set.h"
#include "eta-reduction.h"
#include "create-and-destroy.h"

static int generatedVariableNumber = 0;

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

LC_EXPR * betaReduce(LC_EXPR * expr, int maxDepth, BetaReductionStrategy strategy) {
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

/* **** The End **** */
