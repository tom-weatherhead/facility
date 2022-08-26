/* facility/src/eta-reduction.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
/* #include <ctype.h> */
/* #include <assert.h> */

#include "boolean.h"

#include "types.h"

#include "string-set.h"
#include "main.h"

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

LC_EXPR * etaReduce(LC_EXPR * expr) {
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

/* **** The End **** */
