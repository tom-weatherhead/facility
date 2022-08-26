/* facility/src/main.h */

LC_EXPR * createVariable(char * name);
LC_EXPR * createLambdaExpr(char * argName, LC_EXPR * body);
LC_EXPR * createFunctionCall(LC_EXPR * expr, LC_EXPR * expr2);
BOOL containsUnboundVariableNamed(LC_EXPR * expr, char * varName, STRING_SET * boundVariableNames);
LC_EXPR * substituteForUnboundVariable(LC_EXPR * expr, char * varName, LC_EXPR * replacementExpr);
LC_EXPR * etaReduce(LC_EXPR * expr);

/* **** The End **** */
