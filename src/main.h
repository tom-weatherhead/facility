/* facility/src/main.h */

LC_EXPR * createVariable(char * name);
LC_EXPR * createLambdaExpr(char * argName, LC_EXPR * body);
LC_EXPR * createFunctionCall(LC_EXPR * expr, LC_EXPR * expr2);

/* **** The End **** */
