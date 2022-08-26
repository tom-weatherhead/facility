/* facility/src/eta-reduction.h */

BOOL containsUnboundVariableNamed(LC_EXPR * expr, char * varName, STRING_SET * boundVariableNames);
LC_EXPR * etaReduce(LC_EXPR * expr);

/* **** The End **** */
