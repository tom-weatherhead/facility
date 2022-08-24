/* facility/src/types.h */

/* Preprocessor defines */

/* const int maxStringValueLength = 8; */
#define maxStringValueLength 8

/* Forward declarations of some structs */

typedef struct LC_EXPR_STRUCT {
	int mark; /* For use by a mark-and-sweep garbage collector */
	int type;
	char name[maxStringValueLength]; /* Used for Variable and LambdaExpr */
	struct LC_EXPR_STRUCT * expr; /* Used for LambdaExpr and FunctionCall */
	struct LC_EXPR_STRUCT * expr2; /* Used for FunctionCall */
} LC_EXPR; /* A Lambda calculus expression */

/* Enums */

enum {
	lcExpressionType_Variable,
	lcExpressionType_LambdaExpr,
	lcExpressionType_FunctionCall
};

/* **** The End **** */
