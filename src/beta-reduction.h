/* facility/src/beta-reduction.h */

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

LC_EXPR * betaReduce(LC_EXPR * expr, int maxDepth, BetaReductionStrategy strategy);

/* **** The End **** */
