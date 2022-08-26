/* facility/src/memory-manager.h */

typedef struct MEMMGR_RECORD_STRUCT {
	LC_EXPR * expr;
	struct MEMMGR_RECORD_STRUCT * next;
} MEMMGR_RECORD;

void addItemToMemMgrRecords(LC_EXPR * item);
int getNumMemMgrRecords();
void collectGarbage(LC_EXPR * exprTreesToMark[]);
void freeAllStructs();

void printMemMgrSelfReport();

/* **** The End **** */
