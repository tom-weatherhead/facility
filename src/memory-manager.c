/* facility/src/memory-manager.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
/* #include <ctype.h> */
/* #include <assert.h> */

#include "boolean.h"

#include "types.h"
#include "memory-manager.h"

void incNumFreesInCreateAndDestroy();

static int numMallocs = 0;
static int numFrees = 0;

void printMemMgrSelfReport() {
	printf("  Memory manager itself: %d mallocs, %d frees", numMallocs, numFrees);

	if (numMallocs > numFrees) {
		printf(" : **** LEAKAGE ****");
	}

	printf("\n");
}

/* **** BEGIN Memory manager version 1 **** */

MEMMGR_RECORD * memmgrRecords = NULL;

void addItemToMemMgrRecords(LC_EXPR * item) {
	MEMMGR_RECORD * mmRec = (MEMMGR_RECORD *)malloc(sizeof(MEMMGR_RECORD));

	++numMallocs;
	mmRec->expr = item;
	mmRec->next = memmgrRecords;
	memmgrRecords = mmRec;
}

int getNumMemMgrRecords() {
	int n = 0;
	MEMMGR_RECORD * mmRec = memmgrRecords;

	while (mmRec != NULL) {
		++n;
		mmRec = mmRec->next;
	}

	return n;
}

void clearMarks() {
	MEMMGR_RECORD * mmRec;

	for (mmRec = memmgrRecords; mmRec != NULL; mmRec = mmRec->next) {
		mmRec->expr->mark = 0;
	}
}

void setMarksInExprTree(LC_EXPR * expr) {
	/* Do this recursively */
	expr->mark = 1;

	if (expr->expr != NULL) {
		setMarksInExprTree(expr->expr);
	}

	if (expr->expr2 != NULL) {
		setMarksInExprTree(expr->expr2);
	}
}

void freeUnmarkedStructs() {
	MEMMGR_RECORD ** ppmmRec = &memmgrRecords;
	MEMMGR_RECORD * mmRec = *ppmmRec;

	while (mmRec != NULL) {

		if (mmRec->expr->mark == 0) {
			/* Free mmRec->expr. Do not free recursively. */
			mmRec->expr->expr = NULL;
			mmRec->expr->expr2 = NULL;
			free(mmRec->expr);
			/* ++numFrees; */
			incNumFreesInCreateAndDestroy();
			mmRec->expr = NULL;

			/* Then free mmRec, preserving the integrity of the linked list */
			MEMMGR_RECORD * nextmmRec = mmRec->next;

			mmRec->expr = NULL;
			mmRec->next = NULL;
			free(mmRec);
			++numFrees;
			*ppmmRec = nextmmRec;
		} else {
			ppmmRec = &mmRec->next;
		}

		mmRec = *ppmmRec;
	}
}

void collectGarbage(LC_EXPR * exprTreesToMark[]) {
	int i;

	clearMarks();

	for (i = 0; exprTreesToMark[i] != NULL; ++i) {
		setMarksInExprTree(exprTreesToMark[i]);
	}

	freeUnmarkedStructs();
}

void freeAllStructs() {
	clearMarks();
	freeUnmarkedStructs();
}

/* **** END Memory manager version 1 **** */

/* **** BEGIN Memory manager version 2 (TODO) **** */

/*
typedef struct MEMMGR_RECORD_STRUCT {
	void * ptr;
	struct MEMMGR_RECORD_STRUCT * next;
} MEMMGR_RECORD;

typedef struct {
	void (*mark)(void * ptr);
	void (*unmark)(void * ptr);
	BOOL (*isMarked)(void * ptr);
	/ * MEMMGR_RECORD * memmgrRecords; * /
} MEMMGR;

void markExpr(void * ptr) {
	((LC_EXPR *)ptr)->mark = 1;
}

void unmarkExpr(void * ptr) {
	((LC_EXPR *)ptr)->mark = 0;
}

BOOL isExprMarked(void * ptr) {
	return ((LC_EXPR *)ptr)->mark != 0;
}

MEMMGR * createMemoryManager(void (*mark)(void * ptr), void (*unmark)(void * ptr), BOOL (*isMarked)(void * ptr)) {
	MEMMGR * mm = (MEMMGR *)malloc(sizeof(MEMMGR));

	++numMallocs;
	mm->mark = mark;
	mm->unmark = unmark;
	mm->isMarked = isMarked;
	/ * mm->memmgrRecords = NULL; * /

	return mm;
}

MEMMGR * exprMemMgr = NULL;
MEMMGR * stringListMemMgr = NULL;
MEMMGR * stringSetMemMgr = NULL;

void initMemoryManagers() {
	exprMemMgr = createMemoryManager(markExpr, unmarkExpr, isExprMarked);
	/ * stringListMemMgr = createMemoryManager(...);
	stringSetMemMgr = createMemoryManager(...); * /
}

void terminateMemoryManagers() {

	if (exprMemMgr != NULL) {
		free(exprMemMgr);
		exprMemMgr = NULL;
		++numFrees;
	}

	generateMemoryManagementReport();
}
*/

/* **** END Memory manager version 2 (TODO) **** */

/* **** The End **** */
