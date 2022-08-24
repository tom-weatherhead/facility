/* atrocity/src/char-source.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "boolean.h"

#include "char-source.h"

static int numMallocs = 0;
static int numFrees = 0;

void printCharSourceMemMgrReport() {
	printf("  Char sources: %d mallocs, %d frees", numMallocs, numFrees);

	if (numMallocs > numFrees) {
		printf(" : **** LEAKAGE ****");
	}

	printf("\n");
}

// **** CharSource functions ****

CharSource * createCharSource(char * str) {
	CharSource * cs = (CharSource *)malloc(sizeof(CharSource));

	++numMallocs;

	/* TODO? : Clone the string? */
	cs->str = str;

	cs->len = strlen(str);
	cs->i = 0;

	return cs;
}

void freeCharSource(CharSource * cs) {
	cs->str = NULL; /* Note bene: We don't call free() here */
	free(cs);
	++numFrees;
}

int getNextChar(CharSource * cs) {

	while (cs->i < cs->len) {
		const int c = (int)cs->str[cs->i];

		++cs->i;

		if (c != (int)' ') {
			return c;
		}
	}

	return EOF;
}

void rewindOneChar(CharSource * cs) {

	if (cs->i > 0) {
		--cs->i;
	}
}

static BOOL isEOF(CharSource * cs) {
	return cs->i >= cs->len;
}

static BOOL isWhiteSpace(char c) {
	return c == ' ' || c == '\t' ? TRUE : FALSE;
}

static void skipWhiteSpace(CharSource * cs) {

	while (cs->i < cs->len && isWhiteSpace(cs->str[cs->i])) {
		++cs->i;
	}
}

int getIdentifier(CharSource * cs, char * dstBuf, int dstBufSize) {
	memset(dstBuf, 0, dstBufSize);

	skipWhiteSpace(cs);

	if (isEOF(cs)) {
		return 0;
	}

	if (cs->str[cs->i] == '(' || cs->str[cs->i] == ')' || cs->str[cs->i] == '.') {
		memcpy(dstBuf, &cs->str[cs->i++], 1);
		return 1;
	}

	const int start = cs->i;

	while (cs->i < cs->len) {
		const char c = cs->str[cs->i];

		if (isWhiteSpace(c) || c == '(' || c == ')' || c == '.' /* || c == '\0' */) {
			break;
		}

		++cs->i;
	}

	const int end = cs->i;
	const int len = end - start;
	const int lenToCopy = (dstBufSize - 1 < len) ? dstBufSize - 1 : len;

	memcpy(dstBuf, &cs->str[start], lenToCopy);
	/* Or: memcpy(dstBuf, cs->str + start, lenToCopy); */

	return lenToCopy;
}

/* **** The End **** */
