/* atrocity/src/char-source.h */

typedef struct {
	char * str;
	int len;
	int i;
} CharSource;

CharSource * createCharSource(char * str);
void freeCharSource(CharSource * cs);
int getNextChar(CharSource * cs);
void rewindOneChar(CharSource * cs);
int getIdentifier(CharSource * cs, char * dstBuf, int dstBufSize);

/* **** The End **** */
