/* facility/src/string-set.h */

typedef struct STRING_SET_STRUCT {
	char * str;
	struct STRING_SET_STRUCT * next;
} STRING_SET;

BOOL stringSetContains(STRING_SET * set, char * str);
STRING_SET * addStringToSet(char * str, STRING_SET * set);
STRING_SET * unionOfStringSets(STRING_SET * set1, STRING_SET * set2);
void freeStringSet(STRING_SET * set);

void printStringSetMemMgrReport();

/* **** The End **** */
