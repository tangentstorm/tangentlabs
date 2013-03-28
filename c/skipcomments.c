/**
 * Example of a recursive descent parser that skips C-style comments.
 * Completely un-tested. Use at your own risk, etc, etc.
 * This code is in the public domain. 
 */

typedef enum { PLUS, MINUS, TIMES, DIV, MOD, SLCMT, MLCMT, END_OF_TEXT } token;
typedef enum { false, true } bool;

// global compiler state:
char *str;  // populate this with the input
int stroff; // offset into the input string

char ch;
int curLine = 0;
bool complete = false;

// call this to set up the system:
void init()
{
   load_the_input_from_somewhere(str); // TODO, obviously
   nextChar();
}

const char EOT = 4; // ^D , the ascii end of text character

char nextChar()
{
  ch = (strPtr < strlen(str)) ? str[strOff++] : EOT;
  if (ch == '\n') curLine++;
  if (ch == EOT && !complete) { 
     printf("unexpected end of input on line %0", curLine);
     exit(-1);
  }
  return ch;
}

token nextToken()
{
  switch (nextChar())
  {
     case EOT : return END_OF_TEXT;
     case '+' : return PLUS;
     case '-' : return MINUS;
     case '*' : return TIMES;
     case '/' :
	switch (nextChar()) 
	{
	   case '/' : skipSLComment(); return SLCMT;
	   case '*' : skipMLComment(); return MLCMT;
	   default  : return DIV; // I think PL/0 actually uses DIV and MOD, but whatever. :)
	}
     default : 
	// TODO: handle other tokens, obviously
  }
}


void skipSLComment()
{
   while ch != '\n' do nextChar();
}

void skipMLComment()
{
   bool done = false;
   while (!done)
   {
      while ch != '*' do nextChar();
      done = ch == '/';
   }
}
