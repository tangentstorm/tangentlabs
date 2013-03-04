#include<stdio.h>

// program to challenge the assertion that
// c disallows switching on characters.

int  main() {
  char ch;
  for (ch = 'a'; ch < 'z'; ch++) {
    switch(ch) {
      case 't': printf("t[angentstorm]"); break;
      default : putchar(ch);
    }
  }
  putchar('\n');
  return 0;
}
