// program to demonstrate how argc works.

#include<stdio.h>

int main (int argc, char *argv[]) {
  int i=0;
  printf("%i arguments given\n", argc);
  for (i=0; i<argc; i++) printf("arg %i: %s\n", i, argv[i]);
}
