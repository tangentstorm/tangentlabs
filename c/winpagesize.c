// http://en.wikipedia.org/wiki/Page_(computer_memory)
#include <stdio.h>
#include <windows.h>
 
int main(void) {
  SYSTEM_INFO si;
  GetSystemInfo(&si);
 
  printf("The page size for this system is %u bytes.\n", si.dwPageSize);
 
  return 0;
}
