

int main() {

  // If you're using a compound statement whose second
  // part can either be a block ( { } ) or a single statement,
  // and you only want to use the single statement, then 
  // consider putting the entire compound statement on one line.

  // In my experience, this leads to fewer mistakes.

  // EXAMPLE: suppose you have:
  while (condition)
    consequence();    // :(

  // later, while debugging, you want to add some debug code.
  // it's easy to overlook the missing { }
  while (condition)
    printSomething();
    consequence();  // no longer in the loop!! :(

  // instead, EITHER write it like this:
  while (condition) consequence();   // much harder to fool yourself now
  
  // OR, just always include the braces.
  while (condition) {
    consequence();
  }

  return 0;
}
