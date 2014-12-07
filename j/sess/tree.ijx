(0212.2014)
18:45:55 ischtche ) trepl =: 1 : '[ ^: (u -: ]) L: (_,L.u)'
18:45:55 jconn ischtche: |ok
18:46:38 ischtche ) (<'d';'d') (5 trepl) <L:0;/'abc'
18:46:38 jconn ischtche: +---+---+---+
18:46:39 jconn ischtche: |+-+|+-+|+-+|
18:46:39 jconn ischtche: ||a|||b|||c||
18:46:39 jconn ischtche: |+-+|+-+|+-+|
18:46:39 jconn ischtche: +---+---+---+
18:46:57 ischtche ) (<'d';'d') ((<'b') trepl) <L:0;/'abc'
18:46:58 jconn ischtche: +---+-------+---+
18:46:58 jconn ischtche: |+-+|+-----+|+-+|
18:46:58 jconn ischtche: ||a|||+-+-+|||c||
18:46:58 jconn ischtche: |+-+|||d|d|||+-+|
18:46:58 jconn ischtche: |   ||+-+-+||   |
18:46:58 jconn ischtche: ...




NB. given the following tree, how to replace 3 with 33 ?
NB.
NB.    1;2;<3;4
NB.
NB. ┌─┬─┬─────┐
NB. │1│2│┌─┬─┐│
NB. │ │ ││3│4││
NB. │ │ │└─┴─┘│
NB. └─┴─┴─────┘

t =: 1;2;<3;4
{:: t
┌─┬─┬─────┐
│1│2│┌─┬─┐│
│ │ ││3│4││
│ │ │└─┴─┘│
└─┴─┴─────┘

 NB. [(S: 0) a   -> spread identity function over the leaves of a
leaves =: [S:0


NB. {:: a       ->
NB. f (S: n) a  -> apply f to items of n at level a
NB. create a function that


NB. new (paths) } arr ->  replaces items in array

NB. ------------
NB. start with a nested structure:


NB. use *y (signum) with   @. (agenda) to select from the agenda

NB. how agenda works:
NB. double or half, depending on whether it's  odd or even:

   dorh =. (+:  -:  @. (2:|])
   dorh i.10
0 0.5 4 1.5 8 2.5 12 3.5 16 4.5


   NB. So now let's select based on whether an array is empty nor not:
   ('cat'"0`2:)@. (*@#)


   n =: [: < 'n'"_      NB. tag indicating 'nothing'
   j =: [: < 'j'"_ ; ]  NB. tag indicating 'just y'

   (n;j) 1
┌───┬─────┐
│┌─┐│┌─┬─┐│
││n│││j│1││
│└─┘│└─┴─┘│
└───┴─────┘


NB. Constant functions
NB. ------------------

  _5: 1 2 3 4           NB. apply constant function to entire list.
_5

  3:"0 ] 1 2 3 4        NB. apply to each item of the list
3 3 3 3

  1 2 3 (4:) 5 6        NB. dyadic example
4

   (0:, 9:) 1           NB. two different constant functions applied to same argument.
0 9



NB. Empty arrays.
NB. -------------

   a:                   NB. a: ('Ace') is a boxed empty array.
┌┐
││
└┘
   >a:                  NB. Unbox the ace to get an empty array. (It's invisible.)

   i.0                  NB. An empty array of integers.

   ''                   NB. An empty array of characters.

   $ 123                NB. Since a scalar has 0 dimensions, its shape is an empty array.

   0 $ 123              NB. We can also reshape anything to length 0 and get an empty array.


NB. Detecting empty arrays.
NB. -----------------------

   em =: $ 0            NB. define a variable called 'em' holding an empty value.

   a: = em              NB. We can't check for equality directly, because
                        NB. the '=' verb is applied to 0 pairs of items,
                        NB. producing an empty array of results.

   a: = <em             NB. We *can* compare using '=' if we box the value first.
1


NB. higher dimensional empty arrays
NB. -------------------------------

   ] y0 =: ] i. 0       NB. An empty array of scalars. -> []

   ] y1 =: ] i. 0 1     NB. An empty array of arrays scalars. -> []

   ] x =: 'x'           NB. An arbitrary scalar. -> x
x
   x , i. 0             NB. Appending a scalar to an empty array.  -> [x]
x

   i. 0 1               NB. An empty array of 1-dimensional arrays. -> []
   x , i. 0 1           NB. An array of one scalar.
x

   'x' , i.0            NB.
x

   'x', i. 0 2 2
xx
xx


NB. Other ways to detect empty arrays:
NB. ----------------------------------

   boxes =: (i.0) ; (i.1) ; (i. 0 0) ; (i.0 1) ; (i. 1 0) ; (i. 1 1)

   a: = boxes           NB. This is the simplest test. (Again, only for boxed items.)
1 0 0 0 0 0

   (a:&=) cases         NB. This is the simplest test.
1 0 0 0 0 0

   $ em                 NB. It's a 1-dimensional array with 0 items, so its shape is 0.
0
                        NB. But $ doesn't always return a scalar, so it's not a great test.
   ($ i.0) ; ($ i.5) ; ($ i.5 5)
┌─┬─┬───┐
│0│5│5 5│
└─┴─┴───┘
                        NB. But $ doesn't always return a scalar, so it's not a great test.
   ($ i.0) ; ($ i.5) ; ($ i.5 5)
┌─┬─┬───┐
│0│5│5 5│
└─┴─┴───┘
                        NB. `#` al
   (# i.0) ; (# i.5) ; (# i.5 5)
┌─┬─┬─┐
│0│5│5│
└─┴─┴─┘

   # em                 NB. '#' (tally) reports 0 items along its first axis.
0

   **# em               NB. '#' (tally) reports 0 items along its first axis.


   a: = ((i.0) ; (i.1) ; (i. 0 0) ; (i.0 1) ; (i. 1 0) ; (i. 1 1))


NB. So here's how we'll do it:

   empty =: (a: = <)   NB. monadic fork:  (a:) = 9<y)
   empty i.0
1
   empty i.1
0
   empty >a:
1

NB. selecting a function based on a predicate
NB. -----------------------------------------
NB. Now we will show how to select a function based on whether the argument
NB. is empty or not.

   ] g =. _9:  9:       NB. a 'gerund' - an array of boxed verbs
┌───┬──┐
│_9:│9:│
└───┴──┘
   g @. 0               NB. 'Agenda' (@.) selects a verb from gerund by index.
_9:
   g @. 1               NB. With two items (indices 0 and 1), 'agenda' acts like 'if'.
9:
   g @. empty i. 1
_9
   g @. empty i. 0      NB. Agenda uses the verb on the right to select from the gerund.
9
   (g @. empty) i. 0    NB. It associates like this. Notice the result is 9, a scalar.
9
   g @. (empty i. 0)    NB. It's NOT doing this. The result here is 9:, a constant function.
9:


NB. head and behead
NB. ---------------
   {. 'xxs'             NB. head.
x
   }. 'xxs'             NB. behead.
xs


NB. explicit verbs
NB. --------------

   (3 : 'y') 'arg'      NB. (3 : 'y') creates a monadic verb that returns its argument (y).
arg
   (3 : '{. y') 'arg'   NB. head.
a
   (3 : '}. y') 'arg'   NB. behead.
rg


NB. back to the goal
NB. -----------------------------------
NB. We need a triadic function:
NB.
NB.    (path ; value) ammend tree
NB.
NB. we need to walk the tree


   ] tree =: a;<b;<c;d [ 'a b c d' =: 'ab_d'
┌─┬─────────┐
│a│┌─┬─────┐│
│ ││b│┌─┬─┐││
│ ││ ││_│d│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘

NB. goal: replace the _ in the structure above with a c.


NB. {:: ('Map') -> paths to each leaf item:

   {:: tree
┌───┬─────────────────────────┐
│┌─┐│┌─────┬─────────────────┐│
││0│││┌─┬─┐│┌───────┬───────┐││
│└─┘│││1│0│││┌─┬─┬─┐│┌─┬─┬─┐│││
│   ││└─┴─┘│││1│1│0│││1│1│1││││
│   ││     ││└─┴─┴─┘│└─┴─┴─┘│││
│   ││     │└───────┴───────┘││
│   │└─────┴─────────────────┘│
└───┴─────────────────────────┘

NB. L: 0 ('leaf') adv. -> apply a verb to each leaf.

   (< L: 0) tree
┌───┬───────────────┐
│┌─┐│┌───┬─────────┐│
││a│││┌─┐│┌───┬───┐││
│└─┘│││b│││┌─┐│┌─┐│││
│   ││└─┘│││_│││d││││
│   ││   ││└─┘│└─┘│││
│   ││   │└───┴───┘││
│   │└───┴─────────┘│
└───┴───────────────┘

NB. S: ('spread') adv. : works like L: but returns a list.

   (< S: 0) tree
┌─┬─┬─┬─┐
│a│b│_│d│
└─┴─┴─┴─┘

NB. So let's use spread to fetch the paths:


   {:: tree                     NB. we saw this earlier.
┌───┬─────────────────────────┐
│┌─┐│┌─────┬─────────────────┐│
││0│││┌─┬─┐│┌───────┬───────┐││
│└─┘│││1│0│││┌─┬─┬─┐│┌─┬─┬─┐│││
│   ││└─┴─┘│││1│1│0│││1│1│1││││
│   ││     ││└─┴─┴─┘│└─┴─┴─┘│││
│   ││     │└───────┴───────┘││
│   │└─────┴─────────────────┘│
└───┴─────────────────────────┘

   (< S: 0) {:: tree          NB. This boxes each /leaf/ of the path,
┌─┬─┬─┬─┬─┬─┬─┬─┬─┐           NB. but this isn't actually what we want.
│0│1│0│1│1│0│1│1│1│
└─┴─┴─┴─┴─┴─┴─┴─┴─┘

   (< S: 1) {:: tree          NB. Much better.
┌───┬─────┬───────┬───────┐   NB. L: and S: both take a numeric rank argument.
│┌─┐│┌─┬─┐│┌─┬─┬─┐│┌─┬─┬─┐│   NB. 0 matches leaves. 1 matches the next level up.
││0│││1│0│││1│1│0│││1│1│1││
│└─┘│└─┴─┘│└─┴─┴─┘│└─┴─┴─┘│
└───┴─────┴───────┴───────┘


NB. we can use ,: (laminate) to make a table:

   ( (< S: 0) ,: ((< S: 1) @ {::) ) tree
┌───┬─────┬───────┬───────┐
│a  │b    │_      │d      │
├───┼─────┼───────┼───────┤
│┌─┐│┌─┬─┐│┌─┬─┬─┐│┌─┬─┬─┐│
││0│││1│0│││1│1│0│││1│1│1││
│└─┘│└─┴─┘│└─┴─┴─┘│└─┴─┴─┘│
└───┴─────┴───────┴───────┘

NB. We can apply (> L: 1) to unbox the items.

   (> L: 1) ( (< S: 0) ,: ((< S: 1) @ {::) ) tree
┌─┬─┬─┬─┐
│a│b│_│d│
├─┼─┼─┼─┤
│0│1│1│1│
│ │0│1│1│
│ │ │0│1│
└─┴─┴─┴─┘

NB. Or we can use the train ',/ @ >' to reshape the lists:
NB. this is just the composition of ',/' with unboxing.

   (,/ @ > L: 1) ( (< S: 0) ,: ((< S: 1) @ {::) ) tree
┌─┬───┬─────┬─────┐
│a│b  │_    │d    │
├─┼───┼─────┼─────┤
│0│1 0│1 1 0│1 1 1│
└─┴───┴─────┴─────┘


NB. let's simplify that:

   values =: (< S: 0)
   ] values tree
┌─┬─┬─┬─┐
│a│b│_│d│
└─┴─┴─┴─┘

   ([: < ;/ @ >)  S: 1 {:: tree
┌─┬───┬─────┬─────┐
│0│1 0│1 1 0│1 1 1│
└─┴───┴─────┴─────┘

NB. That's two verbs: '{::' and everything to the left.
NB. We can use either (f @ g) or ([: f g) to extract the function.

   paths =: ([: < ;/ @ >) S: 1   @   {::
   ] paths tree
┌─┬───┬─────┬─────┐
│0│1 0│1 1 0│1 1 1│
└─┴───┴─────┴─────┘

   (values ,: paths) tree
┌─┬───┬─────┬─────┐
│a│b  │_    │d    │
├─┼───┼─────┼─────┤
│0│1 0│1 1 0│1 1 1│
└─┴───┴─────┴─────┘

   |: (values ,: paths) tree
┌─┬─────┐
│a│0    │
├─┼─────┤
│b│1 0  │
├─┼─────┤
│_│1 1 0│
├─┼─────┤
│d│1 1 1│
└─┴─────┘

NB. okay so anyway. for each item

NB. ------------------------------------------------------------------------
NB. -- apply the update function to the indices, not the original tree!  ---
NB. ------------------------------------------------------------------------

NB. 1. We can use (f L: 0) to apply a function to all leaves.

   (5: L: 0) tree
┌─┬─────────┐
│5│┌─┬─────┐│
│ ││5│┌─┬─┐││
│ ││ ││5│5│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘

NB. 2. We can use (f L: 1) @ {:: to apply a function to all paths.

   (4: L: 1) {:: tree
┌─┬─────────┐
│4│┌─┬─────┐│
│ ││4│┌─┬─┐││
│ ││ ││4│4│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘


NB. we can create an adverb to do this:

   update =: (1 : '(u L: 1) {:: y')
   2: update tree
┌─┬─────────┐
│2│┌─┬─────┐│
│ ││2│┌─┬─┐││
│ ││ ││2│2│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘



NB. Find the underscore:

   ((= & '_')  L: 0) tree
┌─┬─────────┐
│0│┌─┬─────┐│
│ ││0│┌─┬─┐││
│ ││ ││1│0│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘

NB. Change the underscore to a constant:

   (([ ` 0:) @. (= & '_')  L: 0) tree
┌─┬─────────┐
│a│┌─┬─────┐│
│ ││b│┌─┬─┐││
│ ││ ││0│d│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘

NB. Change the underscore to the specific constant we want:

   (([ ` ('c'"_)) @. (= & '_')  L: 0) tree
┌─┬─────────┐
│a│┌─┬─────┐│
│ ││b│┌─┬─┐││
│ ││ ││c│d│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘


NB. Here's how we can match the path instead of the value:

   (( 1 1 0 )&( 4 : '(<x) = <,/>y') L: 1 ) {:: tree
┌─┬─────────┐
│0│┌─┬─────┐│
│ ││0│┌─┬─┐││
│ ││ ││1│0│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘

NB. and with constant functions
   (( (2:`4:) @.(( 1 1 0 )&( 4 : '(<x) = <,/>y'))) L: 1 ) {:: tree
┌─┬─────────┐
│2│┌─┬─────┐│
│ ││2│┌─┬─┐││
│ ││ ││4│2│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘

NB. And then with a constant 'c' function:

      (( (2:`('c'"_)) @.(( 1 1 0 )&( 4 : '(<x) = <,/>y'))) L: 1 ) {:: tree
┌─┬─────────┐
│2│┌─┬─────┐│
│ ││2│┌─┬─┐││
│ ││ ││c│2│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘


NB. And then, finally, by selecting the original value with {:: & tree for
NB. the non-matching path.

   (( (({:: & tree)`('c'"_)) @.(( 1 1 0 )&( 4 : '(<x) = <,/>y'))) L: 1 ) {:: tree
┌─┬─────────┐
│a│┌─┬─────┐│
│ ││b│┌─┬─┐││
│ ││ ││c│d│││
│ ││ │└─┴─┘││
│ │└─┴─────┘│
└─┴─────────┘




NB. (TODO) Alternate solution: recursion with $: ('Self Reference')
NB. ---------------------------------------------------------------
NB. According to the docs,  $: denotes the longest verb that contains it.
NB.
NB. I originally thought I'd be required to use this, but it turned out
NB. not to be necesssary.

