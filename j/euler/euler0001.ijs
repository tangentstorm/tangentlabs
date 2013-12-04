NB. euler problem #1:
NB.
NB.    > If we list all the natural numbers below 10 that are multiples of
NB.    > 3 or 5, we get 3, 5, 6 and 9. The sum of these multiples is 23.
NB.    >
NB.    > Find the sum of all the multiples of 3 or 5 below 1000.
NB.
NB. My initial answer:

+/ (~:#])  , (13 : 'y -.~ x * >: i.(y - x|y) % x' & 1000) S:0 ] 3 ; 5


NB. This gives the correct answer but it's more complicated than I'd like.
NB. Reading left to right, this code finds the sum ('+/') of the unique
NB. items ('~:#]') of the flattened array of elements (',' - called 'ravel' in j)
NB. of a parenthesized function (discussed below) applied to each item (S:0)
NB. of the boxed sequence (3 ';' 5).

NB. The first refactoring is easy, because there's actually a primitive that
NB. does what (~: # ]) does. You can get the unique items directly using the
NB. verb '~.', called 'nub' in j.

+/ ~. , (13 : 'y -.~ x * >: i.(y - x|y) % x' & 1000) S:0 ] 3 ; 5

NB. The long verb in the middle returns all multiples of some x less than y,
NB. where x is the left argument and y is the right argument. The '& 1000' is a
NB. partial application of the verb to right argument 1000, producing a new monad
NB. (single argument verb).

NB. Here is the verb by itself:

13 : 'y -.~ x * >: i.(y - x|y) % x'

NB. Reading left to right, '13 :' compiles the string to its right into a new
NB. verb. Since the string mentions both x and y the verb produced will be dyadic.
NB.
NB. This removes y ('y -.~', where '~' swaps the order of the arguments for '-.',
NB. which returns the array x with the elements of y removed) from the product ('*')
NB. of x times each element of the numbers 1 through (y - x|y)%x. ('i. n' is the array
NB. 0 .. n-1 and '>:' adds 1 to each item in the array). x|y is 'y mod x' (the arguments
NB. are backwards from what you might expect) and y%x is y divided by x.
NB.
NB. So, working backward: the function is finding the remainder of y divided by x,
NB. then subtracting the remainder so that x now divides it evenly. It then divides
NB. by this number, giving us the number of multiples (n) of x less than or equeal to y.
NB. So then it creates an array of 0..n(1), adds 1 to get 1..n, multiplies by x to
NB. get the array of actual multiples, and then removes y itself from the array
NB. (if present) because for this problem, we only want the ones less than or
NB. equal to y.

NB. Incidentally, the '13 :' also rewrites the verb in tacit form. In this case
NB. the transformation succeeds, and the result is the verb:
NB.
NB. ] -.~ [ * [: >: [: i. [ %~ ] - |
NB.
NB. This makes slightly more sense if you rearrange it first:
NB.
NB. y -.~ x *    >:    i. (y - x|y) % x     (original)
NB. y -.~ x *    >:    i. x %~ (y - (x|y)   (transposed. x f~ y <--> y f x)
NB. ] -.~ [ * [: >: [: i. [ %~  ] -   |     (the tacit form produced by [:)
NB.
NB. See http://www.jsoftware.com/docs/help701/dictionary/d502.htm if you want to
NB. understand how '[:' works. Basically it just allows parts of a dyadic chain to
NB. be evaluated as if it were monadic.


NB. possible refactorings:
NB. ---------------------------------------------------------------
NB. The to find the largest multiple less than y can be rewritten 
NB. using a loop ('^:') that shrinks y by 1 ('<:') each step until
NB. the remainder of x | y becomes 0:

<:^:(3|]) 1000   NB. ->  999
<:^:(5|]) 1000   NB. -> 1000  (whoops!)

NB. We can use <: on the right here because we don't want y itself as
NB. a multiple. it serves the same purpose as  'y -. ~' above.

<:^:(3|]) <: 1000  NB. -> 999
<:^:(5|]) <: 1000  NB. -> 995


NB. The rules for the ^: conjunction (taken from the docs) are:
NB.
NB. x u ^: v y <--> x u^:(x v y) y
NB.   u ^: v y <-->   u^:(  v y) y        (u and v are arbitrary verbs.)
NB.
NB. In our case, we're creating a verb '(5|])' which is applied to y,
NB. So we're working with the case in the lower left.
NB.
NB.   u   ^:    v    y
NB.  <:   ^:  (5|])
NB.
NB. To factor out the 5 as a parameter, we will need to rewrite this
NB. to match the pattern in the upper left.
NB.
NB.   x u  ^: v y   <-->  x u  ^:(x v y) y
NB.   5 <: ^: v y   <-->  5 <: ^:(5 v y) y
NB.
NB. But what can we use for v?


NB. User 'ischtche' in the #jsoftware IRC channel provided this
NB. alternate form::

5 ( <:@:]^:| <:) 1000     NB. -> 995

NB. How does it work?
NB.
NB. The conjunction '@:' (pronounced 'at') in a dyadic context
NB. follows the rule:
NB.
NB.    x  u  @: v y <-->  u x v y
NB.    5 <:  @: ] y <--> <: 5 ] y      (left part of ischtche's verb)
NB.
NB. Since '<: 5 ] y' is evaluated right to left, and ']' is the right
NB. argument, this expression shortens to '<: y'.
NB.
NB. This doesn't help us at all in the 'v' slot above, but by sticking
NB. it in the 'u' slot, we can use '|' for 'v':
NB.
NB.   x   u    ^: v y   <-->  x   u   ^: (x v y) y   (rule for dyadic ^: again)
NB.   x  <:@:] ^: | y         x <:@:] ^: (x | y) y
NB.
NB. When this is evaluated, (x <:@:] y) is evaluated recursively
NB. until x|y returns 0. Here's how it looks when traced:
NB.
NB.     y   5<:@:]y   5|y
NB.  ----   -------  ----
NB.   999       998     4
NB.   998       997     3
NB.   997       996     2
NB.   996       995     1
NB.   995       994     0

NB. I had thought this approach might shorten the middle
NB. term, but in fact it's slighly longer not as clear:

13 : 'y -.~ x * >: i. (y - x|y) % x'   NB. old
13 : 'x * >: i. x %~ x <:@:]^:| <: y'  NB. new

