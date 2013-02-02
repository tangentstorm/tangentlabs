# -*- coding: utf-8 -*-
# ------------------------------------------------------
# ruby syntax experiments
# by tangentstorm on feb 2, 2013
#
# https://github.com/tangentstorm/tangentlabs
#
# you may do anything you want with this code.
#
# ------------------------------------------------------
#
# NOTE: nothing here is meant to be taken as good ruby 
# style! In fact, some of this code is downright ugly,
# on purpose, to see what ruby will accept.
#
# I am an experienced programmer but have only minimal
# ruby experience (worked on one rails app, and I read
# the pickaxe book *many* years ago). I'm simply using
# this file to collect a bunch of simple things that I
# expect to be able to do in any language.
#
# You can find things like this for many languages on
# "chrestomanthy" sites like:
#
#  http://pleac.sourceforge.net/
#  http://rosettacode.org/wiki/Rosetta_Code
#  http://hyperpolyglot.org/
#  http://benchmarksgame.alioth.debian.org/
#
# But: for basic syntax and i/o operations, I think it's 
# kind of fun (and a good learning tool) to compile these
# things myself, before I go hunting for a reference.
#
# To develop this file, i just started typing at the top
# and kept appending to the bottom, usually running the
# whole thing again after adding each little block.
#
# ------------------------------------------------------

# BTW, if you want to work hrough this file the way I 
# wrote it, you can uncomment the following line and just 
# keep moving it down through the file as you experiment
# with each little block of code.

# puts "<exit>"; exit

# ------------------------------------------------------
i = 0
print "while:"
while i < 2 do  print " ", i ;  i += 1 end
while i < 4 do
print " #{i}"
  i += 1 
end



# !!!
# given ruby's smalltalk heritage, i expect there 
# is also something like this:
#
#    { i < 6 }.whileTrue do ... end
#
# ... but I haven't found it yet.

# simple function/procedures 
def nl ; print "\n" end  # "puts" seems to do print + nl already

nl ; print "newline:"; nl

# modify a "global/module" variable?
# iirc, there are neither of these things, only classes
# with Object being the default class/namespace.
# though possibly "i" appears to be local to this file?

  # first attempt:
  def inc ; i = i + 1 end
  # inc # nope. "undefined local variable or method 'i' for main:Object

  # second attempt:
  @i = i
  def inc ; @i = @i + 1 end
  def i? ; print " ", @i end
  print "inc:";  i? ; print " ->" ; inc ; i? ; nl


# repeat loops
print "repeat:"
begin
  inc ; i?
end until @i > 7

nl


# loop through lines of a file  ( also "break" )
i = 0
for line in File.open("ruby.rb") do
  i += 1
  print "#{ i.to_s.rjust 3, ' ' } | #{line}"
  break if i > 3
end


# for loop ( python style )
print "for:"
for i in 1..3 do
  print " #{i}"
end
nl

# "ruby-style-javascript"-style iterators ;)
print "each:" ; (1..3).each do inc; i? end ; nl

# begin end nl  # <- nope. need a semicolon or newline after 'end'

# block syntax
print "'..'/do: "; [@i..( @i + 3 )].each do |x| print x end; nl
print "'..'/{}: "; [@i..( @i + 3 )].each { |x| print x }; nl

# lambda and higher order functions?
lambda { puts "lambda!" }.call
lambda { |x| puts x }.call "lambda(x)!" 
def ex ( msg, func )
  print msg, ":"
  func.call( lambda { inc; i? } )
  nl
end
ex "step", lambda { |f| 2.step 4 do f.call end } # yay! :)

# ex "step2", { |f| 2.step 4 do f.call end }
# ex "step2", do { |f| 2.step 4 do f.call end } end

# At this point, I was mis-remembering some other syntax
# that was more like smalltalk's [ .. ] and didn't require a keyword. 
#
# Asking google for "ruby block syntax" turned up this:
# http://www.robertsosinski.com/2008/12/21/understanding-ruby-blocks-procs-and-lambdas/
#
# Looks like "do..end" and "{..}" are "blocks" which can't be
# passed around. lambda and Proc.new make procedures. The
# difference is in the semantics for "return"


# robert sosinski's examples of proc/lambda

def proc_return 
  Proc.new { return "Proc.new"}.call
  return "proc_return method finished"
end

def lambda_return
  lambda { return "lambda" }.call
  return "lambda_return method finished"
end

puts proc_return
puts lambda_return

# he says: "Part of Ruby’s syntax is that arguments (a Proc in this
# example) cannot have a return keyword in it."
#
# Not entirely sure I believe this, so:

# ex "syntax-error?", Proc.new { |x| return x }  # yep. syntax error.

# ... he's right! it's a syntax error, not a runtime error. interesting.
# and he's right about lambda, too:

ex "syntax-error?", lambda { |x| return x }  # works fine

# sorry, robert sosinski. never should have doubted you. :)
# moving on!

# so.. what happens if it the "return" isn't directly inside the
# argument?
x = Proc.new { return 5 }  # no problem
# ex "now what?", x        # runtime error
# x.call                   # runtime error


# try .. except?
begin
  puts "cause an error: "
  x.call
rescue
  ex "recue? ", lambda { |x| print " saved!" }
end  

# more interesting:
@i = 1
begin
  print "fix an error #{ @i }: "
  x.call
rescue
  inc
  x = Proc.new { puts " repaired!" }
  retry
end  

# raise and finally ( "ensure" )
@i = 0
thunk = lambda { raise "oh no" }
begin
  inc
  begin
    print "ensure #{@i}: "
    thunk.call
  ensure
    puts " newline!"
  end
rescue
  puts "[ repairing ]"
  thunk = lambda { print "[ repaired ]" }
  retry
end

# rescue / ensure together
begin
  print "raise:"
  raise "oh no"
rescue
  print "rescued!"
ensure
  puts "finally!"
end

# introspection
ex "five integer methods", Proc.new { 
  ( 1..5 ).each do |i| print " ", i.methods[ i ] end }

# the first is "-@" .. what the heck is that?
puts "1.-@ is: #{ 1.-@ }"   # oh. :)



#def can-i-use-dashes? ; end  # nope.
#def how_about_prime?' ; end  # nope.
def do_i_need_parens? a, b ; put "no parens needed." end

def assert the_truth; 
  if not the_truth then raise "LIES!" end
end

# unicode?
def ≠ a, b ; a != b end
assert ≠( 1, 2 )
assert ! ≠( 1, 1 )

puts "0.class: #{ 0.class }"
puts "0.class.class: #{ 0.class.class }"
puts "0.class.class.class: #{ 0.class.class.class }"

# 0 is a Fixnum, so:
class Fixnum 
  def ≠ other
    self != other
  end
end

assert ≠( 1, 2 )
assert ! ≠( 5, 5 )

def try code
  puts "#{ code } -> #{ eval code }"
end
try "1 .≠ 2"


# but why limit it to that one class?
# Object.≠ = Fixnum.≠  # no. tries to call the method
# Object.≠ = lambda { |this, other| self > other } # no. undefined method "≠=" !!

# after http://stackoverflow.com/questions/11874579/define-custom-ruby-operator
# i tried "gem install superators19". 

require 'superators19'
class Object
  # superator "≠" do |other|  self != other  end  # runtime: "not a valid superator!"
  # superator "<>" do |other|  self != other end  # same thing
  superator "%~" do |other|  self != other end    # seems to "work"
end

# but:
try "1 %~ 2"  # -> -2 !!

# But... I missed the note that superator doesn't work for fixnums.
# so let's try strings:

try "'a' %~ 'b'"  # ... 'a' ?
try "'a' != 'b'"  # true

# well, okay. this is not something really need anyway :)
class Object
  def ≠ other
    self != other
  end
end

try "'a' .≠ 'b'" # -> true
try "'a' .≠ 'a'" # -> false


# doesn't look like there are optional parameters
# http://stackoverflow.com/questions/812058/ruby-optional-parameters
# but it supports default ones:

# nil, yield, default arguments..
# -------------------------------
# this is especially messy. i'm just testing syntax here
# especially. the the conditional syntaxes
def range ( a, b=nil, c=nil ) 
  start = b ? a : 0
  stop  = if b then b else a end
  # nested routines?
  def step_for n, m
    if n < m then 1 else -1 end
  end
  step = if c then c else step_for start, stop end
  raise "step cannot be 0" if step == 0
  test = if step > 0 then lambda{ |a,b| a < b }
         else lambda{ |a,b| a > b } end
  count = start
  # oberon/pascal-style would have used <= and >= above
  # but i'm used to thinking in python...  :)
  print " { #{ start } to #{ stop - step } by #{ step } } "
  while test.call count, stop do
    yield count
    count += step
  end
end

# one more "immediate if" test. ( used to have to do this in python )
try "1 > 0 and 1 or -1"

# print "range a: "; range 10 do |x| print " #{ x }" end; nl
# print "range a: "; range -2, 8, 2 do |x| print " #{ x }" end; nl
# print "range a: "; range 7, 2 do |x| print " #{ x }" end; nl


def show_range a, b=nil, c=nil
  print "range( #{a}, #{b}, #{c} ) : "; 
  range a, b, c do
    |x| print " #{ x }" 
  end; nl
end
show_range 10
show_range -2, 8, 2
show_range 7, 2


# after coffeescript or c# or something, i was expecting ??
# to test for nil. instead:
puts "?? is: #{ ?? }"
puts "?a is: #{ ?a }"


# case statement
range 10 do |i|
  print "case #{ i }: "
  print case i # ... make that "case expression!"
        when 0 then 'zero'
        when 1 then 'one'
        when 2 then 'two'
        when 3..5 then 'a few'
        when 6..7 then 'a bunch'
        else "too many to count"
        end
  nl
end


# Okay, I think that's enough for me.
# I'm alredy familiar with the *basics* of how
# ruby's lists, arrays, strings, and classes work
# but if you're not, you might want to try writing
# some little experiments on your own.

# I'm sure I'll run into something I don't understand
# soon enough. If so, I'll probably write an isolated
# test program to explore the problem.
