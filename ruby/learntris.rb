#!/usr/bin/env ruby
# coding: utf-8
# --------------------------------------------------------------
# a learntris implementation in ruby
# copyright © 2015 michal j wallace <http://tangentstorm.com/>
# https://github.com/learnprogramming/learntris
# --------------------------------------------------------------
require 'matrix'

# in ruby, a 'Matrix' is a specific class for 2d arrays.
# in tetris, the 'matrix' is the container that holds all the blocks.
# after this next line, i will use 'matrix' only in the tetris sense,
# and refer to 2d arrays as 'grids'.

class Grid < Matrix

  def []=(i, j, x)
    @rows[i][j] = x
  end

  def emit
    row_vectors.each do |row|
      row.each {|ch| print "#{ch} "}
      puts
    end
  end

end

def grid here
  Grid.rows [ *here.split("\n").collect {|line| line.split } ]
end



# width and height of the testris matrix
@mh = 22; @mw = 10

# initialize to empty space
@m = Grid.build(@mh, @mw) {'.'}

def given_matrix
  @mh.times do |y|
    STDIN.readline.split.each_with_index do |ch, x|
      @m[y,x] = ch
    end
  end
end

def clear_matrix
  @mh.times do |y| @mw.times do |x| @m[y,x]='.' end end
end


tetI = grid <<END
. . . .
c c c c
. . . .
. . . .
END

@t = tetI



@lines = 0 # number of lines that have been cleared
@score = 0 # score for those lines

def step
  @mh.times do |y|
    space_count = @m.row(y).select {|ch| ch == '.'}.length
    if space_count == 0 then
      @mw.times {|x| @m[y,x]='.'}
      @lines += 1
      @score += 100
    end
  end
end


# buffer input so we can read one char at a time, on demand
@buf = ''; @pos = 1
def next_char
  while @pos >= @buf.length do @buf = STDIN.readline; @pos = 0 end
  r = @buf[@pos]; @pos += 1; r
end

# main loop
loop do
  case next_char
  when 'c' then clear_matrix
  when 'g' then given_matrix
  when 'p' then @m.emit
  when 'q' then exit
  when 's' then step
  when 't' then @t.emit
  when '?' then
    case next_char
    when 's' then puts @score
    when 'n' then puts @lines
    end
  end
end
