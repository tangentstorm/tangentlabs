#!/usr/bin/env ruby
# coding: utf-8
# --------------------------------------------------------------
# a learntris implementation in ruby
# copyright © 2015 michal j wallace <http://tangentstorm.com/>
# https://github.com/learnprogramming/learntris
# --------------------------------------------------------------
require 'matrix'

# monkeypatch std matrix class to allow updating
class Matrix
  def []=(i, j, x)
    @rows[i][j] = x
  end
end


# width and height of the testris matrix
@mh = 22; @mw = 10

# initialize to empty space
@m = Matrix.build(@mh, @mw) {'.'}

def print_matrix
  @m.row_vectors.each do |row|
    row.each {|ch| print "#{ch} "}
    puts
  end
end

def given_matrix
  @mh.times do |y|
    STDIN.readline.split.each_with_index do |ch, x|
      @m[y,x] = ch
    end
  end
end


# main loop
loop do
  STDIN.readline.each_char do |c|
    case c
    when 'q' then exit
    when 'p' then print_matrix
    when 'g' then given_matrix
    end
  end
end
