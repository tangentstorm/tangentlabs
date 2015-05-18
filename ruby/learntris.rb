#!/usr/bin/env ruby
# coding: utf-8
# --------------------------------------------------------------
# a learntris implementation in ruby
# copyright © 2015 michal j wallace <http://tangentstorm.com/>
# https://github.com/learnprogramming/learntris
# --------------------------------------------------------------
require 'matrix'

@m = Matrix.build(22, 10) {'.'}

def print_matrix
  @m.row_vectors.each do |row|
    row.each {|ch| print "#{ch} "}
    puts
  end
end


loop do
  STDIN.readline.each_char do |c|
    case c
    when 'q' then exit
    when 'p' then print_matrix
    end
  end
end
