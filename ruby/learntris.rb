#!/usr/bin/env ruby
# coding: utf-8
# --------------------------------------------------------------
# a learntris implementation in ruby
# copyright © 2015 michal j wallace <http://tangentstorm.com/>
# https://github.com/learnprogramming/learntris
# --------------------------------------------------------------

loop do
  STDIN.readline.each_char do |c|
    case c
    when 'q' then exit
    when 'p' then 22.times { 10.times { print '. ' }; puts'' }
    end
  end
end
