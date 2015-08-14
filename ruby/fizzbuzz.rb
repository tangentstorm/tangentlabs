# fizzbuzz, per https://www.codeeval.com/open_challenges/1/
# this scored 90/100% but there's no indication of why. :/
# ruby 1.9.3
File.open(ARGV[0]).each_line do |line|
  unless line.strip.empty?
    x, y, n = line.split.map &:to_i
    xy = x * y
    puts (1..n).map { |i|
      if    i % xy == 0 then "FB"
      elsif i % x  == 0 then "F"
      elsif i %  y == 0 then "B"
      else i.to_s end
    }.join ' '
  end
end
