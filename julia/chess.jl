#=
Mockup of a simple chess engine shell in julia

This was just a "hello world" kind of thing...
There's a really nice chess package here:

https://romstad.github.io/Chess.jl/dev/manual/

(Although it does suffer from the AGPL...)
=#

@enum Piece ♔ ♕ ♖ ♗ ♘ ♙ ♚ ♛ ♜ ♝ ♞ ♟ ◻ # last is for null piece
START = "RNBQKBNR/PPPPPPPP/8/8/8/8/pppppppp/rnbqkbnr w KQkq - 0 1"
RANKS = "abcdefgh"
rank = x-> 9-x
file = x-> (i = findfirst(x, RANKS)) == nothing ? 0 : i.start
show = g-> for r in g for c in r print(c, ' ') end; println() end
setc = (s, i, c)-> s[1:i-1] * c * s[i+1:end]

function fen2grid(fen)
  # replace digit x with that many dots (empty squares)
  dots = ""
  for i in 1:8
    dots = dots * "."
    fen = replace(fen, string(i)=>dots)
  end
  # now build the array of strings representing the board
  res = [""]; x = y = 1
  for ch in fen
    if x > 8
      x, y = 1, y + 1
      push!(res, "")
    end
    if ch != '/'
      x += 1
      res[y] = res[y] * ch
    end
    if ch == ' ' break end
  end
  return res
end


function move(grid, sq0, sq1)
  # returns a new grid with the object on sq0 moved to sq1 and replaced with '.'
  g = copy(grid)
  y0, x0 = rank(sq0[2]), file(sq0[1])
  y1, x1 = rank(sq1[2]), file(sq1[1])
  p = g[y0][x0]
  g[y0] = setc(g[y0], x0, ".")
  g[y1] = setc(g[y1], x0, p)
  return g
end

grid = fen2grid(START)
show(grid)
println()
grid = move(grid, ("e",2), ("e",4))
show(grid)
