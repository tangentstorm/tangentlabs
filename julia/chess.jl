#=
Mockup of a simple chess engine shell in julia
=#

startpos = "RNBQKBNR/PPPPPPPP/8/8/8/8/pppppppp/rnbqkbnr"

function fen2grid(fen)
    s = ""; dots = ""
    for i in 1:8
        dots = dots * "."
        fen = replace(fen, string(i)=>dots)
    end
    res = [""]; x = y =1
    for ch in fen
        if x > 8
            x, y = 1, y + 1
            push!(res, "")
        end
        if ch != '/'
            x = x + 1
            res[y] = res[y] * ch
        end
    end
    return res
end


function file(x)
    i = findfirst(x, "abcdefgh")
    if i != nothing
        return i.start
    end
    return 0
end

function rank(x)
    return 9-x
end

function setchar(s, i, c)
    s[1:i-1] * c * s[i+1:end]
end

function move(grid, sq0, sq1)
    g = copy(grid)
    y0, x0 = rank(sq0[2]), file(sq0[1])
    y1, x1 = rank(sq1[2]), file(sq1[1])
    p = g[y0][x0]
    g[y0] = setchar(g[y0], x0, ".")
    g[y1] = setchar(g[y1], x0, p)
    return g
end

function show(grid)
    for row in grid
        for cell in row
            print(cell)
            print(' ')
        end
        println()
    end
end

grid = fen2grid(startpos)
show(grid)
println()
grid = move(grid, ("e",2), ("e",4))
show(grid)
