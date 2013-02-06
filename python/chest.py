#!/usr/local/bin/python
#
# $Id: //projects/chess/chest.py#8 $ $Date: 2002/12/07 $

"""
A simple test program to demonstrate the chess engine.
"""

__package__ = 'chess'


import chess
import string
import sys


def brief():
    """Non-interactive version for batch processing (one move per line
    with a . to end)."""
    game = chess.Game(None, None)
    lines = sys.stdin.readlines()
    while game.ok() and lines:
        command = lines.pop(0)
        command = command[:-1]
        words = string.split(command)
        try:
            if command == '':
                pass
            elif command[0] == '#':
                pass
            elif command == '.':
                break
            else:
                move = game.move(command)
                print "%d %s %s %s" % (game.round + 1, \
                                       chess.COLORS[game.turn], command, \
                                       move.longAlgebraic())
                game.advance()
        except chess.Error, e:
            print str(e) + ": " + command
            break


def main():
    """Interactive mode.  Type ? for help."""
    game = chess.Game(None, None)
    board = game.board
    for line in game.show():
        print line
    while game.ok():
        print '%s> ' % chess.COLORS[game.turn], 
        command = raw_input()
        words = string.split(command)
        print
        try:
            if len(words) == 1 and \
               (command == '?' or command == 'help'):
                print \
"""\
show             Show the current board.
turn             Indicate who's turn it is.
query (move)     Show the results of disambiguating move.
move (move)      Make move.
test (loc)       Show legal moves for loc with *.
info (loc)       Show internal info for loc.
threat (loc)     Show pieces currently threatening loc with #.
dump             Dump current gamestate to stdout.
read             Read current gamestate from stdin.\
"""
            elif command == '':
                pass
            elif command[0] == '#':
                pass # comment
            elif len(words) == 1 and \
                 (words[0] == 'show' or words[0] == 'board'):
                for line in game.show():
                    print line
            elif len(words) == 1 and words[0] == 'turn':
                print "%s's turn" % chess.COLORS[game.turn]
            elif len(words) == 2 and words[0] == 'query':
                print game.disambiguate(words[1])
            elif len(words) == 2 and words[0] == 'move':
                move = game.move(words[1])
                print "%s moves %s" % \
                      (chess.COLORS[game.turn], move.longAlgebraic())
                if move.capture:
                    print "%s takes %s" % (move.piece.name, move.capture.name)
                for line in game.show():
                    print line
                game.advance()
            elif len(words) == 2 and words[0] == 'test':
                loc = chess.AlgebraicLoc(words[1])
                piece = board.get(loc)
                rep = board.asArray()
                for loc in piece.possible(board):
                    rep[loc.x][loc.y] = '*'
                for line in board.pretty(rep):
                    print line
            elif len(words) == 2 and words[0] == 'info':
                loc = chess.AlgebraicLoc(words[1])
                piece = board.get(loc)
                print "piece %s (%s)" % (piece.name, piece.symbol[piece.color])
                print "location %s" % `piece.loc`
                print "color %s" % chess.COLORS[piece.color]
                print "moves %d" % piece.moves
                print "idle %d" % piece.idle
            elif len(words) == 2 and words[0] == 'threat':
                loc = chess.AlgebraicLoc(words[1])
                rep = board.asArray()
                color = game.turn
                there = board.at(loc)
                if there:
                    color = there.color
                for piece in board.threat(loc, color):
                    rep[piece.loc.x][piece.loc.y] = '#'
                for line in board.pretty(rep):
                    print line
            elif len(words) == 1 and words[0] == 'possible':
                # List all possible moves.
                pieces = board.findAll(game.turn)
                for piece in pieces:
                    possible = piece.possible(board)
                    if possible:
                        print '%s%s' % (piece, piece.loc), possible
            elif len(words) == 1 and words[0] == 'dump':
                game.save(sys.stdout)
            elif len(words) == 1 and words[0] == 'read':
                game.load(sys.stdin)
            else:
                print "i don't understand"
            check = game.checked()
            if check is not None:
                print "%s in check" % chess.COLORS[check]
        except chess.Error, e:
            print str(e)

    checkmate = game.checkmated()
    print "%s checkmated" % chess.COLORS[checkmate]
        

if __name__ == '__main__':
    if len(sys.argv) > 1:
        brief()
    else:
        main()
