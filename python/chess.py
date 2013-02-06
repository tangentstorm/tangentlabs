#!/usr/local/bin/python
#
# $Id: //projects/chess/chess.py#11 $ $Date: 2009/03/10 $

"""
A chess adjudicator, which understands several standard notations for moves.
"""

__version__ = '1.0.2b'
__program__ = 'chess'
__author__ = 'Erik Max Francis <max@alcyone.com>'
__copyright__ = 'Copyright (C) 2001-2009 Erik Max Francis'
__license__ = 'BSD'


import string


# Basic definitions.
SIZE = 8
WHITE, BLACK = range(2)

# Castling types.
KINGSIDE, QUEENSIDE = +1, -1

# Lookup tables.
FILES = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
RANKS = ['1', '2', '3', '4', '5', '6', '7', '8']
COLORS = {WHITE: 'white', BLACK: 'black'}

PIECES = None # forward reference; defined after piece classes
SYMBOLS = None # forward reference; defined after piece classes

# Repr of initial board configuration.
INITIAL = 'rnbqkbnr ' \
          'pppppppp ' \
          '........ ' \
          '........ ' \
          '........ ' \
          '........ ' \
          'PPPPPPPP ' \
          'RNBQKBNR'


class Error(Exception):
    """The base error class.  All chess-related exceptions derive from
    this one."""
    def __init__(self, x=None):
        Exception.__init__(self, x)
        self.x = x

    def __str__(self):
        result = str(self.__class__)
        if self.x:
            result = result + ": " + str(self.x)
        return result

class ParseError(Error):
    """Unrecognized command."""
    pass

class FileFormatError(Error):
    """A save file format was not recognized."""
    pass

class EmptySquareError(Error):
    """A move was attempted from an empty square."""
    pass
    
class IllegalMoveError(Error):
    """An illegal move was attempted."""
    pass
    
class AmbiguousMoveError(Error):
    """An ambiguous move was attempted."""
    pass

class NoMatchesError(Error):
    """A search for a piece resulted in no matches."""
    pass

class ConsistencyError(Error):
    """An internal inconsistency check failed (internal error)."""
    pass


class Loc:
    """A raw location on the board, represented as a file (x) and a rank (y)
    value, both indexing from zero."""
    
    def __init__(self, x, y):
        self.x, self.y = x, y

    def tuple(self):
        """Return the location as a tuple."""
        return self.x, self.y

    def normalize(self):
        """Maintain directions but make components size no more than 1."""
        if self.x:
            self.x = self.x/abs(self.x)
        if self.y:
            self.y = self.y/abs(self.y)
        return Loc(self.x, self.y)

    def traverse(self, other, delta):
        """Return a path from SELF to OTHER (not including SELF, but including
        OTHER if appropriate), counting by increments of DELTA.  Return None
        if no such path is possible."""
        if self == other or delta.tuple() == (0, 0):
            return None
        path = []
        x = self
        while x != other:
            x = x + delta
            path.append(x)
        return path

    def match(self, pattern):
        """Match SELF against a PATTERN, where PATTERN is a Loc in which
        wildcards are represented with a None."""
        if pattern.x is None and pattern.y is None:
            return 1
        elif pattern.x is None and pattern.y is not None:
            return self.y == pattern.y
        elif pattern.x is not None and pattern.y is None:
            return self.x == pattern.x
        else:
            return self.x == pattern.x and self.y == pattern.y

    def __cmp__(self, other):
        """Not very meaningful for inequalities."""
        return cmp(self.tuple(), other.tuple())

    def __add__(self, other):
        """Vector sum."""
        return Loc(self.x + other.x, self.y + other.y)

    def __sub__(self, other):
        """Vector difference."""
        return Loc(self.x - other.x, self.y - other.y)

    def __getitem__(self, key):
        """Index as a sequence."""
        if key == 0:
            return self.x
        elif key == 1:
            return self.y
        else:
            raise KeyError, "key must be in 0, 1"

    def __repr__(self):
        s = ''
        if self.x is None:
            s = s + '?'
        else:
            s = s + FILES[self.x]
        if self.y is None:
            s = s + '?'
        else:
            s = s + RANKS[self.y]
        return s


class AlgebraicLoc(Loc):
    """A Loc expressed using algebraic notation."""
    
    def __init__(self, s):
        """Create an algebraic location from the two-character string S."""
        Loc.__init__(self, 0, 0)
        try:
            if s and s[0] in FILES:
                self.x = FILES.index(s[0])
                s = s[1:]
            else:
                self.x = None
            if s and s[0] in RANKS:
                self.y = RANKS.index(s[0])
                s = s[1:]
            else:
                self.y = None
            if s:
                raise ParseError, "bad algebraic notation"
        except TypeError:
            raise ParseError, "bad algebraic location"


class Piece:
    """A piece, on or off the board."""
    
    name = None # full name of piece type
    symbol = None # 2-tuple of white, black piece symbols (letters)
    
    def __init__(self, color):
        self.color = color
        self.loc = None
        self.moves = 0
        self.idle = 0

    def cardinal(self, start, end, max=8):
        """Return a cardinal direction path from START to END with no more
        than MAX moves, or None."""
        d = end - start
        if (not d.x or not d.y) and (abs(d.x) <= max and abs(d.y) <= max):
            delta = d.normalize()
            return start.traverse(end, delta)
        else:
            return None

    def ordinal(self, start, end, max=8):
        """Return an ordinal (diagonal) direction path from START to END
        with no more than MAX moves, or None."""
        d = end - start
        if abs(d.x) == abs(d.y) and abs(d.x) <= max:
            delta = d.normalize()
            return start.traverse(end, delta)
        else:
            return None

    def omni(self, start, end, max=8):
        """Return an omnidirectional path from START to END with no more
        than MAX moves, or None."""
        d = end - start
        if (((not d.x or not d.y) or abs(d.x) == abs(d.y)) and \
            (abs(d.x) <= max and abs(d.y) <= max)):
            delta = d.normalize()
            return start.traverse(end, delta)
        else:
            return None

    def path(self, start, end):
        """Return a path from START to END."""
        raise NotImplementedError, "Piece.path is abstract"

    def walk(self, path, board):
        """Return true if PATH is a reasonable move on BOARD, independent of
        piece type."""
        if path:
            head, tail = path[:-1], path[-1]
            for loc in head:
                if board.at(loc):
                    return 0
            if board.at(tail):
                return board.at(tail).color != self.color
            else:
                return 1
        else:
            return 0

    def validate(self, to, board):
        """First phase of move validation; see if this piece can move to TO
        on BOARD under the allowed rules for this type of piece."""
        path = self.path(self.loc, to)
        return self.walk(path, board)

    def verify(self, to, board):
        """Second phase of move validation; after verifying that TO is a
        legal move on BOARD for this piece, verify that in the context of
        the state of the game it is legal; e.g., a piece can make a move
        that would put its own king in check."""
        if not self.validate(to, board):
            return 0
        return not board.wouldCheck(self.loc, to)

    def finalize(self, start, end, board):
        """After a move from START to END on BOARD is complete, complete
        any necessary cleanup."""
        self.moves = self.moves + 1
        self.idle = 0
        if hasattr(self, 'special'):
            del self.special

    def move(self, loc, board):
        """Move this piece to LOC on BOARD."""
        if not self.verify(loc, board):
            raise IllegalMoveError, "cannot move"
        start = self.loc
        capture = board.move(self.loc, loc)
        override = self.finalize(start, loc, board)
        if override:
            capture = override
        return capture

    def threat(self, board):
        """Is this piece on BOARD currently under threat?"""
        return board.threat(self.loc, self.color)

    def possible(self, board):
        """Return a list of all possible moves for this piece on BOARD."""
        list = []
        for i in range(SIZE):
            for j in range(SIZE):
                loc = Loc(i, j)
                if self.verify(loc, board):
                    list.append(loc)
        return list

    def clone(self):
        """Make a clone of this piece."""
        other = self.__class__(self.color)
        other.moves = self.moves
        other.loc = self.loc
        other.idle = self.idle
        if hasattr(self, 'special'):
            other.special = self.special
        if hasattr(self, 'request'):
            other.request = self.request
        return other

    def __repr__(self):
        return self.symbol[self.color]


class King(Piece):
    """The king.  Supports castling."""
    
    name = 'king'
    symbol = 'K', 'k'

    def path(self, start, end):
        return self.omni(start, end, 1)

    def getCastleRook(self, board, side):
        """Return the rook (by looking in the right place for a rook) for
        a castle of type SIDE on BOARD, or None."""
        rook = None
        d = Loc(side, 0)
        if d.x > 0:
            rook = board.at(Loc(7, self.loc.y))
        else:
            rook = board.at(Loc(0, self.loc.y))
        if not rook or not isinstance(rook, Rook):
            return None
        else:
            return rook

    def validate(self, to, board):
        d = to - self.loc
        if d.tuple() in [(2, 0), (-2, 0)]:
            dd = d.normalize()
            side = dd.x
            # find the rook to castle with
            rook = self.getCastleRook(board, side)
            if not rook:
                return 0
            # make sure neither have moved yet
            if self.moves or rook.moves:
                return 0
            # make sure intervening spaces are empty
            path = self.loc.traverse(rook.loc, dd)
            path = path[:-1]
            for loc in path:
                if board.at(loc):
                    return 0
            # get info and stow it
            kingStart = self.loc
            kingEnd = self.loc + Loc(2*side, 0)
            rookStart = rook.loc
            rookEnd = self.loc + Loc(side, 0)
            self.special = rook, side, kingStart, kingEnd, rookStart, rookEnd
            return 1
        else:
            return Piece.validate(self, to, board)

    def verify(self, to, board):
        if not self.validate(to, board):
            return 0
        d = to - self.loc
        if d.tuple() in [(2, 0), (-2, 0)]:
            dd = d.normalize()
            # retrieve info
            if not hasattr(self, 'special'):
                raise ConsistencyError, "thought we were castling"
            rook, side, kingStart, kingEnd, rookStart, rookEnd = self.special
            # check for threats
            hyp = board.clone()
            hyp.move(kingStart, kingEnd)
            hyp.move(rookStart, rookEnd)
            path = kingStart.traverse(kingEnd, dd)
            for loc in path:
                if hyp.threat(loc, self.color):
                    return 0
            return 1
        else:
            return Piece.verify(self, to, board)

    def finalize(self, start, end, board):
        d = end - start
        if d.tuple() in [(2, 0), (-2, 0)]:
            # retrieve info
            if not hasattr(self, 'special'):
                raise ConsistencyError, "thought we were castling"
            rook, side, kingStart, kingEnd, rookStart, rookEnd = self.special
            # actually move pieces
            board.move(rookStart, rookEnd)
            rook.finalize(rookStart, rookEnd, board)
        return Piece.finalize(self, start, end, board)

    def castle(self, side, board):
        """Do a castle."""
        d = Loc(2*side, 0)
        return self.move(self.loc + d, board)


class Queen(Piece):
    """The queen."""
    
    name = 'queen'
    symbol = 'Q', 'q'

    def path(self, start, end):
        return self.omni(start, end)


class Rook(Piece):
    """The rook."""
    
    name = 'rook'
    symbol = 'R', 'r'

    def path(self, start, end):
        return self.cardinal(start, end)


class Bishop(Piece):
    """The bishop."""
    
    name = 'bishop'
    symbol = 'B', 'b'

    def path(self, start, end):
        return self.ordinal(start, end)


class Knight(Piece):
    """The knight."""
    
    name = 'knight'
    symbol = 'N', 'n'

    def path(self, start, end):
        d = end - start
        if (abs(d.x) == 1 and abs(d.y) == 2) or \
           (abs(d.x) == 2 and abs(d.y) == 1):
            return [end]
        else:
            return None


class Pawn(Piece):
    """The pawn.  Supports promotion, en passant captures."""
    
    name = 'pawn'
    symbol = 'P', 'p'

    def movePath(self, start, end):
        """Return a path from START to END for a move, or None."""
        d = end - start
        if self.color == WHITE:
            if (d.tuple() == (0, 2) and not self.moves) or \
               d.tuple() == (0, 1):
                return start.traverse(end, d.normalize())
        else:
            if (d.tuple() == (0, -2) and not self.moves) or \
               d.tuple() == (0, -1):
                return start.traverse(end, d.normalize())
        return None

    def attackPath(self, start, end):
        """Return a path from START to END for an attack, or None."""
        d = end - start
        if self.color == WHITE:
            if d.tuple() in [(1, 1), (-1, 1)]:
                return start.traverse(end, d)
        else:
            if d.tuple() in [(1, -1), (-1, -1)]:
                return start.traverse(end, d)

    def enPassantPath(self, start, end, board):
        """Return a path from START to END on BOARD for an en passant
        move/attack, or None."""
        d = end - start
        if self.color == WHITE:
            if not d.tuple() in [(1, 1), (-1, 1)]:
                return None
        else:
            if not d.tuple() in [(1, -1), (-1, -1)]:
                return None
        dx = Loc(d.x, 0)
        piece = board.at(start + dx)
        if not piece: return 0
        if piece and piece.color != self.color and \
           isinstance(piece, Pawn) and piece.moves == 1 and piece.idle < 2:
            self.special = piece
            print 'here'
            return start.traverse(end, d)

    def validate(self, to, board):
        start = self.loc
        if board.at(to):
            path = self.attackPath(start, to)
        else:
            path = self.movePath(start, to)
        if not path:
            path = self.enPassantPath(start, to, board)
        return self.walk(path, board)

    def finalize(self, start, end, board):
        if end.y in (0, 7):
            # handle pawn promotion
            if not hasattr(self, 'request'):
                promote = Queen
            else:
                promote = self.request
            piece = promote(self.color)
            board.place(end, piece)
        elif hasattr(self, 'special'):
            piece = self.special
            loc = piece.loc
            board.take(loc)
            Piece.finalize(self, start, end, board)
            return piece
        return Piece.finalize(self, start, end, board)
        

PIECES = {'P': Pawn,
          'R': Rook,
          'N': Knight,
          'B': Bishop,
          'Q': Queen,
          'K': King}

SYMBOLS = {'P': (Pawn, WHITE),
           'R': (Rook, WHITE),
           'N': (Knight, WHITE),
           'B': (Bishop, WHITE),
           'Q': (Queen, WHITE),
           'K': (King, WHITE),
           'p': (Pawn, BLACK),
           'r': (Rook, BLACK),
           'n': (Knight, BLACK),
           'b': (Bishop, BLACK),
           'q': (Queen, BLACK),
           'k': (King, BLACK)}


class Board:
    """Representation of a chessboard."""
    
    def __init__(self):
        self.array = []
        for i in range(SIZE):
            seq = []
            for j in range(SIZE):
                seq.append(None)
            self.array.append(seq)

    def at(self, loc):
        """Return piece at LOC or None."""
        return self.array[loc.x][loc.y]

    def get(self, loc):
        """Return piece at LOC or raise."""
        piece = self.at(loc)
        if piece:
            return piece
        else:
            raise EmptySquareError

    def take(self, loc):
        """Remove a piece at LOC (in preparation for moving it) and return
        it."""
        piece = self.at(loc)
        if piece:
            self.array[loc.x][loc.y] = None
            piece.loc = None
            return piece
        else:
            raise EmptySquareError

    def place(self, loc, piece):
        """Place a previously-taken PIECE at LOC."""
        self.array[loc.x][loc.y] = piece
        piece.loc = loc

    def move(self, start, end):
        """Move a piece from START to END."""
        piece = self.take(start)
        capture = self.at(end)
        self.place(end, piece)
        return capture

    def pieces(self):
        """Get a list of all pieces on the board."""
        list = []
        for i in range(SIZE):
            for j in range(SIZE):
                piece = self.at(Loc(i, j))
                if piece:
                    list.append(piece)
        return list

    def selectFirst(self, func):
        """Return the first piece where FUNC returns true or raise."""
        for piece in self.pieces():
            if func(piece):
                return piece
        else:
            raise NoMatchesError

    def selectAll(self, func):
        """Return all pieces where FUNC returns true."""
        list = []
        for piece in self.pieces():
            if func(piece):
                list.append(piece)
        return list

    def findAll(self, color):
        """Return a list of all pieces of color COLOR."""
        list = []
        for piece in self.pieces():
            if piece.color == color:
                list.append(piece)
        return list

    def findAllNonKings(self, color):
        """Return a list of all non-king pieces of color COLOR."""
        list = []
        for piece in self.pieces():
            if piece.color == color and not isinstance(piece, King):
                list.append(piece)
        return list

    def findByKind(self, kind, color):
        """Return first found piece of type KIND and color COLOR or raise."""
        for piece in self.pieces():
            if isinstance(piece, kind) and piece.color == color:
                return piece
        else:
            raise NoMatchesError

    def findAllByKind(self, kind, color):
        """Return a list of all piece of type KIND and color COLOR."""
        list = []
        for piece in self.pieces():
            if isinstance(piece, kind) and piece.color == color:
                list.append(piece)
        return list

    def king(self, color):
        """Return COLOR's king."""
        return self.findByKind(King, color)

    def threat(self, loc, color):
        """What pieces can currently threaten LOC if it were covered
        with a COLOR piece?"""
        threats = []
        for piece in self.pieces():
            if piece.color != color:
                if piece.validate(loc, self):
                    threats.append(piece)
        return threats

    def couldMove(self, end, color):
        """If it were COLOR's turn, who could move to END?"""
        pieces = []
        for piece in self.pieces():
            if piece.color == color:
                try:
                    hyp = self.clone()
                    hypPiece = hyp.get(piece.loc)
                    hypPiece.move(end, hyp)
                except IllegalMoveError:
                    pass
                else:
                    pieces.append(piece)
        return pieces

    def wouldCheck(self, start, end, color=None):
        """If a COLOR piece moved from START to END, would COLOR's king
        be in check?"""
        hyp = self.clone()
        piece = hyp.get(start)
        if color is None:
            color = piece.color
        hyp.move(start, end)
        piece.finalize(start, end, hyp)
        king = hyp.king(color)
        return king.threat(hyp)

    def check(self, color):
        """Is COLOR in check?"""
        king = self.king(color)
        return king.threat(self)

    def checkmate(self, color):
        """Is COLOR checkmated?"""
        king = self.king(color)
        # If the king is not under threat then it is not checkmated.
        if not king.threat(self):
            return 0
        # If the king is under threat but has legal moves then it is not
        # checkmated.
        if king.possible(self):
            return 0
        # Finally, if the king is under threat and has no legal moves, then
        # we must go through every other piece owned by that color and
        # see if it has any legal moves (i.e., moves which take the king
        # out of check); if none do, then it is checkmated.
        pieces = self.findAllNonKings(color)
        for piece in pieces:
            if piece.possible(self):
                return 0
        else:
            return 1

    def clear(self):
        """Clear the board."""
        for i in range(SIZE):
            for j in range(SIZE):
                self.array[i][j] = None

    def set(self, rep):
        """Set the board to the configuration indicated by the string REP."""
        self.clear()
        data = string.split(rep)
        for i in range(SIZE):
            for j in range(SIZE):
                char = data[SIZE - j - 1][i]
                if char != '.':
                    type, color = SYMBOLS[char]
                    piece = type(color)
                    self.place(Loc(i, j), piece)

    def reset(self):
        """Reset the board to the base state."""
        self.clear()
        self.set(INITIAL)

    def pretty(self, rep):
        """Return a "pretty" ASCII representation of the board represented
        by REP."""
        lines = []
        lines.append('. . a b c d e f g h . .')
        lines.append('. +-----------------+ .')
        for j in range(SIZE - 1, -1, -1):
            line = '%d | ' % (j + 1,)
            for i in range(SIZE):
                line = line + "%s " % rep[i][j]
            line = line + '| %d' % (j + 1,)
            lines.append(line)
        lines.append('. +-----------------+ .')
        lines.append('. . a b c d e f g h . .')
        return lines

    def prettyMarkup(self, rep):
        """Return a marked-up "pretty" representation.  Internal use only."""
        lines = []
        lines.append('. . a b c d e f g h . .')
        lines.append('. <escape="[41m">+-----------------+<default><escape="[40m"> .')
        for j in range(SIZE - 1, -1, -1):
            line = '%d <escape="[41m">| ' % (j + 1,)
            for i in range(SIZE):
                piece = self.at(Loc(i, j))
                if piece is not None:
                    if piece.color == WHITE:
                        line = line + '<escape="[1;37m">'
                    else:
                        line = line + '<escape="[1;30m">'
                line = line + "%s" % rep[i][j]
                if piece is not None:
                    line = line + '<default><escape="[41m">'
                line = line + ' '
            line = line + '|<default><escape="[40m"> %d' % (j + 1,)
            lines.append(line)
        lines.append('. <escape="[41m">+-----------------+<default><escape="[40m"> .')
        lines.append('. . a b c d e f g h . .')
        return lines

    def show(self):
        """Return a "pretty" ASCII representation of the current state of
        the board."""
        return self.pretty(self.asArray())

    def showMarkup(self):
        """Show a marked-up "pretty" representation.  Internal use only."""
        return self.prettyMarkup(self.asArray())

    def clone(self):
        """Make a clone of the entire board (including pieces)."""
        other = Board()
        for i in range(SIZE):
            for j in range(SIZE):
                if self.array[i][j]:
                    other.array[i][j] = self.array[i][j].clone()
        return other

    def asArray(self):
        """Return the state of the board as an array of arrays of chars."""
        array = []
        for i in range(SIZE):
            line = []
            for j in range(SIZE):
                if self.array[i][j]:
                    line.append(`self.array[i][j]`)
                else:
                    line.append('.')
            array.append(line)
        return array

    def __repr__(self):
        rep = ''
        for j in range(SIZE - 1, -1, -1):
            for i in range(SIZE):
                if self.array[i][j]:
                    rep = rep + `self.array[i][j]`
                else:
                    rep = rep + '.'
            rep = rep + ' '
        return rep[:-1]


class Move:
    """Encapsulates a single move."""
    def __init__(self, command, start, end):
        self.command = command # raw move command
        self.start = start # begin loc
        self.end = end # end loc
        self.piece = None # the piece which moved
        self.isCheck = 0 # causes check?
        self.isCheckmate = 0 # causes checkmate?
        self.capture = None # captured piece

    def algebraic(self):
        """Display the move in algebraic notation."""
        return `self.start` + `self.end`

    def longAlgebraic(self):
        """Display the move in long algebraic notation."""
        takes = '-'
        if self.capture:
            takes = 'x'
        suffix = ''
        if self.isCheck:
            suffix = '+'
        elif self.isCheckmate:
            suffix = '#'
        return self.piece.symbol[WHITE] + `self.start` + \
               takes + `self.end` + suffix


class Game:
    """Encapsulates a game."""
    
    def __init__(self, white=None, black=None):
        self.state = 'playing'
        self.players = white, black
        self.turn = WHITE
        self.round = 0
        self.moves = []
        self.board = Board()
        self.board.reset()

    def load(self, file):
        """Load the state of the game from FILE."""
        try:
            line = file.readline()
            line = line[:-1]
            self.players = string.split(line)
            if len(self.players) != 2:
                raise FileFormatError, "wrong number of player names"
            line = file.readline()
            line = line[:-1]
            self.turn, self.round = map(int, string.split(line))
            line = file.readline()
            line = line[:-1]
            self.board.clear()
            reps = string.split(line)
            for rep in reps:
                fields = string.split(rep, '.')
                if len(fields) != 4:
                    raise FileFormatError, "wrong number of piece fields"
                type, color = SYMBOLS[fields[0]]
                piece = type(color)
                self.board.place(AlgebraicLoc(fields[1]), piece)
                piece.moves, piece.idle = int(fields[2]), int(fields[3])
            line = file.readline()
            line = line[:-1]
            self.moves = []
            reps = string.split(line)
            for rep in reps:
                if len(rep) != 4:
                    raise FileFormatError, "invalid move"
                start, end = AlgebraicLoc(rep[0:2]), AlgebraicLoc(rep[2:4])
                self.moves.append((start, end))
        except FileFormatError:
            raise
        except:
            raise FileFormatError, "miscellaneous error"

    def save(self, file):
        """Save the state of the game to FILE."""
        file.write("%s %s\n" % tuple(self.players))
        file.write("%d %d\n" % (self.turn, self.round))
        pieces = []
        for piece in self.board.pieces():
            rep = "%s.%s.%d.%d" % (`piece`, `piece.loc`, \
                                  piece.moves, piece.idle)
            pieces.append(rep)
        file.write(string.join(pieces, ' ') + "\n")
        moves = []
        for move in self.moves:
            rep = `move[0]` + `move[1]`
            moves.append(rep)
        file.write(string.join(moves, ' ') + "\n")

    def isPlaying(self, player):
        """Return true if PLAYER is participating in this game."""
        return player in self.players

    def show(self):
        """Return an ASCII representation of the board."""
        return self.board.show()

    def whose(self):
        """Whose turn is it?"""
        return self.players[self.turn]

    def advance(self):
        if self.checkmated() is not None:
            self.state = 'checkmated'
        else:
            self.turn = not self.turn
            for piece in self.board.pieces():
                piece.idle = piece.idle + 1
            if not self.turn:
                self.round = self.round + 1
       
    def ensure(self, loc, color):
        """Ensure that LOC is occupied by a COLOR piece."""
        piece = self.board.at(loc)
        if piece:
            if piece.color != color:
                raise IllegalMoveError, "enemy piece"
        else:
            raise EmptySquareError
        return piece and piece.color == color

    def disambiguate(self, command):
        """Disambiguate a move given by COMMAND and return a 2-tuple of
        the starting and ending positions."""
        # First, replace archaic Kn notation to N.
        command = command.replace('Kn', 'N')
        # Test for check (+ suffix) or checkmate (# suffix).
        isCheck, isCheckmate = 0, 0
        if command:
            if command[-1] == '+':
                isCheck = 1
                command = command[:-1]
            elif command[-1] == '#':
                isCheckmate = 1
                command = command[:-1]
        if command == 'O-O':
            king = self.board.king(self.turn)
            return king.loc, king.loc + Loc(2, 0)
        elif command == 'O-O-O':
            king = self.board.king(self.turn)
            return king.loc, king.loc + Loc(-2, 0)
        elif len(command) == 4 and \
           command[0] in 'abcdefgh' and command[1] in '12345678' and \
           command[2] in 'abcdefgh' and command[3] in '12345678':
            # Algebraic notation.
            start, end = AlgebraicLoc(command[0:2]), AlgebraicLoc(command[2:4])
            self.ensure(start, self.turn)
            return start, end
        else:
            try:
                # Long or standard algebraic notation.
                # Check for pawn promotion.
                promote = None
                if len(command) > 2 and command[-2] == '=' and \
                   command[-1] in PIECES.keys():
                    promote = PIECES[command[-1]]
                    if not promote in (Queen, Knight, Bishop, Rook):
                        raise IllegalMoveError, "cannot promote to king, pawn"
                    command = command[:-2]
                # Always ends with algebraic for destination.
                command, endAlgebraic = command[:-2], command[-2:]
                end = AlgebraicLoc(endAlgebraic)
                # Check for a capture (x).
                takes = 0
                if command:
                    if command[-1] == 'x':
                        takes = 1
                        command = command[:-1]
                    elif command[-1] == '-':
                        command = command[:-1]
                # If first character is an uppercase letter then it represents
                # the kind of piece, otherwise it is a pawn.
                if command:
                    if command[0] in string.uppercase:
                        kind = PIECES[command[0]]
                        command = command[1:]
                    elif command[0] == '?':
                        kind = None
                        command = command[1:]
                    else:
                        kind = Pawn
                else:
                    kind = Pawn
                # The remainder is now the pattern for the starting position.
                pattern = AlgebraicLoc(command)
                # Now get a list of pieces which could move to the end
                # position.
                pieces = self.board.couldMove(end, self.turn)
                # Filter out ones that don't match the pattern.
                pieces = filter(lambda x, p = pattern: x.loc.match(p), pieces)
                # Filter out ones that aren't the right kind.
                if kind is not None:
                    pieces = filter(lambda x, k = kind: \
                                    x.__class__ == k, pieces)
                # If there's more than one choice left, it's ambiguous.
                if not pieces:
                    raise IllegalMoveError, "no legal moves"
                elif len(pieces) > 1:
                    raise AmbiguousMoveError, "multiple legal moves"
                piece = pieces[0]
                start = piece.loc
                # Test capture
                if takes:
                    capture = self.board.at(end)
                    if not capture:
                        hyp = self.board.clone()
                        hypPiece = hyp.get(start)
                        hypCapture = hypPiece.move(end, hyp)
                        if not hypCapture:
                            raise IllegalMoveError, "would not capture"
                # If we're a pawn in the final row, mark a promotion.
                if isinstance(piece, Pawn) and end.y in (0, 7):
                    if promote is None:
                        promote = Queen
                elif promote:    
                    raise IllegalMoveError, "pawn would not promote"
                if promote:
                    piece.request = promote
                # If we're supposed to check and don't, error.
                if isCheck and \
                   not self.board.wouldCheck(start, end, not self.turn):
                    raise IllegalMoveError, "would not check"
                # Done!
                return start, end
            except (IndexError, ValueError, TypeError, KeyError):
                raise ParseError, "error during parsing"

    def move(self, command):
        """Commit a move given by COMMAND and return a move indicating it."""
        start, end = self.disambiguate(command)
        move = Move(command, start, end)
        self.moves.append((start, end))
        move.piece = self.board.get(start)
        move.capture = move.piece.move(end, self.board)
        if self.checked() == (not self.turn):
            if self.checkmated() == (not self.turn):
                move.isCheckmate = 1
            else:
                move.isCheck = 1
        return move

    def checked(self):
        """Return who is in check or None."""
        if self.board.check(WHITE):
            return WHITE
        elif self.board.check(BLACK):
            return BLACK
        else:
            return None

    def checkmated(self):
        """Return which color has been checkmated or None."""
        if self.board.checkmate(WHITE):
            return WHITE
        elif self.board.checkmate(BLACK):
            return BLACK
        else:
            return None

    def ok(self):
        """Is the game done?"""
        return self.state == 'playing'
