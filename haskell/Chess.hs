module Chess where

type Rank = Int

data Square = A Rank | B Rank | C Rank | D Rank | E Rank | G Rank | H Rank
            deriving Show

data Unit = White Piece Square
          | Black Piece Square
            deriving Show

data Piece = King
           | Queen
           | Rook
           | Bishop
           | Knight
           | Pawn
             deriving Show


data Unit = Piece | Pawn


instance Board = [[Rk, Nk, Bk, Qk, Kk, Bk, Nk, Rk ]]