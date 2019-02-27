module Primitives

import Data.Fin
import Data.Vect

%default total

data Color = Black | White | Empty

data Board : Nat -> Type where
  MkBoard : (size : Nat) -> Board size

interface BoardState (size : Nat) (board : Board size) ty where
  emptyBoard : ty
  getTileColor : ty -> (row : Fin size) -> (col : Fin size) -> Color
  setTileColor : ty -> Color -> (row : Fin size) -> (col : Fin size) -> ty

-- Standard implementation (TODO: Move this somewhere else)
SimpleBoardState : Board size -> Type
SimpleBoardState (MkBoard size) = Vect size (Vect size Color)
    
BoardState size (MkBoard size) (SimpleBoardState (MkBoard size)) where
  emptyBoard {size} = replicate size (replicate size Empty)
  getTileColor bs row col = index row (index col bs)
  setTileColor bs x row col = updateAt row (replaceAt col x) bs

