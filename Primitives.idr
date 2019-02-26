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
  setTileColor : Color -> (row : Fin size) -> (col : Fin size) -> ty

SimpleBoardState : Board size -> Type
SimpleBoardState (MkBoard size) = Vect size (Vect size Color)
    
-- TODO: Figure out why the commented out code throws a type error
BoardState size (MkBoard size) (SimpleBoardState (MkBoard size)) where
  emptyBoard = ?hole1 -- replicate size (replicate size Empty)
  getTileColor bs row col = ?hole2
  setTileColor c row col = ?hole3

