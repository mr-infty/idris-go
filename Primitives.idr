module Primitives

import Data.Fin

%default total

data Color = Black | White | Empty

data Board : Nat -> Type where
  MkBoard : (size : Nat) -> Board size

data BoardState : (Board size) -> Type where
  EmptyBoard : BoardState _

tileColor : {board : Board size} -> BoardState board -> (row : Fin size) -> (col : Fin size) -> Color
