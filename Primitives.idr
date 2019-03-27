module Primitives

import Data.Fin
import Data.Vect
import Generics

%default total

-- This module should specify the basic primitives of Go in a rule-agnostic way, that is,
-- for each of the common rulesets (Japanese, Chinese, logical, ...) there should be a different
-- type, but each of these rulesets/types should be defined in terms of the basic notions introduced
-- in this module.

||| Abstract game boards given by a type of *points* and a symmetric and irreflexive
||| relation of *adjacency* on it
record Board' where
  constructor MkBoard'
  ||| the points of the board
  points : Type
  ||| the symmetric and irreflexive relation on points that defines adjancency
  adjRel : SymmIrreflRelOn points

data Color = Black | White -- TODO: Instead of having an "Empty" color, I use 
                           -- the type Maybe Color, with Nothing corresponding
                           -- to an empty tile. Is that reasonable?

data Board : Nat -> Type where
  MkBoard : (size : Nat) -> Board size

||| Points on a board.
||| @ board the board on which the point lies
record Point (board : Board size) where
  constructor MkPoint
  row : Fin size
  col : Fin size

||| Propositional type describing when two points are adjacent.
data Adjacent : Point board -> Point board -> Type where
  LiesNorth : {row : Fin k} ->
              {col : Fin (S k)} ->
              Adjacent (MkPoint (FS row) col)
                       (MkPoint (weaken row) col)
  LiesWest : {row : Fin (S k)} ->
             {col : Fin k} ->
             Adjacent (MkPoint row (weaken col))
                      (MkPoint row (FS col))
  LiesSouth : {row : Fin k} ->
              {col : Fin (S k)} ->
              Adjacent (MkPoint (weaken row) col)
                       (MkPoint (FS row) col)
  LiesEast : {row : Fin (S k)} ->
             {col : Fin k} ->
             Adjacent (MkPoint row (weaken col))
                      (MkPoint row (FS col))

interface BoardState (size : Nat) (board : Board size) ty where
  emptyBoard : ty
  getTileColor : ty -> (row : Fin size) -> (col : Fin size) -> Maybe Color
  setTileColor : ty -> (Maybe Color) -> (row : Fin size) -> (col : Fin size) -> ty

-- Standard implementation (TODO: Move this somewhere else)
SimpleBoardState : Board size -> Type
SimpleBoardState (MkBoard size) = Vect size (Vect size (Maybe Color))
    
BoardState size (MkBoard size) (SimpleBoardState (MkBoard size)) where
  emptyBoard {size} = replicate size (replicate size Nothing)
  getTileColor bs row col = index row (index col bs)
  setTileColor bs x row col = updateAt row (replaceAt col x) bs
