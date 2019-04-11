module Primitives

import Data.Fin
import Data.Vect
import Generics

%default total

-- This module should specify the basic primitives of Go in a rule-agnostic way, that is,
-- for each of the common rulesets (Japanese, Chinese, logical, ...) there should be a different
-- type, but each of these rulesets/types should be defined in terms of the basic notions introduced
-- in this module.

--------------------------------------------------------------------------------
-- Rule 0
--------------------------------------------------------------------------------

||| Abstract game boards given by a type of *points* and a symmetric and irreflexive
||| relation of *adjacency* on it
record Board where
  constructor MkBoard
  ||| the points of the board
  points : Type
  ||| the symmetric and irreflexive relation on points that defines adjancency
  adjRel : DiscreteMetricOn points

--standardGoBoard : (n : Nat) -> Board
--standardGoBoard n = MkBoard (Fin n, Fin n) taxi_adj taxi_adj_pf where
--  taxi_adj : (Fin n, Fin n) -> (Fin n, Fin n) -> Bool
--  taxi_adj (x, y) (x', y') = let i = finToInteger x
--                                 j = finToInteger y
--                                 i' = finToInteger x'
--                                 j' = finToInteger y' in
--                                 abs (i-i') + abs (j-j') == 1
--  SymmetricFunction taxi_adj where
--    sym = ?hole1
--  IrreflexiveRelation taxi_adj where
--    irrefl = ?hole2
--  taxi_adj_pf : SymmetricIrreflexiveRelation taxi_adj
--  taxi_adj_pf = ?taxi_adj_pf_rhs

data Color = Black | White -- TODO: Instead of having an "Empty" color, I use 
                           -- the type Maybe Color, with Nothing corresponding
                           -- to an empty tile. Is that reasonable?

interface BoardState (board : Board) ty where
  emptyBoard : ty
  getTileColor : ty -> points board -> Maybe Color
  setTileColor : ty -> (Maybe Color) -> points board -> ty
