module Generics

%default total
%access public export

--interface Relation (rel : ty -> ty -> Type) where
--  elim : (r : rel x y) -> (r' : rel x y) -> (r = r')
--
--interface Relation rel => DecidableRelation (rel : ty -> ty -> Type) where
--  decRel : (x : ty) -> (y : ty) -> Dec (rel x y)
--
--interface Relation rel => SymmetricRelation (rel : ty -> ty -> Type) where
--  sym : rel x y -> rel y x
--
--interface Relation rel => IrreflexiveRelation (rel : ty -> ty -> Type) where
--  irrefl : rel x x -> Void
--
--interface (SymmetricRelation rel, IrreflexiveRelation rel, DecidableRelation rel) => SymIrrDecRel (rel : ty -> ty -> Type) where

interface SymmetricFunction (f : ty -> ty -> ty') where
  sym : {x : ty} -> {y : ty} -> (f x y = f y x)

interface IrreflexiveRelation (rel : ty -> ty -> Bool) where
  irrefl : (rel x x = False)

interface (SymmetricFunction rel, IrreflexiveRelation rel) => SymmetricIrreflexiveRelation (rel : ty -> ty -> Bool) where
