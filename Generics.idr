module Generics

%default total
%access public export

interface SymmetricFunction (f : ty -> ty -> ty') where
  sym : {x : ty} -> {y : ty} -> (f x y = f y x)

interface IrreflexiveRelation (rel : ty -> ty -> Bool) where
  irrefl : (rel x x = False)

interface (SymmetricFunction rel, IrreflexiveRelation rel) => SymmetricIrreflexiveRelation (rel : ty -> ty -> Bool) where
