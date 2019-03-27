module Generics

%default total
%access public export

RelationOn : Type -> Type
RelationOn ty = ty -> ty -> Type

interface Relation (rel : ty -> ty -> Type) where
  elim : (r : rel x y) -> (r' : rel x y) -> (r = r')

interface Relation rel => SymmetricRelation (rel : ty -> ty -> Type) where
  sym : rel x y -> rel y x

interface Relation rel => IrreflexiveRelation (rel : ty -> ty -> Type) where
  irrefl : rel x x -> Void

SymmIrreflRelOn : Type -> Type
SymmIrreflRelOn ty = Subset (ty -> ty -> Type) (\rel => (SymmetricRelation rel, IrreflexiveRelation rel))
