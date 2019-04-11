module Relations

%default total
%access public export

RelationOn : Type -> Type
RelationOn ty = ty -> ty -> Type

data Relation : RelationOn ty -> Type where
  HasElim : {rel : RelationOn ty} ->
            (elim : (r : rel x y) -> (r' : rel x y) -> (r = r')) ->
            Relation rel

data DecidableRelation : RelationOn ty -> Type where
  HasDec : Relation rel =>
           (decRel : (x : ty) -> (y : ty) -> Dec (rel x y)) ->
           DecidableRelation rel

data SymmetricRelation : RelationOn ty -> Type where
  HasSym : Relation rel =>
           (sym : rel x y -> rel y x) ->
           SymmetricRelation rel

data IrreflexiveRelation : RelationOn ty -> Type where
  HasIrrefl : Relation rel =>
              (irrefl : rel x x -> Void) ->
              IrreflexiveRelation rel

data DiscreteMetric : RelationOn ty -> Type where
  MkDiscreteMetric : DecidableRelation rel =>
                     SymmetricRelation rel =>
                     IrreflexiveRelation rel =>
                     DiscreteMetric rel
