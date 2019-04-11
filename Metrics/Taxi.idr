module Metrics.Taxi

import Relations
import Data.Fin
import Data.So

%default total

taxiSpace : {n : Nat} -> Type
taxiSpace {n} = (Fin n, Fin n)

taxi_rel : taxiSpace {n} -> taxiSpace {n} -> Type
taxi_rel (i,j) (i',j') = let i = finToInteger i
                             j = finToInteger j
                             i' = finToInteger i'
                             j' = finToInteger j' in
                             abs(i-i') + abs(j-j') = 1

unique_identity : {ty : Type} -> {x,y : ty} -> (r : x = y) -> (r' : x = y) -> (r = r')
unique_identity Refl Refl = Refl

taxi_elim : (r : taxi_rel x y) -> (r' : taxi_rel x y) -> (r = r')
taxi_elim {x=(i,j)} {y=(i',j')} = unique_identity

taxi_dec : (x : taxiSpace {n}) -> (y : taxiSpace {n}) -> Dec (taxi_rel x y)
taxi_dec (i,j) (i',j') = let i = finToInteger i
                             j = finToInteger j
                             i' = finToInteger i'
                             j' = finToInteger j' in
                             decEq (abs(i-i') + abs(j-j')) 1

abs_lemma_1 : {i : Integer} -> So (i < 0) -> abs i = i

abs_lemma_2 : {i : Integer} -> abs i = abs (-i)
abs_lemma_2 {i} = if i < 0 then ?abs_lemma_1_rhs
                           else ?abs_lemma_1_rhs_2

abs_lemma_3 : {i,j : Integer} -> abs(i-j) = abs(j-i)
abs_lemma_3 = ?abs_lemma_rhs

taxi_sym : taxi_rel x y -> taxi_rel y x
taxi_sym {x=(i,j)} {y=(i',j')} r = ?taxi_sym_rhs1
