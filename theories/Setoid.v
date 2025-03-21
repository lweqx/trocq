From Coq Require Import ssreflect.
From HoTT Require Import HoTT.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Polymorphic Inductive Cumulativity.

Class Setoid@{i} (A: Type@{i}) := {
  equiv : A -> A -> Type@{i} ;
  #[global] Setoid_Reflexive :: Reflexive equiv ;
  #[global] Setoid_Symmetric :: Symmetric equiv ;
  symmetry_involutive {x y} (r: equiv x y):
    (* TODO: Can this be made prettier? *)
    Setoid_Symmetric _ _ (Setoid_Symmetric _ _ r) = r ;
  #[global] Setoid_Transitive :: Transitive equiv
}.

#[global] Existing Instance Setoid_Reflexive.
#[global] Existing Instance Setoid_Symmetric.
#[global] Existing Instance Setoid_Transitive.

Notation " x ~ y " := (equiv x y) (at level 70, no associativity) : type_scope.
Notation " x ^ " := (Setoid_Symmetric _ _ x) : type_scope.
Notation " f =~= g " := (forall x, f x ~ g x) (at level 70, no associativity).

(* Morphism of setoids *)
Record MorphismSetoid@{i j} (A: Type@{i}) (B: Type@{j}) `{Setoid A} `{Setoid B} := {
  f :> A -> B ;
  preserves_rel : forall a a', a ~ a' -> f a ~ f a'
}.
