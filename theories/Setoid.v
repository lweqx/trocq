From Coq Require Import ssreflect.
From HoTT Require Import HoTT.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Polymorphic Inductive Cumulativity.

Class Setoid@{i} (A: Type@{i}) := {
  equiv : A -> A -> Type@{i} ;
  #[global] Setoid_Reflexive :: Reflexive equiv ;
  #[global] Setoid_Symmetric :: Symmetric equiv ;
  symmetry : forall {x y}, equiv x y -> equiv y x ;
  symmetry_involutive {x y} (r: equiv x y): symmetry (symmetry r) = r
}.

#[global] Existing Instance Setoid_Reflexive.
#[global] Existing Instance Setoid_Symmetric.

Notation " x ~ y " := (equiv x y) (at level 70, no associativity) : type_scope.
Notation " x ^ " := (symmetry x) : type_scope.
