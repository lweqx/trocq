From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
From elpi Require Import elpi.

From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Polymorphic Inductive Cumulativity.

Class Setoid@{i} (A: Type@{i}) := {
  equiv : A -> A -> Type@{i} ;
  #[global] Setoid_Reflexive :: Reflexive equiv ;
  #[global] Setoid_Symmetric :: Symmetric equiv ;
  #[global] Setoid_Transitive :: Transitive equiv
}.

Notation " x ~ y " := (equiv x y) (at level 70, no associativity) : type_scope.
Notation " x ^ " := (Setoid_Symmetric _ _ x) : type_scope.
Notation " f =~= g " := (forall x, f x ~ g x) (at level 70, no associativity).

Register Setoid as trocq.setoid.
Register equiv as trocq.equiv.

Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;
  level1 :: forall {a b: A}, Setoid (a ~ b) ;

  symmetry1_involutive : forall (a b: A) (r: a ~ b),
    (r^)^ ~ r ;
  symmetry1_preserves_rel : forall (a b: A) (r1 r2 : a ~ b),
    r1 ~ r2 -> r1^ ~ r2^
}.

Register SetoidTower as trocq.setoid_tower.
Register level0 as trocq.setoid_tower_level0.
Register level1 as trocq.setoid_tower_level1.

(* Morphism of setoids *)
Record MorphismSetoid@{i j} (A: Type@{i}) (B: Type@{j}) `{Setoid A} `{Setoid B} := {
  f :> A -> B ;
  preserves_rel : forall a a', a ~ a' -> f a ~ f a'
}.

Notation "A ~> B" := (MorphismSetoid A B) (at level 99, right associativity, B at level 200).

Definition id_morphism (A: Type) `{Setoid A} : A ~> A.
Proof. by exists idmap. Defined.

Definition inverse_morphism (A: Type) `{SetoidTower A} (a b: A) : (a ~ b) ~> (b ~ a).
Proof.
  unshelve eexists.
  - move=> r ; by symmetry.
  - by apply symmetry1_preserves_rel.
Defined.
