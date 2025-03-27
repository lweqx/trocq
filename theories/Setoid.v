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

Class SetoidTower0@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;
}.

Class SetoidTower1@{i} (A: Type@{i}) := {
  tower0 :: SetoidTower0 A ;

  level1 :: forall {a b: A}, Setoid (a ~ b) ;
  symmetry1_involutive : forall {a b: A} {r: a ~ b},
    (r^)^ ~ r ;
  symmetry1_preserves_rel : forall {a b: A} {r1 r2: a ~ b},
    r1 ~ r2 -> r1^ ~ r2^
}.

Class SetoidTower2@{i} (A: Type@{i}) := {
  tower1 :: SetoidTower1 A ;

  level2 :: forall {a b: A} {r1 r2: a ~ b}, Setoid (r1 ~ r2) ;
  symmetry2_involutive : forall {a b: A} {r1 r2: a ~ b} {u: r1 ~ r2},
    (u^)^ ~ u ;
  symmetry2_preserves_rel : forall {a b: A} {r1 r2 : a ~ b} {u1 u2: r1 ~ r2},
    u1 ~ u2 -> u1^ ~ u2^ ;
  symmetry1_preserves_rel_preserves_rel : forall {a b: A} {r1 r2: a ~ b} {u1 u2: r1 ~ r2},
    u1 ~ u2 -> symmetry1_preserves_rel u1 ~ symmetry1_preserves_rel u2
}.

Class SetoidTower3@{i} (A: Type@{i}) := {
  tower2 :: SetoidTower2 A ;

  level3 :: forall {a b: A} {r1 r2: a ~ b} {u1 u2: r1 ~ r2},
    Setoid (u1 ~ u2) ;
  symmetry3_involutive : forall {a b: A} {r1 r2: a ~ b} {u1 u2: r1 ~ r2} {v: u1 ~ u2},
    (v^)^ ~ v ;
  symmetry3_preserves_rel : forall {a b: A} {r1 r2 : a ~ b} {u1 u2: r1 ~ r2} {v1 v2: u1 ~ u2},
    v1 ~ v2 -> v1^ ~ v2^ ;
  symmetry2_preserves_rel_preserves_rel : forall {a b: A} {r1 r2: a ~ b} {u1 u2: r1 ~ r2} {v1 v2: u1 ~ u2},
    v1 ~ v2 -> symmetry2_preserves_rel v1 ~ symmetry2_preserves_rel v2 ;
}.

#[global]
Instance tower_2_to_1_rel@{i} {A: Type@{i}} {a a': A}:
  forall `{SetoidTower2 A}, SetoidTower1 (a ~ a').
Proof.
  move=> [
    tower1
    level2 symmetry2_involutive symmetry1_preserves_rel symmetry2_preserves_rel_preserves_rel
  ].

  unshelve eexists.
  - exists ; exact level1.
  - apply level2.
  - apply (symmetry2_involutive _ _).
  - apply symmetry1_preserves_rel.
Defined.

#[global]
Instance tower_3_to_2_rel@{i} {A: Type@{i}} {a a': A}:
  forall `{SetoidTower3 A}, SetoidTower2 (a ~ a').
Proof.
  move=> [
    tower2
    level3 symmetry3_involutive symmetry3_preserves_rel symmetry2_preserves_rel_preserves_rel
  ].

  unshelve eexists.
  - apply symmetry3_involutive.
  - apply symmetry3_preserves_rel.
  - apply symmetry2_preserves_rel_preserves_rel.
Defined.

Register SetoidTower0 as trocq.setoid_tower0.
Register level0 as trocq.setoid_tower_level0.

Register SetoidTower1 as trocq.setoid_tower1.
Register tower0 as trocq.setoid_tower_tower0.
Register level1 as trocq.setoid_tower_level1.
Register symmetry1_involutive as trocq.setoid_tower_symmetry1_involutive.
Register symmetry1_preserves_rel as trocq.setoid_tower_symmetry1_preserves_rel.

Register SetoidTower2 as trocq.setoid_tower2.
Register tower1 as trocq.setoid_tower_tower1.
Register level2 as trocq.setoid_tower_level2.
Register symmetry2_involutive as trocq.setoid_tower_symmetry2_involutive.
Register symmetry2_preserves_rel as trocq.setoid_tower_symmetry2_preserves_rel.
Register symmetry1_preserves_rel_preserves_rel as trocq.setoid_tower_symmetry1_preserves_rel_preserves_rel.

Register SetoidTower3 as trocq.setoid_tower3.
Register tower2 as trocq.setoid_tower_tower2.
Register level3 as trocq.setoid_tower_level3.
Register symmetry3_involutive as trocq.setoid_tower_symmetry3_involutive.
Register symmetry3_preserves_rel as trocq.setoid_tower_symmetry3_preserves_rel.
Register symmetry2_preserves_rel_preserves_rel as trocq.setoid_tower_symmetry2_preserves_rel_preserves_rel.

(* Morphism of setoids *)
Record MorphismSetoid@{i j} (A: Type@{i}) (B: Type@{j}) `{SetoidTower2 A} `{SetoidTower2 B} := {
  f :> A -> B ;
  preserves_rel : forall {a a'},
    a ~ a' -> f a ~ f a' ;
  preserves_rel_preserves_rel : forall {a a'} {aR aR': a ~ a'},
    aR ~ aR' -> preserves_rel aR ~ preserves_rel aR'
}.
Arguments preserves_rel {_ _ _ _} _ {a a'}.
Arguments preserves_rel_preserves_rel {_ _ _ _} _ {a a' aR aR'}.

Notation "A ~> B" := (MorphismSetoid A B) (at level 99, right associativity, B at level 200).

Definition id_morphism (A: Type) `{SetoidTower2 A} : A ~> A.
Proof. by exists idmap (fun _ _ => idmap). Defined.

Definition inverse_morphism (A: Type) `{SetoidTower3 A} (a b: A) :
  (a ~ b) ~> (b ~ a).
Proof.
  unshelve eexists.
  - move=> r ; by symmetry.
  - move=> aR aR' aRR /=.
    by apply symmetry1_preserves_rel.
  - move=> aR aR' aRR aRR' aRRR /=.
    by apply symmetry1_preserves_rel_preserves_rel.
Defined.
