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

Module Height0.
Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;
}.
End Height0.
(* It seems like `::` only makes the typeclass locally available? *)
#[global] Existing Instance Height0.level0.

Module Height1.
Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;

  level1 :: forall {a b: A}, Setoid (a ~ b) ;
  symmetry1_involutive : forall (a b: A) (r: a ~ b),
    (r^)^ ~ r ;
  symmetry1_preserves_rel : forall (a b: A) (r1 r2: a ~ b),
    r1 ~ r2 -> r1^ ~ r2^
}.
End Height1.
#[global] Existing Instance Height1.level0.
#[global] Existing Instance Height1.level1.

Module Height2.
Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;

  level1 :: forall {a b: A}, Setoid (a ~ b) ;
  symmetry1_involutive : forall (a b: A) (r: a ~ b),
    (r^)^ ~ r ;
  symmetry1_preserves_rel : forall (a b: A) (r1 r2 : a ~ b),
    r1 ~ r2 -> r1^ ~ r2^ ;

  level2 :: forall {a b: A} {r1 r2: a ~ b}, Setoid (r1 ~ r2) ;
  symmetry2_involutive : forall (a b: A) (r1 r2: a ~ b) (u: r1 ~ r2),
    (u^)^ ~ u ;
  symmetry2_preserves_rel : forall (a b: A) (r1 r2 : a ~ b) (u1 u2: r1 ~ r2),
    u1 ~ u2 -> u1^ ~ u2^ ;
  symmetry1_preserves_rel_preserves_rel : forall (a b: A) (r1 r2: a ~ b) (u1 u2: r1 ~ r2),
    u1 ~ u2 -> symmetry1_preserves_rel a b r1 r2 u1 ~ symmetry1_preserves_rel a b r1 r2 u2
}.
End Height2.
#[global] Existing Instance Height2.level0.
#[global] Existing Instance Height2.level1.
#[global] Existing Instance Height2.level2.

Module Height3.
Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;

  level1 :: forall {a b: A}, Setoid (a ~ b) ;
  symmetry1_involutive : forall (a b: A) (r: a ~ b),
    (r^)^ ~ r ;
  symmetry1_preserves_rel : forall {a b: A} {r1 r2 : a ~ b},
    r1 ~ r2 -> r1^ ~ r2^ ;

  level2 :: forall {a b: A} {r1 r2: a ~ b}, Setoid (r1 ~ r2) ;
  symmetry2_involutive : forall (a b: A) (r1 r2: a ~ b) (u: r1 ~ r2),
    (u^)^ ~ u ;
  symmetry2_preserves_rel : forall {a b: A} {r1 r2 : a ~ b} {u1 u2: r1 ~ r2},
    u1 ~ u2 -> u1^ ~ u2^ ;
  symmetry1_preserves_rel_preserves_rel : forall (a b: A) (r1 r2: a ~ b) (u1 u2: r1 ~ r2),
    u1 ~ u2 -> symmetry1_preserves_rel u1 ~ symmetry1_preserves_rel u2 ;

  level3 :: forall {a b: A} {r1 r2: a ~ b} {u1 u2: r1 ~ r2}, Setoid (u1 ~ u2) ;
  symmetry3_involutive : forall (a b: A) (r1 r2: a ~ b) (u1 u2: r1 ~ r2) (v: u1 ~ u2),
    (v^)^ ~ v ;
  symmetry3_preserves_rel : forall (a b: A) (r1 r2 : a ~ b) (u1 u2: r1 ~ r2) (v1 v2: u1 ~ u2),
    v1 ~ v2 -> v1^ ~ v2^ ;
  symmetry2_preserves_rel_preserves_rel : forall {a b: A} {r1 r2: a ~ b} {u1 u2: r1 ~ r2} {v1 v2: u1 ~ u2},
    v1 ~ v2 -> symmetry2_preserves_rel v1 ~ symmetry2_preserves_rel v2 ;
}.
End Height3.
#[global] Existing Instance Height3.level0.
#[global] Existing Instance Height3.level1.
#[global] Existing Instance Height3.level2.
#[global] Existing Instance Height3.level3.

Definition forget_tower_1_to_0 {A: Type} :
  Height1.SetoidTower A -> Height0.SetoidTower A.
Proof.
  move=> [level0 _ _ _].
  constructor.
  exact level0.
Defined.
#[global] Existing Instance forget_tower_1_to_0.

Definition forget_tower_2_to_1 {A: Type} :
  Height2.SetoidTower A -> Height1.SetoidTower A.
Proof.
  move=> [
    level0
    level1 symmetry1_involutive symmetry1_preserves_rel
    _ _ _ _
  ].
  by econstructor.
Defined.
#[global] Existing Instance forget_tower_2_to_1.

Definition tower_2_to_1_rel {A: Type} {a a': A}:
  forall (tower2: Height2.SetoidTower A), Height1.SetoidTower (a ~ a').
Proof.
  move=> [
    level0
    level1 symmetry1_involutive symmetry1_preserves_rel
    level2 symmetry2_involutive symmetry2_preserves_rel symmetry1_preserves_rel_preserves_rel
  ].
  econstructor.
  - apply symmetry2_involutive.
  - apply symmetry2_preserves_rel.
Defined.
#[global] Existing Instance tower_2_to_1_rel.

Definition forget_tower_3_to_2 {A: Type} :
  Height3.SetoidTower A -> Height2.SetoidTower A.
Proof.
  move=> [
    level0
    level1 symmetry1_involutive symmetry1_preserves_rel
    level2 symmetry2_involutive symmetry2_preserves_rel symmetry1_preserves_rel_preserves_rel
    _ _ _ _
  ].
  econstructor ; trivial.
  (* TODO: why isn't Rocq able to also trivially solve the constructor below? *)
  exact symmetry1_preserves_rel_preserves_rel.
Defined.
#[global] Existing Instance forget_tower_3_to_2.

Definition tower_3_to_2_rel {A: Type} (a a': A):
  forall (tower3: Height3.SetoidTower A), Height2.SetoidTower (a ~ a').
Proof.
  move=> [
    level0
    level1 symmetry1_involutive symmetry1_preserves_rel
    level2 symmetry2_involutive symmetry2_preserves_rel symmetry1_preserves_rel_preserves_rel
    level3 symmetry3_involutive symmetry3_preserves_rel symmetry2_preserves_rel_preserves_rel
  ].
  econstructor.
  - apply symmetry2_involutive.
  - apply symmetry3_involutive.
  - apply symmetry3_preserves_rel.
  - apply symmetry2_preserves_rel_preserves_rel.
Defined.
#[global] Existing Instance tower_3_to_2_rel.

Register Height0.SetoidTower as trocq.setoid_tower0.
Register Height0.level0 as trocq.setoid_tower0_level0.

Register Height1.SetoidTower as trocq.setoid_tower1.
Register Height1.level0 as trocq.setoid_tower1_level0.
Register Height1.level1 as trocq.setoid_tower1_level1.
Register Height1.symmetry1_involutive as trocq.setoid_tower1_symmetry1_involutive.
Register Height1.symmetry1_preserves_rel as trocq.setoid_tower1_symmetry1_preserves_rel.

Register Height2.SetoidTower as trocq.setoid_tower2.
Register Height2.level0 as trocq.setoid_tower2_level0.
Register Height2.level1 as trocq.setoid_tower2_level1.
Register Height2.level2 as trocq.setoid_tower2_level2.
Register Height2.symmetry1_involutive as trocq.setoid_tower2_symmetry1_involutive.
Register Height2.symmetry2_involutive as trocq.setoid_tower2_symmetry2_involutive.
Register Height2.symmetry1_preserves_rel as trocq.setoid_tower2_symmetry1_preserves_rel.
Register Height2.symmetry2_preserves_rel as trocq.setoid_tower2_symmetry2_preserves_rel.
Register Height2.symmetry1_preserves_rel_preserves_rel as trocq.setoid_tower2_symmetry1_preserves_rel_preserves_rel.

Register Height3.SetoidTower as trocq.setoid_tower3.
Register Height3.level0 as trocq.setoid_tower3_level0.
Register Height3.level1 as trocq.setoid_tower3_level1.
Register Height3.level2 as trocq.setoid_tower3_level2.
Register Height3.level3 as trocq.setoid_tower3_level3.
Register Height3.symmetry1_involutive as trocq.setoid_tower3_symmetry1_involutive.
Register Height3.symmetry2_involutive as trocq.setoid_tower3_symmetry2_involutive.
Register Height3.symmetry3_involutive as trocq.setoid_tower3_symmetry3_involutive.
Register Height3.symmetry1_preserves_rel as trocq.setoid_tower3_symmetry1_preserves_rel.
Register Height3.symmetry2_preserves_rel as trocq.setoid_tower3_symmetry2_preserves_rel.
Register Height3.symmetry3_preserves_rel as trocq.setoid_tower3_symmetry3_preserves_rel.
Register Height3.symmetry1_preserves_rel_preserves_rel as trocq.setoid_tower3_symmetry1_preserves_rel_preserves_rel.
Register Height3.symmetry2_preserves_rel_preserves_rel as trocq.setoid_tower3_symmetry2_preserves_rel_preserves_rel.

(* Morphism of setoids *)
Record MorphismSetoid@{i j} (A: Type@{i}) (B: Type@{j}) `{Height2.SetoidTower A} `{Height2.SetoidTower B} := {
  f :> A -> B ;
  preserves_rel : forall {a a'},
    a ~ a' -> f a ~ f a' ;
  preserves_rel_preserves_rel : forall {a a'} {aR aR': a ~ a'},
    aR ~ aR' -> preserves_rel aR ~ preserves_rel aR'
}.
Arguments preserves_rel {_ _ _ _} _ {a a'}.
Arguments preserves_rel_preserves_rel {_ _ _ _} _ {a a' aR aR'}.

Notation "A ~> B" := (MorphismSetoid A B) (at level 99, right associativity, B at level 200).

Definition id_morphism (A: Type) `{Height2.SetoidTower A} : A ~> A.
Proof. by exists idmap (fun _ _ => idmap). Defined.

Definition inverse_morphism (A: Type) `{Height3.SetoidTower A} (a b: A) :
  (a ~ b) ~> (b ~ a).
Proof.
  unshelve eexists.
  - move=> r ; by symmetry.
  - move=> aR aR' aRR /=.
    by apply Height3.symmetry1_preserves_rel.
  - move=> aR aR' aRR aRR' aRRR /=.
    by apply Height3.symmetry1_preserves_rel_preserves_rel.
Defined.
