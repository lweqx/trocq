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

Module Level0.
Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;
}.
End Level0.
(* It seems like `::` only makes the typeclass locally available? *)
#[global] Existing Instance Level0.level0.

Module Level1.
Class SetoidTower@{i} (A: Type@{i}) := {
  level0 :: Setoid A ;

  level1 :: forall {a b: A}, Setoid (a ~ b) ;
  symmetry1_involutive : forall (a b: A) (r: a ~ b),
    (r^)^ ~ r ;
  symmetry1_preserves_rel : forall (a b: A) (r1 r2: a ~ b),
    r1 ~ r2 -> r1^ ~ r2^
}.
End Level1.
#[global] Existing Instance Level1.level0.
#[global] Existing Instance Level1.level1.

Module Level2.
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
End Level2.
#[global] Existing Instance Level2.level0.
#[global] Existing Instance Level2.level1.
#[global] Existing Instance Level2.level2.

Module Level3.
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
End Level3.
#[global] Existing Instance Level3.level0.
#[global] Existing Instance Level3.level1.
#[global] Existing Instance Level3.level2.
#[global] Existing Instance Level3.level3.

Definition forget_tower_1_to_0 {A: Type} :
  Level1.SetoidTower A -> Level0.SetoidTower A.
Proof.
  move=> [level0 _ _ _].
  constructor.
  exact level0.
Defined.
#[global] Existing Instance forget_tower_1_to_0.

Definition forget_tower_2_to_1 {A: Type} :
  Level2.SetoidTower A -> Level1.SetoidTower A.
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
  forall (tower2: Level2.SetoidTower A), Level1.SetoidTower (a ~ a').
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
  Level3.SetoidTower A -> Level2.SetoidTower A.
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
  forall (tower3: Level3.SetoidTower A), Level2.SetoidTower (a ~ a').
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

Register Level0.SetoidTower as trocq.setoid_tower0.
Register Level0.level0 as trocq.setoid_tower0_level0.

Register Level1.SetoidTower as trocq.setoid_tower1.
Register Level1.level0 as trocq.setoid_tower1_level0.
Register Level1.level1 as trocq.setoid_tower1_level1.
Register Level1.symmetry1_involutive as trocq.setoid_tower1_symmetry1_involutive.
Register Level1.symmetry1_preserves_rel as trocq.setoid_tower1_symmetry1_preserves_rel.

Register Level2.SetoidTower as trocq.setoid_tower2.
Register Level2.level0 as trocq.setoid_tower2_level0.
Register Level2.level1 as trocq.setoid_tower2_level1.
Register Level2.level2 as trocq.setoid_tower2_level2.
Register Level2.symmetry1_involutive as trocq.setoid_tower2_symmetry1_involutive.
Register Level2.symmetry2_involutive as trocq.setoid_tower2_symmetry2_involutive.
Register Level2.symmetry1_preserves_rel as trocq.setoid_tower2_symmetry1_preserves_rel.
Register Level2.symmetry2_preserves_rel as trocq.setoid_tower2_symmetry2_preserves_rel.
Register Level2.symmetry1_preserves_rel_preserves_rel as trocq.setoid_tower2_symmetry1_preserves_rel_preserves_rel.

Register Level3.SetoidTower as trocq.setoid_tower3.
Register Level3.level0 as trocq.setoid_tower3_level0.
Register Level3.level1 as trocq.setoid_tower3_level1.
Register Level3.level2 as trocq.setoid_tower3_level2.
Register Level3.level3 as trocq.setoid_tower3_level3.
Register Level3.symmetry1_involutive as trocq.setoid_tower3_symmetry1_involutive.
Register Level3.symmetry2_involutive as trocq.setoid_tower3_symmetry2_involutive.
Register Level3.symmetry3_involutive as trocq.setoid_tower3_symmetry3_involutive.
Register Level3.symmetry1_preserves_rel as trocq.setoid_tower3_symmetry1_preserves_rel.
Register Level3.symmetry2_preserves_rel as trocq.setoid_tower3_symmetry2_preserves_rel.
Register Level3.symmetry3_preserves_rel as trocq.setoid_tower3_symmetry3_preserves_rel.
Register Level3.symmetry1_preserves_rel_preserves_rel as trocq.setoid_tower3_symmetry1_preserves_rel_preserves_rel.
Register Level3.symmetry2_preserves_rel_preserves_rel as trocq.setoid_tower3_symmetry2_preserves_rel_preserves_rel.

(* Morphism of setoids *)
Record MorphismSetoid@{i j} (A: Type@{i}) (B: Type@{j}) `{Level2.SetoidTower A} `{Level2.SetoidTower B} := {
  f :> A -> B ;
  preserves_rel : forall {a a'},
    a ~ a' -> f a ~ f a' ;
  preserves_rel_preserves_rel : forall {a a'} {aR aR': a ~ a'},
    aR ~ aR' -> preserves_rel aR ~ preserves_rel aR'
}.
Arguments preserves_rel {_ _ _ _} _ {a a'}.
Arguments preserves_rel_preserves_rel {_ _ _ _} _ {a a' aR aR'}.

Notation "A ~> B" := (MorphismSetoid A B) (at level 99, right associativity, B at level 200).

Definition id_morphism (A: Type) `{Level2.SetoidTower A} : A ~> A.
Proof. by exists idmap (fun _ _ => idmap). Defined.

Definition inverse_morphism (A: Type) `{Level3.SetoidTower A} (a b: A) :
  (a ~ b) ~> (b ~ a).
Proof.
  unshelve eexists.
  - move=> r ; by symmetry.
  - move=> aR aR' aRR /=.
    by apply Level3.symmetry1_preserves_rel.
  - move=> aR aR' aRR aRR' aRRR /=.
    by apply Level3.symmetry1_preserves_rel_preserves_rel.
Defined.
