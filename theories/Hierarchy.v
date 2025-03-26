(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
Require Import Setoid Database.
From elpi Require Import elpi.

From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.
From Trocq.Elpi Extra Dependency "util.elpi" as util.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Polymorphic Inductive Cumulativity.

(* Coq representation of the hierarchy *)
Inductive map_class : Set := map0 | map1 | map2a | map2b | map3 | map4.

Register map0 as trocq.indc_map0.
Register map1 as trocq.indc_map1.
Register map2a as trocq.indc_map2a.
Register map2b as trocq.indc_map2b.
Register map3 as trocq.indc_map3.
Register map4 as trocq.indc_map4.

Definition sym_rel@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) :=
  fun b a => R a b.
Register sym_rel as trocq.sym_rel.

(*************************)
(* Parametricity Classes *)
(*************************)

(* first unilateral witnesses describing one side of the structure given to a relation *)

Module Map0.
Set Warnings "-non-primitive-record".
Record Has@{i}
  {A B : Type@{i}} `{SetoidTower@{i} A} `{SetoidTower@{i} B}
  (R : A -> B -> Type@{i}) `{forall a b, Setoid@{i} (R a b)} :=
BuildHas {
}.
End Map0.

Module Map1.
Record Has@{i}
  {A B : Type@{i}} `{SetoidTower@{i} A} `{SetoidTower@{i} B}
  (R : A -> B -> Type@{i}) `{forall a b, Setoid@{i} (R a b)} :=
BuildHas {
  map : A ~> B
}.
End Map1.

Module Map2a.
Record Has@{i}
  {A B : Type@{i}} `{SetoidTower@{i} A} `{SetoidTower@{i} B}
  (R : A -> B -> Type@{i}) `{forall a b, Setoid@{i} (R a b)} :=
BuildHas {
  map : A ~> B;
  map_in_R : forall (a : A) (b : B), map a ~ b ~> R a b
}.
End Map2a.

Module Map2b.
Record Has@{i}
  {A B : Type@{i}} `{SetoidTower@{i} A} `{SetoidTower@{i} B}
  (R : A -> B -> Type@{i}) `{forall a b, Setoid@{i} (R a b)} :=
BuildHas {
  map : A ~> B;
  R_in_map : forall (a : A) (b : B), R a b ~> map a ~ b
}.
End Map2b.

Module Map3.
Record Has@{i}
    {A B : Type@{i}} `{SetoidTower@{i} A} `{SetoidTower@{i} B}
    (R : A -> B -> Type@{i}) `{forall a b, Setoid@{i} (R a b)} :=
BuildHas {
  map : A ~> B;
  map_in_R : forall (a : A) (b : B), map a ~ b ~> R a b;
  R_in_map : forall (a : A) (b : B), R a b ~> map a ~ b
}.
End Map3.

Module Map4.
(* An alternative presentation of Sozeau, Tabareau, Tanter's univalent parametricity:
   symmetrical and transport-free *)
Record Has@{i}
    {A B : Type@{i}} `{SetoidTower@{i} A} `{SetoidTower@{i} B}
    (R : A -> B -> Type@{i}) `{forall a b, Setoid@{i} (R a b)} :=
BuildHas {
  map : A ~> B;
  map_in_R : forall (a : A) (b : B), map a ~ b ~> R a b;
  R_in_map : forall (a : A) (b : B), R a b ~> map a ~ b;
  R_in_mapK : forall (a : A) (b : B), (map_in_R a b) o (R_in_map a b) =~= idmap
}.
End Map4.

Register Map0.Has as trocq.map0.
Register Map1.Has as trocq.map1.
Register Map2a.Has as trocq.map2a.
Register Map2b.Has as trocq.map2b.
Register Map3.Has as trocq.map3.
Register Map4.Has as trocq.map4.

(* syntactic representation of annotated universes
 * useful to annotate the initial goal with fresh variables of type map_class
 * that will be mapped to variables in the constraint graph
 *)
Definition PType@{i} (m n : map_class) (* : Type@{i+1} *) := Type@{i}.
(* placeholder for a weakening from (m, n) to (m', n')
 * replaced with a real weakening function once the ground classes are known
 *)
Definition weaken@{i} (m n m' n' : map_class) {A : Type@{i}} (a : A) : A := a.
Register PType as trocq.ptype.
Register weaken as trocq.weaken.

Elpi Command genhierarchy.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.
Elpi Accumulate File util.

Elpi Query lp:{{
  {{:gref lib:trocq.ptype}} = const PType,
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.ptype PType)),
  {{:gref lib:trocq.weaken}} = const Weaken,
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.weaken Weaken)).
}}.
Elpi Typecheck.

(********************)
(* Record Hierarchy *)
(********************)

Elpi Accumulate lp:{{
  % generate a module with a record type containing:
  % - a relation R : A -> B -> Type;
  % - for all a b, a Setoid instance on R a b
  % - a covariant (A to B) instance of one of the classes of Map listed above;
  % - a contravariant (B to A) instance.
  % (projections are generated so that all fields are accessible from the top record)
  pred generate-module i:param-class, i:univ, i:univ.variable.
  generate-module (pc M N as Class) U L :-
    % open module
    coq.env.begin-module {param-class->add-suffix Class "Param"} none,

    % generate record
    coq.univ-instance UI [L],
    map->class M CovariantSubRecord,
    map->class N ContravariantSubRecord,
    CovariantSubRecord_UI = pglobal CovariantSubRecord UI,
    ContravariantSubRecord_UI = pglobal ContravariantSubRecord UI,

    SymRel = pglobal {sym-rel} UI,
    TypeU = sort (typ U),
    Setoid = pglobal {setoid} UI,
    SetoidTower = pglobal {setoid_tower} UI,

    RelDecl =
      parameter "A" _ TypeU (a\
      parameter "B" _ TypeU (b\
      parameter "sA" _ {{lp:SetoidTower lp:a}} (setoid_a\
      parameter "sB" _ {{lp:SetoidTower lp:b}} (setoid_b\
      record "Rel" (sort (typ {coq.univ.super U})) "BuildRel" (
        field [] "R" {{ lp:a -> lp:b -> lp:TypeU }} r\
        field [] "setoidR" {{ forall (a: lp:a) (b: lp:b), lp:Setoid (lp:r a b)}} setoid_r\
        field [] "covariant" {{
          lp:CovariantSubRecord_UI lp:a lp:b lp:setoid_a lp:setoid_b lp:r lp:setoid_r
        }} _\
        field [] "contravariant" {{
          lp:ContravariantSubRecord_UI lp:b lp:a lp:setoid_b lp:setoid_a
          (lp:SymRel lp:a lp:b lp:r) (fun (b: lp:b) (a: lp:a) => lp:setoid_r a b)
        }} _\
      end-record))))),
    @primitive! =>
    @udecl! [L] ff [] ff =>
      coq.env.add-indt RelDecl TrocqInd,
    coq.env.indt TrocqInd _ _ _ _ [TrocqBuild] _,
    coq.env.projections TrocqInd
      [some CR, some SetoidRProj, some CovariantProj, some ContravariantProj],

    % add R to database for later use
    coq.elpi.accumulate _ "trocq.db"
      (clause _ (after "default-r") (trocq.db.r Class CR)),
    coq.elpi.accumulate execution-site "trocq.db"
      (clause _ _ (trocq.db.gref->class (indt TrocqInd) Class)),
    coq.elpi.accumulate execution-site "trocq.db"
      (clause _ _ (trocq.db.rel Class (indt TrocqInd) (indc TrocqBuild)
        (const CR) (const SetoidRProj) (const CovariantProj) (const ContravariantProj))),

    Rel = pglobal (indt TrocqInd) UI,
    R = pglobal (const CR) UI,
    SetoidR = pglobal (const SetoidRProj) UI,
    Covariant = pglobal (const CovariantProj) UI,
    Contravariant = pglobal (const ContravariantProj) UI,

    % generate projections on the covariant subrecord
    CovariantSubRecord = indt CovariantSubRecordIndt,
    std.forall2 {map-class->fields M} {coq.env.projections CovariantSubRecordIndt}
      (field-name\ some-pr\ sigma Decl Pr\
        some-pr = some Pr,
        @udecl! [L] ff [] ff =>
          coq.env.add-const field-name {{
            fun (A: lp:TypeU) (B: lp:TypeU) (SA: lp:SetoidTower A) (SB: lp:SetoidTower B) (P: lp:Rel A B SA SB) =>
              lp:{{pglobal (const Pr) UI}} A B SA SB (lp:R A B SA SB P)) (lp:SetoidR A B SA SB P) (lp:Covariant A B SA SB P)
          }} _ @transparent! _
    ),

    % generate projections on the contravariant subrecord
    ContravariantSubRecord = indt ContravariantSubRecordIndt,
    std.forall2 {map-class->cofields N} {coq.env.projections ContravariantSubRecordIndt}
      (field-name\ some-pr\ sigma Decl Pr\
        some-pr = some Pr,
        @udecl! [L] ff [] ff =>
          coq.env.add-const field-name {{
            fun (A: lp:TypeU) (B: lp:TypeU) (SA: lp:SetoidTower A) (SB: lp:SetoidTower B) (P: lp:Rel A B SA SB) =>
              lp:{{pglobal (const Pr) UI}} B A SB SA (lp:SymRel A B (lp:R A B SA SB P))
                  (fun (b: B) (a: A) => lp:SetoidR A B SA SB P a b) (lp:Contravariant A B SA SB P)
          }} _ @transparent! _
    ),

    % close module
    coq.env.end-module _.
}}.
Elpi Typecheck.

(* generate the hierarchy *)
Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-classes all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-module (pc m n) U L
    )
  )
}}.

(********************)
(* Record Weakening *)
(********************)

Coercion forgetMap43@{i}
  {A B : Type@{i}} `{SetoidTower A} `{SetoidTower B} {R : A -> B -> Type@{i}} `{forall a b, Setoid@{i} (R a b)}
  (m : Map4.Has@{i} R) : Map3.Has@{i} R :=
    Map3.BuildHas _ _ _ _ R _ (Map4.map R m) (Map4.map_in_R R m) (Map4.R_in_map R m).

Coercion forgetMap32a@{i}
  {A B : Type@{i}} `{SetoidTower A} `{SetoidTower B} {R : A -> B -> Type@{i}} `{forall a b, Setoid@{i} (R a b)}
  (m : Map3.Has@{i} R) : Map2a.Has@{i} R :=
    Map2a.BuildHas _ _ _ _ R _ (Map3.map R m) (Map3.map_in_R R m).

Coercion forgetMap32b@{i}
  {A B : Type@{i}} `{SetoidTower A} `{SetoidTower B} {R : A -> B -> Type@{i}} `{forall a b, Setoid@{i} (R a b)}
  (m : Map3.Has@{i} R) : Map2b.Has@{i} R :=
    Map2b.BuildHas _ _ _ _ R _ (Map3.map R m) (Map3.R_in_map R m).

Coercion forgetMap2a1@{i}
  {A B : Type@{i}} `{SetoidTower A} `{SetoidTower B} {R : A -> B -> Type@{i}} `{forall a b, Setoid@{i} (R a b)}
  (m : Map2a.Has@{i} R) : Map1.Has@{i} R :=
    Map1.BuildHas _ _ _ _ R _ (Map2a.map R m).

Coercion forgetMap2b1@{i}
  {A B : Type@{i}} `{SetoidTower A} `{SetoidTower B} {R : A -> B -> Type@{i}} `{forall a b, Setoid@{i} (R a b)}
  (m : Map2b.Has@{i} R) : Map1.Has@{i} R :=
    Map1.BuildHas _ _ _ _ R _ (Map2b.map R m).

Coercion forgetMap10@{i}
  {A B : Type@{i}} `{SetoidTower A} `{SetoidTower B} {R : A -> B -> Type@{i}} `{forall a b, Setoid@{i} (R a b)}
  (m : Map1.Has@{i} R) : Map0.Has@{i} R :=
    Map0.BuildHas _ _ _ _ R _.

Elpi Accumulate lp:{{
  % generate 2 functions of weakening per possible weakening:
  % one on the left and one on the right, if possible
  pred generate-forget i:param-class, i:univ, i:univ.variable.
  generate-forget (pc M N as Class) U L :-
    coq.univ-instance UI [L],
    map->class M MGR,
    map->class N NGR,

    trocq.db.rel Class RelMN _ RMN SetoidRMN CovariantMN ContravariantMN,
    RelMN_UI = pglobal RelMN UI,
    RMN_UI = pglobal RMN UI,
    SetoidRMN_UI = pglobal SetoidRMN UI,
    CovariantMN_UI = pglobal CovariantMN UI,
    ContravariantMN_UI = pglobal ContravariantMN UI,

    TypeU = sort (typ U),
    SetoidTower = pglobal {setoid_tower} UI,

    % covariant weakening
    std.forall {map-class.weakenings-from M} (m1\
      sigma BuildRelM1N BuildRelM1N_UI ForgetMapM ForgetMapM_UI ForgetName ForgetCst M1GR RelM1N\
      std.do! [
        map->class m1 M1GR,
        trocq.db.rel (pc m1 N) RelM1N BuildRelM1N _ _ _ _,
        BuildRelM1N_UI = pglobal BuildRelM1N UI,

        coq.coercion.db-for (grefclass MGR) (grefclass M1GR) [pr ForgetMapM _],
        ForgetMapM_UI = pglobal ForgetMapM UI,

        param-class->add-2-suffix "_" Class (pc m1 N) "forget_" ForgetName,
        @udecl! [L] ff [] ff =>
          coq.env.add-const ForgetName {{
            fun (A: lp:TypeU) (B: lp:TypeU) (SA: lp:SetoidTower A) (SB: lp:SetoidTower B) (P: lp:RelMN_UI A B SA SB) =>
              lp:BuildRelM1N_UI A B SA SB (lp:RMN_UI A B SA SB P) (lp:SetoidRMN_UI A B SA SB P)
                (lp:ForgetMapM_UI A B SA SB (lp:RMN_UI A B SA SB P) (lp:SetoidRMN_UI A B SA SB P) (lp:CovariantMN_UI A B SA SB P))
                (lp:ContravariantMN_UI A B SA SB P)
          }} _ @transparent! ForgetCst,
        @global! => coq.coercion.declare
          (coercion (const ForgetCst) 2 RelMN (grefclass RelM1N))
    ]),

    % contravariant weakening
    SymRel_UI = pglobal {sym-rel} UI,
    std.forall {map-class.weakenings-from N} (n1\
      sigma BuildRelMN1 BuildRelMN1_UI ForgetMapN ForgetMapN_UI ForgetName ForgetCst N1GR RelMN1\
      std.do! [
        map->class n1 N1GR,
        trocq.db.rel (pc M n1) RelMN1 BuildRelMN1 _ _ _ _,
        BuildRelMN1_UI = pglobal BuildRelMN1 UI,

        coq.coercion.db-for (grefclass NGR) (grefclass N1GR) [pr ForgetMapN _],
        ForgetMapN_UI = pglobal ForgetMapN UI,

        param-class->add-2-suffix "_" Class (pc M n1) "forget_" ForgetName,
        @udecl! [L] ff [] ff =>
          coq.env.add-const ForgetName {{
            fun (A: lp:TypeU) (B: lp:TypeU) (SA: lp:SetoidTower A) (SB: lp:SetoidTower B) (P: lp:RelMN_UI A B SA SB) =>
              lp:BuildRelMN1_UI A B SA SB (lp:RMN_UI A B SA SB P) (lp:SetoidRMN_UI A B SA SB P)
                (lp:CovariantMN_UI A B SA SB P)
                (lp:ForgetMapN_UI B A SB SA (lp:SymRel_UI A B (lp:RMN_UI A B SA SB P))
                  (fun (b: B) (a: A) => lp:SetoidRMN_UI A B SA SB P a b) (lp:ContravariantMN_UI A B SA SB P))
          }} _ @transparent! ForgetCst,
        @global! => coq.coercion.declare
          (coercion (const ForgetCst) 2 RelMN (grefclass RelMN1))
    ]).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-classes all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-forget (pc m n) U L
    )
  ).
}}.

(* General projections *)

Definition rel {A B} `{SetoidTower A} `{SetoidTower B} (R : Param00.Rel A B _ _) :=
  Param00.R A B _ _ R.
Coercion rel : Param00.Rel >-> Funclass.
Definition setoid_rel {A B} `{SetoidTower A} `{SetoidTower B} (R : Param00.Rel A B _ _) :=
  Param00.setoidR A B _ _ R.
#[global] Existing Instance setoid_rel.

Definition map {A B} `{SetoidTower A} `{SetoidTower B} (R : Param10.Rel A B _ _) : A ~> B :=
  Map1.map _ (Param10.covariant A B _ _ R).
Definition map_in_R {A B} `{SetoidTower A} `{SetoidTower B} (R : Param2a0.Rel A B _ _) :
  forall (a : A) (b : B), map R a ~ b -> R a b :=
  Map2a.map_in_R _ (Param2a0.covariant A B _ _ R).
Definition R_in_map {A B} `{SetoidTower A} `{SetoidTower B} (R : Param2b0.Rel A B _ _) :
  forall (a : A) (b : B), R a b -> map R a ~ b :=
  Map2b.R_in_map _ (Param2b0.covariant A B _ _ R).
Definition R_in_mapK {A B} `{SetoidTower A} `{SetoidTower B} (R : Param40.Rel A B _ _) :
  forall (a : A) (b : B), (map_in_R R a b) o (R_in_map R a b) =~= idmap :=
  Map4.R_in_mapK _ (Param40.covariant A B _ _ R).

Definition comap {A B} `{SetoidTower A} `{SetoidTower B} (R : Param01.Rel A B _ _) : B ~> A :=
  Map1.map _ (Param01.contravariant A B _ _ R).
Definition comap_in_R {A B} `{SetoidTower A} `{SetoidTower B} (R : Param02a.Rel A B _ _) :
  forall (b : B) (a : A), comap R b ~ a -> R a b :=
  Map2a.map_in_R _ (Param02a.contravariant A B _ _ R).
Definition R_in_comap {A B} `{SetoidTower A} `{SetoidTower B} (R : Param02b.Rel A B _ _) :
  forall (b : B) (a : A), R a b -> comap R b ~ a :=
  Map2b.R_in_map _ (Param02b.contravariant A B _ _ R).
Definition R_in_comapK {A B} `{SetoidTower A} `{SetoidTower B} (R : Param04.Rel A B _ _) :
  forall (b : B) (a : A), (comap_in_R R b a) o (R_in_comap R b a) =~= idmap :=
  Map4.R_in_mapK _ (Param04.contravariant A B _ _ R).

(* Aliasing *)

Declare Scope param_scope.
Local Open Scope param_scope.
Delimit Scope param_scope with P.

Notation UParam := Param44.Rel.
Notation MkUParam := Param44.BuildRel.
Notation "A <=> B" := (Param44.Rel A B _ _) : param_scope.
Notation IsUMap := Map4.Has.
Notation MkUMap := Map4.BuildHas.
Arguments Map4.BuildHas {A B _ _ R}.
Arguments Param44.BuildRel {A B _ _ R}.

(* symmetry lemmas for Map *)

Definition eq_Map0@{i} {A A' : Type@{i}} `{SetoidTower A} `{SetoidTower A'}
    {R R' : A -> A' -> Type@{i}} `{forall a b, SetoidTower@{i} (R a b)} `{forall a b, SetoidTower@{i} (R' a b)} :
  (forall a a', R a a' <=> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof.
  move=> RR' []; exists.
Defined.

Definition eq_Map1@{i} {A A' : Type@{i}} `{SetoidTower A} `{SetoidTower A'}
    {R R' : A -> A' -> Type@{i}} `{forall a b, SetoidTower@{i} (R a b)} `{forall a b, SetoidTower@{i} (R' a b)} :
  (forall a a', R a a' <=> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof.
  move=> RR' [m]; exists. exact.
Defined.

Definition eq_Map2a@{i} {A A' : Type@{i}} `{SetoidTower A} `{SetoidTower A'}
    {R R' : A -> A' -> Type@{i}} `{forall a b, SetoidTower@{i} (R a b)} `{forall a b, SetoidTower@{i} (R' a b)} :
  (forall a a', R a a' <=> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof.
  move=> RR' [m mR]; exists m.
  move=> a a'.
  unshelve eexists.
  - by move /mR /(comap (RR' _ _)).
  - move=> r1 r2 rr /=.
    by do ! apply preserves_rel.
Defined.

Definition eq_Map2b@{i} {A A' : Type@{i}} `{SetoidTower A} `{SetoidTower A'}
    {R R' : A -> A' -> Type@{i}} `{forall a b, SetoidTower@{i} (R a b)} `{forall a b, SetoidTower@{i} (R' a b)} :
  (forall a a', R a a' <=> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof.
  move=> RR' [m Rm]; unshelve eexists m.
  move=> a a'.
  unshelve eexists.
  + by move /(map (RR' _ _)) /Rm.
  + move=> r1 r2 rr /=.
    by do ! apply preserves_rel.
Defined.

Definition eq_Map3@{i} {A A' : Type@{i}} `{SetoidTower A} `{SetoidTower A'}
    {R R' : A -> A' -> Type@{i}} `{forall a b, SetoidTower@{i} (R a b)} `{forall a b, SetoidTower@{i} (R' a b)} :
  (forall a a', R a a' <=> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof.
  move=> RR' [m mR Rm]; unshelve eexists m.
  - move=> a a'.
    unshelve eexists.
    + by move /mR /(comap (RR' _ _)).
    + move=> r1 r2 rr /=.
      by do ! apply preserves_rel.
  - move=> a a'.
    unshelve eexists.
    + by move /(map (RR' _ _)) /Rm.
    + move=> r1 r2 rr /=.
      by do ! apply preserves_rel.
Defined.

Definition eq_Map4@{i} {A A' : Type@{i}} `{SetoidTower A} `{SetoidTower A'}
    {R R' : A -> A' -> Type@{i}} `{forall a b, SetoidTower@{i} (R a b)} `{forall a b, SetoidTower@{i} (R' a b)} :
  (forall a a', R a a' <=> R' a a') ->
  Map4.Has@{i} R' -> Map4.Has@{i} R.
Proof.
  move=> RR' [m mR Rm RmK]; unshelve eexists m _ _.
  - move=> a a'.
    unshelve eexists.
    + by move /mR /(comap (RR' _ _)).
    + move=> r1 r2 rr /=.
      by do ! apply preserves_rel.
  - move=> a a'.
    unshelve eexists.
    + by move /(map (RR' _ _)) /Rm.
    + move=> r1 r2 rr /=.
      by do ! apply preserves_rel.
  - move=> a a' r /=.
    transitivity (comap (RR' a a') (map (RR' a a') r)).
    + apply preserves_rel, RmK.
    + apply (R_in_comap (RR' a a')).
      apply (map_in_R (RR' a a')).
      by reflexivity.
Qed.

(* instances of MapN for A ~ A *)
(* allows to build id_ParamMN : forall A, ParamMN.Rel A A *)

Definition id_Map0 {A : Type} `{SetoidTower A} :
  Map0.Has (fun (a a': A) => a ~ a').
Proof. constructor. Defined.

Definition id_Map0_sym {A : Type} `{SetoidTower A} :
  Map0.Has (sym_rel (fun (a a': A) => a ~ a')).
Proof. constructor. Defined.

Definition id_Map1 {A : Type} `{SetoidTower A} :
  Map1.Has (fun (a a': A) => a ~ a').
Proof. constructor. by apply id_morphism. Defined.

Definition id_Map1_sym {A : Type} `{SetoidTower A} :
  Map1.Has (sym_rel (fun (a a': A) => a ~ a')).
Proof. constructor. by apply id_morphism. Defined.

Definition id_Map2a {A : Type} `{SetoidTower A} :
  Map2a.Has (fun (a a': A) => a ~ a').
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a a' ; apply id_morphism.
Defined.

Definition id_Map2a_sym {A : Type} `{SetoidTower A} :
  Map2a.Has (sym_rel (fun (a a': A) => a ~ a')).
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - by apply inverse_morphism.
Defined.

Definition id_Map2b {A : Type} `{SetoidTower A} :
  Map2b.Has (fun (a a': A) => a ~ a').
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a b ; by apply id_morphism.
Defined.

Definition id_Map2b_sym {A : Type} `{SetoidTower A} :
  Map2b.Has (sym_rel (fun (a a': A) => a ~ a')).
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a b ; by apply inverse_morphism.
Defined.

Definition id_Map3 {A : Type} `{SetoidTower A} :
  Map3.Has (fun (a a': A) => a ~ a').
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a b ; by apply id_morphism.
  - move=> a b ; by apply id_morphism.
Defined.

Definition id_Map3_sym {A : Type} `{SetoidTower A} :
  Map3.Has (sym_rel (fun (a a': A) => a ~ a')).
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a b ; by apply inverse_morphism.
  - move=> a b ; by apply inverse_morphism.
Defined.

Definition id_Map4 {A : Type} `{SetoidTower A} :
  Map4.Has (fun (a a': A) => a ~ a').
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a b ; by apply id_morphism.
  - move=> a b ; by apply id_morphism.
  - move=> a a' r ; reflexivity.
Defined.

Definition id_Map4_sym {A : Type} `{SetoidTower A} :
  Map4.Has (sym_rel (fun (a a': A) => a ~ a')).
Proof.
  unshelve econstructor.
  - by apply id_morphism.
  - move=> a b ; by apply inverse_morphism.
  - move=> a b ; by apply inverse_morphism.
  - rewrite /sym_rel => a a' rel /=.
    apply symmetry1_involutive.
Defined.

(* generate id_ParamMN : forall A, ParamMN.Rel A A for all M N *)
Elpi Accumulate lp:{{
  pred generate-id-param i:param-class, i:univ, i:univ.variable.
  generate-id-param (pc M N as Class) U L :-
    map-class->string M MStr,
    map-class->string N NStr,
    coq.univ-instance UI [L],

    trocq.db.rel Class _ BuildRel _ _ _ _,
    BuildRel_UI = pglobal BuildRel UI,

    coq.locate {calc ("id_Map" ^ MStr)} IdMap,
    coq.locate {calc ("id_Map" ^ NStr ^ "_sym")} IdMapSym,
    IdMap_UI = pglobal IdMap UI,
    IdMapSym_UI = pglobal IdMapSym UI,

    TypeU = sort (typ U),
    SetoidTower = pglobal {setoid_tower} UI,
    Equiv = pglobal {equiv} UI,

    TowerToLevel0 = pglobal {setoid_tower->setoid 0} UI,
    TowerToLevel1 = pglobal {setoid_tower->setoid 1} UI,

    @udecl! [L] ff [] ff =>
      coq.env.add-const {calc ("id_Param" ^ MStr ^ NStr)} {{
        fun (A: lp:TypeU) (SA: lp:SetoidTower A) =>
          lp:BuildRel_UI A A SA SA
            (lp:Equiv A (lp:TowerToLevel0 A SA))
            (lp:TowerToLevel1 A SA)
            (lp:IdMap_UI A SA) (lp:IdMapSym_UI A SA)
      }} _ @transparent! _.
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-classes all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-id-param (pc m n) U L
    )
  ).
}}.

(* symmetry property for Param *)

Elpi Accumulate lp:{{
  pred generate-param-sym i:param-class, i:univ, i:univ.variable.
  generate-param-sym (pc M N) U L :-
    map-class->string M MStr,
    map-class->string N NStr,
    coq.univ-instance UI [L],

    trocq.db.rel (pc M N) RelMN _ RMN SetoidRMN CovariantMN ContravariantMN,
    trocq.db.rel (pc N M) _ BuildRelNM _ _ _ _,
    RelMN_UI = pglobal RelMN UI,
    BuildRelNM_UI = pglobal BuildRelNM UI,
    RMN_UI = pglobal RMN UI,
    SetoidRMN_UI = pglobal SetoidRMN UI,
    CovariantMN_UI = pglobal CovariantMN UI,
    ContravariantMN_UI = pglobal ContravariantMN UI,

    SymRel = pglobal {sym-rel} UI,
    TypeU = sort (typ U),
    SetoidTower = pglobal {setoid_tower} UI,

    @udecl! [L] ff [] ff =>
      coq.env.add-const {calc ("Param" ^ MStr ^ NStr ^ "_sym")} {{
        fun (A B: lp:TypeU) (SA: lp:SetoidTower A) (SB: lp:SetoidTower B) (P: lp:RelMN_UI A B SA SB) =>
          lp:BuildRelNM_UI B A SB SA (lp:SymRel A B (lp:RMN_UI A B SA SB P))
            (fun (b: B) (a: A) => lp:SetoidRMN_UI A B SA SB P a b)
            (lp:ContravariantMN_UI A B SA SB P) (lp:CovariantMN_UI A B SA SB P)
      }} _ @transparent! _.
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-classes all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-param-sym (pc m n) U L
    )
  ).
}}.
