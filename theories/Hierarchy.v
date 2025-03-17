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
From Trocq Require Import HoTT_additions Database.
From elpi Require Import elpi.

From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.
From Trocq.Elpi Extra Dependency "util.elpi" as util.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Polymorphic Inductive Cumulativity.

(* Coq representation of the hierarchy *)
Inductive map_class : Set := map0 | map0a | map0b | map1 | map2a | map2b | map3 | map4.

Register map0 as trocq.indc_map0.
Register map0a as trocq.indc_map1a.
Register map0b as trocq.indc_map1b.
Register map1 as trocq.indc_map1c.
Register map2a as trocq.indc_map2a.
Register map2b as trocq.indc_map2b.
Register map3 as trocq.indc_map3.
Register map4 as trocq.indc_map4.
Register sym_rel as trocq.sym_rel.
Register paths as trocq.paths.

(*************************)
(* Parametricity Classes *)
(*************************)

(* first unilateral witnesses describing one side of the structure given to a relation *)

Module Map0.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
}.
End Map0.

Module Map1a.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_total : forall (P: Type@{i}), IsHProp P ->
             forall a, (forall b, R a b -> P) -> P
}.
End Map1a.

Module Map1b.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_right_unique : forall a b c, R a b -> R a c -> b = c
}.
End Map1b.

Module Map1c.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
}.
End Map1c.

Module Map2a.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_total : forall (P: Type@{i}), IsHProp P ->
            forall a, (forall b, R a b -> P) -> P;
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b
}.
End Map2a.

Module Map2b.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_right_unique : forall a b c, R a b -> R a c -> b = c;
  map : A -> B;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map2b.

Module Map3.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_right_unique : forall a b c, R a b -> R a c -> b = c;
  is_total : forall (P: Type@{i}), IsHProp P ->
             forall a, (forall b, R a b -> P) -> P;
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map3.

Module Map4.
(* An alternative presentation of Sozeau, Tabareau, Tanter's univalent parametricity:
   symmetrical and transport-free *)
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_right_unique : forall a b c, R a b -> R a c -> b = c;
  is_total : forall (P: Type@{i}), IsHProp P ->
             forall a, (forall b, R a b -> P) -> P;
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b;
  R_in_mapK : forall (a : A) (b : B) (r : R a b), (map_in_R a b (R_in_map a b r)) = r
}.
End Map4.

Register Map0.Has as trocq.map0.
Register Map1a.Has as trocq.map1a.
Register Map1b.Has as trocq.map1b.
Register Map1c.Has as trocq.map1c.
Register Map2a.Has as trocq.map2a.
Register Map2b.Has as trocq.map2b.
Register Map3.Has as trocq.map3.
Register Map4.Has as trocq.map4.
Register sym_rel as trocq.sym_rel.

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
    SymRel = {sym-rel},
    TypeU = sort (typ U),
    RelDecl =
      parameter "A" _ TypeU (a\
        parameter "B" _ TypeU (b\
          record "Rel" (sort (typ {coq.univ.super U})) "BuildRel" (
            field [] "R" {{ lp:a -> lp:b -> lp:{{ sort (typ U) }} }} r\
            field [] "covariant" (app [pglobal CovariantSubRecord UI, a, b, r]) _\
            field [] "contravariant"
              (app [pglobal ContravariantSubRecord UI, b, a, app [pglobal SymRel UI, a, b, r]]) (_\
          end-record)))),
    @primitive! => @udecl! [L] ff [] ff => coq.env.add-indt RelDecl TrocqInd,coq.env.indt TrocqInd _ _ _ _ [TrocqBuild] _,
    Rel = indt TrocqInd,
    coq.env.projections TrocqInd
      [some CR, some CovariantProj, some ContravariantProj],
    % add R to database for later use
    R = const CR,
    coq.elpi.accumulate _ "trocq.db"
      (clause _ (after "default-r") (trocq.db.r Class CR)),
    coq.elpi.accumulate execution-site "trocq.db"
      (clause _ _ (trocq.db.gref->class (indt TrocqInd) Class)),
    coq.elpi.accumulate execution-site "trocq.db"
      (clause _ _ (trocq.db.rel Class (indt TrocqInd) (indc TrocqBuild)
        (const CR) (const CovariantProj) (const ContravariantProj))),
    % generate projections on the covariant subrecord
    map-class->fields M MFields,
    CovariantSubRecord = indt CovariantSubRecordIndt,
    coq.env.projections CovariantSubRecordIndt MSomeProjs,
    Covariant = const CovariantProj,
    std.forall2 MFields MSomeProjs (field-name\ some-pr\ sigma Decl Pr\
      some-pr = some Pr,
      Decl =
        (fun `A` (sort (typ U)) a\ fun `B` (sort (typ U)) b\ fun `P` (app [pglobal Rel UI, a, b]) p\
          app [pglobal (const Pr) UI, a, b,
            app [pglobal R UI, a, b, p], app [pglobal Covariant UI, a, b, p]]),
      @udecl! [L] ff [] ff => coq.env.add-const field-name Decl _ @transparent! _
    ),
    % generate projections on the contravariant subrecord
    map-class->cofields N NCoFields,
    Contravariant = const ContravariantProj,
    ContravariantSubRecord = indt ContravariantSubRecordIndt,
    coq.env.projections ContravariantSubRecordIndt NSomeProjs,
    std.forall2 NCoFields NSomeProjs (field-name\ some-pr\ sigma Decl Pr\
      some-pr = some Pr,
      Decl =
        (fun `A` (sort (typ U)) a\ fun `B` (sort (typ U)) b\
          fun `P` (app [pglobal Rel UI, a, b]) p\
            app [pglobal (const Pr) UI, b, a,
              app [pglobal SymRel UI, a, b, app [pglobal R UI, a, b, p]],
              app [pglobal Contravariant UI, a, b, p]]),
      @udecl! [L] ff [] ff => coq.env.add-const field-name Decl _ @transparent! _
    ),
    % close module
    coq.env.end-module _.
}}.
Elpi Typecheck.

(********************)
(* Record Weakening *)
(********************)

Coercion forgetMap43@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map4.Has@{i} R) : Map3.Has@{i} R :=
    @Map3.BuildHas A B R
      (@Map4.is_right_unique A B R m)
      (@Map4.is_total A B R m)
      (@Map4.map A B R m)
      (@Map4.map_in_R A B R m)
      (@Map4.R_in_map A B R m).

Coercion forgetMap32a@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map3.Has@{i} R) : Map2a.Has@{i} R :=
    @Map2a.BuildHas A B R
      (@Map3.is_total A B R m)
      (@Map3.map A B R m)
      (@Map3.map_in_R A B R m).

Coercion forgetMap32b@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map3.Has@{i} R) : Map2b.Has@{i} R :=
    @Map2b.BuildHas A B R
      (@Map3.is_right_unique A B R m)
      (@Map3.map A B R m)
      (@Map3.R_in_map A B R m).

Coercion forgetMap2a1a@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2a.Has@{i} R) : Map1a.Has@{i} R :=
    @Map1a.BuildHas A B R
      (@Map2a.is_total A B R m).

Coercion forgetMap2b1b@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2b.Has@{i} R) : Map1b.Has@{i} R :=
    @Map1b.BuildHas A B R
      (@Map2b.is_right_unique A B R m).

Coercion forgetMap2a1c@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2a.Has@{i} R) : Map1c.Has@{i} R :=
    @Map1c.BuildHas A B R
      (@Map2a.map A B R m).

Coercion forgetMap2b1c@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2b.Has@{i} R) : Map1c.Has@{i} R :=
    @Map1c.BuildHas A B R
      (@Map2b.map A B R m).

Coercion forgetMap1c0@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map1c.Has@{i} R) : Map0.Has@{i} R :=
    @Map0.BuildHas A B R.

Coercion forgetMap1b0@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map1b.Has@{i} R) : Map0.Has@{i} R :=
    @Map0.BuildHas A B R.

Coercion forgetMap1a0@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map1a.Has@{i} R) : Map0.Has@{i} R :=
    @Map0.BuildHas A B R.

Elpi Accumulate lp:{{
  % generate 2 functions of weakening per possible weakening:
  % one on the left and one on the right, if possible
  pred generate-forget i:param-class, i:univ, i:univ.variable.
  generate-forget (pc M N as Class) U L :-
    coq.univ-instance UI [L],
    map->class M MGR,
    map->class N NGR,
    trocq.db.rel Class RelMN _ RMN CovariantMN ContravariantMN,
    % covariant weakening
    std.forall {map-class.weakenings-from M} (m1\
      sigma BuildRelM1N ForgetMapM Decl ForgetName ForgetCst M1GR RelM1N\
      std.do! [
        map->class m1 M1GR,
        trocq.db.rel (pc m1 N) RelM1N BuildRelM1N _ _ _,
        coq.coercion.db-for (grefclass MGR) (grefclass M1GR) [pr ForgetMapM _],
        Decl =
          (fun `A` (sort (typ U)) a\ fun `B` (sort (typ U)) b\
            fun `P` (app [pglobal RelMN UI, a, b]) p\
              app [pglobal BuildRelM1N UI, a, b, app [pglobal RMN UI, a, b, p],
                app [pglobal ForgetMapM UI, a, b, app [pglobal RMN UI, a, b, p],
                  app [pglobal CovariantMN UI, a, b, p]],
                app [pglobal ContravariantMN UI, a, b, p]]),
        param-class->add-2-suffix "_" Class (pc m1 N) "forget_" ForgetName,
        @udecl! [L] ff [] ff =>
          coq.env.add-const ForgetName Decl _ @transparent! ForgetCst,
        @global! => coq.coercion.declare
          (coercion (const ForgetCst) 2 RelMN (grefclass RelM1N))
    ]),
    % contravariant weakening
    SymRel = {sym-rel},
    std.forall {map-class.weakenings-from N} (n1\
      sigma BuildRelMN1 ForgetMapN Decl ForgetName ForgetCst N1GR RelMN1\
      std.do! [
        map->class n1 N1GR,
        trocq.db.rel (pc M n1) RelMN1 BuildRelMN1 _ _ _,
        coq.coercion.db-for (grefclass NGR) (grefclass N1GR) [pr ForgetMapN _],
        Decl =
          (fun `A` (sort (typ U)) a\ fun `B` (sort (typ U)) b\
            fun `P` (app [pglobal RelMN UI, a, b]) p\
              app [pglobal BuildRelMN1 UI, a, b, app [pglobal RMN UI, a, b, p],
                app [pglobal CovariantMN UI, a, b, p],
                app [pglobal ForgetMapN UI, b, a,
                  app [pglobal SymRel UI, a, b, app [pglobal RMN UI, a, b, p]],
                  app [pglobal ContravariantMN UI, a, b, p]]]),
        param-class->add-2-suffix "_" Class (pc M n1) "forget_" ForgetName,
        @udecl! [L] ff [] ff =>
          coq.env.add-const ForgetName Decl _ @transparent! ForgetCst,
        @global! => coq.coercion.declare
          (coercion (const ForgetCst) 2 RelMN (grefclass RelMN1))
    ]).
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
  ).
}}.

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
(* Set Printing Universes. Print Module Param2a3. *)
(* Set Printing Universes. Print forget_42b_41. *)
(* Check forall (p : Param44.Rel nat nat), @paths (Param12a.Rel nat nat) p p. *)

(* General projections *)

Definition rel {A B} (R : Param00.Rel A B) := Param00.R A B R.
Coercion rel : Param00.Rel >-> Funclass.

Definition is_total {A B} (R : Param1a0.Rel A B) :
  forall (P: Type@{i}), IsHProp P ->
  forall a, (forall b, R a b -> P) -> P :=
  Map1a.is_total _ (Param1a0.covariant A B R).
Definition is_right_unique {A B} (R : Param1b0.Rel A B) :
  forall a b c, R a b -> R a c -> b = c :=
  Map1b.is_right_unique _ (Param1b0.covariant A B R).
Definition map {A B} (R : Param1c0.Rel A B) : A -> B :=
  Map1c.map _ (Param1c0.covariant A B R).
Definition map_in_R {A B} (R : Param2a0.Rel A B) :
  forall (a : A) (b : B), map R a = b -> R a b :=
  Map2a.map_in_R _ (Param2a0.covariant A B R).
Definition R_in_map {A B} (R : Param2b0.Rel A B) :
  forall (a : A) (b : B), R a b -> map R a = b :=
  Map2b.R_in_map _ (Param2b0.covariant A B R).
Definition R_in_mapK {A B} (R : Param40.Rel A B) :
  forall (a : A) (b : B), map_in_R R a b o R_in_map R a b == idmap :=
  Map4.R_in_mapK _ (Param40.covariant A B R).

Definition is_right_total {A B} (R : Param01a.Rel A B) :
  forall (P: Type@{i}), IsHProp P ->
  forall a, (forall b, R b a -> P) -> P :=
  Map1a.is_total _ (Param01a.contravariant A B R).
Definition is_left_unique {A B} (R : Param01b.Rel A B) :
  forall a b c, R b a -> R c a -> b = c :=
  Map1b.is_right_unique _ (Param01b.contravariant A B R).
Definition comap {A B} (R : Param01c.Rel A B) : B -> A :=
  Map1c.map _ (Param01c.contravariant A B R).
Definition comap_in_R {A B} (R : Param02a.Rel A B) :
  forall (b : B) (a : A), comap R b = a -> R a b :=
  Map2a.map_in_R _ (Param02a.contravariant A B R).
Definition R_in_comap {A B} (R : Param02b.Rel A B) :
  forall (b : B) (a : A), R a b -> comap R b = a :=
  Map2b.R_in_map _ (Param02b.contravariant A B R).
Definition R_in_comapK {A B} (R : Param04.Rel A B) :
  forall (b : B) (a : A), comap_in_R R b a o R_in_comap R b a == idmap :=
  Map4.R_in_mapK _ (Param04.contravariant A B R).

(***************)

Definition R_arrow@{i j}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param00.Rel@{j} B B') :=
    fun f f' => forall a a', PA a a' -> PB (f a) (f' a').

Definition Map0_arrow@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param00.Rel@{j} B B') :
    Map0.Has@{k} (R_arrow PA PB).
Proof. exists. Defined.

(* (01c, 1c0) -> 1c0 *)
Definition Map1c_arrow@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param01c.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param1c0.Rel@{j} B B') :
    Map1c.Has@{k} (R_arrow PA PB).
Proof.
  exists; exact (fun f a' => map PB (f (comap PA a'))).
Defined.

(* Section Optimality_Map1c.
  Definition p01b : Param01b.Rel False Unit.
  Proof.
    exists (fun _ _ => Unit) ; exists.
    move=> _ [].
  Defined.

  Definition p1c1c_false : Param1c1c.Rel False False.
  Proof. exists (fun _ _ => Unit) ; by exists. Defined.

  Theorem D1c_arrow_left_gt0: not (
    forall (A A' : Type) (AR: Param00.Rel A A'),
    forall (B B' : Type) (BR: Param1c0.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs False Unit p01b).
    specialize (Habs _ _ p1c1c_false).
    move: Habs => [map].
    destruct (map id tt).
  Qed.

  Theorem D1c_arrow_left_isnt_1b: not (
    forall (A A' : Type) (AR: Param01b.Rel A A'),
    forall (B B' : Type) (BR: Param1c0.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs False Unit p01b).
    specialize (Habs _ _ p1c1c_false).
    move: Habs => [map].
    destruct (map id tt).
  Qed.

  Definition merely_to_M1a: forall {A: Type},
    (merely A)
      ->
    Map1a.Has (fun (_: Unit) (_: A) => True).
  Proof.
    move=> A tr_a.
    exists=> _.
    apply (merely_destruct tr_a) => a.
    apply tr ; by exists a.
  Defined.

  Definition p2b0_A {A: Type}: Param2b0.Rel A A.
  Proof.
    exists (fun a a' => a = a').
    - exists id.
      + move=> a b c [] [] //.
      + done.
    - exists.
  Defined.

  From HoTT Require Import Contrib.HoTTBookExercises.

  Theorem D1c_arrow_left_isnt_1a `{Univalence}: not (
    forall (A A' : Type) (AR: Param01a.Rel A A'),
    forall (B B' : Type) (BR: Param1c0.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    move: (fun {A: Type} (tr_a: merely A) =>
      let map1a := merely_to_M1a tr_a in
      let param1a0 := Param01a.BuildRel _ _ _ (Map0.BuildHas _ _ _) map1a in
      Habs _ _ param1a0 A A p2b0_A
    ) => {}Habs.

    move: Habs.
    rewrite /R_arrow /= => Habs.

    pose G A tr_a := Map1c.map _ (Habs A tr_a) id tt.

    elim (Book_3_11 G).
  Qed.

  Definition p1c1c_unit : Param1c1c.Rel Unit Unit.
  Proof.
    exists (fun _ _ => Unit) ; by exists.
  Qed.

  Definition p1b0 : Param1b0.Rel Unit False.
  Proof.
    exists (fun _ _ => Unit) ; exists.
    move=> _ [].
  Defined.
  
  Theorem D1c_arrow_right_is_gt0: not (
    forall (A A' : Type) (AR: Param01c.Rel A A'),
    forall (B B' : Type) (BR: Param00.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs _ _ p1c1c_unit).
    specialize (Habs Unit False p1b0).
    move: Habs => [map].
    destruct (map id tt).
  Qed.

  Theorem D1c_arrow_right_isnt_1b: not (
    forall (A A' : Type) (AR: Param01c.Rel A A'),
    forall (B B' : Type) (BR: Param1b0.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs _ _ p1c1c_unit).
    specialize (Habs Unit False p1b0).
    move: Habs => [map].
    destruct (map id tt).
  Qed.

  Definition p2b2b_bool : Param2b2b.Rel Bool Bool.
  Proof.
    exists (fun b b' => b = b').
    - exists id.
      + move=> a b c eq_ba eq_ca.
        apply inverse in eq_ba.
        exact (concat eq_ba eq_ca).
      + move=> a b. done.
    - exists id.
      + unfold sym_rel.
        move=> a b c eq_ba eq_ca.
        apply inverse in eq_ca.
        exact (concat eq_ba eq_ca).
      + move=> a b. done.
  Defined.

  Theorem D1c_arrow_right_isnt_1a `{Univalence}: not (
    forall (A A' : Type) (AR: Param01c.Rel A A'),
    forall (B B' : Type) (BR: Param1a0.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    move: (Habs _ _ p2b2b_bool) => {}Habs.
    move: (fun {A: Type} (tr_a: merely A) =>
      let map1a := merely_to_M1a tr_a in
      let param1a0 := Param1a0.BuildRel _ _ _ map1a (Map0.BuildHas _ _ _) in
      Habs _ _ param1a0
    ) => {}Habs.

    move: Habs.
    rewrite /R_arrow /= => Habs.

    pose G A tr_a := Map1c.map _ (Habs A tr_a) (fun _ => tt) true.

    elim (Book_3_11 G).
  Qed.
End Optimality_Map1c. *)

Variable A: Type.
Variable B: Type.
Variable R: A -> B -> Type.

Lemma is_pointless `{Univalence}: (
  (forall a, merely (exists b, R a b))
   ->
  (forall P, IsHProp P -> forall a, (forall b, R a b -> P) -> P)
).
Proof.
  move=> merely P P_is_HProp a.
  move=> R_implies_P.
  apply (merely_destruct (merely a)).
  move=> [b Rab].
  by apply (R_implies_P b).
Qed.

Definition Map1b_arrow@{i j k | i <= k, j <= k} `{Funext}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param1b0.Rel@{j} B B') :
    Map1b.Has@{k} (R_arrow PA PB).
Proof.
  exists; rewrite /R_arrow.
  move=> f g h R_fg R_fh.
  apply: path_arrow.
  move=> x'.
  apply (is_right_unique PB (f (comap PA x')) (g x')).
  - by apply /R_fg /(comap_in_R PA).
  - by apply /R_fh /(comap_in_R PA).
Qed.

Section Optimality_Map1b.
  Definition p02b_false : Param02b.Rel Unit Unit.
  Proof.
    exists (fun _ _ => False).
    - exists.
    - exists id.
      + move=> _ _ _ [].
      + move=> _ _ [].
  Defined.

  Theorem D1b_arrow_left_isnt_2b: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param1b0.Rel B B'),

    Map1b.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs _ _ p02b_false).
    specialize (Habs _ _ p2b2b_bool).
    move: Habs => [is_right_unique].
    pose f := unit_name true.
    pose g := unit_name false.
    specialize (is_right_unique f f g).

    enough (f = g) by (
      apply ap10 in X ;
      specialize (X tt) ;
      rewrite /f /g in X ;
      by apply: true_ne_false
    ).

    apply is_right_unique ; move=> _ _ [].
  Qed.

  (* Inductive shelter {A: Type} (a: A) :=.

  Definition p1b0_hides_A {A: Type}: Param1b0.Rel A Unit.
  Proof.
    exists (fun (a: A) _ => shelter a).
    - by exists=> a [] [].
    - exists.
  Qed. *)

  Theorem D1b_arrow_left_gt1a: not (
    forall (A A' : Type) (AR: Param01a.Rel A A'),
    forall (B B' : Type) (BR: Param1b0.Rel B B'),

    Map1b.Has (R_arrow AR BR)
  ).
  Proof.
    (* move=> Habs.
    move: (fun {A: Type} (tr_a: merely A) =>
      let map1a := merely_to_M1a tr_a in
      let param01a := Param01a.BuildRel _ _ _ (Map0.BuildHas _ _ _) map1a in
      Habs _ _ param01a A Unit p1b0_hides_A
    ) => {}Habs.

    assert (forall A, merely A -> A).
    - move=> A tr_a.
      destruct (Habs A tr_a) as [is_right_unique].
      specialize (is_right_unique id id id).

    move: Habs.
    rewrite /R_arrow /= => Habs.
 *)

  Admitted.

  Definition p02a : Param02a.Rel Unit Unit.
  Proof.
    exists (fun _ _ => Unit).
    - exists.
    - exists id=> a.
      + apply tr. exists a. by unfold sym_rel.
      + move=> b _. by unfold sym_rel.
  Defined.

  Definition p2a0_bool : Param2a0.Rel Bool Bool.
  Proof.
    exists (fun b b' => Unit).
    - exists id.
      + move=> a. apply tr.
        by exists a.
      + done.
    - exists.
  Defined.

  Definition p2a2a_true: Param2a2a.Rel Unit Unit.
  Proof.
    exists (fun _ _ => True).
    - exists id.
      + case ; by apply tr.
      + done.
    - exists id.
      + case ; rewrite /sym_rel; by apply tr.
      + done.
  Defined.

  Definition p2a2a_A : Param2a2a.Rel Bool Bool.
  Proof.
    exists (fun _ _ => Unit).
    - exists id => b.
      + apply tr ; by exists b.
      + done.
    - exists id => b.
      + apply tr ; by exists b.
      + done.
  Defined.

  Definition p2a2a_bool : Param2a2a.Rel Bool Bool.
  Proof.
    exists (fun b b' => b = b').
    - exists id.
      + move=> b; apply tr.
        by exists b.
      + done.
    - exists id.
      + move=> b; apply tr.
        by exists b.
      + rewrite /sym_rel //.
  Defined.

  Theorem D1b_arrow_right_isnt_1a: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param1a0.Rel B B'),

    Map1b.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    move: (Habs _ _ p2a2a_true) => {}Habs.
    move: (Habs _ _ p2a2a_A) => {}Habs.
    move: Habs => [is_right_unique].

    specialize (is_right_unique (unit_name true) (unit_name false) (unit_name true)).
    rewrite /R_arrow /p2a2a_true /= in is_right_unique.
    specialize (is_right_unique (fun _ _ _ => tt) (fun _ _ _ => tt)).
    destruct (false_ne_true (ap10 is_right_unique tt)).
  Qed.

  Definition p02a_unit: Param02a.Rel Unit Unit.
  Proof.
    exists (fun _ _ => Unit).
    - exists.
    - exists id.
      + rewrite /sym_rel => _; apply tr; done.
      + done.
  Defined.

  Definition p1c0_unit: Param1c0.Rel Bool Bool.
  Proof.
    exists (fun _ _ => Unit).
    - by exists.
    - exists.
  Defined.

  Theorem D1b_arrow_right_isnt_1c: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param1c0.Rel B B'),

    Map1b.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    specialize (Habs Unit Unit p02a_unit).
    specialize (Habs Bool Bool p1c0_unit).
    move: Habs => [is_right_unique].
    enough (unit_name true = unit_name false) by apply true_ne_false, (ap10 X tt).
    apply (is_right_unique (unit_name true)) ; rewrite /R_arrow /p02a_unit /p1c0_unit //.
  Qed.
End Optimality_Map1b.

(* (02b, 2a0) -> 1a0 *)
Definition Map1a_arrow@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param02b.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param2a0.Rel@{j} B B') :
    Map1a.Has@{k} (R_arrow PA PB).
Proof.
  exists; rewrite /R_arrow => f.

  apply tr.
  exists (fun a' => map PB (f (comap PA a'))).
  move=> a a' aR.
  apply (map_in_R PB).
  by rewrite (R_in_comap PA a' a).
Qed.

Section Optimality_Map1a.
  Definition p02a_bool_bool_id: Param02a.Rel Bool Bool.
  Proof.
    exists (fun b b' => True).
    - exists.
    - exists id.
      + move=> b ; apply tr ; by exists b.
      + rewrite /sym_rel /id => [] [] //.
  Defined.

  Definition p2a0_bool_bool_negb: Param2a0.Rel Bool Bool.
  Proof.
    exists (fun b b' => b = b').
    - exists id.
      + move=> b ; apply tr ; by exists b.
      + rewrite /sym_rel //.
    - exists.
  Defined.

  Theorem D1a_arrow_left_isnt_2a: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),

    Map1a.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs _ _ p02a_bool_bool_id).
    specialize (Habs _ _ p2a0_bool_bool_negb).
    move: Habs => [is_total].
    apply (merely_destruct (is_total id)) => {is_total}.
    move => [b is_total].
    rewrite /R_arrow /p02a_bool_bool_id /p2a0_bool_bool_negb /= in is_total.
    specialize (is_total true true I) as X.
    rewrite -(is_total false true I) in X.
    apply (true_ne_false X).
  Qed.

  Definition p2b2b_true : Param2b2b.Rel Unit Unit.
  Proof.
    exists (fun _ _ => Unit) ;
    exists id => [] [] [] [] ; done.
  Defined.

  Definition p01b_false : Param01b.Rel False Unit.
  Proof.
    exists (fun _ _ => Unit) ;
    exists => [] [] [].
  Defined.

  Definition p2a0_empty_R: Param2a0.Rel False False.
  Proof.
    exists (fun _ _ => False).
    - by exists id.
    - exists.
  Qed.

  Theorem D1a_arrow_left_is_gt1b: not (
    forall (A A' : Type) (AR: Param01b.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),

    Map1a.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    specialize (Habs _ _ p01b_false).
    specialize (Habs _ _ p2a0_empty_R).
    move: Habs => [is_total].
    specialize (is_total id).
    apply (merely_destruct is_total).
    move => [b _] ; destruct (b tt).
  Qed.

  Definition p2b2b_empty_R : Param2b2b.Rel Unit Unit.
  Proof.
    exists (fun _ _ => False) ;
    exists id => [] [] [] [] ; done.
  Defined.

  Theorem D1a_arrow_right_isnt_2b: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param2b0.Rel B B'),

    Map1a.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    specialize (Habs _ _ p2b2b_true).
    specialize (Habs _ _ p2b2b_empty_R).
    move: Habs => [is_total].
    apply (merely_destruct (is_total id)).
    move => [b Ra].
    rewrite /R_arrow /p2b2b_empty_R /= in Ra.
    destruct (Ra tt tt tt).
  Qed.

  Theorem D1a_arrow_right_is_gt1a: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param1a0.Rel B B'),

    Map1a.Has (R_arrow AR BR)
  ).
  Proof.
  Admitted.
End Optimality_Map1a.

(* (02b, 2a0) -> 2a0 *)
Definition Map2a_arrow@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param02b.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param2a0.Rel@{j} B B') :
    Map2a.Has@{k} (R_arrow PA PB).
Proof.
  exists (Map1c.map@{k} _ (Map1c_arrow PA PB)).
  - move=> f; apply tr.
    exists (fun a' => map PB (f (comap PA a'))).
    move=> a a' aR.
    rewrite (R_in_comap PA a' a aR).
    apply (map_in_R PB) => //.
  - move=> f f' /= e a a' aR; apply (map_in_R PB).
    apply (transport (fun t => _ = t a') e) => /=.
    by apply (transport (fun t => _ = map _ (f t)) (R_in_comap PA _ _ aR)^).
Defined.

Section Optimality_Map2a.
  Theorem D2a_arrow_right_isnt_2b: not (
      forall (A A' : Type) (AR: Param02b.Rel A A'),
      forall (B B' : Type) (BR: Param2b0.Rel B B'),

      Map2a.Has (R_arrow AR BR)
    ).
  Proof.
    intro Habs.
    specialize (Habs Unit Unit p2b2b_true).
    specialize (Habs Unit Unit p2b2b_empty_R).
    move: Habs => [is_total map R_in_map].

    move: (R_in_map id (map id) idpath).
    move=> H; move: {H}(H tt tt) => H.
    rewrite /p2b2b_true /p2b2b_empty_R /= in H.
    case: (H tt).
  Qed.

  From HoTT Require Import Contrib.HoTTBookExercises.

  Theorem D2a_arrow_right_isnt_1a `{Univalence}: not (
    forall (A A' : Type) (AR: Param02b.Rel A A'),
    forall (B B' : Type) (BR: Param1a0.Rel B B'),

    Map2a.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    move: (Habs _ _ p2b2b_bool) => {}Habs.
    move: (fun {A: Type} (tr_a: merely A) =>
      let map1a := merely_to_M1a tr_a in
      let param1a0 := Param1a0.BuildRel _ _ _ map1a (Map0.BuildHas _ _ _) in
      Habs _ _ param1a0
    ) => {}Habs.

    move: Habs.
    rewrite /R_arrow /= => Habs.

    pose G A tr_a := Map2a.map _ (Habs A tr_a) (fun _ => tt) true.

    elim (Book_3_11 G).
  Qed.

  Theorem D2a_arrow_left_isnt_2a: not (
      forall (A A' : Type) (AR: Param02a.Rel A A'),
      forall (B B' : Type) (BR: Param2a0.Rel B B'),

      Map2a.Has (R_arrow AR BR)
    ).
  Proof.
    intro Habs.
    specialize (Habs Bool Bool p2a2a_A).
    specialize (Habs Bool Bool p2a2a_bool).
    move: Habs => [is_total map map_in_R].

    move: (map_in_R id (map id) idpath) => H.
    rewrite /R_arrow /p2a2a_A /p2a2a_bool /= in H.

    assert (forall b, b = map id false) as Habs
    by (move=> b; apply (H b false tt)).

    specialize (Habs true) as Htrue.
    move: (Habs false); move=> Hfalse.
    rewrite -Hfalse in Htrue => {Hfalse}.
    destruct (true_ne_false Htrue).
  Qed.

  Theorem D2a_arrow_left_isnt_1b: not (
      forall (A A' : Type) (AR: Param01b.Rel A A'),
      forall (B B' : Type) (BR: Param2a0.Rel B B'),

      Map2a.Has (R_arrow AR BR)
    ).
  Proof.
    intro Habs.
    specialize (Habs False Unit p01b).
    specialize (Habs _ _ p2a0_empty_R).
    move: Habs => [is_total _ _].
    specialize (is_total id).
    apply (merely_destruct is_total).
    move=> [b _] ; destruct (b tt).
  Qed.
End Optimality_Map2a.

(* (02a, 2b0) + funext -> 2b0 *)
Definition Map2b_arrow@{i j k | i <= k, j <= k} `{Funext}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param2b0.Rel@{j} B B') :
    Map2b.Has@{k} (R_arrow PA PB).
Proof.
  exists (Map1c.map@{k} _ (Map1c_arrow PA PB)).
  - move=> f g h Rfg Rfh.
    apply path_forall=> x.
    rewrite -(R_in_map PB (f (comap PA x)) (h x)).
    + rewrite -(R_in_map PB (f (comap PA x)) (g x)) //.
      apply Rfg, (comap_in_R PA) => //.
    + apply Rfh, (comap_in_R PA) => //.
  - move=> f f' /= fR; apply path_forall => a'.
    by apply (R_in_map PB); apply fR; apply (comap_in_R PA).
Defined.

Section Optimality_Map2b.
  Theorem D2b_arrow_right_isnt_2a: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param2a0.Rel B B'),

    Map2b.Has (R_arrow AR BR)
  ).
  Proof.
    intro Habs.
    specialize (Habs Unit Unit p2a2a_true).
    specialize (Habs Bool Bool p2a2a_A).
    move: Habs => [_ map map_in_R].

    assert (forall f g, map f = g) as Habs
    by (move=> f g ; apply map_in_R => //).

    have X := Habs (unit_name true) (unit_name true).
    rewrite (Habs (unit_name true) (unit_name false)) in X.
    destruct (false_ne_true (ap10 X tt)).
  Qed.

  Definition p1b0_unit_false : Param1b0.Rel Unit False.
  Proof.
    exists (fun _ _ => True).
    - exists=> _ []. 
    - exists.
  Defined.

  Theorem D2b_arrow_right_isnt_1b: not (
    forall (A A' : Type) (AR: Param02a.Rel A A'),
    forall (B B' : Type) (BR: Param1b0.Rel B B'),

    Map2b.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    specialize (Habs _ _ p2a2a_true).
    specialize (Habs _ _ p1b0_unit_false).
    move: Habs => [_ map R_in_map].
    destruct (map id tt).
  Qed.

  From HoTT Require Import Contrib.HoTTBookExercises.

  Theorem D2b_arrow_left_isnt_1a `{Univalence}: not (
    forall (A A' : Type) (AR: Param01a.Rel A A'),
    forall (B B' : Type) (BR: Param2b0.Rel B B'),

    Map2b.Has (R_arrow AR BR)
  ).
  Proof.
    move=> Habs.
    move: (fun {A: Type} (tr_a: merely A) =>
      let map1a := merely_to_M1a tr_a in
      let param01a := Param01a.BuildRel _ _ _ (Map0.BuildHas _ _ _) map1a in
      Habs _ _ param01a A A p2b0_A
    ) => {}Habs.

    move: Habs.
    rewrite /R_arrow /= => Habs.

    pose G A tr_a := Map2b.map _ (Habs A tr_a) id tt.

    elim (Book_3_11 G).
  Qed.
End Optimality_Map2b.

(* (03, 30) + funext -> 30 *)
Definition Map3_arrow@{i j k | i <= k, j <= k} `{Funext}
  {A A' : Type@{i}} (PA : Param03.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param30.Rel@{j} B B') :
    Map3.Has@{k} (R_arrow PA PB).
Proof.
  exists (Map1c.map@{k} _ (Map1c_arrow PA PB)).
  - move=> f g h Rfg Rfh.
    apply path_forall=> x.
    rewrite -(R_in_map PB (f (comap PA x)) (h x)).
    + rewrite -(R_in_map PB (f (comap PA x)) (g x)) //.
      apply Rfg, (comap_in_R PA) => //.
    + apply Rfh, (comap_in_R PA) => //.
  - move=> f; apply tr.
    exists (fun a' => map PB (f (comap PA a'))).
    move=> a a' aR.
    rewrite (R_in_comap PA a' a aR).
    apply (map_in_R PB) => //.
  - exact: (Map2a.map_in_R _ (Map2a_arrow PA PB)).
  - move=> f f' /= fR; apply path_arrow => a'.
    by apply (R_in_map PB); apply fR; apply (comap_in_R PA).
Defined.

(* (04, 40) + funext -> 40 *)
Definition Map4_arrow@{i j k | i <= k, j <= k} `{Funext}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param40.Rel@{j} B B') :
    Map4.Has@{k} (R_arrow PA PB).
Proof.
  exists
    (Map1c.map@{k} _ (Map1c_arrow PA PB))
    (Map2a.map_in_R _ (Map2a_arrow PA PB))
    (Map2b.R_in_map _ (Map2b_arrow PA PB)).
  - move=> f g h Rfg Rfh.
    apply path_forall=> x.
    rewrite -(R_in_map PB (f (comap PA x)) (h x)).
    + rewrite -(R_in_map PB (f (comap PA x)) (g x)) //.
      apply Rfg, (comap_in_R PA) => //.
    + apply Rfh, (comap_in_R PA) => //.
  - move=> f; apply tr.
    exists (fun a' => map PB (f (comap PA a'))).
    move=> a a' aR.
    rewrite (R_in_comap PA a' a aR).
    apply (map_in_R PB) => //.
  - move=> f f' fR /=.
    apply path_forall@{i k k} => a.
    apply path_forall@{i k k} => a'.
    apply path_arrow@{i k k} => aR /=.
    rewrite -[in X in _ = X](R_in_comapK PA a' a aR).
    elim (R_in_comap PA a' a aR).
    rewrite transport_apD10 /=.
    rewrite apD10_path_forall_cancel/=.
    rewrite <- (R_in_mapK PB).
    by elim: (R_in_map _ _ _ _).
Defined.

(***************)


(* Aliasing *)

Declare Scope param_scope.
Local Open Scope param_scope.
Delimit Scope param_scope with P.

Notation UParam := Param44.Rel.
Notation MkUParam := Param44.BuildRel.
Notation "A <=> B" := (Param44.Rel A B) : param_scope.
Notation IsUMap := Map4.Has.
Notation MkUMap := Map4.BuildHas.
Arguments Map4.BuildHas {A B R}.
Arguments Param44.BuildRel {A B R}.

(* symmetry lemmas for Map *)

Definition eq_Map0@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof.
  move=> RR' []; exists.
Defined.

Definition eq_Map0a@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map0a.Has@{i} R' -> Map0a.Has@{i} R.
Proof.
  move=> RR' [Sm Pa]; exists Sm. exact.
Defined.

Definition eq_Map0b@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map0b.Has@{i} R' -> Map0b.Has@{i} R.
Proof.
  move=> RR' [Sm Pb]; exists Sm. exact.
Defined.

Definition eq_Map1@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof.
  move=> RR' [Sm Pa Pb m SmR]; exists Sm m ; exact.
Defined.

Definition eq_Map2a@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof.
  move=> RR' [Sm Pa Pb m SmR mR] ; exists Sm m ; try exact.
  - move=> a b /mR /(RR' _ _)^-1%equiv; exact.
Defined.

Definition eq_Map2b@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof.
  move=> RR' [Sm Pa Pb m SmR Rm]. unshelve eexists Sm m ; try exact.
  - move=> a' b /(RR' _ _)/Rm; exact.
Defined.

Definition eq_Map3@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof.
  move=> RR' [Sm Pa Pb m SmR mR Rm]; unshelve eexists Sm m ; try exact.
  - move=> a' b /mR /(RR' _ _)^-1%equiv; exact.
  - move=> a' b /(RR' _ _)/Rm; exact.
Defined.

Definition eq_Map4@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map4.Has@{i} R' -> Map4.Has@{i} R.
Proof.
move=> RR' [Sm Pa Pb m SmR mR Rm RmK]; unshelve eexists Sm m _ _ ; try exact.
- move=> a' b /mR /(RR' _ _)^-1%equiv; exact.
- move=> a' b /(RR' _ _)/Rm; exact.
- by move=> a' b r /=; rewrite RmK [_^-1%function _]equiv_funK.
Defined.

(* joined elimination of comap and comap_in_R *)

Definition comap_ind {A A' : Type} {PA : Param04.Rel A A'}
    (a : A) (a' : A') (aR : PA a a')
    (P : forall (a : A), PA a a' -> Type)  :
   P a aR -> P (comap PA a') (comap_in_R PA a' (comap PA a') idpath).
Proof.
apply (transport
  (fun aR0 : PA a a' =>
    P a aR0 -> P (comap PA a')
                 (comap_in_R PA a' (comap PA a') idpath))
  (R_in_comapK PA a' a aR)
  (paths_rect A (comap PA a')
  (fun (a0 : A) (e : comap PA a' = a0) =>
   P a0 (comap_in_R PA a' a0 e) ->
   P (comap PA a')
    (comap_in_R PA a' (comap PA a') idpath)) idmap a
  (R_in_comap PA a' a aR))).
Defined.

(* proofs about Param44 *)

Lemma umap_equiv_sigma (A B : Type@{i}) (R : A -> B -> Type@{i}) :
  IsUMap R <~>
    { mapR : A -> B -> Type@{i} |
    { is_right_unique : forall a b c, mapR a b -> mapR a c -> b = c |
    { is_total : forall a, merely (exists b, mapR a b) |
    { map : A -> B |
    { mapR_is_map : forall a b, map a = b <-> mapR a b |
    { mR : forall (a : A) (b : B), map a = b -> R a b |
    { Rm : forall (a : A) (b : B), R a b -> map a = b |
      forall (a : A) (b : B), mR a b o Rm a b == idmap } } } } } } }.
Proof. by symmetry; issig. Defined.

Lemma umap_equiv_isfun `{Funext} {A B : Type@{i}}
  (R : A -> B -> Type@{i}) : IsUMap R <~> IsFun R.
Proof.
(* apply (equiv_composeR' (umap_equiv_sigma _ _ R)).
transitivity (forall x : A, {y : B & {r : R x y & forall yr', (y; r) = yr'}});
last first. {
  apply equiv_functor_forall_id => a.
  apply (equiv_compose' (issig_contr _)).
  apply equiv_sigma_assoc'.
}
apply (equiv_compose' (equiv_sig_coind _ _)).
apply equiv_functor_sigma_id => _ _ _ map.
apply (equiv_compose' (equiv_sig_coind _ _)).
apply (equiv_composeR' (equiv_sigma_symm _)).
transitivity {f : forall x, R x (map x) &
  forall (x : A) (y : B) (r :  R x y), (map x; f x) = (y; r)};
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: (equiv_composeR' equiv_forall_sigma).
}
transitivity
  { f : forall x, R x (map x) &
    forall (x : A) (y : B) (r :  R x y), {e : map x = y & e # f x = r} };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  apply (equiv_compose' equiv_path_sigma_dp).
  apply equiv_functor_sigma_id => e.
  exact: equiv_dp_path_transport.
}
transitivity
  { f : forall x, R x (map x) &
    forall x y, {g : forall (r :  R x y), map x = y &
    forall (r :  R x y), g r # f x = r } };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  exact: equiv_sig_coind.
}
transitivity  { f : forall x, R x (map x) &
    forall x, { g : forall (y : B) (r :  R x y), map x = y &
                forall (y : B) (r :  R x y), g y r # f x = r } };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: equiv_sig_coind.
}
transitivity
  { f : forall x, R x (map x) &
    {g : forall (x : A) (y : B) (r :  R x y), map x = y &
         forall x y r, g x y r # f x = r } };
last first.
{ apply equiv_functor_sigma_id => comap; exact: equiv_sig_coind. }
apply (equiv_compose' (equiv_sigma_symm _)).
apply equiv_functor_sigma_id => Rm.
transitivity
  { g : forall (x : A) (y : B) (e : map x = y), R x y &
    forall (x : A) (y : B) (r : R x y), Rm x y r # g x (map x) idpath = r }. {
  apply equiv_functor_sigma_id => mR.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  unshelve econstructor. { apply: concat. elim (Rm a b r). reflexivity. }
  unshelve econstructor. { apply: concat. elim (Rm a b r). reflexivity. }
  all: move=> r'; elim r'; elim (Rm a b r); reflexivity.
}
symmetry.
unshelve eapply equiv_functor_sigma.
- move=> mR a b e; exact (e # mR a).
- move=> mR mRK x y r; apply: mRK.
- apply: isequiv_biinv.
  split; (unshelve eexists; first by move=> + a; apply) => //.
  move=> r; apply path_forall => a; apply path_forall => b.
  by apply path_arrow; elim.
- by move=> mR; unshelve econstructor.
Defined. *)
Admitted.

Lemma uparam_equiv `{Univalence} {A B : Type} : (A <=> B) <~> (A <~> B).
Proof.
apply (equiv_compose' equiv_sig_relequiv^-1).
unshelve eapply equiv_adjointify.
- move=> [R mR msR]; exists R; exact: umap_equiv_isfun.
- move=> [R mR msR]; exists R; exact: (umap_equiv_isfun _)^-1%equiv.
- by move=> [R mR msR]; rewrite !equiv_invK.
- by move=> [R mR msR]; rewrite !equiv_funK.
Defined.

Definition id_umap {A : Type} : IsUMap (@paths A).
Proof.
  unshelve eexists.
  - move=> a b ; exact (a = b).
  - rewrite /id //.
  - rewrite /id //.
  - rewrite /id //.
  - move=> a b c /= [] //.
  - move=> a; apply: tr.
    by exists a.
  - rewrite /id //.
  - rewrite /id //.
Qed.

Definition id_sym_umap {A : Type} : IsUMap (sym_rel (@paths A)).
Proof.
  unshelve eexists.
  - move=> a b ; exact (a = b).
  - rewrite /sym_rel /id //.
  - rewrite /sym_rel /id //.
  - rewrite /sym_rel /id //.
  - move=> a b c /= [] //.
  - move=> a; apply: tr.
    by exists a.
  - rewrite /sym_rel /id //.
  - rewrite /sym_rel /id.
    move=> a b r. apply inv_V.
Qed.

Definition id_uparam {A : Type} : A <=> A :=
  MkUParam id_umap id_sym_umap.

Lemma uparam_induction `{Univalence} A (P : forall B, A <=> B -> Type) :
  P A id_uparam -> forall B f, P B f.
Proof.
move=> PA1 B f; rewrite -[f]/(B; f).2 -[B]/(B; f).1.
suff : (A; id_uparam) = (B; f). { elim. done. }
apply: path_ishprop; apply: hprop_inhabited_contr => _.
apply: (contr_equiv' {x : _ & A = x}).
apply: equiv_functor_sigma_id => {f} B.
symmetry; apply: equiv_compose' uparam_equiv.
exact: equiv_path_universe.
Defined.

Lemma uparam_equiv_id `{Univalence} A :
  uparam_equiv (@id_uparam A) = equiv_idmap.
(* Proof. exact: path_equiv. Defined. *)
Admitted.

(* instances of MapN for A = A *)
(* allows to build id_ParamMN : forall A, ParamMN.Rel A A *)

Definition id_Map0 {A : Type} : Map0.Has (@paths A).
Proof.
  constructor.
  move=> _ _; exact True.
Defined.

Definition id_Map0_sym {A : Type} : Map0.Has (sym_rel (@paths A)).
Proof.
  constructor.
  move=> _ _; exact True.
Defined.

Definition id_Map1 {A : Type} : Map1.Has (@paths A).
Proof.
Admitted.

Definition id_Map1_sym {A : Type} : Map1.Has (sym_rel (@paths A)).
(* Proof. constructor. exact idmap. Defined. *)
Admitted.

Definition id_Map2a {A : Type} : Map2a.Has (@paths A).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined. *)

Definition id_Map2a_sym {A : Type} : Map2a.Has (sym_rel (@paths A)).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined. *)

Definition id_Map2b {A : Type} : Map2b.Has (@paths A).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined. *)

Definition id_Map2b_sym {A : Type} : Map2b.Has (sym_rel (@paths A)).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined. *)

Definition id_Map3 {A : Type} : Map3.Has (@paths A).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
Defined. *)

Definition id_Map3_sym {A : Type} : Map3.Has (sym_rel (@paths A)).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
Defined. *)

Definition id_Map4 {A : Type} : Map4.Has (@paths A).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
  - exact (fun a b e => 1%path).
Defined. *)

Definition id_Map4_sym {A : Type} : Map4.Has (sym_rel (@paths A)).
Proof.
Admitted.
  (* unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
  - exact (fun A B e => inv_V e).
Defined. *)

(* generate id_ParamMN : forall A, ParamMN.Rel A A for all M N *)

Elpi Accumulate lp:{{
  pred generate-id-param i:param-class, i:univ, i:univ.variable.
  generate-id-param (pc M N as Class) U L :-
    map-class->string M MStr,
    map-class->string N NStr,
    coq.univ-instance UI [L],
    trocq.db.rel Class _ BuildRel _ _ _,
    Paths = {paths},
    coq.locate {calc ("id_Map" ^ MStr)} IdMap,
    coq.locate {calc ("id_Map" ^ NStr ^ "_sym")} IdMapSym,
    Decl =
      (fun `A` (sort (typ U)) a\
        app [pglobal BuildRel UI, a, a, app [pglobal Paths UI, a],
          app [pglobal IdMap UI, a],
          app [pglobal IdMapSym UI, a]]),
    IdParam is "id_Param" ^ MStr ^ NStr,
    @udecl! [L] ff [] ff => coq.env.add-const IdParam Decl _ @transparent! _.
}}.
Elpi Typecheck.

(* Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-classes all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-id-param (pc m n) U L
    )
  ).
}}. *)

(* Check id_Param00. *)
(* Check id_Param32b. *)

(* symmetry property for Param *)

Elpi Accumulate lp:{{
  pred generate-param-sym i:param-class, i:univ, i:univ.variable.
  generate-param-sym (pc M N as Class) U L :-
    map-class->string M MStr,
    map-class->string N NStr,
    coq.univ-instance UI [L],
    trocq.db.rel Class RelMN _ RMN CovariantMN ContravariantMN,
    trocq.db.rel (pc N M) _ BuildRelNM _ _ _,
    SymRel = {sym-rel},
    Decl =
      (fun `A` (sort (typ U)) a\ fun `B` (sort (typ U)) b\
        fun `P` (app [pglobal RelMN UI, a, b]) p\
          app [pglobal BuildRelNM UI, b, a,
            app [pglobal SymRel UI, a, b, app [pglobal RMN UI, a, b, p]],
            app [pglobal ContravariantMN UI, a, b, p],
            app [pglobal CovariantMN UI, a, b, p]
          ]),
    ParamSym is "Param" ^ MStr ^ NStr ^ "_sym",
    @udecl! [L] ff [] ff => coq.env.add-const ParamSym Decl _ @transparent! _.
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

(* Check Param33_sym.
Check Param2a4_sym. *)
