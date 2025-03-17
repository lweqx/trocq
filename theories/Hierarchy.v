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

Definition is_epic {A B: Type} (f: A -> B) :=
  forall (C: Type) (g1 g2: B -> C), g1 o f = g2 o f -> g1 = g2.

Lemma epic_implies_merely_surj `{Univalence} {A B: Type} (f: A -> B):
  is_epic f -> forall b, merely (exists a, f a = b).
Proof.
  move=> f_is_epic.

  set g1 := fun (_: B) => True.
  set g2 := fun (b: B) => merely (exists a, f a = b).
  have := f_is_epic _ g1 g2 => H' b.

  assert (g1 o f = g2 o f).
  - apply path_forall=> x.
    rewrite /g1 /g2.
    apply equiv_path_universe.
    unshelve apply /equiv_adjointify.
    + move=> _; apply tr.
      by exists x.
    + done.
    + move=> t ; apply path_ishprop.
    + by case.
  - have := ap10 (H' X) b.
    rewrite /g1 /g2.
    by case: _ /.
Qed.

Definition compose_rel@{i} {A B C: Type@{i}} (Q: B -> C -> Type@{i}) (R: A -> B -> Type@{i}) : A -> C -> Type@{i} :=
  fun a c => exists b, R a b /\ Q b c.
Notation "R 'oR' Q" := (compose_rel R Q).

Definition is_rel_epic@{i +} {A B: Type@{i}} (R: A -> B -> Type@{i}) :=
  forall (C: Type@{i}) (g1 g2: B -> C -> Type@{i}), g1 oR R = g2 oR R -> g1 = g2.

Lemma epic_rel_implies_total `{Univalence} {A B: Type} (R: A -> B -> Type):
  is_rel_epic R -> forall b, merely (exists a, R a b).
Proof.
  move=> R_is_epic.

  set g1 := fun (_: B) (_: Unit) => True.
  set g2 := fun (b: B) (_: Unit) => merely (exists a, R a b).
  have := R_is_epic _ g1 g2 => H' b.

  assert (g1 oR R = g2 oR R).
  - apply path_forall=> x.
    rewrite /g1 /g2 /compose_rel.
    apply path_forall; case.
    apply equiv_path_universe.
    unshelve apply /equiv_adjointify.
    + move=> [b0 [r _]].
      exists b0.
      split ; [exact r |].
      apply tr.
      by exists x.
    + move=> [b0 [r _]].
      exists b0.
      by split.
    + move=> [b0 [r mer]].
      have := path_ishprop (tr (x; r)) mer.
      by case: _ /.
    + move=> [b0 [r t]].
      by case t.
  - have := ap10 (H' X) b.
    rewrite /g1 /g2.
    move=> eq.
    by case: _ / (ap10 eq).
Qed.

(* first unilateral witnesses describing one side of the structure given to a relation *)

Module Map0.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
}.
End Map0.

Module Map1a.
Record Has@{i j} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_total : is_rel_epic@{i j} (sym_rel R)
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
Record Has@{i j} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_total : is_rel_epic@{i j} (sym_rel R);
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
Record Has@{i j} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_total : is_rel_epic@{i j} (sym_rel R);
  is_right_unique : forall a b c, R a b -> R a c -> b = c;
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map3.

Module Map4.
(* An alternative presentation of Sozeau, Tabareau, Tanter's univalent parametricity:
   symmetrical and transport-free *)
Record Has@{i j} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  is_total : is_rel_epic@{i j} (sym_rel R);
  is_right_unique : forall a b c, R a b -> R a c -> b = c;
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

(* Elpi Accumulate lp:{{
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
          end Map0.-record)))),
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
}}. *)

Module Param00.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
  End Param00.

Module Param01a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param01a.

Module Param01b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param01b.

Module Param01c.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param01c.

Module Param02b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param02b.

Module Param02a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param02a.

Module Param03.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param03.

Module Param04.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map0.Has@{u} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param04.

Module Param1c0.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param1c0.

Module Param1c1a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param1c1a.

Module Param1c1b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param1c1b.

Module Param1c1c.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param1c1c.

Module Param1c2b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param1c2b.

Module Param1c2a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param1c2a.

Module Param1c3.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param1c3.

Module Param1c4.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1c.Has@{u} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param1c4.

Module Param1a0.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param1a0.

Module Param1a1a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param1a1a.

Module Param1a1b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param1a1b.

Module Param1a1c.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param1a1c.

Module Param1a2b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param1a2b.

Module Param1a2a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param1a2a.

Module Param1a3.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param1a3.

Module Param1a4.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1a.Has@{u v} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param1a4.

Module Param1b0.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param1b0.

Module Param1b1a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param1b1a.

Module Param1b1b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param1b1b.

Module Param1b1c.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param1b1c.

Module Param1b2b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param1b2b.

Module Param1b2a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param1b2a.

Module Param1b3.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param1b3.

Module Param1b4.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map1b.Has@{u} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param1b4.

Module Param2a0.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param2a0.

Module Param2a1a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param2a1a.

Module Param2a1b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param2a1b.

Module Param2a1c.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param2a1c.

Module Param2a2b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param2a2b.

Module Param2a2a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param2a2a.

Module Param2a3.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param2a3.

Module Param2a4.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2a.Has@{u v} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param2a4.

Module Param2b0.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param2b0.

Module Param2b1a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param2b1a.

Module Param2b1b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param2b1b.

Module Param2b1c.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param2b1c.

Module Param2b2b.
	 Record Rel@{u} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param2b2b.

Module Param2b2a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param2b2a.

Module Param2b3.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param2b3.

Module Param2b4.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map2b.Has@{u} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param2b4.

Module Param30.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param30.

Module Param31a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param31a.

Module Param31b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param31b.

Module Param31c.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param31c.

Module Param32b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param32b.

Module Param32a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param32a.

Module Param33.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param33.

Module Param34.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map3.Has@{u v} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param34.

Module Param40.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map0.Has@{u} (sym_rel@{u} R) }.
   End Param40.

Module Param41a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map1a.Has@{u v} (sym_rel@{u} R) }.
   End Param41a.

Module Param41b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map1b.Has@{u} (sym_rel@{u} R) }.
   End Param41b.

Module Param41c.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map1c.Has@{u} (sym_rel@{u} R) }.
   End Param41c.

Module Param42b.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map2b.Has@{u} (sym_rel@{u} R) }.
   End Param42b.

Module Param42a.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map2a.Has@{u v} (sym_rel@{u} R) }.
   End Param42a.

Module Param43.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map3.Has@{u v} (sym_rel@{u} R) }.
   End Param43.

Module Param44.
	 Record Rel@{u v} (A B : Type@{u}) := BuildRel
       { R : A -> B -> Type@{u};
         covariant : Map4.Has@{u v} R;
         contravariant : Map4.Has@{u v} (sym_rel@{u} R) }.
   End Param44.

(********************)
(* Record Weakening *)
(********************)

Coercion forgetMap43@{i j}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map4.Has@{i j} R) : Map3.Has@{i j} R :=
    @Map3.BuildHas A B R
      (@Map4.is_total A B R m)
      (@Map4.is_right_unique A B R m)
      (@Map4.map A B R m)
      (@Map4.map_in_R A B R m)
      (@Map4.R_in_map A B R m).

Coercion forgetMap32a@{i j}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map3.Has@{i j} R) : Map2a.Has@{i j} R :=
    @Map2a.BuildHas A B R
      (@Map3.is_total A B R m)
      (@Map3.map A B R m)
      (@Map3.map_in_R A B R m).

Coercion forgetMap32b@{i j}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map3.Has@{i j} R) : Map2b.Has@{i} R :=
    @Map2b.BuildHas A B R
      (@Map3.is_right_unique A B R m)
      (@Map3.map A B R m)
      (@Map3.R_in_map A B R m).

Coercion forgetMap2a1a@{i j}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2a.Has@{i j} R) : Map1a.Has@{i j} R :=
    @Map1a.BuildHas A B R
      (@Map2a.is_total A B R m).

Coercion forgetMap2b1b@{i}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2b.Has@{i} R) : Map1b.Has@{i} R :=
    @Map1b.BuildHas A B R
      (@Map2b.is_right_unique A B R m).

Coercion forgetMap2a1c@{i j}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map2a.Has@{i j} R) : Map1c.Has@{i} R :=
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

Coercion forgetMap1a0@{i j}
  {A B : Type@{i}} {R : A -> B -> Type@{i}} (m : Map1a.Has@{i j} R) : Map0.Has@{i} R :=
    @Map0.BuildHas A B R.

(* Elpi Accumulate lp:{{
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

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-classes all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-forget (pc m n) U L
    )
  ).
}}. *)

Coercion forget_01a_00@{u v} :=
fun (A B : Type@{u}) (P : Param01a.Rel@{u v} A B) =>
{|
  Param00.R := Param01a.R@{u v} A B P;
  Param00.covariant := Param01a.covariant@{u v} A B P;
  Param00.contravariant := Param01a.contravariant@{u v} A B P
|}
.


Coercion forget_01b_00@{u} :=
fun (A B : Type@{u}) (P : Param01b.Rel@{u} A B) =>
{|
  Param00.R := Param01b.R@{u} A B P;
  Param00.covariant := Param01b.covariant@{u} A B P;
  Param00.contravariant := Param01b.contravariant@{u} A B P
|}
.


Coercion forget_01c_00@{u} :=
fun (A B : Type@{u}) (P : Param01c.Rel@{u} A B) =>
{|
  Param00.R := Param01c.R@{u} A B P;
  Param00.covariant := Param01c.covariant@{u} A B P;
  Param00.contravariant := Param01c.contravariant@{u} A B P
|}
.


Coercion forget_02a_01a@{u v} :=
fun (A B : Type@{u}) (P : Param02a.Rel@{u v} A B) =>
{|
  Param01a.R := Param02a.R@{u v} A B P;
  Param01a.covariant := Param02a.covariant@{u v} A B P;
  Param01a.contravariant := Param02a.contravariant@{u v} A B P
|}
.


Coercion forget_02a_01c@{u v} :=
fun (A B : Type@{u}) (P : Param02a.Rel@{u v} A B) =>
{|
  Param01c.R := Param02a.R@{u v} A B P;
  Param01c.covariant := Param02a.covariant@{u v} A B P;
  Param01c.contravariant := Param02a.contravariant@{u v} A B P
|}
.


Coercion forget_02b_01b@{u} :=
fun (A B : Type@{u}) (P : Param02b.Rel@{u} A B) =>
{|
  Param01b.R := Param02b.R@{u} A B P;
  Param01b.covariant := Param02b.covariant@{u} A B P;
  Param01b.contravariant := Param02b.contravariant@{u} A B P
|}
.


Coercion forget_02b_01c@{u} :=
fun (A B : Type@{u}) (P : Param02b.Rel@{u} A B) =>
{|
  Param01c.R := Param02b.R@{u} A B P;
  Param01c.covariant := Param02b.covariant@{u} A B P;
  Param01c.contravariant := Param02b.contravariant@{u} A B P
|}
.


Coercion forget_03_02a@{u v} :=
fun (A B : Type@{u}) (P : Param03.Rel@{u v} A B) =>
{|
  Param02a.R := Param03.R@{u v} A B P;
  Param02a.covariant := Param03.covariant@{u v} A B P;
  Param02a.contravariant := Param03.contravariant@{u v} A B P
|}
.


Coercion forget_03_02b@{u v} :=
fun (A B : Type@{u}) (P : Param03.Rel@{u v} A B) =>
{|
  Param02b.R := Param03.R@{u v} A B P;
  Param02b.covariant := Param03.covariant@{u v} A B P;
  Param02b.contravariant := Param03.contravariant@{u v} A B P
|}
.


Coercion forget_04_03@{u v} :=
fun (A B : Type@{u}) (P : Param04.Rel@{u v} A B) =>
{|
  Param03.R := Param04.R@{u v} A B P;
  Param03.covariant := Param04.covariant@{u v} A B P;
  Param03.contravariant := Param04.contravariant@{u v} A B P
|}
.


Coercion forget_1a0_00@{u v} :=
fun (A B : Type@{u}) (P : Param1a0.Rel@{u v} A B) =>
{|
  Param00.R := Param1a0.R@{u v} A B P;
  Param00.covariant := Param1a0.covariant@{u v} A B P;
  Param00.contravariant := Param1a0.contravariant@{u v} A B P
|}
.


Coercion forget_1a1a_01a@{u v} :=
fun (A B : Type@{u}) (P : Param1a1a.Rel@{u v} A B) =>
{|
  Param01a.R := Param1a1a.R@{u v} A B P;
  Param01a.covariant := Param1a1a.covariant@{u v} A B P;
  Param01a.contravariant := Param1a1a.contravariant@{u v} A B P
|}
.


Coercion forget_1a1a_1a0@{u v} :=
fun (A B : Type@{u}) (P : Param1a1a.Rel@{u v} A B) =>
{|
  Param1a0.R := Param1a1a.R@{u v} A B P;
  Param1a0.covariant := Param1a1a.covariant@{u v} A B P;
  Param1a0.contravariant := Param1a1a.contravariant@{u v} A B P
|}
.


Coercion forget_1a1b_01b@{u v} :=
fun (A B : Type@{u}) (P : Param1a1b.Rel@{u v} A B) =>
{|
  Param01b.R := Param1a1b.R@{u v} A B P;
  Param01b.covariant := Param1a1b.covariant@{u v} A B P;
  Param01b.contravariant := Param1a1b.contravariant@{u v} A B P
|}
.


Coercion forget_1a1b_1a0@{u v} :=
fun (A B : Type@{u}) (P : Param1a1b.Rel@{u v} A B) =>
{|
  Param1a0.R := Param1a1b.R@{u v} A B P;
  Param1a0.covariant := Param1a1b.covariant@{u v} A B P;
  Param1a0.contravariant := Param1a1b.contravariant@{u v} A B P
|}
.


Coercion forget_1a1c_01c@{u v} :=
fun (A B : Type@{u}) (P : Param1a1c.Rel@{u v} A B) =>
{|
  Param01c.R := Param1a1c.R@{u v} A B P;
  Param01c.covariant := Param1a1c.covariant@{u v} A B P;
  Param01c.contravariant := Param1a1c.contravariant@{u v} A B P
|}
.


Coercion forget_1a1c_1a0@{u v} :=
fun (A B : Type@{u}) (P : Param1a1c.Rel@{u v} A B) =>
{|
  Param1a0.R := Param1a1c.R@{u v} A B P;
  Param1a0.covariant := Param1a1c.covariant@{u v} A B P;
  Param1a0.contravariant := Param1a1c.contravariant@{u v} A B P
|}
.


Coercion forget_1a2a_02a@{u v} :=
fun (A B : Type@{u}) (P : Param1a2a.Rel@{u v} A B) =>
{|
  Param02a.R := Param1a2a.R@{u v} A B P;
  Param02a.covariant := Param1a2a.covariant@{u v} A B P;
  Param02a.contravariant := Param1a2a.contravariant@{u v} A B P
|}
.


Coercion forget_1a2a_1a1a@{u v} :=
fun (A B : Type@{u}) (P : Param1a2a.Rel@{u v} A B) =>
{|
  Param1a1a.R := Param1a2a.R@{u v} A B P;
  Param1a1a.covariant := Param1a2a.covariant@{u v} A B P;
  Param1a1a.contravariant := Param1a2a.contravariant@{u v} A B P
|}
.


Coercion forget_1a2a_1a1c@{u v} :=
fun (A B : Type@{u}) (P : Param1a2a.Rel@{u v} A B) =>
{|
  Param1a1c.R := Param1a2a.R@{u v} A B P;
  Param1a1c.covariant := Param1a2a.covariant@{u v} A B P;
  Param1a1c.contravariant := Param1a2a.contravariant@{u v} A B P
|}
.


Coercion forget_1a2b_02b@{u v} :=
fun (A B : Type@{u}) (P : Param1a2b.Rel@{u v} A B) =>
{|
  Param02b.R := Param1a2b.R@{u v} A B P;
  Param02b.covariant := Param1a2b.covariant@{u v} A B P;
  Param02b.contravariant := Param1a2b.contravariant@{u v} A B P
|}
.


Coercion forget_1a2b_1a1b@{u v} :=
fun (A B : Type@{u}) (P : Param1a2b.Rel@{u v} A B) =>
{|
  Param1a1b.R := Param1a2b.R@{u v} A B P;
  Param1a1b.covariant := Param1a2b.covariant@{u v} A B P;
  Param1a1b.contravariant := Param1a2b.contravariant@{u v} A B P
|}
.


Coercion forget_1a2b_1a1c@{u v} :=
fun (A B : Type@{u}) (P : Param1a2b.Rel@{u v} A B) =>
{|
  Param1a1c.R := Param1a2b.R@{u v} A B P;
  Param1a1c.covariant := Param1a2b.covariant@{u v} A B P;
  Param1a1c.contravariant := Param1a2b.contravariant@{u v} A B P
|}
.


Coercion forget_1a3_03@{u v} :=
fun (A B : Type@{u}) (P : Param1a3.Rel@{u v} A B) =>
{|
  Param03.R := Param1a3.R@{u v} A B P;
  Param03.covariant := Param1a3.covariant@{u v} A B P;
  Param03.contravariant := Param1a3.contravariant@{u v} A B P
|}
.


Coercion forget_1a3_1a2a@{u v} :=
fun (A B : Type@{u}) (P : Param1a3.Rel@{u v} A B) =>
{|
  Param1a2a.R := Param1a3.R@{u v} A B P;
  Param1a2a.covariant := Param1a3.covariant@{u v} A B P;
  Param1a2a.contravariant := Param1a3.contravariant@{u v} A B P
|}
.


Coercion forget_1a3_1a2b@{u v} :=
fun (A B : Type@{u}) (P : Param1a3.Rel@{u v} A B) =>
{|
  Param1a2b.R := Param1a3.R@{u v} A B P;
  Param1a2b.covariant := Param1a3.covariant@{u v} A B P;
  Param1a2b.contravariant := Param1a3.contravariant@{u v} A B P
|}
.


Coercion forget_1a4_04@{u v} :=
fun (A B : Type@{u}) (P : Param1a4.Rel@{u v} A B) =>
{|
  Param04.R := Param1a4.R@{u v} A B P;
  Param04.covariant := Param1a4.covariant@{u v} A B P;
  Param04.contravariant := Param1a4.contravariant@{u v} A B P
|}
.


Coercion forget_1a4_1a3@{u v} :=
fun (A B : Type@{u}) (P : Param1a4.Rel@{u v} A B) =>
{|
  Param1a3.R := Param1a4.R@{u v} A B P;
  Param1a3.covariant := Param1a4.covariant@{u v} A B P;
  Param1a3.contravariant := Param1a4.contravariant@{u v} A B P
|}
.


Coercion forget_1b0_00@{u} :=
fun (A B : Type@{u}) (P : Param1b0.Rel@{u} A B) =>
{|
  Param00.R := Param1b0.R@{u} A B P;
  Param00.covariant := Param1b0.covariant@{u} A B P;
  Param00.contravariant := Param1b0.contravariant@{u} A B P
|}
.


Coercion forget_1b1a_01a@{u v} :=
fun (A B : Type@{u}) (P : Param1b1a.Rel@{u v} A B) =>
{|
  Param01a.R := Param1b1a.R@{u v} A B P;
  Param01a.covariant := Param1b1a.covariant@{u v} A B P;
  Param01a.contravariant := Param1b1a.contravariant@{u v} A B P
|}
.


Coercion forget_1b1a_1b0@{u v} :=
fun (A B : Type@{u}) (P : Param1b1a.Rel@{u v} A B) =>
{|
  Param1b0.R := Param1b1a.R@{u v} A B P;
  Param1b0.covariant := Param1b1a.covariant@{u v} A B P;
  Param1b0.contravariant := Param1b1a.contravariant@{u v} A B P
|}
.


Coercion forget_1b1b_01b@{u} :=
fun (A B : Type@{u}) (P : Param1b1b.Rel@{u} A B) =>
{|
  Param01b.R := Param1b1b.R@{u} A B P;
  Param01b.covariant := Param1b1b.covariant@{u} A B P;
  Param01b.contravariant := Param1b1b.contravariant@{u} A B P
|}
.


Coercion forget_1b1b_1b0@{u} :=
fun (A B : Type@{u}) (P : Param1b1b.Rel@{u} A B) =>
{|
  Param1b0.R := Param1b1b.R@{u} A B P;
  Param1b0.covariant := Param1b1b.covariant@{u} A B P;
  Param1b0.contravariant := Param1b1b.contravariant@{u} A B P
|}
.


Coercion forget_1b1c_01c@{u} :=
fun (A B : Type@{u}) (P : Param1b1c.Rel@{u} A B) =>
{|
  Param01c.R := Param1b1c.R@{u} A B P;
  Param01c.covariant := Param1b1c.covariant@{u} A B P;
  Param01c.contravariant := Param1b1c.contravariant@{u} A B P
|}
.


Coercion forget_1b1c_1b0@{u} :=
fun (A B : Type@{u}) (P : Param1b1c.Rel@{u} A B) =>
{|
  Param1b0.R := Param1b1c.R@{u} A B P;
  Param1b0.covariant := Param1b1c.covariant@{u} A B P;
  Param1b0.contravariant := Param1b1c.contravariant@{u} A B P
|}
.


Coercion forget_1b2a_02a@{u v} :=
fun (A B : Type@{u}) (P : Param1b2a.Rel@{u v} A B) =>
{|
  Param02a.R := Param1b2a.R@{u v} A B P;
  Param02a.covariant := Param1b2a.covariant@{u v} A B P;
  Param02a.contravariant := Param1b2a.contravariant@{u v} A B P
|}
.


Coercion forget_1b2a_1b1a@{u v} :=
fun (A B : Type@{u}) (P : Param1b2a.Rel@{u v} A B) =>
{|
  Param1b1a.R := Param1b2a.R@{u v} A B P;
  Param1b1a.covariant := Param1b2a.covariant@{u v} A B P;
  Param1b1a.contravariant := Param1b2a.contravariant@{u v} A B P
|}
.


Coercion forget_1b2a_1b1c@{u v} :=
fun (A B : Type@{u}) (P : Param1b2a.Rel@{u v} A B) =>
{|
  Param1b1c.R := Param1b2a.R@{u v} A B P;
  Param1b1c.covariant := Param1b2a.covariant@{u v} A B P;
  Param1b1c.contravariant := Param1b2a.contravariant@{u v} A B P
|}
.


Coercion forget_1b2b_02b@{u} :=
fun (A B : Type@{u}) (P : Param1b2b.Rel@{u} A B) =>
{|
  Param02b.R := Param1b2b.R@{u} A B P;
  Param02b.covariant := Param1b2b.covariant@{u} A B P;
  Param02b.contravariant := Param1b2b.contravariant@{u} A B P
|}
.


Coercion forget_1b2b_1b1b@{u} :=
fun (A B : Type@{u}) (P : Param1b2b.Rel@{u} A B) =>
{|
  Param1b1b.R := Param1b2b.R@{u} A B P;
  Param1b1b.covariant := Param1b2b.covariant@{u} A B P;
  Param1b1b.contravariant := Param1b2b.contravariant@{u} A B P
|}
.


Coercion forget_1b2b_1b1c@{u} :=
fun (A B : Type@{u}) (P : Param1b2b.Rel@{u} A B) =>
{|
  Param1b1c.R := Param1b2b.R@{u} A B P;
  Param1b1c.covariant := Param1b2b.covariant@{u} A B P;
  Param1b1c.contravariant := Param1b2b.contravariant@{u} A B P
|}
.


Coercion forget_1b3_03@{u v} :=
fun (A B : Type@{u}) (P : Param1b3.Rel@{u v} A B) =>
{|
  Param03.R := Param1b3.R@{u v} A B P;
  Param03.covariant := Param1b3.covariant@{u v} A B P;
  Param03.contravariant := Param1b3.contravariant@{u v} A B P
|}
.


Coercion forget_1b3_1b2a@{u v} :=
fun (A B : Type@{u}) (P : Param1b3.Rel@{u v} A B) =>
{|
  Param1b2a.R := Param1b3.R@{u v} A B P;
  Param1b2a.covariant := Param1b3.covariant@{u v} A B P;
  Param1b2a.contravariant := Param1b3.contravariant@{u v} A B P
|}
.


Coercion forget_1b3_1b2b@{u v} :=
fun (A B : Type@{u}) (P : Param1b3.Rel@{u v} A B) =>
{|
  Param1b2b.R := Param1b3.R@{u v} A B P;
  Param1b2b.covariant := Param1b3.covariant@{u v} A B P;
  Param1b2b.contravariant := Param1b3.contravariant@{u v} A B P
|}
.


Coercion forget_1b4_04@{u v} :=
fun (A B : Type@{u}) (P : Param1b4.Rel@{u v} A B) =>
{|
  Param04.R := Param1b4.R@{u v} A B P;
  Param04.covariant := Param1b4.covariant@{u v} A B P;
  Param04.contravariant := Param1b4.contravariant@{u v} A B P
|}
.


Coercion forget_1b4_1b3@{u v} :=
fun (A B : Type@{u}) (P : Param1b4.Rel@{u v} A B) =>
{|
  Param1b3.R := Param1b4.R@{u v} A B P;
  Param1b3.covariant := Param1b4.covariant@{u v} A B P;
  Param1b3.contravariant := Param1b4.contravariant@{u v} A B P
|}
.


Coercion forget_1c0_00@{u} :=
fun (A B : Type@{u}) (P : Param1c0.Rel@{u} A B) =>
{|
  Param00.R := Param1c0.R@{u} A B P;
  Param00.covariant := Param1c0.covariant@{u} A B P;
  Param00.contravariant := Param1c0.contravariant@{u} A B P
|}
.


Coercion forget_1c1a_01a@{u v} :=
fun (A B : Type@{u}) (P : Param1c1a.Rel@{u v} A B) =>
{|
  Param01a.R := Param1c1a.R@{u v} A B P;
  Param01a.covariant := Param1c1a.covariant@{u v} A B P;
  Param01a.contravariant := Param1c1a.contravariant@{u v} A B P
|}
.


Coercion forget_1c1a_1c0@{u v} :=
fun (A B : Type@{u}) (P : Param1c1a.Rel@{u v} A B) =>
{|
  Param1c0.R := Param1c1a.R@{u v} A B P;
  Param1c0.covariant := Param1c1a.covariant@{u v} A B P;
  Param1c0.contravariant := Param1c1a.contravariant@{u v} A B P
|}
.


Coercion forget_1c1b_01b@{u} :=
fun (A B : Type@{u}) (P : Param1c1b.Rel@{u} A B) =>
{|
  Param01b.R := Param1c1b.R@{u} A B P;
  Param01b.covariant := Param1c1b.covariant@{u} A B P;
  Param01b.contravariant := Param1c1b.contravariant@{u} A B P
|}
.


Coercion forget_1c1b_1c0@{u} :=
fun (A B : Type@{u}) (P : Param1c1b.Rel@{u} A B) =>
{|
  Param1c0.R := Param1c1b.R@{u} A B P;
  Param1c0.covariant := Param1c1b.covariant@{u} A B P;
  Param1c0.contravariant := Param1c1b.contravariant@{u} A B P
|}
.


Coercion forget_1c1c_01c@{u} :=
fun (A B : Type@{u}) (P : Param1c1c.Rel@{u} A B) =>
{|
  Param01c.R := Param1c1c.R@{u} A B P;
  Param01c.covariant := Param1c1c.covariant@{u} A B P;
  Param01c.contravariant := Param1c1c.contravariant@{u} A B P
|}
.


Coercion forget_1c1c_1c0@{u} :=
fun (A B : Type@{u}) (P : Param1c1c.Rel@{u} A B) =>
{|
  Param1c0.R := Param1c1c.R@{u} A B P;
  Param1c0.covariant := Param1c1c.covariant@{u} A B P;
  Param1c0.contravariant := Param1c1c.contravariant@{u} A B P
|}
.


Coercion forget_1c2a_02a@{u v} :=
fun (A B : Type@{u}) (P : Param1c2a.Rel@{u v} A B) =>
{|
  Param02a.R := Param1c2a.R@{u v} A B P;
  Param02a.covariant := Param1c2a.covariant@{u v} A B P;
  Param02a.contravariant := Param1c2a.contravariant@{u v} A B P
|}
.


Coercion forget_1c2a_1c1a@{u v} :=
fun (A B : Type@{u}) (P : Param1c2a.Rel@{u v} A B) =>
{|
  Param1c1a.R := Param1c2a.R@{u v} A B P;
  Param1c1a.covariant := Param1c2a.covariant@{u v} A B P;
  Param1c1a.contravariant := Param1c2a.contravariant@{u v} A B P
|}
.


Coercion forget_1c2a_1c1c@{u v} :=
fun (A B : Type@{u}) (P : Param1c2a.Rel@{u v} A B) =>
{|
  Param1c1c.R := Param1c2a.R@{u v} A B P;
  Param1c1c.covariant := Param1c2a.covariant@{u v} A B P;
  Param1c1c.contravariant := Param1c2a.contravariant@{u v} A B P
|}
.


Coercion forget_1c2b_02b@{u} :=
fun (A B : Type@{u}) (P : Param1c2b.Rel@{u} A B) =>
{|
  Param02b.R := Param1c2b.R@{u} A B P;
  Param02b.covariant := Param1c2b.covariant@{u} A B P;
  Param02b.contravariant := Param1c2b.contravariant@{u} A B P
|}
.


Coercion forget_1c2b_1c1b@{u} :=
fun (A B : Type@{u}) (P : Param1c2b.Rel@{u} A B) =>
{|
  Param1c1b.R := Param1c2b.R@{u} A B P;
  Param1c1b.covariant := Param1c2b.covariant@{u} A B P;
  Param1c1b.contravariant := Param1c2b.contravariant@{u} A B P
|}
.


Coercion forget_1c2b_1c1c@{u} :=
fun (A B : Type@{u}) (P : Param1c2b.Rel@{u} A B) =>
{|
  Param1c1c.R := Param1c2b.R@{u} A B P;
  Param1c1c.covariant := Param1c2b.covariant@{u} A B P;
  Param1c1c.contravariant := Param1c2b.contravariant@{u} A B P
|}
.


Coercion forget_1c3_03@{u v} :=
fun (A B : Type@{u}) (P : Param1c3.Rel@{u v} A B) =>
{|
  Param03.R := Param1c3.R@{u v} A B P;
  Param03.covariant := Param1c3.covariant@{u v} A B P;
  Param03.contravariant := Param1c3.contravariant@{u v} A B P
|}
.


Coercion forget_1c3_1c2a@{u v} :=
fun (A B : Type@{u}) (P : Param1c3.Rel@{u v} A B) =>
{|
  Param1c2a.R := Param1c3.R@{u v} A B P;
  Param1c2a.covariant := Param1c3.covariant@{u v} A B P;
  Param1c2a.contravariant := Param1c3.contravariant@{u v} A B P
|}
.


Coercion forget_1c3_1c2b@{u v} :=
fun (A B : Type@{u}) (P : Param1c3.Rel@{u v} A B) =>
{|
  Param1c2b.R := Param1c3.R@{u v} A B P;
  Param1c2b.covariant := Param1c3.covariant@{u v} A B P;
  Param1c2b.contravariant := Param1c3.contravariant@{u v} A B P
|}
.


Coercion forget_1c4_04@{u v} :=
fun (A B : Type@{u}) (P : Param1c4.Rel@{u v} A B) =>
{|
  Param04.R := Param1c4.R@{u v} A B P;
  Param04.covariant := Param1c4.covariant@{u v} A B P;
  Param04.contravariant := Param1c4.contravariant@{u v} A B P
|}
.


Coercion forget_1c4_1c3@{u v} :=
fun (A B : Type@{u}) (P : Param1c4.Rel@{u v} A B) =>
{|
  Param1c3.R := Param1c4.R@{u v} A B P;
  Param1c3.covariant := Param1c4.covariant@{u v} A B P;
  Param1c3.contravariant := Param1c4.contravariant@{u v} A B P
|}
.


Coercion forget_2a0_1a0@{u v} :=
fun (A B : Type@{u}) (P : Param2a0.Rel@{u v} A B) =>
{|
  Param1a0.R := Param2a0.R@{u v} A B P;
  Param1a0.covariant := Param2a0.covariant@{u v} A B P;
  Param1a0.contravariant := Param2a0.contravariant@{u v} A B P
|}
.


Coercion forget_2a0_1c0@{u v} :=
fun (A B : Type@{u}) (P : Param2a0.Rel@{u v} A B) =>
{|
  Param1c0.R := Param2a0.R@{u v} A B P;
  Param1c0.covariant := Param2a0.covariant@{u v} A B P;
  Param1c0.contravariant := Param2a0.contravariant@{u v} A B P
|}
.


Coercion forget_2a1a_1a1a@{u v} :=
fun (A B : Type@{u}) (P : Param2a1a.Rel@{u v} A B) =>
{|
  Param1a1a.R := Param2a1a.R@{u v} A B P;
  Param1a1a.covariant := Param2a1a.covariant@{u v} A B P;
  Param1a1a.contravariant := Param2a1a.contravariant@{u v} A B P
|}
.


Coercion forget_2a1a_1c1a@{u v} :=
fun (A B : Type@{u}) (P : Param2a1a.Rel@{u v} A B) =>
{|
  Param1c1a.R := Param2a1a.R@{u v} A B P;
  Param1c1a.covariant := Param2a1a.covariant@{u v} A B P;
  Param1c1a.contravariant := Param2a1a.contravariant@{u v} A B P
|}
.


Coercion forget_2a1a_2a0@{u v} :=
fun (A B : Type@{u}) (P : Param2a1a.Rel@{u v} A B) =>
{|
  Param2a0.R := Param2a1a.R@{u v} A B P;
  Param2a0.covariant := Param2a1a.covariant@{u v} A B P;
  Param2a0.contravariant := Param2a1a.contravariant@{u v} A B P
|}
.


Coercion forget_2a1b_1a1b@{u v} :=
fun (A B : Type@{u}) (P : Param2a1b.Rel@{u v} A B) =>
{|
  Param1a1b.R := Param2a1b.R@{u v} A B P;
  Param1a1b.covariant := Param2a1b.covariant@{u v} A B P;
  Param1a1b.contravariant := Param2a1b.contravariant@{u v} A B P
|}
.


Coercion forget_2a1b_1c1b@{u v} :=
fun (A B : Type@{u}) (P : Param2a1b.Rel@{u v} A B) =>
{|
  Param1c1b.R := Param2a1b.R@{u v} A B P;
  Param1c1b.covariant := Param2a1b.covariant@{u v} A B P;
  Param1c1b.contravariant := Param2a1b.contravariant@{u v} A B P
|}
.


Coercion forget_2a1b_2a0@{u v} :=
fun (A B : Type@{u}) (P : Param2a1b.Rel@{u v} A B) =>
{|
  Param2a0.R := Param2a1b.R@{u v} A B P;
  Param2a0.covariant := Param2a1b.covariant@{u v} A B P;
  Param2a0.contravariant := Param2a1b.contravariant@{u v} A B P
|}
.


Coercion forget_2a1c_1a1c@{u v} :=
fun (A B : Type@{u}) (P : Param2a1c.Rel@{u v} A B) =>
{|
  Param1a1c.R := Param2a1c.R@{u v} A B P;
  Param1a1c.covariant := Param2a1c.covariant@{u v} A B P;
  Param1a1c.contravariant := Param2a1c.contravariant@{u v} A B P
|}
.


Coercion forget_2a1c_1c1c@{u v} :=
fun (A B : Type@{u}) (P : Param2a1c.Rel@{u v} A B) =>
{|
  Param1c1c.R := Param2a1c.R@{u v} A B P;
  Param1c1c.covariant := Param2a1c.covariant@{u v} A B P;
  Param1c1c.contravariant := Param2a1c.contravariant@{u v} A B P
|}
.


Coercion forget_2a1c_2a0@{u v} :=
fun (A B : Type@{u}) (P : Param2a1c.Rel@{u v} A B) =>
{|
  Param2a0.R := Param2a1c.R@{u v} A B P;
  Param2a0.covariant := Param2a1c.covariant@{u v} A B P;
  Param2a0.contravariant := Param2a1c.contravariant@{u v} A B P
|}
.


Coercion forget_2a2a_1a2a@{u v} :=
fun (A B : Type@{u}) (P : Param2a2a.Rel@{u v} A B) =>
{|
  Param1a2a.R := Param2a2a.R@{u v} A B P;
  Param1a2a.covariant := Param2a2a.covariant@{u v} A B P;
  Param1a2a.contravariant := Param2a2a.contravariant@{u v} A B P
|}
.


Coercion forget_2a2a_1c2a@{u v} :=
fun (A B : Type@{u}) (P : Param2a2a.Rel@{u v} A B) =>
{|
  Param1c2a.R := Param2a2a.R@{u v} A B P;
  Param1c2a.covariant := Param2a2a.covariant@{u v} A B P;
  Param1c2a.contravariant := Param2a2a.contravariant@{u v} A B P
|}
.


Coercion forget_2a2a_2a1a@{u v} :=
fun (A B : Type@{u}) (P : Param2a2a.Rel@{u v} A B) =>
{|
  Param2a1a.R := Param2a2a.R@{u v} A B P;
  Param2a1a.covariant := Param2a2a.covariant@{u v} A B P;
  Param2a1a.contravariant := Param2a2a.contravariant@{u v} A B P
|}
.


Coercion forget_2a2a_2a1c@{u v} :=
fun (A B : Type@{u}) (P : Param2a2a.Rel@{u v} A B) =>
{|
  Param2a1c.R := Param2a2a.R@{u v} A B P;
  Param2a1c.covariant := Param2a2a.covariant@{u v} A B P;
  Param2a1c.contravariant := Param2a2a.contravariant@{u v} A B P
|}
.


Coercion forget_2a2b_1a2b@{u v} :=
fun (A B : Type@{u}) (P : Param2a2b.Rel@{u v} A B) =>
{|
  Param1a2b.R := Param2a2b.R@{u v} A B P;
  Param1a2b.covariant := Param2a2b.covariant@{u v} A B P;
  Param1a2b.contravariant := Param2a2b.contravariant@{u v} A B P
|}
.


Coercion forget_2a2b_1c2b@{u v} :=
fun (A B : Type@{u}) (P : Param2a2b.Rel@{u v} A B) =>
{|
  Param1c2b.R := Param2a2b.R@{u v} A B P;
  Param1c2b.covariant := Param2a2b.covariant@{u v} A B P;
  Param1c2b.contravariant := Param2a2b.contravariant@{u v} A B P
|}
.


Coercion forget_2a2b_2a1b@{u v} :=
fun (A B : Type@{u}) (P : Param2a2b.Rel@{u v} A B) =>
{|
  Param2a1b.R := Param2a2b.R@{u v} A B P;
  Param2a1b.covariant := Param2a2b.covariant@{u v} A B P;
  Param2a1b.contravariant := Param2a2b.contravariant@{u v} A B P
|}
.


Coercion forget_2a2b_2a1c@{u v} :=
fun (A B : Type@{u}) (P : Param2a2b.Rel@{u v} A B) =>
{|
  Param2a1c.R := Param2a2b.R@{u v} A B P;
  Param2a1c.covariant := Param2a2b.covariant@{u v} A B P;
  Param2a1c.contravariant := Param2a2b.contravariant@{u v} A B P
|}
.


Coercion forget_2a3_1a3@{u v} :=
fun (A B : Type@{u}) (P : Param2a3.Rel@{u v} A B) =>
{|
  Param1a3.R := Param2a3.R@{u v} A B P;
  Param1a3.covariant := Param2a3.covariant@{u v} A B P;
  Param1a3.contravariant := Param2a3.contravariant@{u v} A B P
|}
.


Coercion forget_2a3_1c3@{u v} :=
fun (A B : Type@{u}) (P : Param2a3.Rel@{u v} A B) =>
{|
  Param1c3.R := Param2a3.R@{u v} A B P;
  Param1c3.covariant := Param2a3.covariant@{u v} A B P;
  Param1c3.contravariant := Param2a3.contravariant@{u v} A B P
|}
.


Coercion forget_2a3_2a2a@{u v} :=
fun (A B : Type@{u}) (P : Param2a3.Rel@{u v} A B) =>
{|
  Param2a2a.R := Param2a3.R@{u v} A B P;
  Param2a2a.covariant := Param2a3.covariant@{u v} A B P;
  Param2a2a.contravariant := Param2a3.contravariant@{u v} A B P
|}
.


Coercion forget_2a3_2a2b@{u v} :=
fun (A B : Type@{u}) (P : Param2a3.Rel@{u v} A B) =>
{|
  Param2a2b.R := Param2a3.R@{u v} A B P;
  Param2a2b.covariant := Param2a3.covariant@{u v} A B P;
  Param2a2b.contravariant := Param2a3.contravariant@{u v} A B P
|}
.


Coercion forget_2a4_1a4@{u v} :=
fun (A B : Type@{u}) (P : Param2a4.Rel@{u v} A B) =>
{|
  Param1a4.R := Param2a4.R@{u v} A B P;
  Param1a4.covariant := Param2a4.covariant@{u v} A B P;
  Param1a4.contravariant := Param2a4.contravariant@{u v} A B P
|}
.


Coercion forget_2a4_1c4@{u v} :=
fun (A B : Type@{u}) (P : Param2a4.Rel@{u v} A B) =>
{|
  Param1c4.R := Param2a4.R@{u v} A B P;
  Param1c4.covariant := Param2a4.covariant@{u v} A B P;
  Param1c4.contravariant := Param2a4.contravariant@{u v} A B P
|}
.


Coercion forget_2a4_2a3@{u v} :=
fun (A B : Type@{u}) (P : Param2a4.Rel@{u v} A B) =>
{|
  Param2a3.R := Param2a4.R@{u v} A B P;
  Param2a3.covariant := Param2a4.covariant@{u v} A B P;
  Param2a3.contravariant := Param2a4.contravariant@{u v} A B P
|}
.


Coercion forget_2b0_1b0@{u} :=
fun (A B : Type@{u}) (P : Param2b0.Rel@{u} A B) =>
{|
  Param1b0.R := Param2b0.R@{u} A B P;
  Param1b0.covariant := Param2b0.covariant@{u} A B P;
  Param1b0.contravariant := Param2b0.contravariant@{u} A B P
|}
.


Coercion forget_2b0_1c0@{u} :=
fun (A B : Type@{u}) (P : Param2b0.Rel@{u} A B) =>
{|
  Param1c0.R := Param2b0.R@{u} A B P;
  Param1c0.covariant := Param2b0.covariant@{u} A B P;
  Param1c0.contravariant := Param2b0.contravariant@{u} A B P
|}
.


Coercion forget_2b1a_1b1a@{u v} :=
fun (A B : Type@{u}) (P : Param2b1a.Rel@{u v} A B) =>
{|
  Param1b1a.R := Param2b1a.R@{u v} A B P;
  Param1b1a.covariant := Param2b1a.covariant@{u v} A B P;
  Param1b1a.contravariant := Param2b1a.contravariant@{u v} A B P
|}
.


Coercion forget_2b1a_1c1a@{u v} :=
fun (A B : Type@{u}) (P : Param2b1a.Rel@{u v} A B) =>
{|
  Param1c1a.R := Param2b1a.R@{u v} A B P;
  Param1c1a.covariant := Param2b1a.covariant@{u v} A B P;
  Param1c1a.contravariant := Param2b1a.contravariant@{u v} A B P
|}
.


Coercion forget_2b1a_2b0@{u v} :=
fun (A B : Type@{u}) (P : Param2b1a.Rel@{u v} A B) =>
{|
  Param2b0.R := Param2b1a.R@{u v} A B P;
  Param2b0.covariant := Param2b1a.covariant@{u v} A B P;
  Param2b0.contravariant := Param2b1a.contravariant@{u v} A B P
|}
.


Coercion forget_2b1b_1b1b@{u} :=
fun (A B : Type@{u}) (P : Param2b1b.Rel@{u} A B) =>
{|
  Param1b1b.R := Param2b1b.R@{u} A B P;
  Param1b1b.covariant := Param2b1b.covariant@{u} A B P;
  Param1b1b.contravariant := Param2b1b.contravariant@{u} A B P
|}
.


Coercion forget_2b1b_1c1b@{u} :=
fun (A B : Type@{u}) (P : Param2b1b.Rel@{u} A B) =>
{|
  Param1c1b.R := Param2b1b.R@{u} A B P;
  Param1c1b.covariant := Param2b1b.covariant@{u} A B P;
  Param1c1b.contravariant := Param2b1b.contravariant@{u} A B P
|}
.


Coercion forget_2b1b_2b0@{u} :=
fun (A B : Type@{u}) (P : Param2b1b.Rel@{u} A B) =>
{|
  Param2b0.R := Param2b1b.R@{u} A B P;
  Param2b0.covariant := Param2b1b.covariant@{u} A B P;
  Param2b0.contravariant := Param2b1b.contravariant@{u} A B P
|}
.


Coercion forget_2b1c_1b1c@{u} :=
fun (A B : Type@{u}) (P : Param2b1c.Rel@{u} A B) =>
{|
  Param1b1c.R := Param2b1c.R@{u} A B P;
  Param1b1c.covariant := Param2b1c.covariant@{u} A B P;
  Param1b1c.contravariant := Param2b1c.contravariant@{u} A B P
|}
.


Coercion forget_2b1c_1c1c@{u} :=
fun (A B : Type@{u}) (P : Param2b1c.Rel@{u} A B) =>
{|
  Param1c1c.R := Param2b1c.R@{u} A B P;
  Param1c1c.covariant := Param2b1c.covariant@{u} A B P;
  Param1c1c.contravariant := Param2b1c.contravariant@{u} A B P
|}
.


Coercion forget_2b1c_2b0@{u} :=
fun (A B : Type@{u}) (P : Param2b1c.Rel@{u} A B) =>
{|
  Param2b0.R := Param2b1c.R@{u} A B P;
  Param2b0.covariant := Param2b1c.covariant@{u} A B P;
  Param2b0.contravariant := Param2b1c.contravariant@{u} A B P
|}
.


Coercion forget_2b2a_1b2a@{u v} :=
fun (A B : Type@{u}) (P : Param2b2a.Rel@{u v} A B) =>
{|
  Param1b2a.R := Param2b2a.R@{u v} A B P;
  Param1b2a.covariant := Param2b2a.covariant@{u v} A B P;
  Param1b2a.contravariant := Param2b2a.contravariant@{u v} A B P
|}
.


Coercion forget_2b2a_1c2a@{u v} :=
fun (A B : Type@{u}) (P : Param2b2a.Rel@{u v} A B) =>
{|
  Param1c2a.R := Param2b2a.R@{u v} A B P;
  Param1c2a.covariant := Param2b2a.covariant@{u v} A B P;
  Param1c2a.contravariant := Param2b2a.contravariant@{u v} A B P
|}
.


Coercion forget_2b2a_2b1a@{u v} :=
fun (A B : Type@{u}) (P : Param2b2a.Rel@{u v} A B) =>
{|
  Param2b1a.R := Param2b2a.R@{u v} A B P;
  Param2b1a.covariant := Param2b2a.covariant@{u v} A B P;
  Param2b1a.contravariant := Param2b2a.contravariant@{u v} A B P
|}
.


Coercion forget_2b2a_2b1c@{u v} :=
fun (A B : Type@{u}) (P : Param2b2a.Rel@{u v} A B) =>
{|
  Param2b1c.R := Param2b2a.R@{u v} A B P;
  Param2b1c.covariant := Param2b2a.covariant@{u v} A B P;
  Param2b1c.contravariant := Param2b2a.contravariant@{u v} A B P
|}
.


Coercion forget_2b2b_1b2b@{u} :=
fun (A B : Type@{u}) (P : Param2b2b.Rel@{u} A B) =>
{|
  Param1b2b.R := Param2b2b.R@{u} A B P;
  Param1b2b.covariant := Param2b2b.covariant@{u} A B P;
  Param1b2b.contravariant := Param2b2b.contravariant@{u} A B P
|}
.


Coercion forget_2b2b_1c2b@{u} :=
fun (A B : Type@{u}) (P : Param2b2b.Rel@{u} A B) =>
{|
  Param1c2b.R := Param2b2b.R@{u} A B P;
  Param1c2b.covariant := Param2b2b.covariant@{u} A B P;
  Param1c2b.contravariant := Param2b2b.contravariant@{u} A B P
|}
.


Coercion forget_2b2b_2b1b@{u} :=
fun (A B : Type@{u}) (P : Param2b2b.Rel@{u} A B) =>
{|
  Param2b1b.R := Param2b2b.R@{u} A B P;
  Param2b1b.covariant := Param2b2b.covariant@{u} A B P;
  Param2b1b.contravariant := Param2b2b.contravariant@{u} A B P
|}
.


Coercion forget_2b2b_2b1c@{u} :=
fun (A B : Type@{u}) (P : Param2b2b.Rel@{u} A B) =>
{|
  Param2b1c.R := Param2b2b.R@{u} A B P;
  Param2b1c.covariant := Param2b2b.covariant@{u} A B P;
  Param2b1c.contravariant := Param2b2b.contravariant@{u} A B P
|}
.


Coercion forget_2b3_1b3@{u v} :=
fun (A B : Type@{u}) (P : Param2b3.Rel@{u v} A B) =>
{|
  Param1b3.R := Param2b3.R@{u v} A B P;
  Param1b3.covariant := Param2b3.covariant@{u v} A B P;
  Param1b3.contravariant := Param2b3.contravariant@{u v} A B P
|}
.


Coercion forget_2b3_1c3@{u v} :=
fun (A B : Type@{u}) (P : Param2b3.Rel@{u v} A B) =>
{|
  Param1c3.R := Param2b3.R@{u v} A B P;
  Param1c3.covariant := Param2b3.covariant@{u v} A B P;
  Param1c3.contravariant := Param2b3.contravariant@{u v} A B P
|}
.


Coercion forget_2b3_2b2a@{u v} :=
fun (A B : Type@{u}) (P : Param2b3.Rel@{u v} A B) =>
{|
  Param2b2a.R := Param2b3.R@{u v} A B P;
  Param2b2a.covariant := Param2b3.covariant@{u v} A B P;
  Param2b2a.contravariant := Param2b3.contravariant@{u v} A B P
|}
.


Coercion forget_2b3_2b2b@{u v} :=
fun (A B : Type@{u}) (P : Param2b3.Rel@{u v} A B) =>
{|
  Param2b2b.R := Param2b3.R@{u v} A B P;
  Param2b2b.covariant := Param2b3.covariant@{u v} A B P;
  Param2b2b.contravariant := Param2b3.contravariant@{u v} A B P
|}
.


Coercion forget_2b4_1b4@{u v} :=
fun (A B : Type@{u}) (P : Param2b4.Rel@{u v} A B) =>
{|
  Param1b4.R := Param2b4.R@{u v} A B P;
  Param1b4.covariant := Param2b4.covariant@{u v} A B P;
  Param1b4.contravariant := Param2b4.contravariant@{u v} A B P
|}
.


Coercion forget_2b4_1c4@{u v} :=
fun (A B : Type@{u}) (P : Param2b4.Rel@{u v} A B) =>
{|
  Param1c4.R := Param2b4.R@{u v} A B P;
  Param1c4.covariant := Param2b4.covariant@{u v} A B P;
  Param1c4.contravariant := Param2b4.contravariant@{u v} A B P
|}
.


Coercion forget_2b4_2b3@{u v} :=
fun (A B : Type@{u}) (P : Param2b4.Rel@{u v} A B) =>
{|
  Param2b3.R := Param2b4.R@{u v} A B P;
  Param2b3.covariant := Param2b4.covariant@{u v} A B P;
  Param2b3.contravariant := Param2b4.contravariant@{u v} A B P
|}
.


Coercion forget_30_2a0@{u v} :=
fun (A B : Type@{u}) (P : Param30.Rel@{u v} A B) =>
{|
  Param2a0.R := Param30.R@{u v} A B P;
  Param2a0.covariant := Param30.covariant@{u v} A B P;
  Param2a0.contravariant := Param30.contravariant@{u v} A B P
|}
.


Coercion forget_30_2b0@{u v} :=
fun (A B : Type@{u}) (P : Param30.Rel@{u v} A B) =>
{|
  Param2b0.R := Param30.R@{u v} A B P;
  Param2b0.covariant := Param30.covariant@{u v} A B P;
  Param2b0.contravariant := Param30.contravariant@{u v} A B P
|}
.


Coercion forget_31a_2a1a@{u v} :=
fun (A B : Type@{u}) (P : Param31a.Rel@{u v} A B) =>
{|
  Param2a1a.R := Param31a.R@{u v} A B P;
  Param2a1a.covariant := Param31a.covariant@{u v} A B P;
  Param2a1a.contravariant := Param31a.contravariant@{u v} A B P
|}
.


Coercion forget_31a_2b1a@{u v} :=
fun (A B : Type@{u}) (P : Param31a.Rel@{u v} A B) =>
{|
  Param2b1a.R := Param31a.R@{u v} A B P;
  Param2b1a.covariant := Param31a.covariant@{u v} A B P;
  Param2b1a.contravariant := Param31a.contravariant@{u v} A B P
|}
.


Coercion forget_31a_30@{u v} :=
fun (A B : Type@{u}) (P : Param31a.Rel@{u v} A B) =>
{|
  Param30.R := Param31a.R@{u v} A B P;
  Param30.covariant := Param31a.covariant@{u v} A B P;
  Param30.contravariant := Param31a.contravariant@{u v} A B P
|}
.


Coercion forget_31b_2a1b@{u v} :=
fun (A B : Type@{u}) (P : Param31b.Rel@{u v} A B) =>
{|
  Param2a1b.R := Param31b.R@{u v} A B P;
  Param2a1b.covariant := Param31b.covariant@{u v} A B P;
  Param2a1b.contravariant := Param31b.contravariant@{u v} A B P
|}
.


Coercion forget_31b_2b1b@{u v} :=
fun (A B : Type@{u}) (P : Param31b.Rel@{u v} A B) =>
{|
  Param2b1b.R := Param31b.R@{u v} A B P;
  Param2b1b.covariant := Param31b.covariant@{u v} A B P;
  Param2b1b.contravariant := Param31b.contravariant@{u v} A B P
|}
.


Coercion forget_31b_30@{u v} :=
fun (A B : Type@{u}) (P : Param31b.Rel@{u v} A B) =>
{|
  Param30.R := Param31b.R@{u v} A B P;
  Param30.covariant := Param31b.covariant@{u v} A B P;
  Param30.contravariant := Param31b.contravariant@{u v} A B P
|}
.


Coercion forget_31c_2a1c@{u v} :=
fun (A B : Type@{u}) (P : Param31c.Rel@{u v} A B) =>
{|
  Param2a1c.R := Param31c.R@{u v} A B P;
  Param2a1c.covariant := Param31c.covariant@{u v} A B P;
  Param2a1c.contravariant := Param31c.contravariant@{u v} A B P
|}
.


Coercion forget_31c_2b1c@{u v} :=
fun (A B : Type@{u}) (P : Param31c.Rel@{u v} A B) =>
{|
  Param2b1c.R := Param31c.R@{u v} A B P;
  Param2b1c.covariant := Param31c.covariant@{u v} A B P;
  Param2b1c.contravariant := Param31c.contravariant@{u v} A B P
|}
.


Coercion forget_31c_30@{u v} :=
fun (A B : Type@{u}) (P : Param31c.Rel@{u v} A B) =>
{|
  Param30.R := Param31c.R@{u v} A B P;
  Param30.covariant := Param31c.covariant@{u v} A B P;
  Param30.contravariant := Param31c.contravariant@{u v} A B P
|}
.


Coercion forget_32a_2a2a@{u v} :=
fun (A B : Type@{u}) (P : Param32a.Rel@{u v} A B) =>
{|
  Param2a2a.R := Param32a.R@{u v} A B P;
  Param2a2a.covariant := Param32a.covariant@{u v} A B P;
  Param2a2a.contravariant := Param32a.contravariant@{u v} A B P
|}
.


Coercion forget_32a_2b2a@{u v} :=
fun (A B : Type@{u}) (P : Param32a.Rel@{u v} A B) =>
{|
  Param2b2a.R := Param32a.R@{u v} A B P;
  Param2b2a.covariant := Param32a.covariant@{u v} A B P;
  Param2b2a.contravariant := Param32a.contravariant@{u v} A B P
|}
.


Coercion forget_32a_31a@{u v} :=
fun (A B : Type@{u}) (P : Param32a.Rel@{u v} A B) =>
{|
  Param31a.R := Param32a.R@{u v} A B P;
  Param31a.covariant := Param32a.covariant@{u v} A B P;
  Param31a.contravariant := Param32a.contravariant@{u v} A B P
|}
.


Coercion forget_32a_31c@{u v} :=
fun (A B : Type@{u}) (P : Param32a.Rel@{u v} A B) =>
{|
  Param31c.R := Param32a.R@{u v} A B P;
  Param31c.covariant := Param32a.covariant@{u v} A B P;
  Param31c.contravariant := Param32a.contravariant@{u v} A B P
|}
.


Coercion forget_32b_2a2b@{u v} :=
fun (A B : Type@{u}) (P : Param32b.Rel@{u v} A B) =>
{|
  Param2a2b.R := Param32b.R@{u v} A B P;
  Param2a2b.covariant := Param32b.covariant@{u v} A B P;
  Param2a2b.contravariant := Param32b.contravariant@{u v} A B P
|}
.


Coercion forget_32b_2b2b@{u v} :=
fun (A B : Type@{u}) (P : Param32b.Rel@{u v} A B) =>
{|
  Param2b2b.R := Param32b.R@{u v} A B P;
  Param2b2b.covariant := Param32b.covariant@{u v} A B P;
  Param2b2b.contravariant := Param32b.contravariant@{u v} A B P
|}
.


Coercion forget_32b_31b@{u v} :=
fun (A B : Type@{u}) (P : Param32b.Rel@{u v} A B) =>
{|
  Param31b.R := Param32b.R@{u v} A B P;
  Param31b.covariant := Param32b.covariant@{u v} A B P;
  Param31b.contravariant := Param32b.contravariant@{u v} A B P
|}
.


Coercion forget_32b_31c@{u v} :=
fun (A B : Type@{u}) (P : Param32b.Rel@{u v} A B) =>
{|
  Param31c.R := Param32b.R@{u v} A B P;
  Param31c.covariant := Param32b.covariant@{u v} A B P;
  Param31c.contravariant := Param32b.contravariant@{u v} A B P
|}
.


Coercion forget_33_2a3@{u v} :=
fun (A B : Type@{u}) (P : Param33.Rel@{u v} A B) =>
{|
  Param2a3.R := Param33.R@{u v} A B P;
  Param2a3.covariant := Param33.covariant@{u v} A B P;
  Param2a3.contravariant := Param33.contravariant@{u v} A B P
|}
.


Coercion forget_33_2b3@{u v} :=
fun (A B : Type@{u}) (P : Param33.Rel@{u v} A B) =>
{|
  Param2b3.R := Param33.R@{u v} A B P;
  Param2b3.covariant := Param33.covariant@{u v} A B P;
  Param2b3.contravariant := Param33.contravariant@{u v} A B P
|}
.


Coercion forget_33_32a@{u v} :=
fun (A B : Type@{u}) (P : Param33.Rel@{u v} A B) =>
{|
  Param32a.R := Param33.R@{u v} A B P;
  Param32a.covariant := Param33.covariant@{u v} A B P;
  Param32a.contravariant := Param33.contravariant@{u v} A B P
|}
.


Coercion forget_33_32b@{u v} :=
fun (A B : Type@{u}) (P : Param33.Rel@{u v} A B) =>
{|
  Param32b.R := Param33.R@{u v} A B P;
  Param32b.covariant := Param33.covariant@{u v} A B P;
  Param32b.contravariant := Param33.contravariant@{u v} A B P
|}
.


Coercion forget_34_2a4@{u v} :=
fun (A B : Type@{u}) (P : Param34.Rel@{u v} A B) =>
{|
  Param2a4.R := Param34.R@{u v} A B P;
  Param2a4.covariant := Param34.covariant@{u v} A B P;
  Param2a4.contravariant := Param34.contravariant@{u v} A B P
|}
.


Coercion forget_34_2b4@{u v} :=
fun (A B : Type@{u}) (P : Param34.Rel@{u v} A B) =>
{|
  Param2b4.R := Param34.R@{u v} A B P;
  Param2b4.covariant := Param34.covariant@{u v} A B P;
  Param2b4.contravariant := Param34.contravariant@{u v} A B P
|}
.


Coercion forget_34_33@{u v} :=
fun (A B : Type@{u}) (P : Param34.Rel@{u v} A B) =>
{|
  Param33.R := Param34.R@{u v} A B P;
  Param33.covariant := Param34.covariant@{u v} A B P;
  Param33.contravariant := Param34.contravariant@{u v} A B P
|}
.


Coercion forget_40_30@{u v} :=
fun (A B : Type@{u}) (P : Param40.Rel@{u v} A B) =>
{|
  Param30.R := Param40.R@{u v} A B P;
  Param30.covariant := Param40.covariant@{u v} A B P;
  Param30.contravariant := Param40.contravariant@{u v} A B P
|}
.


Coercion forget_41a_31a@{u v} :=
fun (A B : Type@{u}) (P : Param41a.Rel@{u v} A B) =>
{|
  Param31a.R := Param41a.R@{u v} A B P;
  Param31a.covariant := Param41a.covariant@{u v} A B P;
  Param31a.contravariant := Param41a.contravariant@{u v} A B P
|}
.


Coercion forget_41a_40@{u v} :=
fun (A B : Type@{u}) (P : Param41a.Rel@{u v} A B) =>
{|
  Param40.R := Param41a.R@{u v} A B P;
  Param40.covariant := Param41a.covariant@{u v} A B P;
  Param40.contravariant := Param41a.contravariant@{u v} A B P
|}
.


Coercion forget_41b_31b@{u v} :=
fun (A B : Type@{u}) (P : Param41b.Rel@{u v} A B) =>
{|
  Param31b.R := Param41b.R@{u v} A B P;
  Param31b.covariant := Param41b.covariant@{u v} A B P;
  Param31b.contravariant := Param41b.contravariant@{u v} A B P
|}
.


Coercion forget_41b_40@{u v} :=
fun (A B : Type@{u}) (P : Param41b.Rel@{u v} A B) =>
{|
  Param40.R := Param41b.R@{u v} A B P;
  Param40.covariant := Param41b.covariant@{u v} A B P;
  Param40.contravariant := Param41b.contravariant@{u v} A B P
|}
.


Coercion forget_41c_31c@{u v} :=
fun (A B : Type@{u}) (P : Param41c.Rel@{u v} A B) =>
{|
  Param31c.R := Param41c.R@{u v} A B P;
  Param31c.covariant := Param41c.covariant@{u v} A B P;
  Param31c.contravariant := Param41c.contravariant@{u v} A B P
|}
.


Coercion forget_41c_40@{u v} :=
fun (A B : Type@{u}) (P : Param41c.Rel@{u v} A B) =>
{|
  Param40.R := Param41c.R@{u v} A B P;
  Param40.covariant := Param41c.covariant@{u v} A B P;
  Param40.contravariant := Param41c.contravariant@{u v} A B P
|}
.


Coercion forget_42a_32a@{u v} :=
fun (A B : Type@{u}) (P : Param42a.Rel@{u v} A B) =>
{|
  Param32a.R := Param42a.R@{u v} A B P;
  Param32a.covariant := Param42a.covariant@{u v} A B P;
  Param32a.contravariant := Param42a.contravariant@{u v} A B P
|}
.


Coercion forget_42a_41a@{u v} :=
fun (A B : Type@{u}) (P : Param42a.Rel@{u v} A B) =>
{|
  Param41a.R := Param42a.R@{u v} A B P;
  Param41a.covariant := Param42a.covariant@{u v} A B P;
  Param41a.contravariant := Param42a.contravariant@{u v} A B P
|}
.


Coercion forget_42a_41c@{u v} :=
fun (A B : Type@{u}) (P : Param42a.Rel@{u v} A B) =>
{|
  Param41c.R := Param42a.R@{u v} A B P;
  Param41c.covariant := Param42a.covariant@{u v} A B P;
  Param41c.contravariant := Param42a.contravariant@{u v} A B P
|}
.


Coercion forget_42b_32b@{u v} :=
fun (A B : Type@{u}) (P : Param42b.Rel@{u v} A B) =>
{|
  Param32b.R := Param42b.R@{u v} A B P;
  Param32b.covariant := Param42b.covariant@{u v} A B P;
  Param32b.contravariant := Param42b.contravariant@{u v} A B P
|}
.


Coercion forget_42b_41b@{u v} :=
fun (A B : Type@{u}) (P : Param42b.Rel@{u v} A B) =>
{|
  Param41b.R := Param42b.R@{u v} A B P;
  Param41b.covariant := Param42b.covariant@{u v} A B P;
  Param41b.contravariant := Param42b.contravariant@{u v} A B P
|}
.


Coercion forget_42b_41c@{u v} :=
fun (A B : Type@{u}) (P : Param42b.Rel@{u v} A B) =>
{|
  Param41c.R := Param42b.R@{u v} A B P;
  Param41c.covariant := Param42b.covariant@{u v} A B P;
  Param41c.contravariant := Param42b.contravariant@{u v} A B P
|}
.


Coercion forget_43_33@{u v} :=
fun (A B : Type@{u}) (P : Param43.Rel@{u v} A B) =>
{|
  Param33.R := Param43.R@{u v} A B P;
  Param33.covariant := Param43.covariant@{u v} A B P;
  Param33.contravariant := Param43.contravariant@{u v} A B P
|}
.


Coercion forget_43_42a@{u v} :=
fun (A B : Type@{u}) (P : Param43.Rel@{u v} A B) =>
{|
  Param42a.R := Param43.R@{u v} A B P;
  Param42a.covariant := Param43.covariant@{u v} A B P;
  Param42a.contravariant := Param43.contravariant@{u v} A B P
|}
.


Coercion forget_43_42b@{u v} :=
fun (A B : Type@{u}) (P : Param43.Rel@{u v} A B) =>
{|
  Param42b.R := Param43.R@{u v} A B P;
  Param42b.covariant := Param43.covariant@{u v} A B P;
  Param42b.contravariant := Param43.contravariant@{u v} A B P
|}
.


Coercion forget_44_34@{u v} :=
fun (A B : Type@{u}) (P : Param44.Rel@{u v} A B) =>
{|
  Param34.R := Param44.R@{u v} A B P;
  Param34.covariant := Param44.covariant@{u v} A B P;
  Param34.contravariant := Param44.contravariant@{u v} A B P
|}
.


Coercion forget_44_43@{u v} :=
fun (A B : Type@{u}) (P : Param44.Rel@{u v} A B) =>
{|
  Param43.R := Param44.R@{u v} A B P;
  Param43.covariant := Param44.covariant@{u v} A B P;
  Param43.contravariant := Param44.contravariant@{u v} A B P
|}
.

(* Set Printing Universes. Print Module Param2a3. *)
(* Set Printing Universes. Print forget_42b_41. *)
(* Check forall (p : Param44.Rel nat nat), @paths (Param12a.Rel nat nat) p p. *)

(* General projections *)

Definition rel {A B} (R : Param00.Rel A B) := Param00.R A B R.
Coercion rel : Param00.Rel >-> Funclass.

Definition is_total {A B} (R : Param1a0.Rel A B) :
  is_rel_epic (sym_rel ((Param1a0.R A B R))) :=
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
  is_rel_epic (sym_rel (sym_rel ((Param01a.R A B R)))) :=
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

Section Optimality_Map1c.
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

  Theorem D1c_arrow_left_isnt_1a `{Univalence}: not (
    forall (A A' : Type) (AR: Param01a.Rel A A'),
    forall (B B' : Type) (BR: Param1c0.Rel B B'),

    Map1c.Has (R_arrow AR BR)
  ).
  Proof.
  Admitted.

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
  Admitted.
End Optimality_Map1c.

Lemma sig_eq `{Univalence} {X: Type} (x: X) (P: X -> Type) :
  { y: X | (y = x) /\ P y } = P x.
Proof.
  apply path_universe_uncurried.
  unshelve apply /equiv_adjointify.
  - move=> [y [eq Py]].
    by case: _ / eq.
  - move=> Px.
    by exists x.
  - move=> Px //.
  - move=> [y [eq Py]].
    by case: _ / eq.
Qed.
Lemma sig_eq' `{Univalence} {X: Type} (x: X) (P: X -> Type) :
  { y: X | (x = y) /\ P y } = P x.
Proof.
  apply path_universe_uncurried.
  unshelve apply /equiv_adjointify.
  - move=> [y [eq Py]].
    by case: _ / eq^.
  - move=> Px.
    by exists x.
  - move=> Px //.
  - move=> [y [eq Py]].
    induction eq => //.
Qed.

Definition p33_eq {A: Type} `{Univalence}: Param33.Rel A A.
Proof.
  exists (fun a a' => a = a').
  - exists id.
    + rewrite /sym_rel /is_rel_epic /compose_rel.
      move=> C g1 g2 g1_eq_g2.
      apply path_forall=> a.
      apply path_forall=> c.
      move: (ap10 g1_eq_g2 a)=> {}g1_eq_g2.
      move: (ap10 g1_eq_g2 c)=> {}g1_eq_g2.
      by rewrite !sig_eq in g1_eq_g2.
    + move=> _ _ _ [] [] //.
    + by rewrite /id.
    + by rewrite /id.
  - exists id.
    + rewrite /sym_rel /is_rel_epic /compose_rel.
      move=> C g1 g2 g1_eq_g2.
      apply path_forall=> a.
      apply path_forall=> c.
      move: (ap10 g1_eq_g2 a)=> {}g1_eq_g2.
      move: (ap10 g1_eq_g2 c)=> {}g1_eq_g2.
      by rewrite !sig_eq' in g1_eq_g2.
    + move=> _ _ _ [] [] //.
    + by rewrite /sym_rel /id.
    + by rewrite /sym_rel /id.
Defined.

(* Univalence is only needed to instanciate p33_eq because level 1a requires it.
   using a different definition for 1a would remove the dependency on the axiom *)
Lemma map1b_would_imply_funext `{Univalence}: (
  (forall (A A' : Type) (PA : Param00.Rel A A')
          (B B' : Type) (PB : Param00.Rel B B'),
    Map1b.Has (R_arrow PA PB))
      ->
  (forall (A B: Type) (f g: A -> B), f == g -> f = g)
).
Proof.
  move=> map1b A B f g f_eq_g.
  specialize (map1b A A p33_eq B B p33_eq).
  destruct map1b as [is_right_unique].
  apply (is_right_unique f).
  + move=> a a' [] //.
  + rewrite /R_arrow /p33_eq /=.
    move=> a a' [].
    apply f_eq_g.
Qed.

Lemma map1a_would_imply_funext' `{Univalence}: (
  (forall (A A' : Type) (PA : Param01a.Rel A A')
          (B B' : Type) (PB : Param1b0.Rel B B'),
    Map1a.Has (R_arrow PA PB))
      ->
  (forall (A B C: Type) (f g: (A -> B) -> C -> Type), (forall a b, f a b = g a b) -> f = g)
).
Proof.
  move=> map1a A B C f g f_eq_g.
  specialize (map1a A A p33_eq B B p33_eq).
  destruct map1a as [is_total].
  apply is_total.
  rewrite /sym_rel /is_rel_epic /compose_rel.
  + move=> a a' [] //.
  + rewrite /R_arrow /p33_eq /=.
    move=> a a' [].
    apply f_eq_g.
Qed.

(* (02a, 1b0) -> 1b0 *)
Definition Map1b_arrow@{i j k l | i <= k, j <= k, i < l} `{Univalence}
  {A A' : Type@{i}} (PA : Param01a.Rel@{i l} A A')
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
