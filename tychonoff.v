Require Import Reals Epsilon.
From Coquelicot Require Import Hierarchy.
From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun eqtype bigop ssralg
  matrix fintype zmodp.
Require Import coquelicotComplements vect.
From ZornsLemma Require Import ZornsLemma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import List Classical_Prop Classical_Pred_Type Iter.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Module TopologicalSpace.

Record mixin_of (T : Type) := Mixin {
  open : set T -> Prop ;
  op_setU : forall (I : eqType) (f : I -> set T),
    (forall i, open (f i)) -> open (\bigcup_i f i) ;
  op_setI : forall (A B : set T), open A -> open B -> open (A `&` B) ;
  op_setT : open setT
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Definition class (cT : type) := let: Pack _ c _ := cT return class_of cT in c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Notation TopologicalSpace := type.

End Exports.

End TopologicalSpace.

Export TopologicalSpace.Exports.

Section TopologicalSpaceTheory.

Context {T : TopologicalSpace}.

Definition open (A : set T) :=
  TopologicalSpace.open (TopologicalSpace.class T) A.

Lemma open_setU (I : eqType) (f : I -> set T) :
  (forall i, open (f i)) -> open (\bigcup_i f i).
Proof. exact: TopologicalSpace.op_setU. Qed.

Lemma open_setI (A B : set T) : open A -> open B -> open (A `&` B).
Proof. exact: TopologicalSpace.op_setI. Qed.

Lemma open_setT : open setT.
Proof. exact: TopologicalSpace.op_setT. Qed.

Definition neighbour (p : T) (A : set T) := open A /\ A p.

Lemma neighbour_setT (p : T) : neighbour p setT.
Proof. by split=> //; apply: open_setT. Qed.

Lemma neighbour_setI (p : T) (A B : set T) :
  neighbour p A -> neighbour p B -> neighbour p (A `&` B).
Proof.
by move=> [Aop Ap] [Bop Bp]; split; [apply: open_setI|split].
Qed.

Definition cluster (F : set (set T)) (p : T) :=
  forall A B, F A -> neighbour p B -> A `&` B !=set0.

End TopologicalSpaceTheory.

(* Module FilteredSpace. *)

(* Record mixin_of (T : Type) := Mixin { *)
(*   locally : T -> set (set T) ; *)
(*   locally_filter : forall p : T, ProperFilter (locally p) *)
(* }. *)

(* Notation class_of := mixin_of (only parsing). *)

(* Section ClassDef. *)

(* Structure type := Pack { sort; _ : class_of sort ; _ : Type }. *)
(* Local Coercion sort : type >-> Sortclass. *)
(* Definition class (cT : type) := let: Pack _ c _ := cT return class_of cT in c. *)

(* End ClassDef. *)

(* Module Exports. *)

(* Coercion sort : type >-> Sortclass. *)
(* Notation FilteredSpace := type. *)

(* End Exports. *)

(* End FilteredSpace. *)

(* Export FilteredSpace.Exports. *)

(* Section FilteredSpaceTheory. *)

(* Context {T : FilteredSpace}. *)

(* Definition locally (p : T) := FilteredSpace.locally (FilteredSpace.class T) p. *)

(* Global Instance locally_filter (p : T) : ProperFilter (locally p). *)
(* Proof. exact: FilteredSpace.locally_filter. Qed. *)

(* End FilteredSpaceTheory. *)

(* Section FilteredIsTopological. *)

(* Context (T : FilteredSpace). *)

(* Definition filter_open (A : set T) := forall p, A p -> locally p A. *)

(* Lemma filter_op_setU (I : eqType) (f : I -> set T) : *)
(*   (forall i, filter_open (f i)) -> filter_open (\bigcup_i f i). *)
(* Proof. *)
(* by move=> fop p [i _ /fop]; apply: filter_imp => q fiq; exists i. *)
(* Qed. *)

(* Lemma filter_op_setI (A B : set T) : *)
(*   filter_open A -> filter_open B -> filter_open (A `&` B). *)
(* Proof. *)
(* by move=> Aop Bop p [/Aop p_A /Bop p_B]; apply: filter_and. *)
(* Qed. *)

(* Lemma filter_op_setT : filter_open setT. *)
(* Proof. by move=> ??; apply: filter_true. Qed. *)

(* Definition filteredTopologyMixin := *)
(*   TopologicalSpace.Mixin filter_op_setU filter_op_setI filter_op_setT. *)

(* Definition filteredTopologicalSpace := *)
(*   TopologicalSpace.Pack filteredTopologyMixin T. *)

(* End FilteredIsTopological. *)

(* Section TopologicalIsFiltered. *)

(* Context (T : TopologicalSpace). *)

(* Definition topo_locally (p : T) (A : set T) := *)
(*   exists B, neighbour p B /\ B `<=` A. *)

(* Instance topo_locally_filter (p : T) : ProperFilter (topo_locally p). *)
(* Proof. *)
(* split; first by move=> A [B [[_ Bp] sBA]]; exists p; apply: sBA. *)
(* split; first by exists setT; split=> //; apply: neighbour_setT. *)
(*   move=> A B [C [p_C sCA]] [D [p_D sDB]]. *)
(*   exists (C `&` D); split; first exact: neighbour_setI. *)
(*   by move=> q [/sCA Aq /sDB Bq]; split. *)
(* move=> A B sAB [C [p_C sCA]]. *)
(* by exists C; split=> //; apply: subset_trans sAB. *)
(* Qed. *)

(* Definition topologicalFilteredMixin := *)
(*   FilteredSpace.Mixin topo_locally_filter. *)

(* Definition topologicalFilteredSpace := *)
(*   FilteredSpace.Pack topologicalFilteredMixin T. *)

(* End TopologicalIsFiltered. *)

Definition continuous (S T : TopologicalSpace) (f : S -> T) :=
  forall A : set T, open A -> open (f @^-1` A).

Definition cv (U : TopologicalSpace) (F : set (set U)) p := F --> neighbour p.

Lemma cv_cluster (U : TopologicalSpace) (F : set (set U)) p :
  ProperFilter F ->
  cluster F p <-> exists G : set (set U), ProperFilter G /\ cv G p /\ F `<=` G.
Proof.
move=> Fproper; split=> [clFp|[G [Gproper [cvGp sFG]]] A B]; last first.
  by move=> /sFG GA /cvGp GB; apply/filter_ex/filter_and.
exists ([set A | exists B, B `<=` A /\
  (\bigcup_(C in F) [set C `&` D | D in neighbour p]) B]); split.
  split.
    move=> A [B [sBA [C FC [D p_D CD_eqB]]]].
    by have := clFp _ _ FC p_D; rewrite CD_eqB => - [q /sBA]; exists q.
  split.
  - exists setT; split=> //; exists setT ; first exact: filter_true.
    by exists setT; [split=> //; apply: open_setT|apply: setIT].
  - move=> A1 A2 [B1 [sBA1 [C1 FC1 [D1 [D1op D1p] CD_eqB1]]]]
      [B2 [sBA2 [C2 FC2 [D2 [D2op D2p] CD_eqB2]]]].
    exists (B1 `&` B2); split; first by move=> ? [/sBA1 ? /sBA2].
    exists (C1 `&` C2); first exact: filter_and.
    exists (D1 `&` D2); first by split; [apply: open_setI|].
    by rewrite setIA [C2 `&` _]setIC setIA [_ `&` C2]setIC -setIA CD_eqB1
      CD_eqB2.
  - move=> A B sAB [C [sCA FIneighp_C]].
    by exists C; split=> //; apply: subset_trans sAB.
split.
  move=> A p_A; exists A; split=> //; exists setT; first exact: filter_true.
  by exists A => //; rewrite setIC subsetI_eq.
move=> A FA; exists A; split=> //; exists A => //; exists setT.
  by split=> //; apply: open_setT.
by rewrite subsetI_eq.
Qed.

Section Uniform_Topology.

Context {U : UniformSpace}.

Definition uopen (A : set U) := Hierarchy.open A.

Lemma uop_setU (I : eqType) (g : I -> set U) :
  (forall i, uopen (g i)) -> uopen (\bigcup_i g i).
Proof. by move=> gop; apply: open_bigcup => i _; apply: gop. Qed.

Lemma uop_setI (A B : set U) : uopen A -> uopen B -> uopen (A `&` B).
Proof. exact: open_and. Qed.

Lemma uop_setT : uopen setT.
Proof. exact: open_true. Qed.

Definition uniformTopologyMixin :=
  TopologicalSpace.Mixin uop_setU uop_setI uop_setT.

Canonical uniformTopologicalSpace :=
  TopologicalSpace.Pack uniformTopologyMixin U.

End Uniform_Topology.

Lemma neighbourP (U : UniformSpace) p (A : set U) :
  neighbour p A -> locally p A.
Proof. by move=> [Aop Ap]; apply: Aop. Qed.

Lemma clusterP (U : UniformSpace) (F : set (set U)) (p : U) :
  cluster F p <-> coquelicotComplements.cluster F p.
Proof.
split=> clFp A B FA p_B.
  suff [q [Aq Bint_q]] : A `&` interior B !=set0.
    by exists q; split=> //; apply: interior_subset.
  by apply: clFp FA _; split=> //; apply: open_interior.
by apply: clFp FA _; apply: neighbourP.
Qed.

Definition compact (T : TopologicalSpace) A := forall (F : set (set T)), F A ->
  ProperFilter F -> A `&` cluster F !=set0.

Lemma uniform_compactP (U : UniformSpace) (A : set U) :
  coquelicotComplements.compact A <-> compact A.
Proof.
split=> Aco F FA Fproper.
  have [p [Ap clFp]] : A `&` (coquelicotComplements.cluster F) !=set0.
    exact: Aco.
  by exists p; split=> //; apply/clusterP.
have [p [Ap clFp]] : A `&` (cluster F) !=set0 by exact: Aco.
by exists p; split=> //; apply/clusterP.
Qed.

Section Weak_topology.

Variable (S : Type) (T : TopologicalSpace) (f : S -> T).

Definition wopen (A : set S) := exists B : set T, open B /\ A = f @^-1` B.

Lemma wop_setU (I : eqType) (g : I -> set S) :
  (forall i, wopen (g i)) -> wopen (\bigcup_i g i).
Proof.
move=> gop.
have {gop} gop : forall i, {B : set T | open B /\ g i = f @^-1` B}.
  by move=> i; apply/constructive_indefinite_description/gop.
have g_preim : forall i, g i = f @^-1` sval (gop i).
  by move=> i; have [] := svalP (gop i).
have gopi : forall i, open (sval (gop i)).
  by move=> i; have [] := svalP (gop i).
exists (\bigcup_i sval (gop i)); split; first exact: open_setU.
apply/funext=> p; apply/propext; split=> [[i _]|[i _]].
  by rewrite g_preim; exists i.
by rewrite -[sval _ _]/((f @^-1` _) _) -g_preim; exists i.
Qed.

Lemma wop_setI (A B : set S) : wopen A -> wopen B -> wopen (A `&` B).
Proof.
move=> [C [Cop ->]] [D [Dop ->]]; exists (C `&` D).
by split; [apply: open_setI|rewrite preimage_setI].
Qed.

Lemma wop_setT : wopen setT.
Proof.
exists setT; split; first exact: open_setT.
by apply/funext=> ?; apply/propext; split.
Qed.

Definition weakTopologyMixin :=
  TopologicalSpace.Mixin wop_setU wop_setI wop_setT.

Definition weakTopologicalSpace := TopologicalSpace.Pack weakTopologyMixin T.

Lemma weak_continuous : @continuous weakTopologicalSpace _ f.
Proof. by move=> A Aop; exists A. Qed.

Lemma cv_image (F : set (set S)) (s : S) :
  f @` setT = setT -> Filter F ->
  @cv weakTopologicalSpace F s <-> cv [set f @` A | A in F] (f s).
Proof.
move=> fsurj Ffilt; split=> [cvFs|cvfFfs].
  move=> A [/weak_continuous [B [Bop preim_AeqB]] Afs].
  exists (f @^-1` B); last by rewrite -preim_AeqB image_preimage.
  by apply: cvFs; split; [apply/weak_continuous|rewrite -preim_AeqB].
move=> _ [[B [Bop ->]] Bfs].
have /cvfFfs [C FC <-] : neighbour (f s) B by [].
by apply: filter_imp FC; apply: preimage_image.
Qed.

End Weak_topology.

Lemma weak_weakest (S T : TopologicalSpace) (f : S -> T) :
  continuous f -> forall A : set S, @open (weakTopologicalSpace f) A -> open A.
Proof. by move=> fcont _ [B [Bop ->]]; apply: fcont. Qed.

Section Sup_topology.

Variable (T : Type) (I : eqType) (i : I)
  (Tm : I -> TopologicalSpace.mixin_of T).

Let TS := fun i => TopologicalSpace.Pack (Tm i) T.

Definition fin_setI (A : set T) :=
  exists (J : finType) (toI : J -> I) (f : J -> set T),
  (forall j : J, @open (TS (toI j)) (f j)) /\
  A = \bigcap_(j : J) f j.

Definition sopen (A : set T) :=
  exists (f : {J : Type & J -> set T}),
  (forall j, fin_setI (projT2 f j)) /\ A = \bigcup_(j : projT1 f) projT2 f j.

Lemma sop_setU (J : eqType) (f : J -> set T) :
  (forall j, sopen (f j)) -> sopen (\bigcup_j f j).
Proof.
move=> fop.
have {fop} fop : forall j, {g : {K : Type & K -> set T} |
  (forall k, fin_setI (projT2 g k)) /\ f j = \bigcup_k projT2 g k}.
  by move=> j; apply/constructive_indefinite_description/fop.
set K := fun j => projT1 (sval (fop j)).
set g := fun j => projT2 (sval (fop j)).
set K' := sigT K; set g' : K' -> set T := fun p => g (projT1 p) (projT2 p).
exists (existT _ K' g'); split.
  by move=> [j Kj] /=; have [finI _] := svalP (fop j); apply: finI.
apply/funext=> p; apply/propext; split=> /=.
  move=> [j _ fjp]; have [_ fjval] := svalP (fop j).
  by move: fjp; rewrite fjval => - [k]; exists (existT _ j k).
move=> [[j Kj] _ ?]; exists j => //.
by have [_ ->] := svalP (fop j); exists Kj.
Qed.

Lemma sop_setI (A B : set T) : sopen A -> sopen B -> sopen (A `&` B).
Proof.
move=> [[J1 f1] /= [finIf1] ->] [[J2 f2] /= [finIf2] ->]; rewrite bigcupI.
exists (existT (fun J => J -> set T) _ (fun ij => f1 ij.1 `&` f2 ij.2)).
split=> /=; last first.
  by apply/funext=> p; apply/propext; split=> [[ij _ []]|[ij]]; exists ij.
move=> ij.
have [K1 [toI1 [g1 [g1op ->]]]] := finIf1 ij.1.
have [K2 [toI2 [g2 [g2op ->]]]] := finIf2 ij.2.
rewrite bigcapI; exists [finType of sum K1 K2].
exists (fun k => match k with | inl i => toI1 i | inr j => toI2 j end).
exists (fun k => match k with | inl i => g1 i | inr j => g2 j end).
split; first by case=> ?; [apply: g1op|apply: g2op].
by apply/funext=> p; apply/propext; split=> Igp k _; apply: (Igp k); case: k.
Qed.

Lemma sop_setT : sopen setT.
Proof.
exists (existT _ 'I_1 (fun _ => setT)); split; last first.
  by apply/funext=> p; apply/propext; split=> // _; exists ord0.
move=> _ /=; exists [finType of unit]; exists (fun _ => i);
  exists (fun _ => setT).
split; first by move=> _; apply: open_setT.
by apply/funext=> p; apply/propext.
Qed.

Definition supTopologyMixin :=
  TopologicalSpace.Mixin sop_setU sop_setI sop_setT.

Definition supTopologicalSpace := TopologicalSpace.Pack supTopologyMixin T.

Lemma cv_sup (F : set (set T)) (t : T) :
  Filter F -> @cv supTopologicalSpace F t <-> forall i, @cv (TS i) F t.
Proof.
move=> Ffilt; split=> cvFt.
  move=> j A [Aop At]; apply: cvFt; split=> //.
  exists (existT _ 'I_1 (fun _ => A)); split; last first.
    by apply/funext=> p; apply/propext; split=> [Ap|[]] //; exists ord0.
  move=> _ /=; exists [finType of 'I_1]; exists (fun _ => j);
    exists (fun _ => A).
  split=> //; apply/funext=> p; apply/propext; split=> [?|Ap] //.
  exact: (Ap ord0).
move=> A [[[J f] /= [finIf ->]] [j _ fjt]].
suff : F (f j) by apply: filter_imp; exists j.
have [K [toI [g [gop fjval]]]] := finIf j.
rewrite fjval; apply: filter_bigcap.
  by exists (enum K) => k; split=> // _; apply/In_mem; rewrite mem_enum.
move=> k Kk; apply: (cvFt (toI k)); split; first exact: gop.
by move: fjt; rewrite fjval; apply.
Qed.

End Sup_topology.

Section Product_topology.

Variable (T : TopologicalSpace) (I : eqType) (i : I).

Definition prodTopologicalSpace :=
  supTopologicalSpace i (fun i => weakTopologyMixin (fun f : I -> T => f i)).

Lemma cv_prod (F : set (set (I -> T))) (f : I -> T) :
  Filter F ->
  @cv prodTopologicalSpace F f <->
  forall i, @cv (weakTopologicalSpace (fun g => g i)) F f.
Proof. exact: cv_sup. Qed.

End Product_topology.

Class UltraFilter T (F : set (set T)) := {
  ultra_proper :> ProperFilter F ;
  max_filter : forall G : set (set T), ProperFilter G -> F `<=` G -> G = F
}.

Lemma ultraFilterLemma T (F : set (set T)) :
  ProperFilter F -> exists G, UltraFilter G /\ F `<=` G.
Proof.
move=> Fproper.
set filter_preordset := ({G : set (set T) & ProperFilter G /\ F `<=` G}).
set preorder := fun G1 G2 : filter_preordset => projT1 G1 `<=` projT1 G2.
suff [G Gmax] : exists G : filter_preordset, premaximal preorder G.
  have [Gproper sFG] := projT2 G.
  exists (projT1 G); split=> //; split=> // H Hproper sGH.
  have sFH : F `<=` H by apply: subset_trans sGH.
  suff sHG : preorder (existT _ H (conj Hproper sFH)) G.
    by apply/funext => ?; apply/propext; split=> [/sHG|/sGH].
  exact: Gmax.
apply: ZornsLemmaForPreorders.
  by constructor=> [?|G H I sGH sHI ? /sGH /sHI].
move=> S Schain.
apply: or_ind (classic (Inhabited S)) => [[G SG]|S0]; last first.
  have sFF : F `<=` F by [].
  exists (existT _ F (conj Fproper sFF)).
  by move=> G SG; exfalso; apply: S0; apply: Inhabited_intro SG.
have [Gproper sFG] := projT2 G.
have USproper : ProperFilter (\bigcup_(H in S) projT1 H).
  constructor.
    move=> A [H SH HA]; have [Hproper _] := projT2 H.
    exact: filter_ex HA.
  constructor.
  - by exists G => //; apply: filter_true.
  - move=> A B [H1 SH1 H1A] [H2 SH2 H2B].
    apply: or_ind (Schain _ _ SH1 SH2) => [sH12|sH21].
      have /sH12 H2A := H1A; have [H2proper _] := projT2 H2.
      by exists H2 => //; apply: filter_and.
    have /sH21 H1B := H2B; have [H1proper _] := projT2 H1.
    by exists H1 => //; apply: filter_and.
  - move=> A B sAB [H SH HA]; have [Hproper _] := projT2 H.
    by exists H => //; apply: filter_imp HA.
have sFUS : F `<=` \bigcup_(H in S) projT1 H.
  by move=> A FA; exists G => //; apply: sFG.
exists (existT _ (\bigcup_(H in S) projT1 H) (conj USproper sFUS)).
by move=> H SH A HA; exists H.
Qed.

Lemma subset_fin_inter_ultra T Ti (f : family T Ti) :
  finite_inter f -> exists F, UltraFilter F /\ forall i, ind f i -> F (f i).
Proof.
move=> /fin_inter_proper /ultraFilterLemma [F [Fultra sfF]].
exists F; split=> // j fij; apply: sfF.
by exists (Ff (finfam_sing j f)); split; [split=> // ? ->|move=> ?; apply].
Qed.

Lemma ultra_cv_cluster (T : TopologicalSpace) (F : set (set T)) p :
  UltraFilter F -> cluster F p <-> cv F p.
Proof.
move=> Fultra; split.
  by move=> /cv_cluster [G [Gproper [cvGp /max_filter <-]]].
move=> cvFp; apply/cv_cluster; exists F.
by split; [apply: ultra_proper|split].
Qed.

Lemma compact_ultra (T : TopologicalSpace) A :
  compact A <->
  forall F : set (set T), F A -> UltraFilter F -> A `&` cv F !=set0.
Proof.
split=> Aco F FA Ffilt.
  suff [p [Ap clFp]] : A `&` cluster F !=set0.
    by exists p; split=> //; apply/ultra_cv_cluster.
  exact: Aco.
have [G [Gultra sFG]] := ultraFilterLemma Ffilt.
have /Aco /(_ Gultra) [p [Ap cvGp]] : G A by apply: sFG.
exists p; split=> //; apply/cv_cluster; exists G; split=> //.
exact: ultra_proper.
Qed.

Instance filter_image (U V : Type) (f : U -> V) (F : set (set U)) :
  f @` setT = setT -> Filter F -> Filter [set f @` A | A in F].
Proof.
move=> fsurj Ffilt; split.
- by exists setT => //; apply: filter_true.
- move=> _ _ [A FA <-] [B FB <-].
  exists (f @^-1` (f @` A `&` f @` B)); last by rewrite image_preimage.
  have sAB : A `&` B `<=` f @^-1` (f @` A `&` f @` B).
    by move=> x [Ax Bx]; split; exists x.
  by apply: filter_imp sAB _; apply: filter_and.
- move=> A B sAB [C FC fC_eqA].
  exists (f @^-1` B); last by rewrite image_preimage.
  apply: filter_imp FC => p Cp.
  by apply: sAB; rewrite -fC_eqA; exists p.
Qed.

Instance proper_image (U V : Type) (f : U -> V) (F : set (set U)) :
  f @` setT = setT -> ProperFilter F -> ProperFilter [set f @` A | A in F].
Proof.
move=> fsurj Fproper; split; last exact: filter_image.
by move=> _ [A FA <-]; have /filter_ex [p Ap] := FA; exists (f p); exists p.
Qed.

Fixpoint nodup T (l : list T) :=
  match l with
  | nil => True
  | t :: l => ~ In t l /\ nodup l
  end.

Lemma undup_list T (l : list T) :
  exists l', nodup l' /\ (In (A:=T))^~ l `=` (In (A:=T))^~ l'.
Proof.
elim: l => [|t l [l' [ndupl' leql']]]; first by exists nil.
case: (classic (In t l)) => [lt|nlt].
  exists l'; split=> // s; split=> [|ls]; last by right; apply/leql'.
  by apply: or_ind => [<-|ls]; apply/leql'.
exists (t :: l'); split; first by split=> // /leql'.
move=> s; split; by apply: or_ind => [->|/leql' l's]; [left|right].
Qed.

Lemma sub_finite_set T (A B : set T) : A `<=` B -> finite_set B -> finite_set A.
Proof.
move=> sAB [l' Beql']; have [l [ndupl l'eql]] := undup_list l'.
have Beql : B `=` (In (A:=T))^~ l by move=> t; apply: iff_trans (l'eql t).
move=> {Beql' l'eql l'}.
elim: l ndupl A B sAB Beql=> [_ A B sAB Beql|t l ihl [nlt ndupl A B sAB Beqtl]].
  by exists nil => ?; split=> // /sAB /Beql.
move: ihl; move=> /(_ ndupl) ihl.
case: (classic (A t)) => [At|nAt].
  suff [l' Anteql'] : finite_set (A `\ t).
    exists (t :: l') => s; split; last by apply: or_ind => [<-|/Anteql' []].
    move=> sA; case: (classic (s = t))=> [->|snet]; first by left.
    by right; apply/Anteql'.
  have sAntBnt : A `\ t `<=` B `\ t by move=> ? [/sAB].
  apply: ihl sAntBnt _ => s; split=> [[/Beqtl]|ls].
    by apply: or_ind => // -> /(_ (Logic.eq_refl _)).
  by split; [apply/Beqtl; right|move=> seqt; move: ls; rewrite seqt].
have sABnt : A `<=` B `\ t.
  by move=> s As; split; [apply: sAB|move=> seqt; apply: nAt; rewrite -seqt].
apply: ihl sABnt _ => s; split=> [[]|ls]; last first.
  by split; [apply/Beqtl; right|move=> seqt; apply: nlt; rewrite -seqt].
by move/Beqtl; apply: or_ind => [-> /(_ (Logic.eq_refl _))|].
Qed.

Lemma in_ultra_setVsetC U (F : set (set U)) (A : set U) :
  UltraFilter F -> F A \/ F (~` A).
Proof.
move=> Fultra; case: (classic (F (~` A))); first by right.
move=> nFnA; left.
have AIFn0 : forall B, F B -> A `&` B !=set0.
  apply: NNPP.
  move=> /not_all_ex_not [B /(imply_to_and (F _)) [FB /not_ex_all_not AB0]].
  by apply: nFnA; apply: filter_imp FB => p Bp Ap; apply: (AB0 p).
have : finite_inter (mkfamily (F `|` [set A]) id).
  move=> f [ind_sfFA ideqf].
  case: (classic (ind f A))=> [fA|nfA]; last first.
    have : sub_family (mkfamily F id) f.
      split=> // B fB; have /ind_sfFA := fB; apply: or_ind=> // BeqA.
      by exfalso; apply: nfA; rewrite -BeqA.
    exact: filter_finite_inter.
  suff [p [Ap fnAIp]] : A `&` inter_fam (mkfamily (ind f `\ A) f) !=set0.
    exists p => B fB; case: (classic (B = A)) => [->|BneA]; last exact: fnAIp.
    by have /ideqf := Ap; apply.
  apply: AIFn0; apply: filter_bigcap; last first.
    move=> B [fB BneA]; have /ind_sfFA := fB; apply: or_ind=> //.
    suff -> : f B = B by [].
    by apply/funext=> ?; apply/propext; apply: iff_sym; have := ideqf _ fB;
      apply.
  have sfinAfi : ind f `\ A `<=` ind f by move=> ? [].
  by apply: sub_finite_set sfinAfi _; apply: hfam.
move=> /subset_fin_inter_ultra [G [Gultra sFAG]].
have -> : F = G by apply/Logic.eq_sym/max_filter => B FB; apply: sFAG; left.
by apply: sFAG; right.
Qed.

Instance ultra_image (U V : Type) (f : U -> V) (F : set (set U)) :
  f @` setT = setT -> UltraFilter F -> UltraFilter [set f @` A | A in F].
Proof.
move=> fsurj Fultra; split; first exact: proper_image.
move=> G Gproper sfFG; apply/funext=> A; apply/propext; split; last exact: sfFG.
move=> GA; exists (f @^-1` A); last by rewrite image_preimage.
apply: or_ind (in_ultra_setVsetC (f @^-1` A) Fultra)=> // FnpreimA; exfalso.
have : ~ G (f @` (~` (f @^-1` A))).
  rewrite preimage_setC image_preimage // => GnA.
  by have /filter_ex [? []] : G (A `&` (~` A)) by apply: filter_and.
by apply; apply: sfFG; exists (~` (f @^-1` A)).
Qed.

Lemma tychonoff (T : TopologicalSpace) (I : eqType) (i : I) (A : I -> set T) :
  (forall i, compact (A i)) ->
  @compact (prodTopologicalSpace T i) [set f : I -> T | forall i, A i (f i)].
Proof.
move=> Aco; apply/compact_ultra => F FA Fultra.
set pr := fun i (f : I -> T) => f i.
have prT p f j :  pr j (fun k => if j == k then p else f k) = p.
  by rewrite /pr ifT.
have [f Af] := filter_ex _ FA.
have pr_surj : forall i, pr i @` setT = setT.
  move=> j; apply/funext => p; apply/propext; split => // _.
  by exists (fun k => if j == k then p else f k).
set pF := fun i => [set pr i @` B | B in F].
have pFultra : forall i, UltraFilter (pF i).
  by move=> j; apply ultra_image.
have pFA : forall i, pF i (A i).
  move=> j; exists [set w : I -> T | forall i, A i (w i)]=> //.
  apply/funext=> p; apply/propext; split; first by move=> [w Aw <-]; apply: Aw.
  move=> Ajp; exists (fun k => if j == k then p else f k) => // k.
  by case: (eqVneq j k)=> [<-|jnek]; [rewrite ifT|rewrite ifN].
have cvpFA : forall i, {p | (A i `&` cv (pF i)) p}.
  move=> j; apply: constructive_indefinite_description.
  have [p [Ap clpFp]] : A j `&` cluster (pF j) !=set0.
    by apply: (Aco j).
  by exists p; split=> //; apply/ultra_cv_cluster.
set g := fun i => sval (cvpFA i).
exists g; split; first by move=> j; have [] := svalP (cvpFA j).
apply/cv_prod => j; apply/cv_image; first exact: pr_surj.
by have [] := svalP (cvpFA j).
Qed.

Lemma continuous_component (U : UniformSpace) n i (v : 'I_n -> U) :
  Continuity.continuous (fun w : 'I_n -> U => w i) v.
Proof. by move=> A [e vie_A]; exists e => w ve_w; apply/vie_A/ve_w. Qed.

Lemma bigRmin_gt (I : finType) (P : pred I) (i : I) F x :
  P i -> (forall j, P j -> x < F j) -> x < \big[Rmin/(F i)]_(j in P) F j.
Proof.
move=> Pi Fgtx; rewrite unlock.
elim: (index_enum I)=> [|j l ihl] /=; first exact: Fgtx.
have := Fgtx j; rewrite /in_mem /=; case: (P j) => // xltFj.
by apply: Rmin_glb_lt ihl; apply: xltFj.
Qed.

Lemma bigRmin_le (I : finType) (P : pred I) (i : I) F j :
  P i -> P j -> \big[Rmin/(F i)]_(k in P) F k <= F j.
Proof.
have := mem_index_enum j; rewrite unlock; elim: (index_enum I) => //= k l ihl.
rewrite seq.in_cons => /orP; apply: or_ind=> [/eqP<- Pi Pj|lj Pi Pj].
  by rewrite ifT //; apply: Rmin_l.
by case: (k \in P); [apply: Rle_trans (Rmin_r _ _) _|]; apply: ihl.
Qed.

Lemma row_simpl U n (w : 'rV[U]_n.+1) : \row_j (w ord0 j) = w.
Proof. by apply/rowP => ?; rewrite mxE. Qed.

Lemma vect_prod_topologyP (U : UniformSpace) n (A : set 'rV[U]_n.+1) :
  @open uniformTopologicalSpace A <->
  @open (prodTopologicalSpace _ ord0) [set f : 'I_n.+1 -> U | A (\row_j f j)].
Proof.
set B := [set f : 'I_n.+1 -> U | A (\row_j f j)].
set pr := fun j => (fun g : 'I_n.+1 -> U => g j).
split=> [Aop|].
  have {Aop} Bop : @open uniformTopologicalSpace B.
    move=> f /Aop [e fe_A]; exists e => g fe_g; apply: fe_A.
    by move=> ?; rewrite !mxE; apply: fe_g.
  have {Bop} Bop : forall f, B f -> {e : posreal | ball f e `<=` B}.
    by move=> f /Bop; apply: constructive_indefinite_description.
  exists (existT (fun J => J -> set ('I_n.+1 -> U)) _
    (fun f => interior (ball (projT1 f) (sval (Bop _ (projT2 f)))))) => /=.
  split; last first.
    apply/funext=> f; apply/propext; split=> [Bf|[[g Bg] _ bgf]].
      by exists (existT _ f Bf)=> //=; apply: locally_ball.
    by apply: (svalP (Bop _ Bg)); apply: interior_subset.
  move=> [f Bf] /=; exists [finType of 'I_n.+1]; exists id.
  exists (fun j => pr j @^-1` (interior (pr j @` (ball f (sval (Bop f Bf)))))).
  split.
    move=> j; exists (interior (pr j @` (ball f (sval (Bop f Bf))))).
    by split=> //; apply: open_interior.
  have prT p g i :  pr i (fun j => if i == j then p else g j) = p.
    by rewrite /pr ifT.
  apply/funext=> g; apply/propext; split.
    move=> [e ge_bf] j _; exists e=> p bpjgp.
    exists (fun i => if j == i then p else g i) => //; apply: ge_bf => i.
    case: (eqVneq j i)=> [<-|jnei]; first by rewrite ifT.
    by rewrite ifN //; apply: ball_center.
  move=> Ibfg; have {Ibfg} Ibfg : forall j, {ej : posreal |
    ball (g j) ej `<=` pr j @` ball f (sval (Bop f Bf))}.
    by move=> j; apply: constructive_indefinite_description; apply: Ibfg.
  set e := fun j => sval (Ibfg j); set eps := \big[Rmin/(e ord0 : R)]_j e j.
  have eps_gt0 : 0 < eps by apply: bigRmin_gt => // j _; apply: cond_pos.
  exists (mkposreal _ eps_gt0) => h geps_h j.
  suff /(svalP (Ibfg j)) [h' bfh' <-] : ball (g j) (e j) (h j) by apply: bfh'.
  by apply: (ball_le _ eps); [apply: (@bigRmin_le _ predT)|apply: geps_h].
move=> [[J f] /= [finIf BeqUf]] v Av.
have : B (v ord0) by rewrite /B row_simpl.
rewrite BeqUf => - [j _ fjv]; have [K [toI [g [gop fjeqIg]]]] := finIf j.
suff [e ve_fj] : locally (v ord0 : _ -> _) (f j).
  exists e => w ve_w; rewrite -[w]row_simpl -[A _]/(B _) BeqUf; exists j => //.
  exact: ve_fj.
have := fjv; rewrite fjeqIg => Igv.
have v_g : forall k, locally (v ord0 : _ -> _) (g k).
  move=> k; have [C [Cop geqCpreim]] := gop k.
  rewrite geqCpreim; apply: locally_preimage (@continuous_component _ _ _ _) _.
  by apply: Cop; have := Igv k; rewrite geqCpreim; apply.
have {v_g} v_g : forall k, {ek : posreal | ball (v ord0 : _ -> _) ek `<=` g k}.
  by move=> k; apply: constructive_indefinite_description; apply: v_g.
have := mem_enum K; case: (enum K)=> [K0|k l kleqK].
  by exists (mkposreal _ Rlt_0_1)=> ?? i; have := K0 i.
set e := fun k => sval (v_g k); set eps := \big[Rmin/(e k : R)]_j e j.
have eps_gt0 : 0 < eps by apply: bigRmin_gt => // k' _; apply: cond_pos.
exists (mkposreal _ eps_gt0) => h geps_h k' _; apply: (svalP (v_g k')).
by apply: (ball_le _ eps); [apply: (@bigRmin_le _ predT)|apply: geps_h].
Qed.

Lemma simpl_row U n (f : 'I_n -> U) : (\row_j f j) ord0 = f.
Proof. by apply/funext=> ?; rewrite mxE. Qed.

Lemma vect_compactP (U : UniformSpace) n (A : set 'rV[U]_n.+1) :
  @compact uniformTopologicalSpace A <->
  @compact (prodTopologicalSpace _ ord0)
    [set f : 'I_n.+1 -> U | A (\row_j f j)].
Proof.
have set_simpl C : [set v : 'rV[U]_n.+1 | C (\row_j (v ord0 j))] = C.
  by apply/funext=> ?; rewrite row_simpl.
have simpl_set C : [set f | C ((\row_j f j) ord0)] = C.
  by apply/funext=> ?; rewrite simpl_row.
split=> Aco F FA Fproper.
  set G := [set [set v : 'rV[U]_n.+1 | B (v ord0)] | B in F].
  suff [v [Av clGv]] : A `&` @cluster uniformTopologicalSpace G !=set0.
    exists (v ord0); split; first by rewrite row_simpl.
    move=> B C FB [Cop Cv].
    have GB : G [set v | B (v ord0)] by exists B.
    have v_C : @neighbour uniformTopologicalSpace v [set v | C (v ord0)].
      by split=> //; apply/vect_prod_topologyP; rewrite simpl_set.
    by have [w []] := clGv _ _ GB v_C; exists (w ord0).
  have Gproper : ProperFilter G.
    split.
      move=> _ [B FB <-]; have /filter_ex [f Bf] := FB.
      by exists (\row_j f j); rewrite simpl_row.
    split.
    - by exists setT=> //; apply: filter_true.
    - by move=> _ _ [B FB <-] [C FC <-]; exists (B `&` C) => //;
        apply: filter_and.
    - move=> B C sBC [D FD DeqB].
      exists [set f | C (\row_j f j)] => //; apply: filter_imp FD.
      by move=> f Df; apply/sBC; rewrite -DeqB simpl_row.
  by apply: Aco; exists [set f | A (\row_j f j)].
set G := [set [set f : 'I_n.+1 -> U | B (\row_j f j)] | B in F].
suff [f [Af clGf]] :
  [set f | A (\row_j f j)] `&` @cluster (prodTopologicalSpace _ ord0) G !=set0.
  exists (\row_j f j); split=> // B C FB [Cop Cf].
  have GB : G [set g | B (\row_j g j)] by exists B.
  have f_C :
    @neighbour (prodTopologicalSpace _ ord0) f [set g | C (\row_j g j)].
    by split=> //; apply/vect_prod_topologyP.
  by have [g []] := clGf _ _ GB f_C; exists (\row_j g j).
have Gproper : ProperFilter G.
split.
  move=> _ [B FB <-]; have /filter_ex [v Bv] := FB.
  by exists (v ord0); rewrite row_simpl.
split.
- by exists setT => //; apply: filter_true.
- by move=> _ _ [B FB <-] [C FC <-]; exists (B `&` C) => //; apply: filter_and.
- move=> B C sBC [D FD DeqB].
  exists [set v : 'rV[U]_n.+1 | C (v ord0)]; last by rewrite simpl_set.
  by apply: filter_imp FD => v Dv; apply/sBC; rewrite -DeqB row_simpl.
by apply: Aco; exists A.
Qed.

Lemma vect_compact (U : UniformSpace) n (A : 'I_n.+1 -> set U) :
  (forall i, coquelicotComplements.compact (A i)) ->
  coquelicotComplements.compact
    [set v : 'rV[U]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico; apply/uniform_compactP/vect_compactP.
have -> :
  [set f | forall i, A i ((\row_j f j) ord0 i)] = [set f | forall i, A i (f i)].
  by apply/funext=> ?; rewrite simpl_row.
by apply: tychonoff => i; apply/uniform_compactP/Aico.
Qed.

Lemma bounded_closed_compact n (A : set 'rV[R]_n.+1) :
  is_bounded A -> is_closed A -> coquelicotComplements.compact A.
Proof.
move=> [M normAltM] Acl.
have Mnco : coquelicotComplements.compact
  [set v : 'rV[R]_n.+1 | forall i, seg (- M) M (v ord0 i)].
  by apply: (@vect_compact _ _ (fun _ => seg (- M) M)) => _; apply: seg_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvltM i.
suff /Rabs_def2 [/Rlt_le ? /Rlt_le] : norm (v ord0 i) < M by [].
apply: Rle_lt_trans normvltM.
apply: (@bigRmax_leq _ (fun i => norm (v ord0 i))) (Rle_refl _) _.
by move=> ?; apply: norm_ge_0.
Qed.