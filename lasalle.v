Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import fintype bigop ssralg ssrnum finmap interval ssrint.
From mathcomp Require Import boolp reals Rstruct Rbar classical_sets posnum.
From mathcomp Require Import topology normedtype landau derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Section PositiveLimitingSet.

Variable U : uniformType.

Definition pos_limit_set (y : R -> U) :=
  \bigcap_(eps in [set e | 0 < e]) \bigcap_(T in [set T | 0 < T])
    [set p | ltr T `&` (y @^-1` ball p eps) !=set0].

Lemma plim_cluster (y : R -> U) :
  pos_limit_set y = cluster (y @ +oo).
Proof.
rewrite predeqE => p; split.
  move=> plim_p A B [M ygtM_A] /locallyP [e egt0 pe_B].
  wlog Mgt0 : M ygtM_A / 0 < M; last first.
    by have [t [/ygtM_A Ayt /pe_B Byt]] := plim_p _ egt0 _ Mgt0; exists (y t).
  move=> /(_ (maxr M 1)) []; last by move=> q ?; exists q.
    by move=> ?; rewrite ltr_maxl => /andP [/ygtM_A].
  by rewrite ltr_maxr orbC ltr01.
move=> clyp e egt0 T Tgt0.
have [] := clyp (y @` ltr T) (ball p e); first by exists T; apply: imageP.
  by rewrite -locally_ballE; exists e.
by move=> _ [[t ? <-] ?]; exists t.
Qed.

(* mathcomp/analysis issue: should be inferred *)
Instance infty_proper : ProperFilter [filter of +oo].
Proof. exact: Rbar_locally_filter. Qed.

Lemma plimn0 y (A : set U) :
  compact A -> (y @ +oo) A -> cluster (y @ +oo) !=set0.
Proof. by move=> Aco /Aco [p []]; exists p. Qed.

Lemma closed_plim (y : R -> U) : closed (cluster (y @ +oo)).
Proof.
by rewrite clusterE; apply: closed_bigI => ??; apply: closed_closure.
Qed.

Lemma filter_cluster (F : set (set U)) (A : set U) :
  ProperFilter F -> F A -> compact A ->
  forall e, 0 < e -> F (ball_set (cluster F) e).
Proof.
move=> FF FA; rewrite compact_In0 => Aco e egt0.
set B := ball_set (cluster F) e.
have Fn0 : F !=set0 by exists A.
have : A `&` (cluster F `\` B^°) = set0.
  suff -> : cluster F `\` B^° = set0 by rewrite setI0.
  rewrite setD_eq0 => p clFp.
  by rewrite /interior -locally_ballE; exists e => // ??; exists p.
rewrite clusterE [_ `\` _]setI_bigcapl // setIC setI_bigcapl // => IFBoA0.
set f := fun C => closure C `&` ~` B^° `&` A.
have [G sGF IGBoA0] : exists2 G : {fset (set U)},
  {subset G <= F} & \bigcap_(C in [set C | C \in G]) f C = set0.
  have {IFBoA0} IFBoA0 : ~ (\bigcap_(C in F) f C !=set0).
    by move=> [p IFBoAp]; rewrite -[False]/(set0 p) -IFBoA0.
  have /Aco : closed_fam_of A F f.
    exists (fun C => closure C `&` ~` B^°).
      move=> C _; apply: closedI (@closed_closure _ _) _.
      exact/closedC/open_interior.
    by move=> ? _; rewrite setIC.
  move=> /contrap /(_ IFBoA0) /asboolPn /existsp_asboolPn [H /asboolPn].
  move=> /imply_asboolPn [sHF IHBoA0]; exists H => //.
  by rewrite predeqE => p; split=> // IHBoAp; apply: IHBoA0; exists p.
have Gn0 : [set C | C \in G] !=set0.
  apply: contrapT => /asboolPn /forallp_asboolPn G0.
  by rewrite -[False]/(@set0 U point) -IGBoA0 => ? /G0.
move: IGBoA0; have -> : \bigcap_(C in [set C | C \in G]) f C =
  \bigcap_(C in [set C | C \in G]) (A `&` closure C `&` ~` B^°).
  by rewrite predeqE => a; split=> IGBoAa ? /IGBoAa [[]].
rewrite -setI_bigcapl // setD_eq0 => sIGABo.
suff : F B^° by apply: filterS => ?; apply: locally_singleton.
apply: filterS sIGABo _; apply: filter_bigI => C /sGF; rewrite in_setE => FC.
by apply: filterI FA _; apply: filterS (@subset_closure _ C) _.
Qed.

Lemma cvg_to_plim (y : R -> U) (A : set U) :
  (y @ +oo) A -> compact A -> y @ +oo --> cluster (y @ +oo).
Proof.
move=> yinftyA coA B [e egt0 scleB].
by apply: filterS scleB _; apply: filter_cluster coA _ egt0.
Qed.

(* Lemma cvg_to_plim y (A : set U) : *)
(*   (y @ +oo) A -> compact A -> y @ +oo --> cluster (y @ +oo). *)
(* Proof. *)
(* move=> yinftyA coA; apply/NNP. *)
(* move=> /asboolPn /existsp_asboolPn [B] /asboolPn /imply_asboolPn. *)
(* move=> [[e egt0 plim_e_B] /asboolPn /forallp_asboolPn nygtxB]. *)
(* suff : ~` B `&` B !=set0 by case=> ? []. *)
(* have proper_within_CB : ProperFilter (within (~` B) (y @ +oo)). *)
(*   apply: Build_ProperFilter=> C [T ygtTsBC]. *)
(*   have /asboolPn /existsp_asboolPn [t /asboolPn /imply_asboolPn [tgtT nByt]] *)
(*     := nygtxB T. *)
(*   by exists (y t); apply: ygtTsBC. *)
(* have [|p [Ap plimnBp]] := coA _ proper_within_CB. *)
(*   exact: flim_within yinftyA. *)
(* apply plimnBp; first exact: withinT. *)
(* rewrite -locally_ballE; exists e => // q pe_q; apply: plim_e_B. *)
(* by exists p => // C D yinftyC; apply/plimnBp; apply: flim_within yinftyC. *)
(* Qed. *)

Lemma sub_image_at_infty y (A : set U) : y @` (>= 0) `<=` A -> (y @ +oo) A.
Proof. by move=> syRpA; exists 0 => t tgt0; apply/syRpA/imageP/ltrW. Qed.

Lemma sub_plim_clos_invar y (A : set U) :
  y @` (>= 0) `<=` A -> cluster (y @ +oo) `<=` closure A.
Proof. by move=> syRpA p ypp B /ypp; apply; apply: sub_image_at_infty. Qed.

(* to mathcomp/analysis ? *)
Definition continuous_on (T U : topologicalType) (A : set T) (f : T -> U) :=
  forall p, A p -> f @ (within A [filter of p]) --> f p.
Lemma map_sub_cluster (S T : topologicalType) (F : set (set S)) (f : S -> T)
  (A : set S) : Filter F -> continuous_on A f -> F A -> closed A ->
  f @` (cluster F) `<=` cluster (f @ F).
Proof.
move=> Ffilt fcont FA Acl _ [p clFp <-] B C fFB.
have Ap : A p by apply: Acl => ? /clFp - /(_ _ FA).
move=> /(fcont _ Ap) fp_C.
suff /clFp /(_ fp_C) [q [[Aq ?] /(_ Aq)]] : F (A `&` f @^-1` B) by exists (f q).
exact: filterI.
Qed.

Lemma c0_cvg_cst_on_plim A y (V : U -> R) (l : R) :
  continuous_on A V -> V \o y @ +oo --> l ->
  closed A -> y @` (>= 0) `<=` A -> cluster (y @ +oo) `<=` V @^-1` [set l].
Proof.
move=> Vcont Vypl Acl syRpA p plimp.
have Aypinfty : (y @ +oo) A by apply: sub_image_at_infty.
have : (V @` cluster (y @ +oo)) (V p) by exists p.
move=> /(map_sub_cluster _ Vcont Aypinfty Acl).
by move=> /(flim_cluster Vypl) /Rhausdorff ->.
Qed.

End PositiveLimitingSet.

Lemma bounded_plim (K : absRingType) (V : normedModType K) (y : R -> V) :
  bounded (y @` (>= 0)) -> bounded (cluster (y @ +oo)).
Proof.
rewrite /bounded => - [N ybndN].
wlog Ngt0 : N ybndN / 0 < N.
  move=> bnd_plim; apply: (bnd_plim (maxr N 1)); last first.
    by rewrite ltr_maxr orbC ltr01.
  by move=> ?; rewrite ltr_maxl => /andP [/ybndN].
near=> M => p plimp.
have [] := plimp (y @` (>= 0)) (ball_ norm p (PosNum Ngt0)%:num).
- exact: sub_image_at_infty.
- exact: locally_ball_norm.
move=> _ [[t tge0 <-] pN_yt]; rewrite -[p](subrK (y t)).
apply: ler_lt_trans (ler_normm_add _ _) _.
rewrite -ltr_subr_addr; apply: ltr_trans pN_yt _.
rewrite ltr_subr_addr addrC -ltr_subr_addr; apply: ybndN; last by exists t.
by rewrite ltr_subr_addr; near: M; exists (N + N).
Grab Existential Variables. all: end_near. Qed.

Lemma continuous_on_compact (S T : topologicalType) (f : S -> T) (A : set S) :
  continuous_on A f -> compact A -> compact (f @` A).
Proof.
move=> fcont Aco F FF FfA; set G := filter_from F (fun C => A `&` f @^-1` C).
have GF : ProperFilter G.
  apply: (filter_from_proper (filter_from_filter _ _)); first by exists (f @` A).
    move=> C1 C2 F1 F2; exists (C1 `&` C2); first exact: filterI.
    by move=> ?[?[]]; split; split.
  by move=> C /(filterI FfA) /filter_ex [_ [[p ? <-]]]; eexists p.
case: Aco; first by exists (f @` A) => // ? [].
move=> p [Ap clsGp]; exists (f p); split; first exact/imageP.
move=> B C FB /(fcont _ Ap) /= p_Cf.
have : G (A `&` f @^-1` B) by exists B.
by move=> /clsGp /(_ p_Cf) [q [[Aq ?] /(_ Aq)]]; exists (f q).
Qed.

Section DifferentialSystem.

Variable U : normedModType R.
Let hU : hausdorff U := @normedModType_hausdorff _ U.

(* function defining the differential system *)
Variable F : U -> U.

Definition is_sol (y : R^o -> U) :=
  (forall t, t < 0 -> y t = 2 *: (y 0) - (y (- t))) /\
  forall t, 0 <= t -> is_derive (t : R^o) 1 y (F (y t)).

(* compact set used in LaSalle's invariance principle *)
Variable K : set U.
Hypothesis Kco : compact K.

(* solution function *)
Variable (sol : U -> R -> U).
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y, K (y 0) -> is_sol y <-> y = sol (y 0).
Hypothesis sol_cont : forall t, continuous_on K (sol^~ t).

Lemma sol_is_sol p : K p -> is_sol (sol p).
Proof. by move=> Kp; apply/solP; rewrite sol0. Qed.
Hint Resolve sol_is_sol.

Lemma uniq_sol x y :
  K (x 0) -> K (y 0) -> is_sol x -> is_sol y -> x 0 = y 0 -> x = y.
Proof. by move=> Kx0 Ky0 /(solP Kx0)-> /(solP Ky0)->; rewrite !sol0 => ->. Qed.

Definition is_invariant A := forall p, A p -> forall t, 0 <= t -> A (sol p t).

Hypothesis Kinvar : is_invariant K.

Definition shift_sol p t0 t :=
  if t >= 0 then sol p (t + t0) else 2 *: (sol p t0) - (sol p (- t + t0)).

(* to mathcomp/analysis *)
Lemma nearN (R : absRingType) (P : set R) :
  (\forall x \near (0 : R), P x) = (\forall x \near (0 : R), P (- x)).
Proof.
by rewrite propeqE; split=> /locallyP [e egt0 seP]; exists e => // x;
  rewrite /AbsRing_ball /= sub0r -absrN -sub0r => /seP //; rewrite opprK.
Qed.

Lemma sol_shift p t0 : K p -> 0 <= t0 -> is_sol (shift_sol p t0).
Proof.
move=> Kp t0ge0; split=> [t tlt0|t tge0].
  by rewrite /shift_sol lerNgt tlt0 lerr add0r ltrW ?oppr_gt0.
suff dshift : (shift_sol p t0) \o shift t = cst (shift_sol p t0 t) +
  (fun h => h *: F (shift_sol p t0 t)) +o_ (0 : R^o) id.
  have dshiftE : 'd (shift_sol p t0) (t : R^o) =
    (fun h => h *: F (shift_sol p t0 t)) :> (R^o -> U).
    have lin_scal : linear (fun h : R^o => h *: F (shift_sol p t0 t)).
      by move=> ???; rewrite scalerDl scalerA.
    have ->: (fun h : R^o => h *: F (shift_sol p t0 t)) = Linear lin_scal by [].
    apply: diff_unique; first exact: scalel_continuous.
    by apply/eqaddoE; rewrite dshift.
  have diff_shift : differentiable (shift_sol p t0 : R^o -> _) t.
    apply/diff_locallyP; split; last by apply/eqaddoE; rewrite dshift dshiftE.
    by rewrite dshiftE; apply: scalel_continuous.
  apply: DeriveDef; first exact/derivable1_diffP.
  by rewrite deriveE // dshiftE scale1r.
have /sol_is_sol [_ solp] := Kp.
have /solp solp' : 0 <= t + t0 by apply: addr_ge0 => //; apply: ltrW.
rewrite /shift_sol tge0.
move: tge0; rewrite ler_eqVlt orbC => /orP [tgt0|/eqP teq0].
  apply/eqaddoP => _ /posnumP[e]; near=> s.
  rewrite -![(_ + _ : _ -> _) _]/(_ + _) /=.
  have /derivable_locally : derivable (sol p : R^o -> U) (t + t0) 1 by [].
  rewrite funeqE => /(_ s) /=; rewrite addrA [_%:A]mulr1 =>->.
  suff -> /= : 0 <= s + t.
    rewrite derive_val addrC addrA [_ s + _]addrC subrr add0r; near: s.
    by case: e => /=; apply/(eqoP (locally_filter_on (0 : R))).
  near: s; exists t => // s; rewrite /AbsRing_ball /= absrB subr0 => ltst.
  rewrite -ler_subl_addl sub0r; apply/ltrW; apply: ler_lt_trans ltst.
  by rewrite absRE -normrN; apply: ler_norm.
rewrite -teq0 add0r shift0; apply/eqaddoP => _ /posnumP[e]; near=> s.
rewrite -![(_ + _ : _ -> _) _]/(_ + _) /= -[t0]add0r teq0.
have /derivable_locally dsol : derivable (sol p : R^o -> U) (t + t0) 1 by [].
have := dsol; rewrite funeqE => /(_ (- s)) /=; rewrite [_%:A]mulr1 =>->.
have := dsol; rewrite funeqE => /(_ s) /=; rewrite [_%:A]mulr1 =>->.
rewrite -{1}teq0 derive_val; case: (lerP 0 s) => [le0s|lts0].
  rewrite addrC addrA [_ s + _]addrC subrr add0r; near: s.
  by case: e => /=; apply/(eqoP (locally_filter_on (0 : R))).
rewrite !opprD oppox /cst /= addrACA -[(- _ : _ -> _) _]/(- _) !addrA.
rewrite mulr2n scalerDl scale1r -[_ - _ - sol _ _]addrA -opprD subrr sub0r.
rewrite scaleNr opprK addrC addKr -[in X in _ <= X]normmN; near: s.
rewrite !near_simpl -(nearN (fun x : R^o => `|[_ x]| <= e%:num * `|[x]|)).
by case: e => /=; apply/(eqoP (locally_filter_on (0 : R))).
Grab Existential Variables. all: end_near. Qed.

Lemma solD p t0 t :
  K p -> 0 <= t0 -> 0 <= t -> sol p (t + t0) = sol (sol p t0) t.
Proof.
move=> Kp t0ge0 tge0; have /sol_shift /(_ t0ge0) /solP := Kp.
rewrite [shift_sol _ _ _]/shift_sol lerr add0r => <-; last exact: Kinvar.
by rewrite /shift_sol tge0.
Qed.

Lemma invariant_plim p : K p -> is_invariant (cluster (sol p @ +oo)).
Proof.
move=> Kp q plim_q t0 t0_ge0 A B [M].
wlog Mge0 : M / 0 <= M => [sufMge0|] solpMinfty_A.
  apply: (sufMge0 (maxr 0 M)); first by rewrite ler_maxr lerr.
  by move=> x; rewrite ltr_maxl => /andP [_]; apply: solpMinfty_A.
have Kq : K q.
  apply: compact_closed => //.
  by move=> C; apply: plim_q; exists 0 => t /ltrW tge0; apply: Kinvar.
move=> /(sol_cont Kq) /plim_q q_Bsolt0.
have /q_Bsolt0 [_ [[[t tgtM <-] _]]] : (sol p @ +oo) (sol p @` (> M) `&` A).
  by exists M => t tgtM; split; [apply: imageP|apply: solpMinfty_A].
have tge0 : 0 <= t by apply/ltrW; apply: ler_lt_trans tgtM.
have Ksolpt : K (sol p t) by apply: Kinvar.
move=> /(_ Ksolpt) /=; rewrite -solD // => Bsolpt0t; exists (sol p (t0 + t)).
by split=> //; apply/solpMinfty_A/ltr_paddl.
Qed.

Definition limS (A : set U) := \bigcup_(q in A) cluster (sol q @ +oo).

Lemma invariant_limS A : A `<=` K -> is_invariant (limS A).
Proof.
move=> sAK p [q Aq plimp] t tge0.
by exists q => //; apply: invariant_plim => //; apply: sAK.
Qed.

Lemma nincr_lb_cvg (f : R -> R) :
  (forall x y, 0 <= x <= y -> f y <= f x) ->
  (exists M, f @` (>= 0) `<=` (> M)) -> cvg (f @ +oo).
Proof.
move=> fnincr [M ltMf].
apply/cvg_ex; exists (inf (fun x => x \in f @` (>= 0))).
move=> A /locallyP [_ /posnumP[e] infe_A].
have imf_inf : has_inf (fun x => x \in f @` (>= 0)).
  apply/has_infP; split; first by exists (f 0); rewrite in_setE; apply: imageP.
  by exists M; apply/lbP => ?; rewrite in_setE => /ltMf /ltrW.
have := imf_inf => /inf_adherent /(_ [gt0 of e%:num]) [x].
rewrite in_setE => - [t tge0 <-] ltftinfe; exists t => s ltts; apply: infe_A.
rewrite ball_absE /= absrB absRE ger0_norm.
  rewrite ltr_subl_addl.
  by apply: ler_lt_trans ltftinfe; apply: fnincr; rewrite tge0 (ltrW ltts).
rewrite subr_ge0 inf_lower_bound // in_setE; apply: imageP.
by apply: ltrW; apply: ler_lt_trans ltts.
Qed.

(* todo: use directional derivative *)
Lemma stable_limS (V : U -> R^o) :
  continuous_on K V ->
  (forall p t, K p -> 0 <= t -> derivable (V \o sol p : R^o -> R^o) t 1) ->
  (forall (p : U), K p -> derive1 (V \o sol p) 0 <= 0) ->
  limS K `<=` [set p | derive1 (V \o sol p) 0 = 0].
Proof.
move=> Vcont Vsol_drvbl Vsol'le0 p [q Kq plimp].
have ssqRpK : sol q @` (>= 0) `<=` K by move=> _ [t tge0 <-]; apply: Kinvar.
(* should be inferred *)
have atrF := at_right_proper_filter 0.
suff : exists l, cluster (sol q @ +oo) `<=` V @^-1` [set l].
  move=> [l Vpliml]; rewrite derive1E /derive cvg_at_rightE; last first.
    apply: Vsol_drvbl => //; apply: compact_closed => //.
    exact: sub_plim_clos_invar plimp.
  apply: flim_map_lim => A A0; rewrite !near_simpl; near=> h.
  rewrite /= sol0 addr0 [_%:A]mulr1 Vpliml.
    by rewrite Vpliml // subrr scaler0; apply: locally_singleton.
  by apply: invariant_plim => //; apply: ltrW; near: h; exists 1.
suff cvVsol : cvg (V \o sol q @ +oo).
  exists (lim (V \o sol q @ +oo)); apply: (c0_cvg_cst_on_plim Vcont)=> //.
  exact: compact_closed.
apply: nincr_lb_cvg; last first.
  have: compact (V @` K) by apply: continuous_on_compact.
  move=> /compact_bounded [N imVltN].
  exists (- (N + 1))=> _ [t tge0 <-].
  suff : `|(V \o sol q) t| < N + 1 by rewrite ltr_norml => /andP [].
  by apply: imVltN; [rewrite ltr_addl|apply/imageP/Kinvar].
move=> s t /andP [sge0 slet].
apply: ler0_derive1_nincr (lerr _) slet (lerr _).
  move=> r rst; apply: Vsol_drvbl => //; apply: ler_trans sge0 _.
  by rewrite (itvP rst).
move=> r rst; have rge0 : 0 <= r by apply: ler_trans sge0 _; rewrite (itvP rst).
suff -> : derive1 (V \o sol q) r = derive1 (V \o (sol (sol q r))) 0.
  exact/Vsol'le0/Kinvar.
rewrite derive1E /derive cvg_at_rightE; last exact: Vsol_drvbl.
rewrite derive1E /derive cvg_at_rightE; last first.
  by apply: Vsol_drvbl => //; apply: Kinvar.
congr (lim _); rewrite predeqE /= locally_filterE => A; split.
  move=> [_/posnumP[e] Ae]; exists e%:num => // x xe xgt0.
  by rewrite sol0 addr0 -solD //; [apply: Ae|rewrite [_%:A]mulr1 ltrW].
move=> [_/posnumP[e] Ae]; exists e%:num => // x xe xgt0.
by have /Ae - /(_ xe) := xgt0; rewrite sol0 addr0 -solD // [_%:A]mulr1 ltrW.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_to_limS (A : set U) : compact A -> is_invariant A ->
  forall p, A p -> sol p @ +oo --> (limS A : set [uniformType of U]).
Proof.
move=> Aco Ainvar p Ap B [_/posnumP[e] limSeB].
apply: (cvg_to_plim _ Aco); first by exists 0 => _/posnumP[?]; apply: Ainvar.
by exists e%:num=> // q [r plimr re_q]; apply: limSeB; exists r => //; exists p.
Qed.

End DifferentialSystem.
