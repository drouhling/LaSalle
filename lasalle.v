Require Import Reals.
Require Import Lra.

From Coquelicot Require Import Hierarchy Rcomplements Rbar Derive Continuity.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.

Require Import coquelicotComplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Classical_Pred_Type Classical_Prop.

Local Open Scope R_scope.
Local Open Scope classical_set_scope.

Lemma ball_prod (U V : UniformSpace) (p p' : U) (q q' : V) eps :
  ball (p, q) eps (p', q') <-> (ball p eps p') /\ (ball q eps q').
Proof. by []. Qed.
Local Notation "{ 'all' A }" := (forall p, A p : Prop) (at level 0).

Section PositiveLimitingSet.

Variable U : UniformSpace.

Hint Resolve locally_ball.

Definition pos_limit_set (x : R -> U) :=
  \bigcap_(eps : posreal) \bigcap_(T : posreal)
    [set p | Rlt T `&` (x @^-1` ball p eps) !=set0].

Lemma plim_set_cluster (x : R -> U) :
  pos_limit_set x = cluster (x @ +oo).
Proof.
apply/funext=> p; apply/propext.
split=> [plim_p A B [M xMinfty_A] [eps peps_B]|cluster_p eps _ T _].
  wlog Mgt0 : M xMinfty_A / 0 < M.
    move=> /(_ (Rmax M 1)) []; last (by move=> q ABq; exists q).
      by move=> q /Rmax_Rlt [] /xMinfty_A.
    exact: Rlt_le_trans Rlt_0_1 (Rmax_r _ _).
  have [t [/xMinfty_A Axt /peps_B Bxt]] := plim_p eps I (mkposreal _ Mgt0) I.
  by exists (x t).
have [] := cluster_p (x @` Rlt T) (ball p eps);
  first by exists T; apply: imageP.
  exact: locally_ball.
by move=> _ [[t tgtT <-] xt_eps_p]; exists t.
Qed.

Lemma nonempty_pos_limit_set x (A : set U) :
  compact A -> (x @ +oo) A -> cluster (x @ +oo) !=set0.
Proof. by move=> cA /cA [p []]; exists p. Qed.

Lemma closed_pos_lim_set (x : R -> U) : closed (cluster (x @ +oo)).
Proof.
rewrite clusterE; set G := fun B => exists A, (x @ +oo) A /\ B = closure A.
have clIG : closure (\bigcap_(B in G) B) `<=` \bigcap_(B in G) B.
  by apply/closedP; apply:closed_bigcap => _ [? [_ ->]]; apply: closed_closure.
apply/closedP => p plimbar_p A xinftyA.
apply: clIG; last by exists A.
move=> B /plimbar_p [q [plim_q Bq]]; exists q; split=> // _ [C [xinfty_C ->]].
exact: plim_q.
Qed.

Lemma cvg_to_pos_limit_set x (A : set U) :
  (x @ +oo) A -> compact A -> x @ +oo --> (cluster (x @ +oo) : set U).
Proof.
move=> xinftyA coA; apply: NNPP.
case/not_all_ex_not=> B /(@imply_to_and (locally_set _ _)) [[eps plim_eps_B]].
move=> /not_ex_all_not nxinftyB.
suff : ~` B `&` B !=set0 by case=> ? [].
have proper_within_setC_B : ProperFilter (within (~` B) (x @ +oo)).
  split=> [C [T snBxCxT]|]; last exact: within_filter.
  case /not_all_ex_not : (nxinftyB T) => t /(@imply_to_and (T < t)) [tgtT nBxt].
  by exists (x t); exact: snBxCxT.
case: (coA _ _ proper_within_setC_B); first by exact: filter_le_within.
move=> p [Ap plimnBp]; apply plimnBp; first by exists (mkposreal _ Rlt_0_1).
exists eps=> q hq; apply: plim_eps_B; exists p => // C D xinftyC pD.
by apply: plimnBp pD; apply: filter_le_within.
Qed.

Lemma sub_image_at_infty x (A : set U) : x @` Rle 0 `<=` A -> (x @ +oo) A.
Proof. by move=> sxRpA; exists 0 => t tgt0; apply/sxRpA/imageP/Rlt_le. Qed.

Lemma sub_plim_clos_invar x (A : set U) :
  x @` Rle 0 `<=` A -> cluster (x @ +oo) `<=` closure A.
Proof. by move=> sxRpA p xpp B /xpp; apply; apply: sub_image_at_infty. Qed.

Lemma c0_cvg_cst_on_pos_lim_set A x (V : U -> R) (l : R) :
  continuous_on A V -> V \o x @ +oo --> l ->
  closed A -> x @` Rle 0 `<=` A -> cluster (x @ +oo) `<=` V @^-1` [set l].
Proof.
move=> Vcont Vxpl /closedP Acl sxRpA p plimp; apply: Rhausdorff.
have Ap : A p by apply/Acl/(@sub_plim_clos_invar x).
move=> B C /Vcont - /(_ Ap) VpAB /Vxpl VxpC.
have : (x @ +oo) (A `&` (V @^-1` C)).
  by apply: filter_and; [exact: sub_image_at_infty|exact: VxpC].
by move=> /plimp /(_ VpAB) [q [[Aq CVq] /(_ Aq) BVq]]; exists (V q).
Qed.

End PositiveLimitingSet.

Lemma bounded_pos_limit_set (K : AbsRing) (U : NormedModule K) (x : R -> U) :
  is_bounded (x @` Rle 0) -> is_bounded (cluster (x @ +oo)).
Proof.
move=> [M xRpleM]; exists (M + M) => p plimp.
have Mgt0 : 0 < M.
  apply: Rle_lt_trans (norm_ge_0 (x 1)) _.
  by apply: xRpleM; exists 1 => //; apply: Rle_0_1.
have [] := plimp (x @` Rle 0) (ball_norm p (mkposreal _ Mgt0)).
    exact: sub_image_at_infty.
  exact: locally_ball_norm.
move=> _ [[t tge0 <-] pMxt].
have -> : p = plus (x t) (opp (minus (x t) p)).
  by rewrite -[LHS]plus_zero_r -(plus_opp_r (x t)) plus_comm -plus_assoc
             opp_plus opp_opp.
apply: Rle_lt_trans (norm_triangle (x t) (opp (minus (x t) p))) _.
apply: Rplus_lt_compat; last by rewrite norm_opp.
by apply: xRpleM; exists t.
Qed.

Section DifferentialSystem.

Variable U : {normedModule R}.
Variable X : U -> U.
Variable hU : hausdorff U.

Definition is_sol (x : R -> U) := forall t, is_derive x t (X (x t)).

Variable (sol : U -> R -> U).
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall x, is_sol x <-> x = sol (x 0).

Lemma sol_is_sol p : is_sol (sol p).
Proof. by apply/solP; rewrite sol0. Qed.
Hint Resolve sol_is_sol.

Lemma uniq_sol x y : is_sol x -> is_sol y -> x 0 = y 0 -> x = y.
Proof. by move=> /solP-> /solP->; rewrite !sol0 => ->. Qed.

Definition is_invariant A := forall p, A p -> forall t, 0 <= t -> A (sol p t).

Hypothesis (sol_cont : forall t, {all continuous (sol^~ t)}).

Lemma sol_shift p t0 : sol (sol p t0) = (fun t => sol p (t + t0)).
Proof.
apply: uniq_sol=> //; last by rewrite Rplus_0_l sol0.
by move=> t; apply/is_derive_shift/sol_is_sol.
Qed.

Lemma solD p t0 t : sol p (t + t0) = sol (sol p t0) t.
Proof. by rewrite sol_shift. Qed.

Lemma invariant_pos_limit_set p : is_invariant (cluster (sol p @ +oo)).
Proof.
move=> q plim_q t0 t0_ge0 A B [M solpMinfty_A] /sol_cont /plim_q q_Bsolt0.
have /q_Bsolt0 [_ [[[t tgtM <-] _]]] : (sol p @ +oo) ((sol p) @` (Rlt M) `&` A).
  by exists M => t tgtM; split; [apply: imageP|apply: solpMinfty_A].
rewrite -solD => Bsolpt0t; exists (sol p (t0 + t)); split=> //.
by apply: solpMinfty_A; lra.
Qed.

Definition limS (S : set U) := \bigcup_(q in S) cluster (sol q @ +oo).

Lemma invariant_limS S : is_invariant (limS S).
Proof.
move=> p [q Sq plimxp] t tge0.
by exists q => //; exact: invariant_pos_limit_set.
Qed.

Lemma stable_limS (S : set U) (V : U -> R) (V' : U -> U -> R) :
  compact S -> is_invariant S ->
  (forall p : U, S p -> filterdiff V (locally p) (V' p)) ->
  (forall p : U, S p -> (V' p \o X) p <= 0) ->
  limS S `<=` [set p | (V' p \o X) p = 0].
Proof.
move=> Sco Sinvar Vdif V'le0 p [q Sq plimxp].
have Vsol' r : S r -> forall t, 0 <= t ->
    is_derive (V \o sol r) t ((V' (sol r t) \o X) (sol r t)).
  move=> Sr t tge0; have Srt : S (sol r t) by apply: Sinvar.
  (* We should have rewriting rules for differentiation,
     otherwise it introduces evars... *)
  apply: filterdiff_ext_lin.
  apply: filterdiff_comp'.
    exact: sol_is_sol.
  exact: Vdif.
  move=> u; rewrite linear_scal //.
  by have /Vdif [] := Srt.
have ssqRpS : sol q @` Rle 0 `<=` S.
  by move=> _ [t tge0 <-]; apply: Sinvar.
suff : exists l, cluster (sol q @ +oo) `<=` V @^-1` [set l].
  move=> [l Vpliml]; rewrite -[p]sol0; set y := sol p.
  rewrite -[LHS](is_derive_unique (V \o y) 0).
    rewrite (@derive_ext_ge0 _ (fun=> l)); first exact: Derive_const.
      exact: Rle_refl.
    by move=> t tge0; apply/Vpliml/invariant_pos_limit_set.
  apply: Vsol'=> //; last exact: Rle_refl.
  apply/(@closure_subset _ S).
    exact: (compact_closed hU Sco).
  exact: sub_plim_clos_invar plimxp.
have Vcont : continuous_on S V.
  apply: continuous_on_forall => r Sr.
  by apply: filterdiff_continuous; exists (V' r); apply: Vdif.
suff [l Vxtol] : [cvg V \o sol q @ +oo].
  exists l; apply: (c0_cvg_cst_on_pos_lim_set Vcont)=> //.
  exact: compact_closed.
apply: nincr_lb_cvg.
  move=> s t [sge0 slet].
  apply: (@nincr_function_le _ (Finite 0) (Finite t))=> //; last first.
  - exact: Rle_refl.
  - by move=> t' t'ge0 _; apply: (V'le0 (sol q t')); apply: Sinvar.
  - by move=> t' t'ge0 _; apply: Vsol'.
have: compact (V @` S) by apply: continuous_compact.
move=> /compact_bounded [N hN].
exists (- N)=> y [t tge0 <-].
have /hN : (V @` S) ((V \o sol q) t) by apply/imageP/Sinvar.
by move=> /Rabs_def2 [].
Qed.

Lemma cvg_to_limS (S : set U) : compact S -> is_invariant S ->
  forall p, S p -> sol p @ +oo --> limS S.
Proof.
move=> Sco Sinvar p Sp.
apply: (@cvg_to_superset _ (cluster (sol p @ +oo))).
  by move=> q plimxq; exists p.
apply: cvg_to_pos_limit_set Sco.
by exists 0=> t /Rlt_le tge0; exact: Sinvar.
Qed.

End DifferentialSystem.
