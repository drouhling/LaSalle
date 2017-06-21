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

Definition pos_limit_set (y : R -> U) :=
  \bigcap_(eps : posreal) \bigcap_(T : posreal)
    [set p | Rlt T `&` (y @^-1` ball p eps) !=set0].

Lemma plim_set_cluster (y : R -> U) :
  pos_limit_set y = cluster (y @ +oo).
Proof.
apply/funext=> p; apply/propext.
split=> [plim_p A B [M yMinfty_A] [eps peps_B]|cluster_p eps _ T _].
  wlog Mgt0 : M yMinfty_A / 0 < M.
    move=> /(_ (Rmax M 1)) []; last (by move=> q ABq; exists q).
      by move=> q /Rmax_Rlt [] /yMinfty_A.
    exact: Rlt_le_trans Rlt_0_1 (Rmax_r _ _).
  have [t [/yMinfty_A Ayt /peps_B Byt]] := plim_p eps I (mkposreal _ Mgt0) I.
  by exists (y t).
have [] := cluster_p (y @` Rlt T) (ball p eps);
  first by exists T; apply: imageP.
  exact: locally_ball.
by move=> _ [[t tgtT <-] yt_eps_p]; exists t.
Qed.

Lemma nonempty_pos_limit_set y (A : set U) :
  compact A -> (y @ +oo) A -> cluster (y @ +oo) !=set0.
Proof. by move=> cA /cA [p []]; exists p. Qed.

Lemma closed_pos_lim_set (y : R -> U) : is_closed (cluster (y @ +oo)).
Proof.
by rewrite clusterE; apply: is_closed_bigcap => ??; apply: is_closed_closure.
Qed.

Lemma cvg_to_pos_limit_set y (A : set U) :
  (y @ +oo) A -> compact A -> y @ +oo --> cluster (y @ +oo).
Proof.
move=> yinftyA coA B [eps sclepsB].
by apply: filter_imp sclepsB _; apply: filter_cluster coA eps.
Qed.

(* Lemma cvg_to_pos_limit_set y (A : set U) : *)
(*   (y @ +oo) A -> compact A -> y @ +oo --> cluster (y @ +oo). *)
(* Proof. *)
(* move=> yinftyA coA; apply: NNPP. *)
(* case/not_all_ex_not=> B /(@imply_to_and (locally_set _ _)) [[eps plim_eps_B]]. *)
(* move=> /not_ex_all_not nxinftyB. *)
(* suff : ~` B `&` B !=set0 by case=> ? []. *)
(* have proper_within_setC_B : ProperFilter (within (~` B) (y @ +oo)). *)
(*   split=> [C [T snByCyT]|]; last exact: within_filter. *)
(*   case /not_all_ex_not : (nyinftyB T) => t /(@imply_to_and (T < t)) [tgtT nByt]. *)
(*   by exists (y t); exact: snByCyT. *)
(* case: (coA _ _ proper_within_setC_B); first by exact: filter_le_within. *)
(* move=> p [Ap plimnBp]; apply plimnBp; first by exists (mkposreal _ Rlt_0_1). *)
(* exists eps=> q hq; apply: plim_eps_B; exists p => // C D yinftyC pD. *)
(* by apply: plimnBp pD; apply: filter_le_within. *)
(* Qed. *)

Lemma sub_image_at_infty y (A : set U) : y @` Rle 0 `<=` A -> (y @ +oo) A.
Proof. by move=> syRpA; exists 0 => t tgt0; apply/syRpA/imageP/Rlt_le. Qed.

Lemma sub_plim_clos_invar y (A : set U) :
  y @` Rle 0 `<=` A -> cluster (y @ +oo) `<=` closure A.
Proof. by move=> syRpA p ypp B /ypp; apply; apply: sub_image_at_infty. Qed.

Lemma c0_cvg_cst_on_pos_lim_set A y (V : U -> R) (l : R) :
  continuous_on A V -> V \o y @ +oo --> l ->
  is_closed A -> y @` Rle 0 `<=` A -> cluster (y @ +oo) `<=` V @^-1` [set l].
Proof.
move=> Vcont Vypl Acl syRpA p plimp.
have Aypinfty : (y @ +oo) A by apply: sub_image_at_infty.
have : (V @` cluster (y @ +oo)) (V p) by exists p.
move=> /(map_sub_cluster _ Vcont Aypinfty Acl).
by move=> /(filter_le_cluster Vypl) /Rhausdorff ->.
Qed.

End PositiveLimitingSet.

Lemma bounded_pos_limit_set (K : AbsRing) (U : NormedModule K) (y : R -> U) :
  is_bounded (y @` Rle 0) -> is_bounded (cluster (y @ +oo)).
Proof.
move=> [M yRpleM]; exists (M + M) => p plimp.
have Mgt0 : 0 < M.
  apply: Rle_lt_trans (norm_ge_0 (y 1)) _.
  by apply: yRpleM; exists 1 => //; apply: Rle_0_1.
have [] := plimp (y @` Rle 0) (ball_norm p (mkposreal _ Mgt0)).
    exact: sub_image_at_infty.
  exact: locally_ball_norm.
move=> _ [[t tge0 <-] pMyt].
have -> : p = plus (y t) (opp (minus (y t) p)).
  by rewrite -[LHS]plus_zero_r -(plus_opp_r (y t)) plus_comm -plus_assoc
             opp_plus opp_opp.
apply: Rle_lt_trans (norm_triangle (y t) (opp (minus (y t) p))) _.
apply: Rplus_lt_compat; last by rewrite norm_opp.
by apply: yRpleM; exists t.
Qed.

Section DifferentialSystem.

Variable U : {normedModule R}.
Let hU : hausdorff U := @hausdorff_normed_module _ U.

(* function defining the differential system *)
Variable F : U -> U.

Definition is_sol (y : R -> U) := forall t, 0 <= t -> is_derive y t (F (y t)).

(* set on which there are solutions *)
Variable S : set U.

(* solution function *)
Variable (sol : U -> R -> U).
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y, S (y 0) -> is_sol y <-> y = sol (y 0).
Hypothesis sol_cont : forall t, continuous_on (closure S) (sol^~ t).

Lemma sol_is_sol p : S p -> is_sol (sol p).
Proof. by move=> Sp; apply/solP; rewrite sol0. Qed.
Hint Resolve sol_is_sol.

Lemma uniq_sol x y :
  S (x 0) -> S (y 0) -> is_sol x -> is_sol y -> x 0 = y 0 -> x = y.
Proof. by move=> Sx0 Sy0 /(solP Sx0)-> /(solP Sy0)->; rewrite !sol0 => ->. Qed.

Definition is_invariant A := forall p, A p -> forall t, 0 <= t -> A (sol p t).

Hypothesis Sinvar : is_invariant S.

Lemma sol_shift p t0 :
  S p -> 0 <= t0 -> sol (sol p t0) = (fun t => sol p (t + t0)).
Proof.
move=> Sp t0ge0; apply: uniq_sol;
  try apply: sol_is_sol; rewrite ?Rplus_0_l ?sol0 //; try exact: Sinvar.
by move=> t tge0; apply/is_derive_shift/(sol_is_sol Sp)/Rplus_le_le_0_compat.
Qed.

Lemma solD p t0 t : S p -> 0 <= t0 -> sol p (t + t0) = sol (sol p t0) t.
Proof. by move=> Sp t0ge0; rewrite sol_shift. Qed.

Lemma invariant_pos_limit_set p : S p -> is_invariant (cluster (sol p @ +oo)).
Proof.
move=> Sp q plim_q t0 t0_ge0 A B [M].
wlog Mge0 : M / 0 <= M => [sufMge0|] solpMinfty_A.
  apply: (sufMge0 (Rmax 0 M)); first exact: Rmax_l.
  by move=> x /Rmax_Rlt [_]; apply: solpMinfty_A.
have Sbar_q : closure S q.
  by move=> C; apply: plim_q; exists 0 => t /Rlt_le tge0; apply: Sinvar.
move=> /(sol_cont Sbar_q) /plim_q q_Bsolt0.
have /q_Bsolt0 [_ [[[t tgtM <-] _]]] : (sol p @ +oo) (sol p @` (Rlt M) `&` A).
  by exists M => t tgtM; split; [apply: imageP|apply: solpMinfty_A].
have tge0 : 0 <= t by apply: Rlt_le; apply: Rle_lt_trans tgtM.
have Sbar_solpt : closure S (sol p t) by apply/subset_closure/Sinvar.
move=> /(_ Sbar_solpt); rewrite -solD // => Bsolpt0t; exists (sol p (t0 + t)).
by split=> //; apply: solpMinfty_A; lra.
Qed.

Definition limS (K : set U) := \bigcup_(q in K) cluster (sol q @ +oo).

Lemma invariant_limS K : K `<=` S -> is_invariant (limS K).
Proof.
move=> sKS p [q Kq plimp] t tge0.
by exists q => //; apply: invariant_pos_limit_set => //; apply: sKS.
Qed.

Lemma stable_limS (K : set U) (V : U -> R) (V' : U -> U -> R) :
  compact K -> is_invariant K -> K `<=` S ->
  (forall p : U, K p -> filterdiff V (locally p) (V' p)) ->
  (forall p : U, K p -> (V' p \o F) p <= 0) ->
  limS K `<=` [set p | (V' p \o F) p = 0].
Proof.
move=> Kco Kinvar sKS Vdif V'le0 p [q Kq plimp].
have Vsol' r : K r -> forall t, 0 <= t ->
    is_derive (V \o sol r) t ((V' (sol r t) \o F) (sol r t)).
  move=> Kr t tge0; have Krt : K (sol r t) by apply: Kinvar.
  (* We should have rewriting rules for differentiation,
     otherwise it introduces evars... *)
  apply: filterdiff_ext_lin.
  apply: filterdiff_comp'.
    by apply: sol_is_sol tge0; apply: sKS.
  exact: Vdif.
  move=> u; rewrite linear_scal //.
  by have /Vdif [] := Krt.
have ssqRpK : sol q @` Rle 0 `<=` K.
  by move=> _ [t tge0 <-]; apply: Kinvar.
suff : exists l, cluster (sol q @ +oo) `<=` V @^-1` [set l].
  move=> [l Vpliml]; rewrite -[p]sol0; set y := sol p.
  rewrite -[LHS](is_derive_unique (V \o y) 0).
    rewrite (@derive_ext_ge0 _ (fun=> l)); first exact: Derive_const.
      exact: Rle_refl.
    by move=> t tge0; apply/Vpliml/invariant_pos_limit_set => //; apply: sKS.
  apply: Vsol'=> //; last exact: Rle_refl.
  suff : is_closed K by apply; apply: sub_plim_clos_invar plimp.
  exact: compact_closed hU Kco.
have Vcont : continuous_on K V.
  apply: continuous_on_forall => r Kr.
  by apply: filterdiff_continuous; exists (V' r); apply: Vdif.
suff [l Vsoltol] : [cvg V \o sol q @ +oo].
  exists l; apply: (c0_cvg_cst_on_pos_lim_set Vcont)=> //.
  exact: compact_closed hU Kco.
apply: nincr_lb_cvg.
  move=> s t [sge0 slet].
  apply: (@nincr_function_le _ (Finite 0) (Finite t))=> //; last first.
  - exact: Rle_refl.
  - by move=> t' t'ge0 _; apply: (V'le0 (sol q t')); apply: Kinvar.
  - by move=> t' t'ge0 _; apply: Vsol'.
have: compact (V @` K) by apply: continuous_compact.
move=> /compact_bounded [N hN].
exists (- N)=> _ [t tge0 <-].
have /hN : (V @` K) ((V \o sol q) t) by apply/imageP/Kinvar.
by move=> /Rabs_def2 [].
Qed.

Lemma cvg_to_limS (K : set U) : compact K -> is_invariant K ->
  forall p, K p -> sol p @ +oo --> limS K.
Proof.
move=> Kco Kinvar p Kp.
apply: (@cvg_to_superset _ (cluster (sol p @ +oo))).
  by move=> q plimq; exists p.
apply: cvg_to_pos_limit_set Kco.
by exists 0=> t /Rlt_le tge0; exact: Kinvar.
Qed.

End DifferentialSystem.
