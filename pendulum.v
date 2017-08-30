Require Import Reals Lra.
From mathcomp Require Import ssreflect ssrfun eqtype ssrbool ssrnat bigop ssralg
  matrix fintype zmodp seq.
Require Import lasalle tychonoff coquelicotComplements vect.
From Coquelicot Require Import Hierarchy Rcomplements Continuity Rbar Derive
  Lub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Classical_Prop Classical_Pred_Type.

Local Open Scope seq_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Notation "p [ i ]" := (p 0 (i%:R)) (at level 10).

Local Open Scope R_scope.

Section System.

Parameter m M l g : posreal.

Variable ke kv kx kd : posreal.

Let U := 'rV[R]_5.

(* p = (x, x', cos theta, sin theta, theta') *)
Definition E (p : U) :=
  (1 / 2) * ((M + m) * (p[1] ^ 2) + m * (l ^ 2) * (p[4] ^ 2)) +
  m * l * p[1] * p[2] * p[4] + m * l * g * (p[2] - 1).

Definition E' (p q : U) :=
  (1 / 2) * ((M + m) * (2 * q[1] * (p[1] ^ 1)) +
   m * (l ^ 2) * (2 * q[4] * (p[4] ^ 1))) +
  m * l * ((q[1] * p[2] + p[1] * q[2]) * p[4] + p[1] * p[2] * q[4]) +
  m * l * g * q[2].

Lemma filterdiff_pow n (F : set (set R)) x :
  ProperFilter F -> is_filter_lim F x ->
  filterdiff (pow^~ n) F (fun y => n * y * (x ^ n.-1)).
Proof.
move=> Fprop limFx.
have : forall y, scal y (n * 1 * (x ^ n.-1)) = n * y * (x ^ n.-1).
  by move=> ?; rewrite /scal /= /mult /= Rmult_1_r -Rmult_assoc
    [_ * n]Rmult_comm.
apply: filterdiff_ext_lin; apply: filterdiff_locally limFx _.
by apply/is_derive_pow/is_derive_id.
Qed.

Lemma filterdiff_pow_fct (V : NormedModule R_AbsRing) n (F : set (set V)) :
  ProperFilter F -> forall x, is_filter_lim F x -> forall f lf : V -> R,
  filterdiff f F lf -> continuous f x ->
  filterdiff (fun y => (f y) ^ n) F (fun y => n * (lf y) * ((f x) ^ n.-1)).
Proof.
move=> Fproper x limFx f lf f'lf fcontx.
apply: (filterdiff_comp _ (pow^~ n) _ (fun y => n * y * (f x) ^ n.-1) f'lf _).
by apply: filterdiff_pow; apply: is_filter_lim_filtermap.
Qed.

Lemma filterdiff_pow_component n m (p : U) :
  filterdiff (fun q : U => q[n] ^ m) (locally p)
    (fun q => m * q[n] * (p[n] ^ m.-1)).
Proof.
have := linear_cont _ p (is_linear_component _ n%:R).
by apply filterdiff_pow_fct => //;
  [apply: locally_filter|apply: filterdiff_component].
Qed.

Lemma filterdiff_E (p : U) : filterdiff E (locally p) (E' p).
Proof.
apply: filterdiff_plus_fct; last first.
  apply: filterdiff_scal_r_fct Rmult_comm _.
  have : forall p : U, p[2] + 0 = p[2] by move=> ?; rewrite Rplus_0_r.
  by apply/filterdiff_ext_lin/filterdiff_plus_fct;
    [apply: filterdiff_component|apply: filterdiff_const].
apply: filterdiff_plus_fct.
  apply: filterdiff_scal_r_fct Rmult_comm _.
  by apply: filterdiff_plus_fct; apply: filterdiff_scal_r_fct Rmult_comm _;
    apply: filterdiff_pow_component.
have /filterdiff_ext :
  forall q : U, m * l * (q[1] * q[2] * q[4]) = m * l * q[1] * q[2] * q[4].
  by move=> ?; rewrite !Rmult_assoc.
apply; apply: filterdiff_scal_r_fct Rmult_comm _.
apply: filterdiff_mult_fct Rmult_comm _ _; last exact: filterdiff_component.
by apply: filterdiff_mult_fct Rmult_comm _ _; apply: filterdiff_component.
Qed.

Definition fctrl (p : U) :=
  (kv * m * p[3] * (g * p[2] - l * (p[4] ^ 2)) -
   (M + m * (p[3] ^ 2)) * (kx * p[0] + kd * p[1])) /
  (kv + (M + m * (p[3] ^ 2)) * ke * (E p)).

Definition Fpendulum (p : U) : U :=
  \row_(i < 5) nth 0
   [:: p[1]
     ; ((m * p[3] * (l * (p[4] ^ 2) - g * p[2]) + (fctrl p)) /
        (M + m * (p[3] ^ 2)))
     ; - p[3] * p[4]
     ; p[2] * p[4]
     ; (((M + m) * g * p[3] - p[2] * (m * l * (p[4] ^ 2) * p[3] + (fctrl p))) /
        (l * (M + m * (p[3] ^ 2))))] i.

Definition V (p : U) :=
  (ke / 2) * ((E p) ^ 2) + (kv / 2) * (p[1] ^ 2) + (kx / 2) * (p[0] ^ 2).

Definition V' (p q : U) :=
  (ke / 2) * (2 * (E' p q) * ((E p) ^ 1)) +
  (kv / 2) * (2 * q[1] * (p[1] ^ 1)) + (kx / 2) * (2 * q[0] * (p[0] ^ 1)).

Lemma filterdiff_V F p :
  ProperFilter F -> is_filter_lim F p -> filterdiff V F (V' p).
Proof.
move=> Fproper /filterdiff_locally; apply.
do 2 ?[apply: filterdiff_plus_fct; last
  by apply: filterdiff_scal_r_fct Rmult_comm _;
    apply: filterdiff_pow_component].
apply: filterdiff_scal_r_fct Rmult_comm _.
apply filterdiff_pow_fct => //; [exact: locally_filter|exact: filterdiff_E|].
by apply: filterdiff_continuous; exists (E' p); apply: filterdiff_E.
Qed.

Variable p0 : U.
Let B := ke * ((Rmin (kv / (ke * (M + m))) (2 * m * g * l)) ^ 2) / 2.
(* restriction to make fctrl smooth *)
Hypothesis p0_valid : V p0 < B.

Definition K : set U :=
  [set p : U | (p[2] ^ 2) + (p[3] ^ 2) = 1 /\ V p <= V p0].

Lemma pow_continuous n x : continuous (pow^~ n) x.
Proof.
apply: filterdiff_continuous; exists (fun y => n * y * x ^ n.-1).
exact/filterdiff_pow.
Qed.

Hint Resolve cond_pos.

Lemma is_closed_circ : is_closed ([set p : U | (p[2] ^ 2) + (p[3] ^ 2) = 1]).
Proof.
move=> p clcircp; apply: Req_le_aux => e.
have /pow_continuous [e1 p2e1_sp2he] :=
  locally_ball (p[2] ^ 2) (mkposreal _ (is_pos_div_2 e)).
have /pow_continuous [e2 p3e2_sp3he] :=
  locally_ball (p[3] ^ 2) (mkposreal _ (is_pos_div_2 e)).
have me12_gt0 : 0 < Rmin e1 e2 by apply: Rmin_pos.
have [q [circq pme12_q]] :
  [set p : U | (p[2] ^ 2) + (p[3] ^ 2) = 1] `&`
  ball p (mkposreal _ me12_gt0) !=set0 by apply/clcircp/locally_ball.
rewrite -circq /Rminus Ropp_plus_minus_distr Rplus_assoc
  -[X in _ + X]Rplus_assoc [(p[3] ^ 2) + _]Rplus_comm Rplus_assoc -Rplus_assoc
  [_ e]double_var.
apply: Rle_trans (Rabs_triang _ _) _; apply: Rplus_le_compat; apply: Rlt_le.
  rewrite Rabs_minus_sym; apply: p2e1_sp2he; apply: ball_le (Rmin_l _ e2) _ _.
  exact: pme12_q.
rewrite Rabs_minus_sym; apply: p3e2_sp3he; apply: ball_le (Rmin_r e1 _) _ _.
exact: pme12_q.
Qed.

Lemma is_closed_Vpreim_leVp0 : is_closed (V @^-1` (Rle^~ (V p0))).
Proof.
apply: continuous_closed_preimage.
  move=> p; apply: filterdiff_continuous; exists (V' p).
  by apply: filterdiff_V.
apply: closed_is_closed; apply: closed_le.
Qed.

Lemma is_closed_K : is_closed K.
Proof. exact: is_closed_setI is_closed_circ is_closed_Vpreim_leVp0. Qed.

Lemma bounded_poly a b c d :
  0 < a -> exists M, forall x, a * (x ^ 2) - (b * Rabs x) - c < d -> Rabs x < M.
Proof.
move=> agt0.
have ptoinfty : (fun x => a * (x ^ 2) - (b * Rabs x) - c) @ +oo --> +oo.
  move=> A [M sgtMA].
  exists (Rmax (sqrt (Rmax (M + c) 0)) (((sqrt (Rmax (M + c) 0)) + b) / a)).
  move=> x /Rmax_Rlt [Mpcltx Mpcltaxpb]; apply: sgtMA.
  have xgt0 : 0 < x by apply: Rle_lt_trans (sqrt_pos _) Mpcltx.
  rewrite Rabs_pos_eq; last exact/Rlt_le.
  apply/Rlt_minus_r.
  rewrite /= Rmult_1_r -Rmult_assoc /Rminus Ropp_mult_distr_l
    -Rmult_plus_distr_r.
  have : sqrt (Rmax (M + c) 0) < a * x - b.
    by rewrite Rmult_comm; apply/Rlt_minus_r/Rlt_div_l.
  move=> {Mpcltaxpb} Mpcltaxpb; move: Mpcltx => /Rlt_le Mpclex.
  apply: Rle_lt_trans (Rmult_lt_compat_r _ _ _  xgt0 Mpcltaxpb).
  apply: Rle_trans (Rmult_le_compat_l _ _ _ (sqrt_pos _) Mpclex).
  by rewrite sqrt_def; [apply: Rmax_l|apply: Rmax_r].
have mtoinfty : (fun x => a * (x ^ 2) - (b * Rabs x) - c) @ -oo --> +oo.
  move=> A /ptoinfty [M sgtMAp]; exists (- M) => x.
  rewrite -[X in X < _]Ropp_involutive => /Ropp_lt_cancel /sgtMAp.
  by rewrite -Rsqr_pow2 -Rsqr_neg Rsqr_pow2 Rabs_Ropp.
rewrite /filter_le /filtermap /= in ptoinfty.
have dleatinfty : [filter of +oo] (Rle d) by exists d => ? /Rlt_le.
have /ptoinfty [M1 sgtM1dlep] := dleatinfty.
have /mtoinfty [M2 sltM2dlep] := dleatinfty.
exists ((Rmax M1 (- M2)) + 1) => x pxltd.
apply: Rle_lt_trans (Rlt_plus_1 _); apply/Rnot_gt_le => /Rmax_Rlt [M1ltx M2ltx].
move: pxltd; apply/Rge_not_lt/Rle_ge; case: (Rle_lt_dec 0 x) => [xge0|xlt0].
  by apply: sgtM1dlep; rewrite -(Rabs_pos_eq _ xge0).
by apply/sltM2dlep/Ropp_lt_cancel; rewrite -[X in _ < X](Rabs_left _ xlt0).
Qed.

Lemma is_bounded_K : is_bounded K.
Proof.
have [M1 K0123ltM1] : exists M1, forall p, K p ->
  Rabs (p[0]) < M1 /\ Rabs (p[1]) < M1 /\ Rabs (p[2]) < M1 /\ Rabs (p[3]) < M1.
  exists (Rmax 2 (Rmax (sqrt (2 * B / kv)) (sqrt (2 * B / kx)))).
  move=> p [circp Vps]; split.
    do 2 ?[apply: Rlt_le_trans (Rmax_r _ _)].
    rewrite -sqrt_Rsqr_abs Rsqr_pow2; apply: sqrt_lt_1_alt.
    split; first exact: pow2_ge_0.
    apply/(Rlt_div_r (p[0] ^ 2)) => //.
    rewrite [X in _ < X]Rmult_comm; apply/Rlt_div_l; first exact/Rlt_gt/Rlt_0_2.
    rewrite [_ * _ / _]Rmult_assoc Rmult_comm.
    apply: Rle_lt_trans p0_valid; apply: Rle_trans Vps.
    rewrite -[X in X <= _]Rplus_0_l; apply: Rplus_le_compat_r.
    by apply: Rplus_le_le_0_compat; apply: Rmult_le_pos (pow2_ge_0 _);
      apply: Rlt_le; apply: is_pos_div_2.
  split.
    apply: Rlt_le_trans (Rmax_r _ _); apply: Rlt_le_trans (Rmax_l _ _).
    rewrite -sqrt_Rsqr_abs Rsqr_pow2; apply: sqrt_lt_1_alt.
    split; first exact: pow2_ge_0.
    apply/(Rlt_div_r (p[1] ^ 2)) => //.
    rewrite [X in _ < X]Rmult_comm; apply/Rlt_div_l; first exact/Rlt_gt/Rlt_0_2.
    rewrite [_ * _ / _]Rmult_assoc Rmult_comm.
    apply: Rle_lt_trans p0_valid; apply: Rle_trans Vps.
    rewrite -[X in X <= _]Rplus_0_l [X in _ <= X]Rplus_comm -Rplus_assoc.
    apply: Rplus_le_compat_r.
    by apply: Rplus_le_le_0_compat; apply: Rmult_le_pos (pow2_ge_0 _);
      apply: Rlt_le; apply: is_pos_div_2.
  split; apply: Rlt_le_trans (Rmax_l _ _); apply: Rle_lt_trans (Rlt_n_Sn _);
    rewrite -sqrt_Rsqr_abs Rsqr_pow2 -sqrt_1 -circp;
    apply: sqrt_le_1_alt.
    rewrite -[X in X <= _]Rplus_0_r; apply: Rplus_le_compat_l.
    exact: pow2_ge_0.
  rewrite -[X in X <= _]Rplus_0_l; apply: Rplus_le_compat_r.
  exact: pow2_ge_0.
suff [M2 K4ltM2] : exists M2, forall p, K p -> Rabs (p[4]) < M2.
  exists (Rmax M1 M2) => p Kp.
  have /K0123ltM1 [p0ltM1 [p1ltM1 [p2ltM1 p3ltM1]]] := Kp.
  have /K4ltM2 p4ltM2 := Kp.
  apply: bigRmax_lt.
    apply: Rlt_le_trans (Rmax_l _ _); apply: Rle_lt_trans p0ltM1.
    exact: Rabs_pos.
  case; do 4 ?[case; first by move=> ?; rewrite -[Ordinal _]natr_Zp;
    apply: Rlt_le_trans (Rmax_l _ _)].
  case; last by move=> n ltnp5; exfalso; move: ltnp5; rewrite !ltnS ltn0.
  by move=> ?; rewrite -[Ordinal _]natr_Zp; apply: Rlt_le_trans (Rmax_r _ _).
have hmslgt0 : 0 < (m * (l ^ 2) / 2).
  apply: Rdiv_lt_0_compat Rlt_0_2; apply: Rmult_lt_0_compat => //.
  by apply/pow2_gt_0/Rgt_not_eq.
have [M2 sEsltM2] := bounded_poly (m * l * (M1 ^ 2)) (m * l * g * (M1 + 1))
  (sqrt (2 * B / ke)) hmslgt0.
exists M2 => p Kp; apply: sEsltM2.
have [_ Vps] := Kp; have /K0123ltM1 [_ [p1ltM1 [p2ltM1 _]]] := Kp.
have : E p < sqrt (2 * B / ke).
  apply: Rle_lt_trans (Rle_abs _) _.
  rewrite -sqrt_Rsqr_abs Rsqr_pow2; apply: sqrt_lt_1_alt.
  split; first exact: pow2_ge_0.
  apply/(Rlt_div_r ((E p) ^ 2)) => //.
  rewrite [X in _ < X]Rmult_comm; apply/Rlt_div_l; first exact/Rlt_gt/Rlt_0_2.
  rewrite [_ * _ / _]Rmult_assoc Rmult_comm.
  apply: Rle_lt_trans p0_valid; apply: Rle_trans Vps.
  rewrite -[X in X <= _]Rplus_0_r [V _]Rplus_assoc; apply: Rplus_le_compat_l.
  by apply: Rplus_le_le_0_compat; apply: Rmult_le_pos (pow2_ge_0 _);
    apply: Rlt_le; apply: is_pos_div_2.
apply: Rle_lt_trans; apply: Rplus_le_compat; last first.
  apply: Rlt_le; rewrite !Ropp_mult_distr_r; apply: Rmult_lt_compat_l.
    by do 2 ?[apply: Rmult_lt_0_compat => //].
  rewrite Ropp_plus_distr; apply: Rplus_lt_compat_r.
  by have /Rabs_def2 [] := p2ltM1.
rewrite Rmult_plus_distr_l [1 / 2 * _ + _]Rplus_comm Rplus_assoc.
have -> : 1 / 2 * (m * (l ^ 2) * (p[4] ^ 2)) = m * (l ^ 2) / 2 * (p[4] ^ 2).
  by field.
apply: Rplus_le_compat_l.
rewrite -[X in X <= _]Rplus_0_l; apply: Rplus_le_compat.
  apply: Rmult_le_pos; first exact: Rdiv_le_0_compat Rle_0_1 Rlt_0_2.
  apply: Rmult_le_pos (pow2_ge_0 _).
  by apply: Rplus_le_le_0_compat; apply/Rlt_le.
rewrite Rmult_assoc Ropp_mult_distr_r [X in _ <= X]Rmult_assoc
  [X in _ <= X]Rmult_assoc.
apply: Rmult_le_compat_l; first by apply: Rmult_le_pos; apply: Rlt_le.
case: (Rle_lt_dec 0 (p[4])) => [p4ge0|p4lt0].
  rewrite Ropp_mult_distr_l -Rmult_assoc Rabs_pos_eq => //.
  apply: Rmult_le_compat_r p4ge0 _; rewrite /= Rmult_1_r.
  case: (Rle_lt_dec 0 (p[1])) => [p1ge0|/Rlt_le p1le0].
    rewrite Ropp_mult_distr_r.
    have /Rabs_def2 [_ /Rlt_le p2geoM] := p2ltM1.
    apply: Rle_trans (Rmult_le_compat_l _ _ _ p1ge0 p2geoM).
    rewrite Rmult_comm [X in _ <= X]Rmult_comm.
    apply: Rmult_le_compat_neg_l; last by have /Rabs_def2 [/Rlt_le] := p1ltM1.
    rewrite -Ropp_0; apply/Ropp_le_contravar/Rlt_le.
    by apply: Rle_lt_trans p1ltM1; apply: Rabs_pos.
  rewrite Ropp_mult_distr_l.
  have /Rabs_def2 [/Rlt_le p2leM _] := p2ltM1.
  apply: Rle_trans (Rmult_le_compat_neg_l _ _ _ p1le0 p2leM).
  apply: Rmult_le_compat_r; last by have /Rabs_def2 [_ /Rlt_le] := p1ltM1.
  by apply: Rlt_le; apply: Rle_lt_trans p1ltM1; apply: Rabs_pos.
rewrite (Rabs_left _ p4lt0) Ropp_mult_distr_r Ropp_involutive -Rmult_assoc.
rewrite Rmult_comm [X in _ <= X]Rmult_comm /= Rmult_1_r.
apply: Rmult_le_compat_neg_l; first exact: Rlt_le.
case: (Rle_lt_dec 0 (p[1])) => [p1ge0|/Rlt_le p1le0].
  have /Rabs_def2 [/Rlt_le p2leM1 _] := p2ltM1.
  apply: Rle_trans (Rmult_le_compat_l _ _ _ p1ge0 p2leM1) _.
  apply: Rmult_le_compat_r; last by have /Rabs_def2 [/Rlt_le] := p1ltM1.
  by apply: Rlt_le; apply: Rle_lt_trans p1ltM1; apply: Rabs_pos.
have /Rabs_def2 [_ /Rlt_le p2geoM1] := p2ltM1.
apply: Rle_trans (Rmult_le_compat_neg_l _ _ _ p1le0 p2geoM1) _.
rewrite -Ropp_mult_distr_r Ropp_mult_distr_l.
apply: Rmult_le_compat_r.
  by apply: Rlt_le; apply: Rle_lt_trans p1ltM1; apply: Rabs_pos.
rewrite -[X in _ <= X]Ropp_involutive; apply: Ropp_le_contravar.
by have /Rabs_def2 [_ /Rlt_le] := p1ltM1.
Qed.

Lemma Kco : compact K.
Proof. exact: bounded_closed_compact is_bounded_K is_closed_K. Qed.

Lemma Mp_ms_gt0 (p : U) : 0 < M + m * (p[3] ^ 2).
Proof.
apply: Rplus_lt_le_0_compat => //.
by apply: Rmult_le_pos; [apply/Rlt_le|apply: pow2_ge_0].
Qed.

Lemma E'E (p : U) :
  (p[2] ^ 2) + (p[3] ^ 2) = 1 -> E' p (Fpendulum p) = p[1] * (fctrl p).
Proof.
rewrite -[1](Rplus_minus (p[2] ^ 2)) => /Rplus_eq_reg_l circp.
rewrite /E' !mxE circp /=; field.
split; apply/not_eq_sym/Rlt_not_eq => //.
by rewrite -{2}[p[2]]Rmult_1_r -circp; apply: Mp_ms_gt0.
Qed.

Lemma E_small p : V p < B -> Rabs (E p) < kv / (ke * (M + m)).
Proof.
move=> Vp_s; rewrite -[X in _ < X]Rabs_pos_eq; last first.
  apply: Rdiv_le_0_compat; first exact/Rlt_le.
  by apply: Rmult_lt_0_compat => //; apply: Rplus_lt_0_compat.
apply: Rsqr_lt_abs_0; rewrite !Rsqr_pow2.
have gt20 : 2 > 0 by apply/Rlt_gt/Rlt_0_2.
have : 2 * (V p) / ke < (kv / (ke * (M + m))) ^ 2.
  apply/Rlt_div_l => //; rewrite Rmult_comm; apply/Rlt_div_r => //.
  apply: Rlt_le_trans Vp_s _.
  rewrite /B Rmult_comm ![_ * _ / _]Rmult_assoc; apply/Rmult_le_compat_r.
    by apply: Rdiv_le_0_compat; [apply: Rlt_le|apply: Rgt_lt].
  apply: pow_incr; split; last exact: Rmin_l.
  apply: Rmin_glb.
    apply: Rdiv_le_0_compat; first exact: Rlt_le.
    by apply: Rmult_lt_0_compat => //; apply: Rplus_lt_0_compat.
  by do 3 ?[apply: Rmult_le_pos; last exact: Rlt_le]; apply: Rlt_le.
apply: Rle_lt_trans; apply/(Rle_div_r (_ ^ 2)) => //.
rewrite [X in _ <= X]Rmult_comm; apply/Rle_div_l; first exact/Rlt_gt/Rlt_0_2.
rewrite [(_ ^ 2) * _ / _]Rmult_assoc Rmult_comm /V Rplus_assoc Rplus_comm.
apply/Rle_minus_l; rewrite Rminus_eq_0.
by apply: Rplus_le_le_0_compat; apply: Rmult_le_pos; try exact: pow2_ge_0;
  apply: Rdiv_le_0_compat; try exact: Rlt_0_2; apply/Rlt_le.
Qed.

Lemma fctrl_wdef (p : U) : (p[2] ^ 2) + (p[3] ^ 2) = 1 -> V p < B ->
  kv + (M + m * (p[3] ^ 2)) * ke * (E p) <> 0.
Proof.
move=> circp Vp_s; rewrite Rmult_comm.
move/Rplus_opp_r_uniq/(Rmult_eq_compat_r (/ ((M + m * (p[3] ^ 2)) * ke))).
have Mmp3ke_gt0 : 0 < (M + m * p [3] ^ 2) * ke.
  by apply: Rmult_lt_0_compat => //; apply: Mp_ms_gt0.
rewrite Rmult_assoc Rinv_r; last exact/not_eq_sym/Rlt_not_eq.
rewrite Rmult_1_r => Epval; have /E_small := Vp_s.
rewrite Epval -Ropp_mult_distr_l Rabs_Ropp Rabs_pos_eq; last first.
  apply: Rdiv_le_0_compat; first exact/Rlt_le.
  by apply: Rmult_lt_0_compat => //; apply: Mp_ms_gt0.
move/(Rmult_lt_reg_l _ _ _ (cond_pos _))/(Rinv_lt_cancel _ _ Mmp3ke_gt0).
rewrite Rmult_comm; move/(Rmult_lt_reg_r _ _ _ (cond_pos _))/Rplus_lt_reg_l.
rewrite -[X in X < _]Rmult_1_r; move/(Rmult_lt_reg_l _ _ _ (cond_pos _)).
apply: Rle_not_lt; rewrite -circp.
by apply/Rle_minus_l; rewrite Rminus_eq_0; apply: pow2_ge_0.
Qed.

Lemma V'E (p : U) : (p[2] ^ 2) + (p[3] ^ 2) = 1 -> V p < B ->
  V' p (Fpendulum p) = - kd * (p[1] ^ 2).
Proof.
move=> circp Vp_s; rewrite /V' (E'E circp) !mxE /= /fctrl; field; split.
  exact: fctrl_wdef.
by rewrite -{2}[p[3]]Rmult_1_r; apply/not_eq_sym/Rlt_not_eq/Mp_ms_gt0.
Qed.

(* TODO: show that Fpendulum is smooth in K and remove these hypotheses using
  Cauchy-Lipschitz *)
Variable (sol : U -> R -> U).
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y, K (y 0) -> is_sol Fpendulum y <-> y = sol (y 0).
Hypothesis sol_cont : forall t, continuous_on K (sol^~ t).

Lemma circ_invar p :
  K p -> forall t, 0 <= t -> (sol p t)[2] ^ 2 + (sol p t)[3] ^ 2 = 1.
Proof.
move=> Kp t tge0; have [circp _] := Kp.
rewrite -circp -[in RHS](sol0 p); apply: Logic.eq_sym.
case: (Rle_lt_or_eq_dec _ _ tge0); last by move<-.
apply: (eq_is_derive (fun s => ((sol p s)[2] ^ 2) + ((sol p s)[3] ^ 2))).
move=> s [sge0 _]; set q := sol p s.
have [_ /(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp.
rewrite -(plus_opp_l (2 * q[2] * q[3] * q[4])); apply: is_derive_plus.
  have -> :
    opp (2 * q[2] * q[3] * q[4]) = 2 * (opp (q[3] * q[4])) * (q[2] ^ 1).
    by rewrite /opp /=; ring.
  apply: is_derive_pow.
  have -> : opp (q[3] * q[4]) = (Fpendulum q)[2].
    by rewrite mxE [LHS]Ropp_mult_distr_l.
  exact: is_derive_component.
have -> : 2 * q[2] * q[3] * q[4] = 2 * (q[2] * q[4]) * (q[3] ^ 1).
  by rewrite /opp /=; ring.
apply: is_derive_pow.
have -> : q[2] * q[4] = (Fpendulum q)[3] by rewrite mxE.
exact: is_derive_component.
Qed.

Lemma is_derive_Esol p t :
  K p -> 0 <= t -> is_derive (E \o (sol p)) t ((sol p t)[1] * fctrl (sol p t)).
Proof.
move=> Kp tge0; rewrite -E'E; last exact: circ_invar.
have [_ /(_ _ tge0) solp'] := sol_is_sol sol0 solP Kp.
have : forall q, E' (sol p t) (scal q (Fpendulum (sol p t))) =
  scal q (E' (sol p t) (Fpendulum (sol p t))).
  by move=> q; rewrite linear_scal //; have [] := filterdiff_E (sol p t).
by apply: filterdiff_ext_lin; apply: filterdiff_comp' solp' (filterdiff_E _).
Qed.

Lemma derive_Vsol p t :
  K p -> 0 <= t -> ((sol p t)[2] ^ 2) + ((sol p t)[3] ^ 2) = 1 ->
  V (sol p t) < B -> is_derive (V \o (sol p)) t (- kd * ((sol p t)[1] ^ 2)).
Proof.
move=> Kp tge0 circ_solpt Vsolpt_s; rewrite -V'E => //.
have [_ /(_ _ tge0) solp'] := sol_is_sol sol0 solP Kp.
have : forall q, V' (sol p t) (scal q (Fpendulum (sol p t))) =
  scal q (V' (sol p t) (Fpendulum (sol p t))).
  move=> q; rewrite linear_scal //.
  by have [] := @filterdiff_V (locally (sol p t)) (sol p t).
apply: filterdiff_ext_lin; apply: filterdiff_comp' solp' _.
exact/filterdiff_V.
Qed.

Lemma defset_invar p : K p -> forall t, 0 <= t ->
  ((sol p t)[2] ^ 2) + ((sol p t)[3] ^ 2) = 1 /\ V (sol p t) < B.
Proof.
move=> Kp t tge0; split; first exact: circ_invar.
set A := [set t | 0 <= t /\ B <= V (sol p t)].
have glbA := Glb_Rbar_correct A.
suff t_ltA : Rbar_lt t (Glb_Rbar A).
  apply: Rnot_le_lt => Vsolpt_ns; apply: Rbar_lt_not_le t_ltA _.
  exact: (proj1 glbA).
have : Glb_Rbar A <> m_infty.
  move=> glbA_minfty; rewrite glbA_minfty in glbA.
  have : Rbar_le 0 m_infty by apply: (proj2 glbA) => ? [].
  exact: Rbar_lt_not_le.
move: glbA; case: (Glb_Rbar A) => //= s s_glbA _; exfalso=> {t tge0}.
have sge0 : Rbar_le 0 s by apply: (proj2 s_glbA) => ? [].
have Vsolp_diff t : 0 <= t -> ex_filterdiff (V \o (sol p)) (locally t).
  move=> tge0; have solp_difft : ex_filterdiff (sol p) (locally t).
    exists (scal^~ (Fpendulum (sol p t))).
    by have [_ /(_ _ tge0)] := sol_is_sol sol0 solP Kp.
  apply: ex_filterdiff_comp => //; exists (V' (sol p t)); apply: filterdiff_V.
  exact: filterdiff_continuous.
have Vsolps_geB : B <= V (sol p s).
  case: (Rle_lt_dec B (V (sol p s))) => // Vsolps_ltB; exfalso.
  have BmVsolps_gt0 : 0 < B - V (sol p s) by apply: Rlt_Rminus.
  have Vsolp_conts : continuous (V \o (sol p)) s.
    by apply/filterdiff_continuous/Vsolp_diff.
  have /Vsolp_conts := locally_ball (V (sol p s)) (mkposreal _ BmVsolps_gt0).
  move=> [e /= se_Vsolp].
  have : Rbar_le (s + e / 2) s.
    apply: (proj2 s_glbA) => r [rge0 Vsolpr_ns]; apply: Rnot_lt_le => rlt_sphe.
    have sler : Rbar_le s r by apply: (proj1 s_glbA).
    have /se_Vsolp /Rabs_def2 [Vsolpr_s _] : ball s e r.
      apply: Rabs_def1; last first.
        have /Rminus_le_0 := sler; apply: Rlt_le_trans.
        exact/Ropp_lt_gt_0_contravar/Rlt_gt.
      have :  e / 2 <= e.
        apply/Rle_div_l; first exact/Rlt_gt/Rlt_0_2.
        rewrite -[X in X <= _]Rmult_1_r.
        by apply: Rmult_le_compat_l; [apply/Rlt_le|apply/Rlt_le/Rlt_n_Sn].
      by apply/Rlt_le_trans/Rlt_minus_l; rewrite Rplus_comm.
    by apply: Rlt_not_le Vsolpr_ns; apply: Rplus_lt_reg_r Vsolpr_s.
  apply/Rlt_not_le.
  rewrite Rplus_comm; apply/Rlt_minus_l; rewrite Rminus_eq_0.
  by apply/Rdiv_lt_0_compat; [|apply: Rlt_0_2].
have sgt0 : 0 < s.
  have /Rle_lt_or_eq_dec := sge0; case=> // seq0; exfalso.
  apply: Rlt_not_le Vsolps_geB; rewrite -seq0 sol0.
  exact: Rle_lt_trans (proj2 Kp) p0_valid.
have Vsol_derive : forall t, Rmin 0 s < t < Rmax 0 s ->
  is_derive (V \o (sol p)) t (- kd * ((sol p t)[1] ^ 2)).
  move=> t; rewrite Rmin_left => //; rewrite Rmax_right => // - [tgt0 tlts].
  apply: derive_Vsol => //; first exact: Rlt_le.
    by apply: circ_invar => //; apply: Rlt_le.
  apply: Rnot_le_lt => Vsolpt_ns; suff /Rlt_not_le : Rbar_le s t by apply.
  by apply: (proj1 s_glbA); split => //; apply: Rlt_le.
have : forall t, Rmin 0 s <= t <= Rmax 0 s -> continuity_pt (V \o (sol p)) t.
  move=> t; rewrite Rmin_left => //; rewrite Rmax_right => // - [tge0 tles].
  exact/continuity_pt_filterlim/filterdiff_continuous/Vsolp_diff.
move=> /(MVT_gen _ _ _ _ Vsol_derive) [t []].
rewrite Rmin_left => //; rewrite Rmax_right => // - [tge0 tles].
rewrite /funcomp sol0 Rminus_0_r; move/(Rmult_eq_compat_r (/ s)).
rewrite Rinv_r_simpl_l=> [VsolpsVpds|]; last exact/not_eq_sym/Rlt_not_eq.
have : (V (sol p s) - V p) / s <= 0.
  rewrite /Rdiv VsolpsVpds -Ropp_mult_distr_l.
  apply/Rge_le/Ropp_0_le_ge_contravar; apply: Rmult_le_pos (pow2_ge_0 _).
  exact/Rlt_le.
apply/Rlt_not_le/Rdiv_lt_0_compat => //.
apply: Rlt_Rminus; apply: Rlt_le_trans Vsolps_geB.
exact: Rle_lt_trans (proj2 Kp) p0_valid.
Qed.

Lemma is_derive_Vsol p t :
  K p -> 0 <= t -> is_derive (V \o (sol p)) t (- kd * ((sol p t)[1] ^ 2)).
Proof.
move=> Kp tge0; have [circpt Vpts] := defset_invar Kp tge0.
exact: derive_Vsol.
Qed.

Lemma Kinvar : is_invariant sol K.
Proof.
move=> p Kp t tge0; have [_ Vp_s] := Kp; split; first exact: circ_invar.
apply: Rle_trans Vp_s; rewrite -[X in _ <= V X]sol0.
have Vderiv : forall s, Rbar_le 0 s -> Rbar_le s t ->
  is_derive (V \o (sol p)) s (- kd * ((sol p s)[1] ^ 2)).
  by case => // s sge0 slet; apply: is_derive_Vsol.
apply: (nincr_function_le Vderiv _ _ tge0); try exact: Rle_refl.
move=> ? _ _; apply: Rmult_le_0_r; last exact: pow2_ge_0.
by rewrite -Ropp_0; apply/Ropp_le_contravar/Rlt_le.
Qed.

Definition homoclinic_orbit : set (vect_UniformSpace R_UniformSpace 5) :=
  [set p : U | p[0] = 0 /\ p[1] = 0 /\ E p = 0].

Lemma limSKinvar : is_invariant sol (limS sol K).
Proof.
move=> p limSKp t tge0.
exact: (@invariant_limS _ _ _ Kco _ sol0 solP sol_cont Kinvar).
Qed.

Lemma subset_limSK_K : limS sol K `<=` K.
Proof.
move=> p [q Kq solq_top].
apply: compact_closed (@vect_hausdorff _ 5 Rhausdorff) Kco _ _.
suff solqK : (sol q @ +oo) K.
  by move=> A /solq_top - /(_ _ solqK) [r []]; exists r.
by exists 0 => ? /Rlt_le; apply: Kinvar.
Qed.

Lemma Vsol_derive p t : K p -> 0 <= t ->
  is_derive (V \o sol p) t ((V' (sol p t) \o Fpendulum) (sol p t)).
Proof.
move=> Kp tge0; have Ksolpt : K (sol p t) by apply: Kinvar.
apply: filterdiff_ext_lin.
  apply: filterdiff_comp'.
    by have [_] := sol_is_sol sol0 solP Kp; apply.
  by apply: filterdiff_V => ?; apply.
move=> u; rewrite linear_scal //.
by have [] := @filterdiff_V (locally (sol p t)) _ _ (fun _ a => a).
Qed.

Lemma Vsol'_eq0 p t :
  limS sol K p -> 0 <= t -> (V' (sol p t) \o Fpendulum) (sol p t) = 0.
Proof.
move=> limSKp tge0; have limSKsolp : limS sol K (sol p t) by apply: limSKinvar.
apply: (@stable_limS _ _ _ Kco _ sol0 solP sol_cont Kinvar V);
  last exact: limSKsolp.
  by move=> ??; apply: filterdiff_V.
move=> r [circr Vrs]; rewrite /funcomp V'E //;
  last exact: Rle_lt_trans p0_valid.
rewrite -Ropp_mult_distr_l -Ropp_0; apply: Ropp_le_contravar.
by apply: Rmult_le_pos; [apply: Rlt_le|apply: pow2_ge_0].
Qed.

Lemma sol1_eq0 p t : limS sol K p -> 0 <= t -> (sol p t)[1] = 0.
Proof.
move=> limSKp tge0; suff : - kd * ((sol p t)[1] ^ 2) = 0.
  move=> /Rmult_integral; apply: or_ind.
    by move=> / RMicromega.Ropp_0 kd0; exfalso; apply: (Rgt_not_eq kd 0) kd0.
  by rewrite /= Rmult_1_r => /Rmult_integral; apply: or_ind.
have /subset_limSK_K Kp := limSKp.
rewrite -[LHS](is_derive_unique (V \o sol p) t); last first.
  exact: is_derive_Vsol tge0.
by rewrite -[RHS](Vsol'_eq0 limSKp tge0); apply/is_derive_unique/Vsol_derive.
Qed.

Lemma sol1'_eq0 p t : limS sol K p -> 0 <= t -> (Fpendulum (sol p t))[1] = 0.
Proof.
move=> limSKp tge0; have /subset_limSK_K Kp := limSKp.
have [_ /(_ _ tge0)] := sol_is_sol sol0 solP Kp.
move=> /(is_derive_component 1%:R) /is_derive_unique <-.
by rewrite (derive_ext_ge0 tge0 (fun s sge0 => @sol1_eq0 _ _ limSKp sge0))
  Derive_const.
Qed.

Lemma sol0_const p t : limS sol K p -> 0 <= t -> (sol p t)[0] = p[0].
Proof.
move=> limSKp tge0; rewrite -[p in RHS]sol0.
apply/Logic.eq_sym; case: (Rle_lt_or_eq_dec _ _ tge0) => [|->] //.
apply: (eq_is_derive (fun s => (sol p s)[0])) => s [sge0 _].
rewrite -[zero](sol1_eq0 limSKp sge0).
have /subset_limSK_K Kp := limSKp.
have [_ /(_ _ sge0) /(is_derive_component (0%:R))] := sol_is_sol sol0 solP Kp.
by rewrite !mxE.
Qed.

Lemma Esol_const p t : limS sol K p -> 0 <= t -> (E \o sol p) t = E p.
Proof.
move=> limSKp tge0; rewrite -[p in RHS]sol0.
apply/Logic.eq_sym; case: (Rle_lt_or_eq_dec _ _ tge0) => [|->] //.
apply: (eq_is_derive (E \o sol p)) => s [sge0 _].
have -> : zero = (sol p s)[1] * (fctrl (sol p s)).
  by rewrite sol1_eq0 ?Rmult_0_l.
by apply: is_derive_Esol sge0; apply: subset_limSK_K.
Qed.

Lemma Efctrl_psol0_eq0 p t : limS sol K p -> 0 <= t ->
  ke * (E (sol p t)) * (fctrl (sol p t)) + kx * (sol p t)[0] = 0.
Proof.
move=> limSKp tge0.
have -> : 0 = - (kd * (sol p t)[1] + kv * (Fpendulum (sol p t))[1]).
  by rewrite sol1_eq0 ?sol1'_eq0 ?Rmult_0_r ?Rplus_0_r ?Ropp_0.
rewrite /Fpendulum !mxE /= /fctrl; field.
split; last by rewrite -{2}[(sol p t)[3]]Rmult_1_r;
  apply/not_eq_sym/Rlt_not_eq/Mp_ms_gt0.
have [circsolt Vsolts] : K (sol p t).
  by apply: Kinvar tge0; apply: subset_limSK_K.
by apply: fctrl_wdef circsolt _; apply: Rle_lt_trans p0_valid.
Qed.

Lemma div_fctrl_mP p t : limS sol K p -> 0 <= t ->
  (sol p t)[3] * (g * (sol p t)[2] - l * ((sol p t)[4] ^ 2)) =
  (fctrl (sol p t)) / m.
Proof.
move=> limSKp tge0; apply/Logic.eq_sym/RMicromega.Rinv_elim.
  exact/Rinv_neq_0_compat/Rgt_not_eq.
rewrite Rinv_involutive; last exact/Rgt_not_eq.
have := sol1'_eq0 limSKp tge0; rewrite !mxE /=.
have IMp_ms_n0 : / (M + m * ((sol p t)[3] ^ 2)) <> 0.
  exact/Rinv_neq_0_compat/Rgt_not_eq/Mp_ms_gt0.
move=> /RMicromega.Rinv_elim - /(_ IMp_ms_n0).
rewrite Rmult_0_l => fctrl_val; have {fctrl_val} := Logic.eq_sym fctrl_val.
by move=> /Rplus_opp_r_uniq ->; ring.
Qed.

Lemma Fpendulum4E p t : limS sol K p -> 0 <= t ->
  (Fpendulum (sol p t))[4] = (g / l) * (sol p t)[3].
Proof.
move=> limSKp tge0; rewrite !mxE /=.
have divfm_val := div_fctrl_mP limSKp tge0.
have /RMicromega.Rinv_elim := Logic.eq_sym divfm_val.
move<-; last exact/Rinv_neq_0_compat/Rgt_not_eq.
field_simplify_eq.
  suff -> : (sol p t)[2] ^ 2 = 1 - ((sol p t)[3] ^ 2) by ring.
  suff [<- _] : K (sol p t) by ring.
  exact/subset_limSK_K/limSKinvar.
do 2 ?[split; first exact: Rgt_not_eq].
by rewrite -[X in _ [3] * X]Rmult_1_r; apply/Rgt_not_eq/Mp_ms_gt0.
Qed.

Lemma En0_fctrlsol_const p t :
  limS sol K p -> E p <> 0 -> 0 <= t -> fctrl (sol p t) = fctrl p.
Proof.
move=> limSKp Epn0 tge0.
have := Efctrl_psol0_eq0 limSKp tge0.
rewrite -(Efctrl_psol0_eq0 limSKp (Rle_refl _)) sol0
  [E (sol p t)](Esol_const limSKp tge0) (sol0_const limSKp tge0).
move=> /Rplus_eq_reg_r /Rmult_eq_reg_l; apply.
by apply: Rmult_integral_contrapositive_currified Epn0; apply/Rgt_not_eq.
Qed.

Lemma is_derive_nneg_unique (f : R -> R) t l1 l2 :
  0 <= t -> filterdiff f (within (Rle 0) (locally t)) (scal^~ l1) ->
  filterdiff f (within (Rle 0) (locally t)) (scal^~ l2) -> l1 = l2.
Proof.
move=> tge0 [_ f'tl1] [_ f'tl2].
have tt : is_filter_lim (within (Rle 0) (locally t)) t.
  by move=> A [e te_A]; exists e => ? /te_A.
have /f'tl1 {f'tl1} f'tl1 := tt; have /f'tl2 {f'tl2} f'tl2 := tt.
apply: Req_le_aux => e.
have [e1 te1f'] := f'tl1 (mkposreal _ (is_pos_div_2 e)).
have [e2 te2f'] := f'tl2 (mkposreal _ (is_pos_div_2 e)).
set s := t + (Rmin e1 e2) / 2.
have hmine12_ge0 : 0 <= (Rmin e1 e2) / 2.
  apply/Rle_div_r; first exact: Rlt_0_2.
  by rewrite Rmult_0_l; apply/Rlt_le/Rmin_pos.
have sge0 : 0 <= s by apply: Rplus_le_le_0_compat tge0 _.
have smt_val : s - t = (Rmin e1 e2) / 2 by rewrite /s; ring.
have : ball t e1 s.
  apply: Rabs_def1; rewrite [minus _ _]smt_val.
    apply/Rlt_div_l; first exact: Rlt_0_2.
    by apply: Rle_lt_trans (Rmin_l _ _) _; have := cond_pos e1; lra.
  by apply: Rlt_le_trans hmine12_ge0; have := cond_pos e1; lra.
move=> /te1f' /(_ sge0) /= hl1.
have : ball t e2 s.
  apply: Rabs_def1; rewrite [minus _ _]smt_val.
    apply/Rlt_div_l; first exact: Rlt_0_2.
    by apply: Rle_lt_trans (Rmin_r _ _) _; have := cond_pos e2; lra.
  by apply: Rlt_le_trans hmine12_ge0; have := cond_pos e2; lra.
move=> /te2f' /(_ sge0) /= hl2.
have -> : l1 - l2 =
  ((((f s) - (f t)) / (s - t)) - l2) - ((((f s) - (f t)) / (s - t)) - l1).
  by ring.
have smt_gt0 : 0 < norm (s - t).
  rewrite smt_val; apply: Rabs_pos_lt.
  apply/Rgt_not_eq/Rlt_div_r; first exact: Rlt_0_2.
  by rewrite Rmult_0_l; apply: Rmin_pos.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite [_ e]double_var; apply: Rplus_le_compat.
  move: hl2 => /(Rle_div_l _ _ _ smt_gt0).
  rewrite -Rabs_div; last first.
    by apply/Rgt_not_eq; move: smt_gt0; rewrite [norm _]Rabs_pos_eq // smt_val.
  rewrite [(minus _ _) / _]RIneq.Rdiv_minus_distr
    [(scal _ _) / _]Rinv_r_simpl_m => //.
  by apply/Rgt_not_eq; move: smt_gt0; rewrite [norm _]Rabs_pos_eq // smt_val.
move: hl1 => /(Rle_div_l _ _ _ smt_gt0).
rewrite Rabs_Ropp -Rabs_div; last first.
  by apply/Rgt_not_eq; move: smt_gt0; rewrite [norm _]Rabs_pos_eq // smt_val.
rewrite [(minus _ _) / _]RIneq.Rdiv_minus_distr
  [(scal _ _) / _]Rinv_r_simpl_m => //.
by apply/Rgt_not_eq; move: smt_gt0; rewrite [norm _]Rabs_pos_eq // smt_val.
Qed.

Lemma derive_nneg_eq (f g : R -> R) t l1 l2 :
  (forall t, 0 <= t -> f t = g t) -> 0 <= t ->
  is_derive f t l1 -> is_derive g t l2 -> l1 = l2.
Proof.
move=> feqg tge0 f'l1 g'l2.
have withinRploct_proper : ProperFilter (within (Rle 0) (locally t)).
  by apply: within_locally_proper => ? /locally_singleton; exists t.
have limt : is_filter_lim (within (Rle 0) (locally t)) t.
  by move=> A [e se_A]; exists e => ? /se_A.
apply: (@is_derive_nneg_unique f t _ _ tge0).
  exact: filterdiff_locally f'l1.
apply: (filterdiff_ext_loc g).
- by exists (mkposreal _ Rlt_0_1) => ???; rewrite feqg.
- move=> s seqt; rewrite feqg //; suff -> : s = t by [].
  have withinRploct_proper' : ProperFilter' (within (Rle 0) (locally t)).
    exact: Proper_StrongProper.
  exact: is_filter_lim_unique seqt _.
- exact: filterdiff_locally g'l2.
Qed.

Lemma cont_is_lim (f : R -> R) x : continuous f x <-> is_lim f x (f x).
Proof.
apply: iff_trans (continuity_pt_filterlim' _ _); apply: iff_sym.
exact: iff_trans (continuity_pt_filterlim _ _) _.
Qed.

Lemma bigRmin_inseq (s : seq R) x :
  List.In x s -> List.In (\big[Rmin/x]_(y <- s) y) s.
Proof.
elim: s => // y s ihs; apply: or_ind; last first.
  move=> /ihs smin; rewrite big_cons.
  by apply: (Rmin_case _ _ (List.In (A:=R)^~ _)); [left|right].
move=> {ihs y} ->; rewrite big_cons.
elim: s => [|y s ihs].
  by rewrite big_nil Rmin_left; [left|apply: Rle_refl].
rewrite big_cons Rmin_assoc [X in Rmin X _]Rmin_comm -Rmin_assoc.
apply: (Rmin_case _ _ (List.In (A:=R)^~ _)); first by right; left.
by apply: or_ind ihs => [<-|ihs]; [left|right;right].
Qed.

Lemma bigRmin_extract (s : seq R) x y :
  List.In y s -> \big[Rmin/x]_(z <- s) z = Rmin y (\big[Rmin/x]_(z <- s) z).
Proof.
elim: s => // z s ihs; rewrite !big_cons; apply: or_ind => [<-|sy].
  by rewrite Rmin_assoc (Rmin_left _ _ (Rle_refl _)).
by rewrite Rmin_assoc [Rmin y z]Rmin_comm -Rmin_assoc -ihs.
Qed.

Lemma glb_finset (A : set R) x l :
  finite_set A -> A x -> is_glb_Rbar A l -> A l.
Proof.
move=> [s Aes] /Aes sx glbl; apply/Aes.
suff [? [? ->]] : exists y, List.In y s /\ l = y by [].
apply: NNPP => /not_ex_all_not nsl.
have smin : List.In (\big[Rmin/x]_(y <- s) y) s by apply/bigRmin_inseq.
have llemin : Rbar_le l (\big[Rmin/x]_(y <- s) y) by apply/(proj1 glbl)/Aes.
apply: (nsl (\big[Rmin/x]_(y <- s) y)); split => //.
apply: Rbar_le_antisym llemin _.
apply: (proj2 glbl) => y /Aes sy; rewrite (bigRmin_extract _ sy).
exact: Rmin_l.
Qed.

Lemma cont_finimage_const (f : R -> R) n (g : 'I_n -> R) :
  (forall t, 0 <= t -> continuous f t) ->
  (forall t, 0 <= t -> exists i, f t = g i) ->
  forall t, 0 <= t -> f t = f 0.
Proof.
case: n g => [g ? finim_f t tge0|]; first by have /finim_f [] := tge0; case.
case=> [|n] g fcont finim_f t tge0.
  have /finim_f [i ->] := tge0; have /finim_f [j ->] := Rle_refl 0.
  by rewrite !ord1.
case: (Req_dec (f t) (f 0)) => // ft_ne_f0; exfalso.
case/Rle_lt_or_eq_dec: tge0 => [tgt0|t0]; last by apply: ft_ne_f0; rewrite t0.
case/Rdichotomy: ft_ne_f0 => [ft_lt_f0|/Rgt_lt f0_lt_ft].
  have gtft_img_f0 : ((Rlt (f t)) `&` (g @` setT)) (f 0).
    by split=> //; have /finim_f [i] := Rle_refl 0; exists i.
  have /lb_finglb : (Rlt (f t)) `&` (g @` setT) !=set0 by exists (f 0).
  case=> [|l glbl]; first by exists (f t) => ? [].
  set y := ((f t) + l) / 2.
  have [ftltl _] : ((Rlt (f t)) `&` (g @` setT)) l.
    apply: glb_finset gtft_img_f0 glbl.
    apply: sub_finite_set (@subsetIr _ _ _) _.
    exists (List.map g (index_enum (ordinal_finType n.+2))) => x.
    split=> [[i _ <-]|].
      apply/List.in_map_iff; exists i; split=> //.
      exact/Iter.In_mem/mem_index_enum.
    elim: (index_enum (ordinal_finType n.+2))=> // i s ihs.
    by apply: or_ind; [move<-; exists i|move=> /ihs].
  case: (IVT_Rbar_decr f 0 t (f 0) (f t) y).
  - exact/cont_is_lim/fcont/Rle_refl.
  - exact/cont_is_lim/fcont/Rlt_le.
  - by move=> x /Rlt_le xge0 _; apply/continuity_pt_filterlim/fcont.
  - by [].
  - split=> //; rewrite /y /=; first by lra.
    suff : l <= f 0 by lra.
    apply: (proj1 glbl); split=> //; have /finim_f [i ?] := Rle_refl 0.
    by exists i.
  - move=> x [/Rlt_le xge0 [xltt fxey]].
    have /finim_f [i] := xge0; rewrite fxey => yegi.
    have : Rbar_le l y.
      by apply: (proj1 glbl); split; [rewrite /y; lra|exists i].
    by apply: Rlt_not_le; rewrite /y; lra.
have gtf0_img_ft : ((Rlt (f 0)) `&` (g @` setT)) (f t).
  by split=> //; have /Rlt_le /finim_f [i] := tgt0; exists i.
have /lb_finglb : (Rlt (f 0)) `&` (g @` setT) !=set0 by exists (f t).
case=> [|l glbl]; first by exists (f 0) => ? [].
set y := ((f 0) + l) / 2.
have [f0ltl _] : ((Rlt (f 0)) `&` (g @` setT)) l.
  apply: glb_finset gtf0_img_ft glbl.
  apply: sub_finite_set (@subsetIr _ _ _) _.
  exists (List.map g (index_enum (ordinal_finType n.+2))) => x.
  split=> [[i _ <-]|].
    apply/List.in_map_iff; exists i; split=> //.
    exact/Iter.In_mem/mem_index_enum.
  elim: (index_enum (ordinal_finType n.+2))=> // i s ihs.
  by apply: or_ind; [move<-; exists i|move=> /ihs].
case: (IVT_Rbar_incr f 0 t (f 0) (f t) y).
- exact/cont_is_lim/fcont/Rle_refl.
- exact/cont_is_lim/fcont/Rlt_le.
- by move=> x /Rlt_le xge0 _; apply/continuity_pt_filterlim/fcont.
- by [].
- split=> //; rewrite /y /=; first by lra.
  suff : l <= f t by lra.
  apply: (proj1 glbl); split=> //; have /Rlt_le /finim_f [i ?] := tgt0.
  by exists i.
- move=> x [/Rlt_le xge0 [xltt fxey]].
  have /finim_f [i] := xge0; rewrite fxey => yegi.
  have : Rbar_le l y.
    by apply: (proj1 glbl); split; [rewrite /y; lra|exists i].
  by apply: Rlt_not_le; rewrite /y; lra.
Qed.

Lemma poly2_factor a b c x :
  a <> 0 -> a * (x ^ 2) + b * x + c = 0 ->
  x = (- b + sqrt ((b ^ 2) - 4 * a * c)) / (2 * a) \/
  x = (- b - sqrt ((b ^ 2) - 4 * a * c)) / (2 * a).
Proof.
move=> ane0 xroot.
set dlt := (b ^ 2) - 4 * a * c.
set x1 := (- b + sqrt dlt) / (2 * a).
set x2 := (- b - sqrt dlt) / (2 * a).
suff poly_fact : a * (x ^ 2) + b * x + c = a * (x - x1) * (x - x2).
  move: xroot; rewrite poly_fact.
  case/Rmult_integral; last by move/Rminus_diag_uniq; right.
  by case/Rmult_integral=> //; move/Rminus_diag_uniq; left.
rewrite /x1 /x2; case: (Rle_or_lt 0 dlt) => [dltge0|dltlt0].
  field_simplify_eq => //=; rewrite [in sqrt _ * _]Rmult_1_r sqrt_sqrt // /dlt.
  by ring.
exfalso; move: xroot.
have -> : a * (x ^ 2) + b * x + c =
  a * ((x + b / (2 * a)) ^ 2) + (c - (b ^ 2) / (4 * a)).
  by field.
have := ane0; case/Rdichotomy => [alt0|/Rgt_lt agt0]; last first.
  apply: tech_Rplus; first by apply: Rmult_le_pos (pow2_ge_0 _); apply: Rlt_le.
  by apply/Rlt_Rminus/Rlt_div_l; [|move: dltlt0; rewrite /dlt]; lra.
move/Ropp_eq_0_compat; rewrite Ropp_plus_distr; apply: tech_Rplus.
  apply/Ropp_0_ge_le_contravar/Rle_ge/Rmult_le_0_r; first exact: Rlt_le.
  exact: pow2_ge_0.
rewrite Ropp_plus_distr.
have -> : - ((b ^ 2) / (4 * a)) = (b ^ 2) / (- 4 * a) by field.
by apply/Rlt_Rminus/Rlt_div_l; [|move: dltlt0; rewrite /dlt]; lra.
Qed.

Lemma En0_sol2_const p :
  limS sol K p -> E p <> 0 -> forall t, 0 <= t -> (sol p t)[2] = p[2].
Proof.
move=> limSKp Epn0 t tge0.
have Kp : K p by apply: subset_limSK_K.
set C1 := - (2 * g + ((2 * (E p))/ (m * l))); set C2 := (fctrl p) / m.
have sol32_val : forall s, 0 <= s ->
  (sol p s)[3] * (3 * g * (sol p s)[2] + C1) = C2.
  move=> s sge0.
  rewrite /C1 /C2 -(Esol_const limSKp sge0) /E /= (sol1_eq0 limSKp sge0)
    -(En0_fctrlsol_const limSKp Epn0 sge0) -(div_fctrl_mP limSKp sge0).
  by field; split; apply: Rgt_not_eq.
have sol423_val s : 0 <= s ->
  (sol p s)[4] * (3 * g * (((sol p s)[2] ^ 2) - ((sol p s)[3] ^ 2)) +
    C1 * (sol p s)[2]) = 0.
  move=> sge0; apply: (derive_nneg_eq sol32_val sge0); last first.
    exact: is_derive_const.
  have -> : (sol p s)[4] * (3 * g * (((sol p s)[2] ^ 2) -
    ((sol p s)[3] ^ 2)) + C1 * (sol p s)[2]) =
    (Fpendulum (sol p s))[3] * (3 * g * (sol p s)[2] + C1) +
    (sol p s)[3] * (3 * g * (Fpendulum (sol p s))[2] + 0).
    by rewrite /Fpendulum !mxE /=; ring.
  have [_/(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp.
  apply: is_derive_mult; first exact: is_derive_component.
  apply: is_derive_plus; last exact: is_derive_const.
  exact/is_derive_scal/is_derive_component.
have sol432_val' s : 0 <= s ->
  (sol p s)[3] * ((g / l) * (3 * g * (((sol p s)[2] ^ 2) -
    ((sol p s)[3] ^ 2)) + C1 * (sol p s)[2]) -
    ((sol p s)[4] ^ 2) * (12 * g * (sol p s)[2] + C1)) = 0.
  move=> sge0; apply: (derive_nneg_eq sol423_val sge0); last first.
    exact: is_derive_const.
  have -> : (sol p s)[3] * ((g / l) * (3 * g * (((sol p s)[2] ^ 2) -
    ((sol p s)[3] ^ 2)) + C1 * (sol p s)[2]) -
    ((sol p s)[4] ^ 2) * (12 * g * (sol p s)[2] + C1)) =
    (Fpendulum (sol p s))[4] * (3 * g * (((sol p s)[2] ^ 2) -
    ((sol p s)[3] ^ 2)) + C1 * (sol p s)[2]) +
    (sol p s)[4] * (3 * g *
    (2 * (Fpendulum (sol p s))[2] * ((sol p s)[2] ^ 2.-1) -
    2 * (Fpendulum (sol p s))[3] * ((sol p s)[3] ^ 2.-1)) +
    C1 * (Fpendulum (sol p s))[2]).
    by rewrite Fpendulum4E // !mxE /=; field; apply: Rgt_not_eq.
  have [_/(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp.
  apply: is_derive_mult; first exact: is_derive_component.
  apply: is_derive_plus; last exact/is_derive_scal/is_derive_component.
  apply/is_derive_scal/is_derive_plus.
    exact/is_derive_pow/is_derive_component.
  exact/is_derive_opp/is_derive_pow/is_derive_component.
set x1 := (- C1 + sqrt ((C1 ^ 2) - 4 * (6 * g) * (- 3 * g))) / (2 * (6 * g)).
set x2 := (- C1 - sqrt ((C1 ^ 2) - 4 * (6 * g) * (- 3 * g))) / (2 * (6 * g)).
set f := fun i : 'I_4 => if i == ord0 then - 1 else
                           if i == 1%:R then 1 else
                             if i == 2%:R then x1 else x2.
rewrite -[p in RHS]sol0.
apply: (@cont_finimage_const (fun s => (sol p s)[2]) _ f) tge0.
  move=> s sge0; apply: filterdiff_continuous.
  exists (scal^~ ((Fpendulum (sol p s))[2])); apply: is_derive_component.
  by have [_ /(_ _ sge0)] := sol_is_sol sol0 solP Kp.
move=> s sge0.
have circsol : ((sol p s)[2] ^ 2) + ((sol p s)[3] ^ 2) = 1.
  suff [] : K (sol p s) by [].
  exact/subset_limSK_K/limSKinvar.
have solroot_imf :
  3 * g * (((sol p s)[2] ^ 2) - ((sol p s)[3] ^ 2)) + C1 * (sol p s)[2] = 0 ->
  exists i, (sol p s)[2] = f i.
  have -> : (sol p s)[3] ^ 2 = 1 - ((sol p s)[2] ^ 2) by rewrite -circsol; ring.
  move=> sol2_val.
  have sol2_root :
    6 * g * ((sol p s)[2] ^ 2) + C1 * (sol p s)[2] + (- 3 * g) = 0.
    by rewrite -sol2_val; ring.
  case/poly2_factor: sol2_root => {sol2_val} [|sol2_val|sol2_val].
  - by apply: Rmult_integral_contrapositive_currified; [|have := cond_pos g];
    lra.
  - by exists (2%:R); rewrite sol2_val.
  - by exists (3%:R); rewrite sol2_val.
case: (Req_dec ((sol p s)[4]) 0) => [sol4e0|sol4ne0]; last first.
  by have /sol423_val /Rmult_integral := sge0; apply: or_ind.
have /sol432_val' := sge0.
rewrite sol4e0 [0 ^ 2]Rmult_0_l Rmult_0_l Rminus_0_r.
case: (Req_dec ((sol p s)[3]) 0) => [sol3e0|sol3ne0].
  move=> _; move: circsol; rewrite sol3e0 [0 ^ 2]Rmult_0_l Rplus_0_r.
  rewrite -Rsqr_pow2 -Rsqr_1 => /Rsqr_eq.
  by apply: or_ind => ->; [exists (1%:R)|exists ord0].
move/Rmult_integral; apply: or_ind => // /Rmult_integral; apply: or_ind => //.
move=> /Rmult_integral gdivl0; exfalso; move: gdivl0; apply: or_ind.
  exact: Rgt_not_eq.
exact/Rinv_neq_0_compat/Rgt_not_eq.
Qed.

Lemma En0_sol3_const p :
  limS sol K p -> E p <> 0 -> forall t, 0 <= t -> (sol p t)[3] = p[3].
Proof.
move=> limSKp Epn0 t tge0.
have circsol s : 0 <= s -> (p[2] ^ 2) + ((sol p s)[3] ^ 2) = 1.
  move=> sge0; rewrite -(En0_sol2_const limSKp Epn0 sge0).
  suff [] : K (sol p s) by [].
  exact/subset_limSK_K/limSKinvar.
set g := fun i : 'I_2 => if i == ord0 then sqrt (1 - (p[2] ^ 2))
                                      else - (sqrt (1 - (p[2] ^ 2))).
rewrite -[p in RHS]sol0.
apply: (@cont_finimage_const (fun t => (sol p t)[3]) _ g) tge0.
  move=> s sge0; apply: filterdiff_continuous.
  exists (scal^~ ((Fpendulum (sol p s))[3])); apply: is_derive_component.
  have Kp : K p by apply: subset_limSK_K.
  by have [_ /(_ _ sge0)] := sol_is_sol sol0 solP Kp.
move=> s sge0.
have /Rsqr_eq : Rsqr ((sol p s)[3]) = Rsqr (sqrt (1 - (p[2] ^ 2))).
  have /circsol <- := sge0.
  ring_simplify (p[2] ^ 2 + (sol p s)[3] ^ 2 - p[2] ^ 2).
  by rewrite Rsqr_sqrt ?Rsqr_pow2 //; apply: pow2_ge_0.
by apply: or_ind => [sols3eg0|sols3eg1]; [exists ord0|exists 1%:R].
Qed.

Lemma En0_sol4_eq0 p :
  limS sol K p -> E p <> 0 -> forall t, 0 <= t -> (sol p t)[4] = 0.
Proof.
move=> limSKp Epn0 t tge0.
have Kp : K p by apply: subset_limSK_K.
have [_ /(_ _ tge0) sol't] := sol_is_sol sol0 solP Kp.
have /Rmult_integral : (sol p t)[3] * (sol p t)[4] = 0.
  apply: RMicromega.Ropp_0; rewrite Ropp_mult_distr_l.
  apply: (derive_nneg_eq (En0_sol2_const limSKp Epn0) tge0); last first.
    exact: is_derive_const.
  have -> : - (sol p t)[3] * (sol p t)[4] = (Fpendulum (sol p t))[2].
    by rewrite mxE.
  exact: is_derive_component.
apply: or_ind => // sol3eq0.
have /Rmult_integral : (sol p t)[2] * (sol p t)[4] = 0.
  apply: (derive_nneg_eq (En0_sol3_const limSKp Epn0) tge0); last first.
    exact: is_derive_const.
  have -> : (sol p t)[2] * (sol p t)[4] = (Fpendulum (sol p t))[3].
    by rewrite mxE.
  exact: is_derive_component.
apply: or_ind => // sol2eq0; exfalso.
have [] : K (sol p t) by apply/Kinvar.
rewrite sol3eq0 sol2eq0 ![_ ^ 2]Rmult_0_l Rplus_0_l => eq01 _.
exact: R1_neq_R0.
Qed.

Lemma En0_sol3_eq0 p t :
  limS sol K p -> E p <> 0 -> 0 <= t -> (sol p t)[3] = 0.
Proof.
move=> limSKp Epn0 tge0; rewrite En0_sol3_const => //.
apply: or_ind (Req_dec (p[3]) 0) => // p3n0; exfalso; apply: p3n0.
have : (Fpendulum (sol p 0))[4] = 0.
  apply: (derive_nneg_eq (En0_sol4_eq0 limSKp Epn0) (Rle_refl 0)); last first.
    exact: is_derive_const.
  have Kp : K p by apply: subset_limSK_K.
  have [_ /(_ _ (Rle_refl 0))] := sol_is_sol sol0 solP Kp.
  exact: is_derive_component.
rewrite Fpendulum4E //; last exact: Rle_refl.
rewrite sol0 => /Rmult_integral; apply: or_ind => // g0; exfalso.
apply: Rmult_integral_contrapositive g0; split; first exact: Rgt_not_eq.
exact/Rinv_neq_0_compat/Rgt_not_eq.
Qed.

Lemma En0_sol2_eq1 p t :
  limS sol K p -> E p <> 0 -> 0 <= t -> (sol p t)[2] = 1.
Proof.
move=> limSKp Epn0 tge0.
have [] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
rewrite En0_sol3_eq0 // [0 ^ _]Rmult_0_l Rplus_0_r -Rsqr_pow2 -{1}Rsqr_1.
case/Rsqr_eq => // sol2_eqm1 _; exfalso.
suff : Rabs (E (sol p t)) < 2 * m * g * l.
  rewrite /E sol1_eq0 // En0_sol4_eq0 // [0 ^ _]Rmult_0_l !Rmult_0_r !Rplus_0_r
          Rmult_0_r Rplus_0_l sol2_eqm1.
  by move=> /Rabs_def2 [_]; apply: Rle_not_lt; lra.
rewrite -[X in _ < X]Rabs_pos_eq; last first.
  by do 3 ?[apply: Rmult_le_pos; last exact: Rlt_le]; apply/Rlt_le/Rlt_0_2.
apply: Rsqr_lt_abs_0; rewrite !Rsqr_pow2.
have gt20 : 2 > 0 by apply/Rlt_gt/Rlt_0_2.
have : 2 * (V (sol p t)) / ke < (2 * m * g * l) ^ 2.
  apply/Rlt_div_l => //; rewrite Rmult_comm; apply/Rlt_div_r => //.
  have Vsolp_s : V (sol p t) < B.
    have [_ Vsolp_s] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
    exact: Rle_lt_trans p0_valid.
  apply: Rlt_le_trans Vsolp_s _.
  rewrite /B Rmult_comm ![_ * _ / _]Rmult_assoc; apply/Rmult_le_compat_r.
    by apply: Rdiv_le_0_compat; [apply: Rlt_le|apply: Rgt_lt].
  apply: pow_incr; split; last exact: Rmin_r.
  apply: Rmin_glb.
    apply: Rdiv_le_0_compat; first exact: Rlt_le.
    by apply: Rmult_lt_0_compat => //; apply: Rplus_lt_0_compat.
  by do 3 ?[apply: Rmult_le_pos; last exact: Rlt_le]; apply: Rlt_le.
apply: Rle_lt_trans; apply/(Rle_div_r (_ ^ 2)) => //.
rewrite [X in _ <= X]Rmult_comm; apply/Rle_div_l; first exact/Rlt_gt/Rlt_0_2.
rewrite [(_ ^ 2) * _ / _]Rmult_assoc Rmult_comm /V Rplus_assoc Rplus_comm.
apply/Rle_minus_l; rewrite Rminus_eq_0.
by apply: Rplus_le_le_0_compat; apply: Rmult_le_pos; try exact: pow2_ge_0;
  apply: Rdiv_le_0_compat; try exact: Rlt_0_2; apply/Rlt_le.
Qed.

Lemma subset_limSK_homoclinic_orbit : limS sol K `<=` homoclinic_orbit.
Proof.
move=> p limSKp.
case: (Req_dec (E p) 0) => [Ep0|Epn0].
  have := sol1_eq0 limSKp (Rle_refl _); rewrite sol0 => p10.
  have := Efctrl_psol0_eq0 limSKp (Rle_refl _).
  rewrite sol0 Ep0 Rmult_0_r Rmult_0_l Rplus_0_l => /Rmult_integral.
  by apply: or_ind => // kx0; exfalso; apply: Rgt_not_eq kx0.
exfalso; apply Epn0; have le00 := Rle_refl 0.
by rewrite /E -[p]sol0 sol1_eq0 // En0_sol4_eq0 // En0_sol2_eq1 //; ring.
Qed.

Lemma cvg_to_homoclinic_orbit p : K p -> sol p @ +oo --> homoclinic_orbit.
Proof.
move=> Kp; apply: cvg_to_superset subset_limSK_homoclinic_orbit _.
exact: cvg_to_limS Kco Kinvar _ Kp.
Qed.

End System.