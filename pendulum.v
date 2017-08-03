Require Import Reals.
From mathcomp Require Import ssreflect ssrfun eqtype ssrbool ssrnat bigop ssralg
  matrix fintype zmodp seq.
Require Import lasalle tychonoff coquelicotComplements vect.
From Coquelicot Require Import Hierarchy Rcomplements Continuity Rbar Derive
  Lub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma is_derive_Vsol p t :
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
  apply: is_derive_Vsol => //; first exact: Rlt_le.
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

Lemma Kinvar : is_invariant sol K.
Proof.
move=> p Kp t tge0; have [_ Vp_s] := Kp; split; first exact: circ_invar.
apply: Rle_trans Vp_s; rewrite -[X in _ <= V X]sol0.
have Vderiv : forall s, Rbar_le 0 s -> Rbar_le s t ->
  is_derive (V \o (sol p)) s (- kd * ((sol p s)[1] ^ 2)).
  case => // s sge0 slet; have [circ_solps Vsolps_s] := defset_invar Kp sge0.
  exact: is_derive_Vsol.
apply: (nincr_function_le Vderiv _ _ tge0); try exact: Rle_refl.
move=> ? _ _; apply: Rmult_le_0_r; last exact: pow2_ge_0.
by rewrite -Ropp_0; apply/Ropp_le_contravar/Rlt_le.
Qed.

End System.