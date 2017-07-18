Require Import Reals.
From Coquelicot Require Import Hierarchy Rcomplements Continuity Rbar Derive.
From mathcomp Require Import ssreflect ssrfun eqtype ssrbool ssrnat bigop ssralg
  matrix fintype zmodp seq.
Require Import lasalle coquelicotComplements vect.

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

Lemma is_filter_lim_locally (T : UniformSpace) (p : T) :
  is_filter_lim (locally p) p.
Proof. by []. Qed.

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

Lemma filterdiff_V (p : U) : filterdiff V (locally p) (V' p).
Proof.
do 2 ?[apply: filterdiff_plus_fct; last
  by apply: filterdiff_scal_r_fct Rmult_comm _;
    apply: filterdiff_pow_component].
apply: filterdiff_scal_r_fct Rmult_comm _.
apply filterdiff_pow_fct => //; [exact: locally_filter|exact: filterdiff_E|].
by apply: filterdiff_continuous; exists (E' p); apply: filterdiff_E.
Qed.

Variable p0 : U.
(* restriction to make fctrl smooth *)
Hypothesis p0_valid :
  V p0 < ke * ((Rmin (kv / (ke * (M + m))) (2 * m * g * l)) ^ 2) / 2.

Definition K : set U :=
  [set p : U | (p[2] ^ 2) + (p[3] ^ 2) = 1 /\ V p <= V p0].

Hint Resolve cond_pos.

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

Lemma E_small p : K p -> Rabs (E p) < kv / (ke * (M + m)).
Proof.
move=> [_ Vps]; rewrite -[X in _ < X]Rabs_pos_eq; last first.
  apply: Rdiv_le_0_compat; first exact/Rlt_le.
  by apply: Rmult_lt_0_compat => //; apply: Rplus_lt_0_compat.
apply: Rsqr_lt_abs_0; rewrite !Rsqr_pow2.
have gt20 : 2 > 0 by apply/Rlt_gt/Rlt_0_2.
have : 2 * (V p0) / ke < (kv / (ke * (M + m))) ^ 2.
  apply/Rlt_div_l => //; rewrite Rmult_comm; apply/Rlt_div_r => //.
  apply: Rlt_le_trans p0_valid _; rewrite Rmult_comm ![_ * _ / _]Rmult_assoc.
  apply/Rmult_le_compat_r.
    by apply: Rdiv_le_0_compat; [apply: Rlt_le|apply: Rgt_lt].
  apply: pow_incr; split; last exact: Rmin_l.
  apply: Rmin_glb.
    apply: Rdiv_le_0_compat; first exact: Rlt_le.
    by apply: Rmult_lt_0_compat => //; apply: Rplus_lt_0_compat.
  by do 3 ?[apply: Rmult_le_pos; last exact: Rlt_le]; apply: Rlt_le.
apply: Rle_lt_trans; apply/(Rle_div_r (_ ^ 2)) => //.
rewrite [X in _ <= X]Rmult_comm; apply/Rle_div_l; first exact/Rlt_gt/Rlt_0_2.
apply: Rle_trans Vps.
rewrite [(_ ^ 2) * _ / _]Rmult_assoc Rmult_comm /V Rplus_assoc Rplus_comm.
apply/Rle_minus_l; rewrite Rminus_eq_0.
by apply: Rplus_le_le_0_compat; apply: Rmult_le_pos; try exact: pow2_ge_0;
  apply: Rdiv_le_0_compat; try exact: Rlt_0_2; apply/Rlt_le.
Qed.

Lemma fctrl_wdef p : K p -> kv + (M + m * (p[3] ^ 2)) * ke * (E p) <> 0.
Proof.
move=> Kp; rewrite Rmult_comm.
move/Rplus_opp_r_uniq/(Rmult_eq_compat_r (/ ((M + m * (p[3] ^ 2)) * ke))).
have Mmp3ke_gt0 : 0 < (M + m * p [3] ^ 2) * ke.
  by apply: Rmult_lt_0_compat => //; apply: Mp_ms_gt0.
rewrite Rmult_assoc Rinv_r; last exact/not_eq_sym/Rlt_not_eq.
rewrite Rmult_1_r => Epval; have /E_small := Kp.
rewrite Epval -Ropp_mult_distr_l Rabs_Ropp Rabs_pos_eq; last first.
  apply: Rdiv_le_0_compat; first exact/Rlt_le.
  by apply: Rmult_lt_0_compat => //; apply: Mp_ms_gt0.
move/(Rmult_lt_reg_l _ _ _ (cond_pos _))/(Rinv_lt_cancel _ _ Mmp3ke_gt0).
rewrite Rmult_comm; move/(Rmult_lt_reg_r _ _ _ (cond_pos _))/Rplus_lt_reg_l.
rewrite -[X in X < _]Rmult_1_r; move/(Rmult_lt_reg_l _ _ _ (cond_pos _)).
apply: Rle_not_lt; rewrite -(proj1 Kp).
by apply/Rle_minus_l; rewrite Rminus_eq_0; apply: pow2_ge_0.
Qed.

Lemma V'E p : K p -> V' p (Fpendulum p) = - kd * (p[1] ^ 2).
Proof.
move=> Kp; rewrite /V' (E'E (proj1 Kp)) !mxE /= /fctrl; field; split.
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
  K p -> 0 <= t -> is_derive (V \o (sol p)) t (- kd * ((sol p t)[1] ^ 2)).
Proof.
move=> Kp tge0; rewrite -V'E.
  have [_ /(_ _ tge0) solp'] := sol_is_sol sol0 solP Kp.
  have : forall q, V' (sol p t) (scal q (Fpendulum (sol p t))) =
    scal q (V' (sol p t) (Fpendulum (sol p t))).
    by move=> q; rewrite linear_scal //; have [] := filterdiff_V (sol p t).
  by apply: filterdiff_ext_lin; apply: filterdiff_comp' solp' (filterdiff_V _).
Admitted.

Lemma Kinvar : is_invariant sol K.
Proof.
move=> p Kp t tge0; have [_ Vp_s] := Kp; split; first exact: circ_invar.
apply: Rle_trans Vp_s; rewrite -[X in _ <= V X]sol0.
have Vderiv : forall s, Rbar_le 0 s -> Rbar_le s t ->
  is_derive (V \o (sol p)) s (- kd * ((sol p s)[1] ^ 2)).
  by case=> // s sge0 slet; apply: is_derive_Vsol.
apply: (nincr_function_le Vderiv _ _ tge0); try exact: Rle_refl.
move=> ? _ _; apply: Rmult_le_0_r; last exact: pow2_ge_0.
by rewrite -Ropp_0; apply/Ropp_le_contravar/Rlt_le.
Qed.

End System.