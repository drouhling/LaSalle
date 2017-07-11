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

Variable p0 : U.
(* restriction to make fctrl smooth *)
Hypothesis p0_valid :
  V p0 < ((Rmin (kv / (ke * (M + m))) 2 * m * g * l) ^ 2) / 2.

Definition K : set U :=
  [set p : U | (p[2] ^ 2) + (p[3] ^ 2) = 1 /\ V p <= V p0].

(* TODO: use p0_valid to show that Fpendulum is smooth in K and remove these
   hypotheses *)
Variable (sol : U -> R -> U).
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y, K (y 0) -> is_sol Fpendulum y <-> y = sol (y 0).
Hypothesis sol_cont : forall t, continuous_on K (sol^~ t).

Lemma is_derive_E p t :
  K p -> 0 <= t -> is_derive (E \o (sol p)) t ((sol p t)[1] * fctrl (sol p t)).
Proof.
Admitted.

Lemma is_derive_V p t :
  K p -> 0 <= t -> is_derive (V \o (sol p)) t (- kd * ((sol p t)[1] ^ 2)).
Proof.
move=> Kp tge0; set q := sol p t.
Admitted.

Lemma Kinvar : is_invariant sol K.
Proof.
move=> p Kp t tge0; have [circp Vp_s] := Kp; split.
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
apply: Rle_trans Vp_s; rewrite -[X in _ <= V X]sol0.
have Vderiv : forall s, Rbar_le 0 s -> Rbar_le s t ->
  is_derive (V \o (sol p)) s (- kd * ((sol p s)[1] ^ 2)).
  by case=> // s sge0 slet; apply: is_derive_V.
apply: (nincr_function_le Vderiv _ _ tge0); try exact: Rle_refl.
move=> ? _ _; apply: Rmult_le_0_r; last exact: pow2_ge_0.
by rewrite -Ropp_0; apply/Ropp_le_contravar/Rlt_le/cond_pos.
Qed.

End System.