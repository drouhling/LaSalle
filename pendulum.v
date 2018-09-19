Require Import Reals ssrring.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import fintype bigop ssralg ssrnum finmap interval ssrint.
From mathcomp Require Import matrix zmodp.
From mathcomp Require Import boolp reals Rstruct Rbar classical_sets posnum.
From mathcomp Require Import topology hierarchy landau derive.
Require Import lasalle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Notation "p ..[ i ]" := (p 0 (inZp i)) (at level 10).

Section System.

Parameter m M l g : posreal.

Variable ke kv kx kd : posreal.

Let U := 'rV[R]_5.

(* p = (x, x', cos theta, sin theta, theta') *)
Definition E (p : U) :=
  (1 / 2) * ((M%:num + m%:num) * (p..[1] ^+ 2) +
  m%:num * (l%:num ^+ 2) * (p..[4] ^+ 2)) +
  m%:num * l%:num * p..[1] * p..[2] * p..[4] +
  m%:num * l%:num * g%:num * (p..[2] - 1).

Definition fctrl (p : U) :=
  (kv%:num * m%:num * p..[3] * (g%:num * p..[2] - l%:num * (p..[4] ^+ 2)) -
   (M%:num + m%:num * (p..[3] ^+ 2)) * (kx%:num * p..[0] + kd%:num * p..[1])) /
  (kv%:num + (M%:num + m%:num * (p..[3] ^+ 2)) * ke%:num * (E p)).

Definition Fpendulum (p : U) : U :=
  \row_(i < 5) nth 0
   [:: p..[1]
     ; ((m%:num * p..[3] * (l%:num * (p..[4] ^+ 2) - g%:num * p..[2]) +
       (fctrl p)) / (M%:num + m%:num * (p..[3] ^+ 2)))
     ; - p..[3] * p..[4]
     ; p..[2] * p..[4]
     ; (((M%:num + m%:num) * g%:num * p..[3] -
       p..[2] * (m%:num * l%:num * (p..[4] ^+ 2) * p..[3] + (fctrl p))) /
       (l%:num * (M%:num + m%:num * (p..[3] ^+ 2))))] i.

Definition V (p : U) :=
  (ke%:num / 2) * ((E p) ^+ 2) + (kv%:num / 2) * (p..[1] ^+ 2) +
  (kx%:num / 2) * (p..[0] ^+ 2).

Global Instance is_diff_component n i (p : 'rV[R]_n.+1) :
  is_diff p (fun q => q..[i] : R^o) (fun q => q..[i]).
Proof.
have comp_lin : linear (fun q : 'rV[R]_n.+1 => q..[i] : R^o).
  by move=> ???; rewrite !mxE.
have comp_cont : continuous (fun q : 'rV[R]_n.+1 => q..[i] : R^o).
  move=> q A [_/posnumP[e] Ae] /=; apply/locallyP; exists e%:num => //.
  by move=> r /(_ ord0) /(_ (inZp i)) /Ae.
apply: DiffDef; first exact: (@linear_differentiable _ _ (Linear comp_lin)).
by rewrite (@diff_lin _ _ (Linear comp_lin)).
Qed.

Global Instance is_diff_component_comp (V : normedModType R) n
  (f : V -> 'rV[R]_n.+1) i p df : is_diff p f df ->
  is_diff p (fun q => (f q)..[i] : R^o) (fun q => (df q)..[i]).
Proof.
move=> dfp.
have -> : (fun q => (f q)..[i]) = (fun v => v..[i]) \o f by rewrite funeqE.
(* This should work *)
(* apply: is_diff_eq. *)
exact: is_diff_comp.
Qed.

Lemma deriveE' (V W : normedModType R) (f : V -> W) x v :
  derive f x v = derive (fun h : R^o => f (h *: v + x)) 0 1.
Proof.
rewrite /derive.
set g1 := fun h => h^-1 *: _; set g2 := fun h => h^-1 *: _.
suff -> : g1 = g2 by [].
by rewrite funeqE /g1 /g2 => h /=; rewrite addr0 scale0r add0r [_%:A]mulr1.
Qed.

Global Instance is_derive_component (V : normedModType R) n
  (f : V -> 'rV[R]_n.+1) i x v df :
  is_derive x v f df -> is_derive x v (fun q => (f q)..[i] : R^o) (df..[i]).
Proof.
move=> dfx.
have diff_f : is_diff (0 : R^o) (fun h => f (h *: v + x)) ( *:%R^~ df ).
  have /derivable1P/derivable1_diffP fdrvbl : derivable f x v by [].
  by apply: DiffDef => //; rewrite diff1E // derive1E -deriveE' derive_val.
apply: DeriveDef; first exact/derivable1P/derivable1_diffP.
by rewrite deriveE' deriveE // diff_val scale1r.
Qed.

Lemma V_continuous : continuous V.
Proof.
by move=> ?; apply: (@differentiable_continuous _ [normedModType R of R^o]).
Qed.

Variable k0 : R.
Let B := ke%:num * ((minr (kv%:num / (ke%:num * (M%:num + m%:num)))
  (2 * m%:num * g%:num * l%:num)) ^+ 2) / 2.
(* restriction to make fctrl smooth *)
Hypothesis k0_valid : k0 < B.

Definition K : set U :=
  [set p : U | (p..[2] ^+ 2) + (p..[3] ^+ 2) = 1 /\ V p <= k0].

Lemma expr_continuous n : continuous (fun x : R^o => x ^+ n.+1 : R^o).
Proof.
move=> x; suff : differentiable x (fun y => y ^+ n.+1).
  by apply: differentiable_continuous.
suff -> : (fun y => y ^+ n.+1) = ((id : R^o -> R^o) ^+ n.+1) by [].
by rewrite exprfunE.
Qed.

Lemma circle_closed : closed [set p : U | p..[2] ^+ 2 + p..[3] ^+ 2 = 1].
Proof.
move=> p clcircp.
apply: (@ball_norm_eq _ [normedModType R of R^o]) => e /=.
have /expr_continuous [_/posnumP[e1] p2e1_sp2he] :=
  locally_ball (p..[2] ^+ 2) (e%:num / 2)%:pos.
have /expr_continuous [_ /posnumP[e2] p3e2_sp3he] :=
  locally_ball (p..[3] ^+ 2) (e%:num / 2)%:pos.
have [q [circq pme12_q]] :
  [set p : U | p..[2] ^+ 2 + p..[3] ^+ 2 = 1] `&`
  ball p (minr e1 e2) !=set0 by apply/clcircp/locally_ball.
rewrite -circq opprD addrACA; apply: ler_lt_trans (ler_normm_add _ _) _.
by rewrite (splitr e%:num) ltr_add //; [apply/p2e1_sp2he|apply/p3e2_sp3he];
  apply: ball_ler (pme12_q _ _); rewrite ler_minl lerr // orbC.
Qed.

Lemma preimV_lek0_closed : closed (V @^-1` (<= k0)).
Proof.
by apply: closed_comp; [move=> ??; apply: V_continuous|apply: closed_le].
Qed.

Lemma K_closed : closed K.
Proof. exact: closedI circle_closed preimV_lek0_closed. Qed.

Lemma bounded_poly (a b c d : R) :
  0 < a -> \forall M \near +oo, forall x,
  a * (x ^+ 2) - (b * `|x|) - c < d -> `|x| < M.
Proof.
move=> agt0.
suff ptoinfty : (fun x => a * (x ^+ 2) - (b * `|x|) - c) @ +oo --> +oo.
  have dleatinfty : [filter of +oo] (>= d) by exists d => ? /ltrW.
  have /ptoinfty [M1 sgtM1pged] := dleatinfty; near=> M.
  move=> x pxltd; rewrite ltrNge; apply/negP => Mlex.
  move: pxltd; rewrite ltrNge => /negP; apply.
  rewrite -(@ger0_norm _ `|x|) // -(@ger0_norm _ (_ ^+ 2)) ?sqr_ge0 // normrX.
  by apply: sgtM1pged; apply: ltr_le_trans Mlex; near: M; exists M1.
move=> A [M sgtMA]; rewrite !near_simpl; near=> x.
have lt0x : 0 < x by near: x; exists 0.
rewrite ger0_norm ?ltrW //; apply: sgtMA.
rewrite ltr_subr_addr expr2 mulrA -mulrBl; apply: ler_lt_trans (ler_norm _) _.
rewrite -[ `|_|%R]sqr_sqrtr // expr2; apply: ltr_pmul; last 1 first.
- by near: x; exists (Num.sqrt `|M + c|).
- exact: sqrtr_ge0.
- exact: sqrtr_ge0.
rewrite ltr_subr_addr -ltr_pdivr_mull //; near: x.
by exists (a^-1 * (Num.sqrt `|M + c| + b)).
Grab Existential Variables. all: end_near. Qed.

Lemma K_bounded : bounded K.
Proof.
suff : \forall M \near +oo, forall p, K p -> forall i, `|p ord0 i| < M.
  rewrite /bounded; apply: filter_app; near=> M.
  move=> Kbnd p /Kbnd ltpM; apply/bigmaxr_ltrP => [|i seqi].
    by rewrite size_map -cardE card_prod !cardE !size_enum_ord.
  by rewrite (nth_map 0); [rewrite ord1 ltpM|move: seqi; rewrite size_map].
suff : \forall M \near +oo, forall p, K p -> `| p..[0] | < M /\
  `| p..[1] | < M /\ `| p..[2] | < M /\ `| p..[3] | < M /\ `| p..[4] | < M.
  apply: filter_app; near=> M.
  move=> Kbnd p /Kbnd [ltp0M [ltp1M [ltp2M [ltp3M ltp4M]]]].
  case; do 5 ?[case; first by move=> ?; rewrite -[ Ordinal _ ]natr_Zp Zp_nat].
  by move=> n ?; suff : (n.+1.+4 < 5)%N by rewrite !ltnS ltn0.
have K1bnd : \forall M \near +oo, forall p, K p -> `| p..[1] | < M.
  near=> M => p [_ Vps].
    suff /ltr_trans : `| p..[1] | < Num.sqrt (2 * B / kv%:num).
    by apply; near: M; exists (Num.sqrt (2 * B / kv%:num)).
  rewrite absRE -sqrtr_sqr ltr_sqrt // mulrAC -ltr_pdivr_mull // invf_div.
  apply: ler_lt_trans k0_valid; apply: ler_trans Vps.
  by rewrite [V _]addrAC ler_addr addr_ge0 // pmulr_rge0 // sqr_ge0.
apply: filter_app (K1bnd); near=> M.
move=> K1ltM p Kp; have [circp Vps] := Kp; split.
  suff /ltr_trans : `| p..[0] | < Num.sqrt (2 * B / kx%:num).
    by apply; near: M; exists (Num.sqrt (2 * B / kx%:num)).
  rewrite absRE -sqrtr_sqr ltr_sqrt // mulrAC -ltr_pdivr_mull // invf_div.
  apply: ler_lt_trans k0_valid; apply: ler_trans Vps.
  by rewrite ler_addr addr_ge0 // pmulr_rge0 // sqr_ge0.
split; first exact: K1ltM; split.
  suff /ler_lt_trans : `| p..[2] | <= 1 by apply; near: M; exists 1.
  by rewrite absRE -sqrtr_sqr -sqrtr1 ler_sqrt // -circp ler_addl sqr_ge0.
split.
  suff /ler_lt_trans : `| p..[3] | <= 1 by apply; near: M; exists 1.
  by rewrite absRE -sqrtr_sqr -sqrtr1 ler_sqrt // -circp ler_addr sqr_ge0.
move: p Kp {circp Vps}; near: M; rewrite /= !near_simpl.
have [M1 sgtM1gtK1] := K1bnd.
have := bounded_poly (m%:num * l%:num * ((`|M1| + 1) ^+ 2))
  (m%:num * l%:num * g%:num * ((`|M1| + 1) + 1)) (Num.sqrt (2 * B / ke%:num))
  [gt0 of m%:num * (l%:num ^+ 2) / 2].
apply: filter_app; near=> M => sEsltM p Kp; have [circp Vps] := Kp.
apply: sEsltM.
have : E p < Num.sqrt (2 * B / ke%:num).
  apply: ler_lt_trans (ler_norm _) _.
  rewrite -sqrtr_sqr ltr_sqrt // mulrAC -ltr_pdivr_mull // invf_div.
  apply: ler_lt_trans k0_valid; apply: ler_trans Vps.
  by rewrite -[V _]addrA ler_addl addr_ge0 // pmulr_rge0 // sqr_ge0.
apply: ler_lt_trans; apply: ler_add; last first.
  rewrite -mulrN opprD ler_wpmul2l // ler_add2r ler_oppl.
  rewrite ler_paddl // (ler_trans (ler_norm _)) // normrN.
  by rewrite -sqrtr_sqr -sqrtr1 ler_sqrt // -circp ler_addl sqr_ge0.
rewrite mulrDr [1 / 2 * _ + _]addrC -addrA [1 / 2 * _]mulrCA mul1r mulrA.
rewrite (expr2 l%:num) ler_add2l; apply: ler_paddl.
  by rewrite pmulr_rge0 // pmulr_rge0 // sqr_ge0.
rewrite -mulrN -!mulrA ler_wpmul2l // ler_wpmul2l // !mulrN ler_oppl.
suff : `| p..[1] | * (`| p..[2] | * `| p..[4] |) <=
  (`|M1| + 1) * ((`|M1| + 1) * `| p..[4] |).
  by apply: ler_trans; rewrite -!normrM -normrN ler_norm.
rewrite !mulrA ler_wpmul2r // ler_pmul //.
  apply/ltrW/sgtM1gtK1 => //; apply: ler_lt_trans (ler_norm _) _.
  by rewrite ltr_addl.
have /(ler_trans _) : 1 <= `|M1| + 1 by rewrite ler_addr.
by apply; rewrite -sqrtr_sqr -sqrtr1 ler_sqrt // -circp ler_addl sqr_ge0.
Unshelve. all: end_near. Grab Existential Variables. all: end_near. Qed.

Lemma K_compact : compact K.
Proof. exact: bounded_closed_compact K_bounded K_closed. Qed.

Lemma Mp_ms_gt0 (p : U) : 0 < M%:num + m%:num * (p..[3] ^+ 2).
Proof. by rewrite ltr_spaddl // pmulr_rge0 // sqr_ge0. Qed.

Lemma ge0_expr_ndecr (R : realDomainType) n (x y : R) :
  0 <= x <= y -> x ^+ n <= y ^+ n.
Proof.
move=> /andP [xge0 yge0]; elim: n => [|n ihn]; first by rewrite !expr0.
by rewrite !exprS ler_pmul // exprn_ge0.
Qed.

Lemma E_small p : V p < B -> `|E p| < kv%:num / (ke%:num * (M%:num + m%:num)).
Proof.
move=> Vp_s; rewrite -ltr_sqr ?nnegrE // -normrX ger0_norm ?sqr_ge0 //.
suff : 2 * (V p) / ke%:num < (kv%:num / (ke%:num * (M%:num + m%:num))) ^+ 2.
  apply: ler_lt_trans.
  rewrite ler_pdivl_mulr // -ler_pdivr_mull // mulrC -mulrA mulrC.
  by rewrite /V -addrA ler_addl addr_ge0 // pmulr_rge0 // sqr_ge0.
rewrite ltr_pdivr_mulr // mulrC -ltr_pdivl_mulr // (ltr_le_trans Vp_s) //.
rewrite -mulrA mulrCA mulrA; apply: ler_pmul => //; apply: ler_pmul => //.
apply/ge0_expr_ndecr/andP; split; last by rewrite ler_minl lerr.
by rewrite ler_minr; apply/andP; split.
Qed.

Lemma fctrl_wdef (p : U) : (p..[2] ^+ 2) + (p..[3] ^+ 2) = 1 -> V p < B ->
  kv%:num + (M%:num + m%:num * (p..[3] ^+ 2)) * ke%:num * (E p) != 0.
Proof.
move=> circp Vp_s; rewrite -normr_gt0.
rewrite -[X in X + _](@mulfVK _ ((M%:num + m%:num * (p..[3] ^+ 2)) * ke%:num));
  last by rewrite lt0r_neq0 // pmulr_rgt0 // Mp_ms_gt0.
rewrite mulrC -mulrDr normrM pmulr_rgt0; last first.
  by rewrite normrM pmulr_rgt0 gtr0_norm // Mp_ms_gt0.
apply: ltr_le_trans (ler_sub_norm_add _ _).
rewrite subr_gt0; apply: ltr_le_trans (E_small Vp_s) _.
rewrite ger0_norm; last first.
  by rewrite pmulr_rge0 // invr_ge0 pmulr_rge0 // Mp_ms_gt0.
rewrite ler_pmul // lef_pinv ?posrE //; last by rewrite pmulr_rgt0 // Mp_ms_gt0.
rewrite mulrC ler_pmul //; first exact/ltrW/Mp_ms_gt0.
rewrite ler_add2l -{2}[m%:num]mulr1 ler_pmul // ?sqr_ge0 //.
by rewrite -circp ler_addr sqr_ge0.
Qed.

(* TODO: show that Fpendulum is smooth in K and remove these hypotheses using
  Cauchy-Lipschitz *)
Variable (sol : U -> R -> U).
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y, K (y 0) -> is_sol Fpendulum y <-> y = sol (y 0).
Hypothesis sol_cont : forall t, continuous_on K (sol^~ t).

(* TODO: generalize *)
Lemma eq0_derive1_cst (f : R^o -> R^o) (a b : R) :
  (forall t, t \in `[a, b] -> is_derive (t : R^o) 1 f 0) ->
  forall t, t \in `[a, b] -> f t = f a.
Proof.
move=> f'eq0 t tab; apply/eqP; rewrite eqr_le; apply/andP; split.
  by apply: (@ler0_derive1_nincr _ a b) => //; rewrite ?(itvP tab) //;
    move=> ? /f'eq0 // df; rewrite derive1E derive_val.
by apply: (@le0r_derive1_ndecr _ a b) => //; rewrite ?(itvP tab) //;
  move=> ? /f'eq0 // df; rewrite derive1E derive_val.
Qed.

Lemma circ_invar p :
  K p -> forall t, 0 <= t -> (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1.
Proof.
move=> Kp t tge0; have [circp _] := Kp; rewrite -circp -[in RHS](sol0 p).
apply (@eq0_derive1_cst (fun s => (sol p s)..[2] ^+ 2 + (sol p s)..[3] ^+ 2) _
  t); last by rewrite inE lerr tge0.
move=> s s0t; have sge0 : s >= 0 by rewrite (itvP s0t).
have [_ /(_ _ sge0) dsol] := sol_is_sol sol0 solP Kp.
apply: is_derive_eq.
by rewrite !mxE /= [_ *: (_ * _)]mulrCA -!mulrDr addrC mulNr subrr.
Qed.

Lemma mul2r (R : ringType) (x : R) : 2 * x = x + x.
Proof. by rewrite -mulr2n mulr_natl. Qed.

Lemma is_derive_Esol p t :
  K p -> 0 <= t -> is_derive (t : R^o) 1 (E \o (sol p) : _ -> R^o)
  ((sol p t)..[1] * fctrl (sol p t)).
Proof.
move=> Kp tge0; have [_ /(_ _ tge0) sol_att] := sol_is_sol sol0 solP Kp.
apply: is_derive_eq.
have /eqP : (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1 by apply: circ_invar.
rewrite eq_sym addrC -subr_eq => /eqP circp.
have Mpmsne0 : M%:num + m%:num * (sol p t)..[3] ^+ 2 != 0.
  by rewrite lt0r_neq0 // Mp_ms_gt0.
rewrite subr0 !mxE /= -circp -![_ *: _]/(_ * _) invrM ?unitfE //; last first.
  by rewrite circp.
set q := sol _ _ _; set x := (M%:num + m%:num * _)^-1; set y := fctrl _.
rewrite [x / _]mulrC; do ![rewrite ?[_ * (_ * x)]mulrA -?(mulrDl _ _ x)].
rewrite [_ * (_ + _ * x)]mulrDr [_ * (_ * x)]mulrA [_ + _ * x]addrC.
do 2 rewrite addrA -(mulrDl _ _ x).
rewrite -!mul2r mul1r mulrDr; do 2 rewrite [2^-1 * _]mulrCA.
do 2 rewrite [2^-1 * _]mulrA mulVf // mul1r.
rewrite [_ / _]mulrC ![_ * (_^-1 * _)]mulrA [_ * (_ / _ * _)]mulrA.
rewrite -[_ + _ + _ * _ * _]addrA -mulrDl.
rewrite [in _ * x]addrAC ![_ * (_ * (_ + _))]mulrA -mulrDl.
rewrite -addrA [_ * (_ * (- _ * _))]mulrA -mulrDl.
apply/(canLR (subrK _))/(canLR (mulfK _)); first by rewrite circp.
rewrite [RHS]mulrDl !mulNr [in RHS]mulrAC; apply: (canRL (addrK _)).
rewrite [(_ + _) * _]mulrDr addrAC [_ + _ * y + _]addrAC.
apply: (canLR (subrK _)); rewrite -mulrBl [_ * (_ + y)]mulrDr opprD addrA.
rewrite [_ * (_ - _ * y)]mulrDr addrA -[- (_ * y)]mulNr [_ * (_ * y)]mulrA.
rewrite [_ + _ * y + _]addrAC; apply: (canLR (subrK _)); rewrite -mulrBl.
rewrite mulrN opprK mulrACA [_ ^+2 / _]mulrAC mulfVK //.
by rewrite [_ / _]mulrC ![_^-1 * _]mulrA [_^-1 * _ * _]mulrC mulVKf //; ssring.
Qed.

Lemma is_deriv_Vsol p t :
  K p -> 0 <= t -> V (sol p t) < B ->
  is_derive (t : R^o) 1 (V \o (sol p) : _ -> R^o)
    (- kd%:num * ((sol p t)..[1] ^+ 2)).
Proof.
move=> Kp tge0 Vsolpt_s.
have [_ /(_ _ tge0) sol_att] := sol_is_sol sol0 solP Kp.
have Esol' := is_derive_Esol Kp tge0; apply: is_derive_eq.
rewrite [in X in _ + X]mxE /= -!mul2r -![_ *: _]/(_ * _).
do 3 rewrite [_ / _]mulrC [_^-1 * _ * _]mulrCA -[_ ^-1 * _ * _]mulrA mulVKf //.
rewrite [_ * fctrl _]mulrC [_ * Fpendulum _ _ _]mulrC mulrA mulrA -addrA.
rewrite ![in X in _ + X]mulrA -!mulrDl expr2 [RHS]mulrA; congr (_ * _).
rewrite addrA mxE /=.
have Mpmsne0 : M%:num + m%:num * (sol p t)..[3] ^+ 2 != 0.
  by rewrite lt0r_neq0 // Mp_ms_gt0.
apply: (canLR (subrK _)); rewrite [kv%:num * _]mulrA.
rewrite -[_ * fctrl _](mulfVK Mpmsne0) [_ / _ * _]mulrAC -mulrDl.
apply: (canLR (mulfK _)) => //; rewrite [kv%:num * _]mulrDr addrA addrAC.
apply: (canLR (subrK _)); rewrite mulrAC -mulrDl /fctrl [LHS]mulrA.
have circp : (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1 by apply: circ_invar.
have fctrl_def := fctrl_wdef circp Vsolpt_s; apply: (canLR (mulfK _)) => //.
by ssring.
Qed.

Lemma defset_invar p : K p -> forall t, 0 <= t ->
  (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1 /\ V (sol p t) < B.
Proof.
move=> Kp t tge0; split; first exact: circ_invar.
set A := [pred t | (0 <= t) && (B <= V (sol p t))].
case: (pselect (reals.nonempty A))=> [An0 |]; last first.
  by move=> /asboolPn /forallp_asboolPn /(_ t) /negP; rewrite inE => /nandP [];
    [rewrite tge0|rewrite -ltrNge].
have infA : has_inf A.
  by apply/has_infP; split=> //; exists 0; apply/lbP => ? /andP [].
exfalso=> {t tge0}; have infge0 : 0 <= inf A.
  by apply: lb_le_inf => //; apply/lbP => ? /andP [].
have Vsolp_drvbl t : 0 <= t -> derivable (V \o (sol p) : R^o -> R^o) t 1.
  by move=> tge0; have [_ /(_ _ tge0) sol_att] := sol_is_sol sol0 solP Kp.
have Vsolpinf_geB : B <= V (sol p (inf A)).
  case: (lerP B (V (sol p (inf A)))) => // Vsolpinf_ltB; rewrite falseE.
  have Vsolp_cont : {for inf A, continuous (V \o (sol p))}.
    suff /differentiable_continuous :
      differentiable (inf A : R^o) (V \o sol p : _ -> R^o) by [].
    exact/derivable1_diffP/Vsolp_drvbl.
  have BmVsolps_gt0 : 0 < B - V (sol p (inf A)) by rewrite subr_gt0.
  have /Vsolp_cont := locally_ball (V (sol p (inf A))) (PosNum BmVsolps_gt0).
  move=> [_ /posnumP[e] /= infe_Vsolp].
  suff : inf A + e%:num / 2 <= inf A.
    by rewrite lerNgt => /negP; apply; rewrite ltr_addl.
  apply: lb_le_inf An0 _; apply/lbP => s /andP [sge0 Vsolps_geB].
  rewrite lerNgt; apply/negP => ltsinfphe; have leinfs : inf A <= s.
    by apply: inf_lower_bound => //; rewrite inE sge0 Vsolps_geB.
  suff /infe_Vsolp : ball (inf A) e%:num s.
    rewrite ball_absE /= absrB absRE => /(ler_lt_trans (ler_norm _)).
    by rewrite ltrNge => /negP; apply; rewrite ler_sub.
  rewrite ball_absE /= absrB absRE ger0_norm ?subr_ge0 // ltr_subl_addl.
  by apply: ltr_trans ltsinfphe _; rewrite ltr_add2l {2}[e%:num]splitr ltr_addl.
have Vsol_drvbl t : t \in `]0, (inf A)[ ->
  is_derive (t : R^o) 1 (V \o sol p : _ -> R^o)
  (- kd%:num * (sol p t)..[1] ^+ 2).
  move=> t0inf; apply: is_deriv_Vsol => //; first by rewrite (itvP t0inf).
  rewrite ltrNge; apply/negP => Vsolpt_geB; suff : inf A <= t.
    by rewrite lerNgt => /negP; apply; rewrite (itvP t0inf).
  apply: inf_lower_bound => //; rewrite inE; apply/andP; split=> //.
  by rewrite (itvP t0inf).
have : {in `[0, (inf A)], continuous (V \o sol p)}.
  move=> t t0inf; suff /differentiable_continuous :
    differentiable (t : R^o) (V \o sol p : _ -> R^o) by [].
  by apply/derivable1_diffP/Vsolp_drvbl; rewrite (itvP t0inf).
move=> /(MVT infge0 Vsol_drvbl) [t t0inf].
rewrite /funcomp sol0 subr0 => dVsol.
have infgt0 : 0 < inf A.
  rewrite ltr_def; apply/andP; split=> //.
  apply/negP => /eqP infA0; have := Vsolpinf_geB.
  rewrite lerNgt => /negP; apply; rewrite infA0 sol0.
  by apply: ler_lt_trans k0_valid; have [] := Kp.
have : V (sol p (inf A)) - V p <= 0.
  by rewrite dVsol !mulNr oppr_le0 pmulr_lge0 // pmulr_rge0 // sqr_ge0.
rewrite lerNgt => /negP; apply.
rewrite subr_gt0; apply: ltr_le_trans Vsolpinf_geB.
by apply: ler_lt_trans k0_valid; have [] := Kp.
Qed.

Lemma is_derive_Vsol p (t : R^o) :
  K p -> 0 <= t -> is_derive t 1 (V \o sol p : _ -> R^o)
  (- kd%:num * (sol p t)..[1] ^+ 2).
Proof.
move=> Kp tge0; have [circpt Vpts] := defset_invar Kp tge0.
exact: is_deriv_Vsol.
Qed.

Lemma Kinvar : is_invariant sol K.
Proof.
move=> p Kp t tge0; have [_ Vp_s] := Kp; split; first exact: circ_invar.
apply: ler_trans Vp_s; rewrite -{2}[p]sol0.
have Vsol_deriv : forall s, s \in `[0, t] ->
  is_derive (s : R^o) 1 (V \o sol p : _ -> R^o)
  (- kd%:num * (sol p s)..[1] ^+ 2) by move=> s /andP [/(is_derive_Vsol Kp)].
apply: (@ler0_derive1_nincr (V \o sol p) 0 t);[idtac|idtac|by [] |by [] |by []].
  by move=> ? /Vsol_deriv.
move=> s /Vsol_deriv dVsols; rewrite derive1E derive_val.
by rewrite !mulNr oppr_le0 pmulr_rge0 // sqr_ge0.
Qed.

Definition homoclinic_orbit : set U := [set p : U | p..[0] = 0 /\ p..[1] = 0 /\
  (1 / 2) * m%:num * (l%:num ^+ 2) * (p..[4] ^+ 2) =
  m%:num * g%:num * l%:num * (1 - p..[2])].

Lemma homoclinicE :
  homoclinic_orbit = [set p : U | p..[0] = 0 /\ p..[1] = 0 /\ E p = 0].
Proof.
rewrite predeqE => p; split.
  move=> [p0eq0 [p1eq0 /eqP]]; rewrite -subr_eq0 => /eqP homoeq.
  split=> //; split=> //; rewrite -homoeq /E p1eq0 expr0n /=.
  rewrite !mulr0 !mul0r addr0 add0r mulrA [_ / _ * _]mulrA -mulrN opprB.
  by rewrite [_ * _ * g%:num]mulrAC.
move=> [p0eq0 [p1eq0 Epeq0]]; split=> //; split=> //.
apply: subr0_eq; rewrite -Epeq0 /E p1eq0 expr0n /=.
rewrite !mulr0 !mul0r addr0 add0r [in RHS] mulrA [_ / _ * _ in RHS]mulrA -mulrN.
by rewrite opprB [_ * _ * g%:num]mulrAC.
Qed.

Lemma limSKinvar : is_invariant sol (limS sol K).
Proof.
move=> p limSKp t tge0.
exact: (@invariant_limS _ _ _ K_compact _ sol0 solP sol_cont Kinvar).
Qed.

Lemma subset_limSK_K : limS sol K `<=` K.
Proof.
move=> p [q Kq solq_top].
apply: compact_closed (@normedModType_hausdorff _ _) K_compact _ _.
have solqK : (sol q @ +oo) K by exists 0 => ? /ltrW; apply: Kinvar.
by move=> A /solq_top - /(_ _ solqK) [r []]; exists r.
Qed.

Lemma Vsol'_eq0 p t :
  limS sol K p -> 0 <= t -> derive1 (V \o sol p : _ -> R^o) t = 0.
Proof.
move=> limSKp tge0; have limSKsolp : limS sol K (sol p t) by apply: limSKinvar.
have Kp : K p by apply: subset_limSK_K.
have -> : derive1 (V \o sol p : _ -> R^o) t =
  derive1 (V \o sol (sol p t) : _ -> R^o) 0.
  have dVsolt := is_derive_Vsol Kp tge0; rewrite derive1E derive_val.
  have Ksolpt : K (sol p t) by apply: subset_limSK_K.
  have dVsolt' := is_derive_Vsol Ksolpt (lerr _); rewrite derive1E derive_val.
  by rewrite -(solD sol0 solP Kinvar) // add0r.
apply: (stable_limS K_compact sol0 solP sol_cont Kinvar (V:=V)) limSKsolp.
- move=> q Kq; have /(_ q) := V_continuous; apply: flim_trans.
  exact: flim_app (@flim_within _ _ _ _).
- by move=> q s Kq sge0; have := is_derive_Vsol Kq sge0.
- move=> q Kq; have dVsolq := is_derive_Vsol Kq (lerr _).
  by rewrite derive1E derive_val mulNr oppr_le0 pmulr_rge0 // sqr_ge0.
Qed.

Lemma sol1_eq0 p t : limS sol K p -> 0 <= t -> (sol p t)..[1] = 0.
Proof.
move=> limSKp tge0; have Kp : K p by apply: subset_limSK_K.
have dVsol := is_derive_Vsol Kp tge0; have /eqP := Vsol'_eq0 limSKp tge0.
rewrite derive1E derive_val mulrI_eq0; last exact/lregN/lregP.
by rewrite sqrf_eq0 => /eqP.
Qed.

Lemma is_derive_nneg_eq (f g : R^o -> R^o) (t : R^o) l1 l2 :
  (forall t, 0 <= t -> f t = g t) -> 0 <= t ->
  is_derive t 1 f l1 -> is_derive t 1 g l2 -> l1 = l2.
Proof.
move=> feg tge0 df dg.
have /@derive_val <- := df; have /@derive_val <- := dg.
apply: subr0_eq; rewrite -deriveB // /derive cvg_at_rightE; last first.
  by rewrite -[cvg _]/(derivable _ _ _).
apply: flim_map_lim => A A0; rewrite !near_simpl; near=> h.
rewrite /= -![(_ - _ : _ -> _) _]/(_ - _) !feg //.
  by rewrite !subrr scaler0; apply: locally_singleton.
by rewrite addr_ge0 // [_%:A]mulr1 ltrW //; near: h; exists 1.
Grab Existential Variables. all: end_near. Qed.

Lemma sol1'_eq0 p t : limS sol K p -> 0 <= t -> (Fpendulum (sol p t))..[1] = 0.
Proof.
move=> limSKp tge0; have := is_derive_cst (0 : R^o) (t : R^o) 1.
have /subset_limSK_K Kp := limSKp.
have [_ /(_ _ tge0) /(is_derive_component 1)] := sol_is_sol sol0 solP Kp.
by apply: is_derive_nneg_eq => // s sge0; rewrite sol1_eq0.
Qed.

Lemma sol0_const p t : limS sol K p -> 0 <= t -> (sol p t)..[0] = p..[0].
Proof.
move=> limSKp tge0; rewrite -[p in RHS]sol0.
apply (@eq0_derive1_cst (fun s => (sol p s)..[0]) 0 t); last first.
  by rewrite inE lerr tge0.
move=> s /andP [sge0 _]; have /subset_limSK_K Kp := limSKp.
have [_ /(_ _ sge0) /(is_derive_component 0) dsol0] := sol_is_sol sol0 solP Kp.
by apply: DeriveDef => //; rewrite derive_val mxE /= sol1_eq0.
Qed.

Lemma Esol_const p t : limS sol K p -> 0 <= t -> (E \o sol p) t = E p.
Proof.
move=> limSKp tge0; rewrite -[p in RHS]sol0.
apply (@eq0_derive1_cst (E \o sol p) 0 t); last first.
  by rewrite inE lerr tge0.
move=> s /andP [sge0 _]; have /subset_limSK_K Kp := limSKp.
have dEsol := is_derive_Esol Kp sge0; apply: DeriveDef => //.
by rewrite derive_val sol1_eq0 // mul0r.
Qed.

Lemma Efctrl_psol0_eq0 p t : limS sol K p -> 0 <= t ->
  ke%:num * (E (sol p t)) * (fctrl (sol p t)) + kx%:num * (sol p t)..[0] = 0.
Proof.
move=> limSKp tge0.
have -> :
  0 = - (kd%:num * (sol p t)..[1] + kv%:num * (Fpendulum (sol p t))..[1]).
  by rewrite sol1'_eq0 // sol1_eq0 // !mulr0 add0r oppr0.
have [circsolt /ler_lt_trans /(_ k0_valid) Vsolts] : K (sol p t).
  by apply: Kinvar tge0; apply: subset_limSK_K.
have fctrl_def := fctrl_wdef circsolt Vsolts.
have Mpmsne0 : M%:num + m%:num * (sol p t)..[3] ^+ 2 != 0.
  by rewrite lt0r_neq0 // Mp_ms_gt0.
rewrite /Fpendulum !mxE /= /fctrl; apply: (canLR (subrK _)); rewrite mulrA.
apply: (canLR (mulfK _)) => //; rewrite [RHS]mulrDl; apply: (canRL (subrK _)).
rewrite opprD [RHS]mulrDl [RHS]addrC; apply/(canRL (subrK _))/Logic.eq_sym.
rewrite mulrC -mulNr mulrA mulrA; apply: (canLR (mulfK _)) => //.
rewrite mulrDr [LHS]mulrDr addrC; apply: (canLR (subrK _)).
by rewrite [LHS]mulrA [LHS]mulrA; apply: (canLR (mulfK _)) => //; ssring.
Qed.

Lemma div_fctrl_mP p t : limS sol K p -> 0 <= t ->
  (sol p t)..[3] * (g%:num * (sol p t)..[2] - l%:num * (sol p t)..[4] ^+ 2) =
  (fctrl (sol p t)) / m%:num.
Proof.
move=> limSKp tge0; apply: (canRL (mulfK _)) => //; apply: subr0_eq.
have := sol1'_eq0 limSKp tge0; rewrite !mxE /= => /(canRL (mulfK _)).
rewrite mul0r => fctrl_val.
rewrite mulrC mulrA -[in X in X - _]opprB mulrN -opprD fctrl_val ?oppr0 //.
exact/invr_neq0/lt0r_neq0/Mp_ms_gt0.
Qed.

Lemma Fpendulum4E p t : limS sol K p -> 0 <= t ->
  (Fpendulum (sol p t))..[4] = g%:num / l%:num * (sol p t)..[3].
Proof.
move=> limSKp tge0; rewrite !mxE /=.
have /(canLR (mulfVK _)) <- // := div_fctrl_mP limSKp tge0.
apply: (canLR (mulfK _)); last apply/Logic.eq_sym.
  by apply: lt0r_neq0; rewrite pmulr_rgt0 // Mp_ms_gt0.
rewrite mulrCA mulrA mulrA [l%:num * _ in LHS]mulrC mulrVK ?unitfE //.
have [] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
by rewrite addrC => /(canRL (addrK _)) -> _; ssring.
Qed.

Lemma En0_fctrlsol_const p t :
  limS sol K p -> E p != 0 -> 0 <= t -> fctrl (sol p t) = fctrl p.
Proof.
move=> limSKp Epn0 tge0.
have := Efctrl_psol0_eq0 limSKp tge0.
rewrite -(Efctrl_psol0_eq0 limSKp (lerr _)) sol0
  [E (sol p t)](Esol_const limSKp tge0) (sol0_const limSKp tge0).
have keEn0 : ke%:num * E p != 0 by rewrite mulrI_eq0 //; apply/lregP.
move/(canRL (addrK _)); rewrite -addrA subrr addr0 mulrC.
by move=> /(canRL (mulfK _)) - /(_ keEn0) ->; rewrite mulrAC -mulrA mulVKf.
Qed.

Lemma inf_in_finset (A : {fset R}) :
  has_inf [pred t | t \in A] -> inf [pred t | t \in A] \in A.
Proof.
move=> infA; have /has_infP [[t At] _] := infA.
have Amin : \big[minr/t]_(s <- enum_fset A) s \in A.
  have : forall s, s \in enum_fset A -> s \in A by [].
  elim: (enum_fset A) => [inA|s l ihl inA]; first by rewrite big_nil.
  rewrite big_cons; case: minrP => _; first by apply: inA; rewrite inE eq_refl.
  by apply: ihl => r lr; apply: inA; rewrite inE orbC lr.
suff -> : inf [pred t | t \in A] = \big[minr/t]_(s <- enum_fset A) s by [].
apply/eqP; rewrite eqr_le; apply/andP; split; first exact: inf_lower_bound Amin.
apply: lb_le_inf; first by have /has_infP [] := infA.
apply/lbP => s As; have : s \in enum_fset A by [].
elim: (enum_fset A) => // r l ihl; rewrite inE => /orP [/eqP <-|].
  by rewrite big_cons ler_minl lerr.
by rewrite big_cons ler_minl orbC => /ihl ->.
Qed.

Lemma continuous_finimage_cst (f : R -> R) n (g : 'I_n -> R) :
  {in (>= 0), continuous f} ->
  (forall t, 0 <= t -> exists i, f t = g i) ->
  forall t, 0 <= t -> f t = f 0.
Proof.
case: n g => [g ? finim_f t tge0|]; first by have /finim_f [] := tge0; case.
case=> [|n] g fcont finim_f t tge0.
  have /finim_f [i ->] := tge0; have /finim_f [j ->] := lerr (0 : R).
  by rewrite !ord1.
case: (eqVneq (f t) (f 0)) => // ftnef0.
set fl := minr (f 0) (f t); set fr := maxr (f 0) (f t).
have ltflr : fl < fr.
  rewrite /fr; case: maxrP => [left0|ltf0t].
    by rewrite /fl minr_r // ltr_def eq_sym ftnef0 left0.
  by rewrite /fl minr_l // ltrW.
set img := [pred x | (fl < x) && (x \in g @` setT)].
have imgfr : (g @` setT) fr.
  rewrite /fr; case: maxrP => _.
    by have /finim_f [i] := lerr (0 : R); exists i.
  by have /finim_f [i] := tge0; exists i.
have imgn0 : reals.nonempty img.
  by exists fr; rewrite !inE ltflr andTb; apply/asboolP.
have infimg : has_inf img.
  by apply/has_infP; split=> //; exists fl; apply/lbP => ? /andP [/ltrW].
have [] := @IVT f _ _ ((fl + inf img) / 2) tge0.
    by move=> s s0t; apply: fcont; rewrite [_ \in _](itvP s0t).
  apply/andP; split.
    rewrite ler_pdivl_mulr // mulrC mul2r ler_add2l.
    by apply: lb_le_inf imgn0 _; apply/lbP => ? /andP [/ltrW].
  rewrite ler_pdivr_mulr // mulrC mul2r ler_add //; first exact: ltrW.
  by apply: inf_lower_bound infimg _ _; apply/andP; split=> //; apply/asboolP.
move=> s s0t fsemid; suff ltfl_inf : fl < inf img.
  have : inf img <= (fl + inf img) / 2.
    apply: inf_lower_bound (infimg) _ _; apply/andP; split; last first.
      have /finim_f [i] : 0 <= s by rewrite (itvP s0t).
      by rewrite fsemid => midegi; apply/asboolP; exists i.
    by rewrite ltr_pdivl_mulr // mulrC mul2r ltr_add2l.
  by rewrite ler_pdivl_mulr // mulrC mul2r ler_add2r lerNgt ltfl_inf.
have imgE : img = pred_of_finset [fset x in
  [seq t <- [seq g i | i : 'I_n.+2] | fl < t]]%fset :> pred R.
  rewrite funeqE => x; rewrite /img /= /pred_of_finset in_fset.
  apply: (@sameP ((fl < x) /\ x \in (g @` setT))); first exact: andP.
  apply: (iffP idP) => [|[ltflx /asboolP [i _ giex]]].
    rewrite mem_filter => /andP [ltflx /mapP [i _ xegi]]; split=> //.
    by apply/asboolP; exists i.
  rewrite mem_filter ltflx andTb; apply/mapP; exists i => //.
  by rewrite enumT.
rewrite imgE; set A := [fset x in _]%fset.
have : inf (pred_of_finset A) \in A.
  by apply: inf_in_finset; rewrite -[X in has_inf X]imgE.
by rewrite /A in_fset mem_filter => /andP [].
Qed.

Lemma poly2_factor (a b c x : R) :
  a != 0 -> a * (x ^+ 2) + b * x + c = 0 ->
  x = (- b + Num.sqrt (b ^+ 2 - 4%:R * a * c)) / (2 * a) \/
  x = (- b - Num.sqrt (b ^+ 2 - 4%:R * a * c)) / (2 * a).
Proof.
move=> ane0 xroot.
set dlt := b ^+ 2 - 4%:R * a * c.
set x1 := (- b + Num.sqrt dlt) / (2 * a).
set x2 := (- b - Num.sqrt dlt) / (2 * a).
suff poly_fact : a * (x ^+ 2) + b * x + c = a * (x - x1) * (x - x2).
  move: xroot; rewrite poly_fact => /eqP; rewrite mulf_eq0 => /orP [].
    by rewrite mulrI_eq0; [rewrite subr_eq0 => /eqP->; left|apply/lregP].
  by rewrite subr_eq0 => /eqP->; right.
rewrite /x1 /x2; case: (lerP 0 dlt) => [dltge0|dltlt0].
  rewrite -mulrA mulrBr mulrBl mulrBl opprB addrA [(x * x + _) + _]addrAC.
  rewrite [_ / _ * x]mulrC -[in RHS]addrA -opprD -mulrDr -mulrDl.
  rewrite addrCA -[- b + _ - _]addrA subrr addr0 -mul2r.
  rewrite invrM ?unitfE // [2 * _ * _]mulrC !mulrA mulrVK ?unitfE //.
  rewrite addrAC mulrN opprK !mulrDr mulrA [a * (x / _ * _)]mulrCA !mulrA.
  rewrite mulrVK ?unitfE // [b * _]mulrC; congr (_ + _ + _).
  rewrite [a * _]mulrC -[_ * a * _]mulrA mulfV // mulr1.
  rewrite ![_ * - _]mulrC !mulrA !mulrDr -!mulrDl !mulrN !mulNr !opprK.
  rewrite [_ * Num.sqrt _]mulrC -addrA addKr -!expr2 sqr_sqrtr // /dlt.
  rewrite opprD addrA subrr opprK add0r -mulrA -invrM ?unitfE //.
  rewrite mulrC !mulrA -mulrA -mulrA [a * _]mulrC mulrVK ?unitfE //.
  by rewrite -natrM -mulrA mulrCA mulVKr // unitfE.
move: xroot; have -> : a * (x ^+ 2) + b * x + c =
  a * ((x + b / (2 * a)) ^+ 2) + (c - b ^+ 2 / (4%:R * a)).
  rewrite [in RHS]expr2 -mulrA mulrDr mulrDl [c - _]addrC addrA !mulrDr.
  rewrite -[_ - _]addrA -[a * _ + _ + _ in RHS]addrA; congr (_ + _ + _).
  rewrite addrA [(x + _) * _]mulrDl mulrDr addrA -mulrDr [x * _]mulrC -mulrDl.
  rewrite -[LHS]addr0 -addrA; congr (_ + _).
    rewrite mulrA; congr (_ * _); rewrite -mulrDl invrM ?unitfE //.
    rewrite mulrC -mulrA [_ * a]mulrC mulVKr ?unitfE // mulrDl.
    exact: splitr.
  rewrite !mulrA [a * _]mulrC -[b * a / _]mulrA invrM ?unitfE //.
  rewrite mulVKr ?unitfE // [b / _ * _]mulrAC -[_ / 2 * _]mulrA -mulrBr.
  rewrite [_^-1 * _]mulrCA invrM ?unitfE // -mulrBr -invrM ?unitfE //.
  by rewrite -natrM subrr !mulr0.
suff : a * (x + b / (2 * a)) ^+ 2 + (c - b ^+ 2 / (4%:R * a)) != 0.
  by move=> pn0 p0; move: pn0; rewrite p0 eq_refl.
have := ane0; rewrite neqr_lt => /orP [alt0|agt0]; last first.
  apply:lt0r_neq0; rewrite ltr_paddl //; first by rewrite pmulr_rge0 // sqr_ge0.
  rewrite subr_gt0 ltr_pdivr_mulr; last by rewrite pmulr_rgt0.
  by rewrite mulrC -subr_lt0.
rewrite -oppr_eq0 opprD; apply: lt0r_neq0; rewrite ltr_paddl //.
  by rewrite oppr_ge0 nmulr_rle0 // sqr_ge0.
rewrite oppr_gt0 subr_lt0 ltr_ndivl_mulr; last by rewrite mulrC nmulr_rlt0.
by rewrite mulrC -subr_lt0.
Qed.

Lemma En0_sol2_const p :
  limS sol K p -> E p != 0 -> forall t, 0 <= t -> (sol p t)..[2] = p..[2].
Proof.
move=> limSKp Epn0 t tge0.
have Kp : K p by apply: subset_limSK_K.
set C1 := - (2 * g%:num + 2 * (E p) / (m%:num * l%:num)).
set C2 := fctrl p / m%:num.
have sol32_val : forall s, 0 <= s ->
  (sol p s)..[3] * (3%:R * g%:num * (sol p s)..[2] + C1) = C2.
  move=> s sge0.
  rewrite /C1 /C2 -(Esol_const limSKp sge0) /E /= (sol1_eq0 limSKp sge0)
    -(En0_fctrlsol_const limSKp Epn0 sge0) -(div_fctrl_mP limSKp sge0).
  rewrite expr0n /= !mulr0 !mul0r add0r addr0 mulrDr mulrA [1 / _]mulrC.
  rewrite mulVKr ?unitfE // mul1r mulrBr addrC; apply: (canLR (subrK _)).
  rewrite -mulNr mulrDr addrC; apply: (canLR (subrK _)).
  by rewrite mulrA; apply: (canLR (mulfK _)) => //; ssring.
have sol423_val s : 0 <= s ->
  (sol p s)..[4] * (3%:R * g%:num * ((sol p s)..[2] ^+ 2 -
  (sol p s)..[3] ^+ 2) + C1 * (sol p s)..[2]) = 0.
  move=> sge0; apply (is_derive_nneg_eq sol32_val sge0); last first.
    exact: is_derive_cst.
  have [_ /(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp; apply: is_derive_eq.
  by rewrite !mxE /=; ssring.
have sol432_val' s : 0 <= s ->
  (sol p s)..[3] * (g%:num / l%:num * (3%:R * g%:num * ((sol p s)..[2] ^+ 2 -
    (sol p s)..[3] ^+ 2) + C1 * (sol p s)..[2]) -
    (sol p s)..[4] ^+ 2 * (12%:R * g%:num * (sol p s)..[2] + C1)) = 0.
  move=> sge0; apply (is_derive_nneg_eq sol423_val sge0); last first.
    exact: is_derive_cst.
  have [_ /(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp; apply: is_derive_eq.
  rewrite Fpendulum4E // !mxE /= addrC; apply: (canLR (subrK _)).
  rewrite -![_ *: _]/(_ * _) mulrA mulrAC mulrA; apply: (canLR (mulfK _)) => //.
  rewrite [in RHS]mulrDl; apply: (canRL (subrK _)).
  rewrite [(sol p s)..[3] * _]mulrDr [in RHS]mulrDl; apply: (canRL (subrK _)).
  rewrite [_ / _ * _]mulrC [in RHS]mulrA [in RHS]mulrA mulrVK ?unitfE //.
  by ssring.
set x1 := (- C1 + Num.sqrt (C1 ^+ 2 - 4%:R * (6%:R * g%:num) *
  (- 3%:R * g%:num))) / (2 * (6%:R * g%:num)).
set x2 := (- C1 - Num.sqrt (C1 ^+ 2 - 4%:R * (6%:R * g%:num) *
  (- 3%:R * g%:num))) / (2 * (6%:R * g%:num)).
set f := fun i : 'I_4 => if i == 0 then - 1 else
                           if i == 1 then 1 else
                             if i == 2 then x1 else x2.
rewrite -[p in RHS]sol0.
apply: (@continuous_finimage_cst (fun s => (sol p s)..[2]) _ f) tge0.
  move=> s sge0; apply: (@differentiable_continuous [normedModType R of R^o]
    [normedModType R of R^o]).
  have [_ /(_ _ sge0) sol_ats]:= sol_is_sol sol0 solP Kp.
  exact/derivable1_diffP.
move=> s sge0.
have circsol : (sol p s)..[2] ^+ 2 + (sol p s)..[3] ^+ 2 = 1.
  suff [] : K (sol p s) by [].
  exact/subset_limSK_K/limSKinvar.
have solroot_imf :
  3%:R * g%:num * ((sol p s)..[2] ^+ 2 - (sol p s)..[3] ^+ 2) +
  C1 * (sol p s)..[2] = 0 -> exists i, (sol p s)..[2] = f i.
  have -> : (sol p s)..[3] ^+ 2 = 1 - (sol p s)..[2] ^+ 2.
    by rewrite -circsol [X in X - _]addrC addrK.
  move=> sol2_val.
  have sol2_root :
    6%:R * g%:num * ((sol p s)..[2] ^+ 2) + C1 * (sol p s)..[2] +
    (- 3%:R * g%:num) = 0.
    by rewrite -sol2_val; ssring.
  case/poly2_factor: sol2_root => {sol2_val} [|sol2_val|sol2_val] //.
    by exists (2%:R); rewrite sol2_val.
  by exists (3%:R); rewrite sol2_val.
case: (eqVneq ((sol p s)..[4]) 0) => [sol4e0|sol4ne0]; last first.
  by have /sol423_val/eqP := sge0; rewrite mulrI_eq0 => [/eqP|]//; apply/lregP.
have /sol432_val' := sge0.
rewrite sol4e0 expr0n /= mul0r subr0.
case: (eqVneq ((sol p s)..[3]) 0) => [sol3e0|sol3ne0].
  move=> _; move: circsol; rewrite sol3e0 expr0n /= addr0.
  rewrite -(expr1n [ringType of R] 2) => /eqP; rewrite eqf_sqr=> /orP [] /eqP->.
    by exists 1.
  by exists 0.
move=> /eqP; rewrite mulrI_eq0; last exact/lregP.
by rewrite mulrI_eq0=> [/eqP|] //; apply/lregP.
Qed.

Lemma En0_sol3_const p :
  limS sol K p -> E p != 0 -> forall t, 0 <= t -> (sol p t)..[3] = p..[3].
Proof.
move=> limSKp Epn0 t tge0.
have circsol s : 0 <= s -> p..[2] ^+ 2 + (sol p s)..[3] ^+ 2 = 1.
  move=> sge0; rewrite -(En0_sol2_const limSKp Epn0 sge0).
  suff [] : K (sol p s) by [].
  exact/subset_limSK_K/limSKinvar.
set g := fun i : 'I_2 => if i == 0 then Num.sqrt (1 - p..[2] ^+ 2)
                                   else - (Num.sqrt (1 - p..[2] ^+ 2)).
rewrite -[p in RHS]sol0.
apply: (@continuous_finimage_cst (fun t => (sol p t)..[3]) _ g) tge0.
  move=> s sge0; apply: (@differentiable_continuous [normedModType R of R^o]
    [normedModType R of R^o]).
  have Kp : K p by apply: subset_limSK_K.
  have [_ /(_ _ sge0) sol_ats]:= sol_is_sol sol0 solP Kp.
  exact/derivable1_diffP.
move=> s sge0.
suff : (sol p s)..[3] ^+ 2 == (Num.sqrt (1 - p..[2] ^+ 2)) ^+2.
  by rewrite eqf_sqr => /orP [/eqP ?|/eqP ?]; [exists 0|exists 1].
have /circsol <- := sge0.
by rewrite -addrA addrCA addrA addrK sqr_sqrtr // sqr_ge0.
Qed.

Lemma En0_sol4_eq0 p :
  limS sol K p -> E p != 0 -> forall t, 0 <= t -> (sol p t)..[4] = 0.
Proof.
move=> limSKp Epn0 t tge0.
have Kp : K p by apply: subset_limSK_K.
have [_ /(_ _ tge0) sol't] := sol_is_sol sol0 solP Kp.
have : (sol p t)..[3] * (sol p t)..[4] == 0.
  rewrite -oppr_eq0 -mulNr; apply/eqP.
  apply (is_derive_nneg_eq (En0_sol2_const limSKp Epn0) tge0); last first.
    exact: is_derive_cst.
  by apply: is_derive_eq; rewrite mxE.
rewrite mulf_eq0 => /orP [] /eqP // sol3eq0.
have /eqP : (sol p t)..[2] * (sol p t)..[4] = 0.
  apply (is_derive_nneg_eq (En0_sol3_const limSKp Epn0) tge0); last first.
    exact: is_derive_cst.
  by apply: is_derive_eq; rewrite mxE.
rewrite mulf_eq0 => /orP [] /eqP // sol2eq0.
have [] : K (sol p t) by apply/Kinvar.
by rewrite sol3eq0 sol2eq0 expr0n /= addr0 => /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma En0_sol3_eq0 p t :
  limS sol K p -> E p != 0 -> 0 <= t -> (sol p t)..[3] = 0.
Proof.
move=> limSKp Epn0 tge0; rewrite En0_sol3_const => //.
case: (eqVneq (p..[3]) 0) => // p3n0.
suff : (Fpendulum (sol p 0))..[4] = 0.
  rewrite Fpendulum4E // sol0 => /eqP; rewrite mulrI_eq0; last exact/lregP.
  by move/eqP.
apply (is_derive_nneg_eq (En0_sol4_eq0 limSKp Epn0) (lerr 0)); last first.
  exact: is_derive_cst.
have Kp : K p by apply: subset_limSK_K.
have [_ /(_ _ (lerr 0))] := sol_is_sol sol0 solP Kp.
exact: is_derive_component.
Qed.

Lemma En0_sol2_eq1 p t :
  limS sol K p -> E p != 0 -> 0 <= t -> (sol p t)..[2] = 1.
Proof.
move=> limSKp Epn0 tge0.
have [] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
rewrite En0_sol3_eq0 // expr0n /= addr0 -{1}(expr1n [ringType of R] 2).
move/eqP; rewrite eqf_sqr => /orP [] /eqP // sol2_eqN1 _.
suff : `|E (sol p t)| < 2 * m%:num * g%:num * l%:num.
  rewrite /E sol1_eq0 // En0_sol4_eq0 // expr0n /= !mulr0 !addr0 mulr0 add0r.
  rewrite sol2_eqN1 -opprD mulrN absrN mulrC !mulrA mulrAC absRE.
  by rewrite -(natrD _ 1 1) addn1 ltr_norml ltrr andbF.
rewrite -[X in _ < X]ger0_norm // absRE -ltr_sqr ?nnegrE // -!normrX.
do 2 rewrite ger0_norm ?sqr_ge0 //.
suff : 2 * (V (sol p t)) / ke%:num < (2 * m%:num * g%:num * l%:num) ^+ 2.
  apply: ler_lt_trans.
  rewrite -mulrA -ler_pdivr_mull // ler_pdivl_mulr // mulrC mulrA.
  by rewrite /V -addrA ler_addl addr_ge0 // pmulr_rge0 // sqr_ge0.
rewrite ltr_pdivr_mulr // -ltr_pdivl_mull // mulrC [_ * ke%:num]mulrC.
have /ltr_le_trans : V (sol p t) < B.
  have [_ Vsolp_s] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
  exact: ler_lt_trans k0_valid.
rewrite /B; apply; apply: ler_pmul => //; apply: ler_pmul => //.
by rewrite ler_expn2r // ?nnegrE // ler_minl lerr orbC.
Qed.

Lemma subset_limSK_homoclinic_orbit : limS sol K `<=` homoclinic_orbit.
Proof.
move=> p limSKp; rewrite homoclinicE; case: (eqVneq (E p) 0) => [Ep0|Epn0].
  have := sol1_eq0 limSKp (lerr _); rewrite sol0 => p10.
  have := Efctrl_psol0_eq0 limSKp (lerr _).
  rewrite sol0 Ep0 mulr0 mul0r add0r => /eqP.
  by rewrite mulrI_eq0 => [/eqP|] //; apply/lregP.
suff Ep0 : E p == 0 by move: Epn0; rewrite Ep0.
rewrite /E -[p]sol0 sol1_eq0 // En0_sol4_eq0 // En0_sol2_eq1 // subrr expr0n /=.
by rewrite !mulr0 !addr0 mulr0.
Qed.

Lemma cvg_to_homoclinic_orbit p : K p ->
  sol p @ +oo --> (homoclinic_orbit : set [uniformType of U]).
Proof.
move=> Kp A [_/posnumP[e] hoe_A]; apply: cvg_to_limS K_compact Kinvar _ Kp _ _.
exists e%:num => // q [r /subset_limSK_homoclinic_orbit hor re_q].
by apply: hoe_A; exists r.
Qed.

End System.