Require Import Reals Psatz Lra RelationClasses.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex
  RInt RInt_analysis Derive_2d.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Require Import complex_core helpers path_independence.

Open Scope program_scope.
Open Scope general_if_scope.

Section CauchyIntegral.
Open Scope C.

Lemma holo_path_local : forall f f' g1 g2 D r t, 
  open D ->
  D (g1 r t, g2 r t) -> 
  (forall z, D (g1 z.1 z.2,g2 z.1 z.2) -> SmoothPath g1 g2 z.1 z.2) ->
  (forall z, D z -> CHolo f f' z) ->
  locally_2d (fun r' t' => CHolo f f' (g1 r' t', g2 r' t')) r t.
Proof.
  move => f f' g1 g2 D r t openD inD smooth holo.
  apply/locally_2d_locally.
  apply: locally_open.
  - apply open_comp with (f0 := fun z => (g1 z.1 z.2, g2 z.1 z.2)) .
    2: apply openD.
    move => x H.
    rewrite -/(continuous _ _).
    move: smooth => /(_ x H). 
    move => [/locally_2d_singleton [H1 _] /locally_2d_singleton [H2 _]].
    apply continuous_pair;simpl;
    apply/continuity_2d_pt_continuous;
    apply/differentiable_continuity_pt; auto.
  - move => *; auto. 
  - simpl; auto.
Qed.


Lemma circ_independence : forall (f: C -> C) z 
  (r1 r2: R) (D: C -> Prop),
  0 <= r1 -> 
  open D -> 
  r1 < r2 ->
  (forall w, r1 <= Cmod (z - w) <= r2 -> D w) ->
  CHolo_on D f ->
  CInt (circC z r1) f =
  CInt (circC z r2) f.
Proof.
  move => f z r1 r2 D ? openD r1_r2 subset [f' holo].
  rewrite /CInt.
  simpl.
  evar ( dg : R -> R -> R*R).
  enough (forall r' t', c_circle' r' t' = ?dg r' t') as dg_eq.
  under RInt_ext => t _.
    rewrite dg_eq.
    simplify_as_R2 (_ + _).
  over.
  symmetry.
  under RInt_ext => t _.
    rewrite dg_eq.
    simplify_as_R2 (_ + _).
  over.
  symmetry.
  apply: (@path_independence_loop 0 (2*PI) r1 r2 
            (fun r t => z.1 + r * cos t)%R
            (fun r t => z.2 + r * sin t)%R
            ).
  - auto.
  - move => r t rbd tbd.
    apply smooth_circ.
  - move => r t rbd tbd.
    apply: holo_path_local.
    + apply openD.
    + apply subset.
      simplify_as_R2 (x in Cmod x).
      rewrite c_circle_norm.
      rewrite Rabs_Ropp Rabs_pos_eq //=.
      lra.
    + move => *; apply smooth_circ.
    + apply holo.
  - move => r rbd.
    repeat replace_Derive.
    rewrite cos_0 sin_0 cos_2PI sin_2PI. 
    auto.
  - move => r' t' //=.
    repeat replace_Derive.
    rewrite /c_circle'.
    simplify_as_R2 LHS;
    simplify_as_R2 RHS.
    auto.
Qed.
      
Lemma cauchy_integral_theorem : forall (f: C -> C) z (D: C -> Prop) (r:posreal),
  open D ->
  CHolo_on D f ->
  (forall w, Cmod (z - w) <= r -> D w) ->
  CInt (circC z r) f = zero.
Proof.
  move => f z D r openD holo subset.
  have? := cond_pos r.
  rewrite -(@circ_independence f z 0 r D ); auto.
  + rewrite /CInt .
    under RInt_ext => t _.
      simpl. rewrite /c_circle /c_circle' ?Cmult_0_l ?Cmult_0_r.
    over.
    rewrite RInt_const.
    rewrite scal_zero_r.
    auto.
  + lra.
  + move => *; apply subset; lra.
Qed.

Lemma rmult_scal : forall (r:R) (z:C),
  (RtoC r) * z = scal r z.
Proof.
  move => r [z1 z2]. unfold_alg; rewrite /prod_scal /scal. unfold_alg.
  simpl.
  by simplify_as_R2 LHS.
Qed.

Open Scope C.
Lemma integral_div_z: forall a (r: posreal), 
  CInt (circC a r) (fun z => /(z-a)) = 2 * PI * Ci.
Proof.
  move => a r.
  have? := cond_pos r. 
  rewrite /CInt split_cint.
  2: shelve.
  simpl.
  simplify_as_R2 RHS.
  rewrite /c_circle /c_circle' //=.
  f_equal.
  - rewrite /compose //=.
    under RInt_ext => t _.
      field_simplify.
    over.
    apply Rlt_0_neq_0.
    field_simplify.
    rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2 /Rsqr.
    field_simplify.
    nra.

    under RInt_ext => t _.
      rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2.
      set p := (0 / _)%R.
      replace p with (0)%R;
      rewrite {}/p.
    over.
    lra.
    rewrite RInt_const /scal //= /mult //=. lra.
  - rewrite /compose //=.
    under RInt_ext => t _.
      field_simplify.
    over.
    apply Rlt_0_neq_0.
    field_simplify.
    rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2 /Rsqr.
    field_simplify.
    nra.
    under RInt_ext => t _.
      set p := (_ / _)%R.
      replace p with (1)%R;
      rewrite {}/p.
    over.
    field_simplify_eq; auto.

    apply Rlt_0_neq_0.
    field_simplify.
    rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2 /Rsqr.
    field_simplify.
    nra.

    rewrite RInt_const /scal //= /mult //=. lra.
  Unshelve.
  apply/(@ex_CInt_RInt (fun q =>/ (q - a)) _).
  apply cts_CInt.
  apply: div_z_continuous_contour.
Qed.

Lemma squeeze: forall {K: AbsRing} {T: NormedModule K} (x:T),
   (forall (eps: posreal), norm x < eps) -> x = zero.
Proof.
  move => ? ? x sqz.
  destruct (Rle_dec 0 (norm x)).
  destruct r. 
  - move: sqz => /(_ (mkposreal _ H)) Q.
    simpl in *.
    lra.
  - apply norm_eq_zero; auto.
  - contradict n. 
    apply norm_ge_0.
Qed.

Lemma squeeze_le: forall {K: AbsRing} {T: NormedModule K} (x:T),
   (forall (eps: posreal), norm x <= eps) -> x = zero.
Proof.
  move => ? ? x sqz.
  apply squeeze => eps.
  have:= (@sqz (pos_div_2 eps)).
  simpl.
  have ?:= cond_pos eps.
  lra.
Qed.

Tactic Notation "max_min_contour" hyp(H) := 
  rewrite Rmin_left in H; last (by left; apply endpoint_interval);
  rewrite Rmax_right in H; last (by left; apply endpoint_interval).
  

Lemma CInt_abs_bound: forall f g M, 
  cts_on_contour f g -> 
  (forall t, l_end g <= t <= r_end g -> abs (f (gamma g t)) <= M) ->
  norm (CInt (g) f) <= scal M (RInt (fun t => norm (gamma' g t)) (l_end g) (r_end g)).
Proof.
  move => f g M cts fbd.
  rewrite /CInt.
  apply: norm_RInt_le.
  3: apply: RInt_correct; apply/ ex_CInt_RInt; apply/ cts_CInt; auto.
  1: left; apply: endpoint_interval.
  2: { 
     rewrite -RInt_scal.
     instantiate(1:= fun x => scal M (norm (gamma' g x))).
     apply: RInt_correct. 
     all: apply ex_RInt_continuous => t tbd; max_min_contour tbd.
     all: auto_cts.
     all: apply continuous_comp; last apply: filterlim_norm.
     all: apply cts_derive; auto.
  }
  move => t tbd.
  simpl.
  set p := norm _.
  `Begin Rle p. { rewrite /p.

  | {( norm( scal (f (gamma g t)) (gamma' g t)) )}  unfold_alg;
      rewrite /prod_norm /norm /Cmod -?Rsqr_pow2 /= /abs /= -?Rsqr_abs.

  | {( (abs (f (gamma g t)) * norm _) )%R}  apply: norm_scal.

  | {( (M * norm _) )%R}  
    apply: Rmult_le_compat_r; first (by apply: norm_ge_0);
    by apply: fbd.
  `Done.
  }
  auto.
Qed.

Program Definition pos_div_2PI (r: posreal): posreal := 
  mkposreal (r / (2 * PI))%R _.
Obligation 1.
Proof.
  apply: RIneq.Rdiv_lt_0_compat.
  - apply: cond_pos.
  - have ?:= PI_RGT_0; lra.
Qed.

Open Scope C.

Lemma pow_n_abs_C : forall (z:C) n, Cmod (pow_n z n)%C = (pow_n (Cmod z) n).
Proof.
  move => z.
  elim.
  - simpl. apply Cmod_1.
  - move => n IH //=. 
    rewrite Cmod_mult IH //=.
Qed.


Lemma pow_n_cts : forall z n, continuous (fun z:C => pow_n z n) z.
Proof.
  move => z.
  elim.
  - simpl; auto_cts. 
  - move => n IH //=. 
    apply/cts_topology_1.
    apply/cts_topology_2.
    apply: continuous_mult; auto_cts.
Qed.

Hint Extern 5 (continuous _ _ ) => 
  (apply: ex_derive_continuous; eexists; eauto) : teardown_leaf.

Lemma cauchy_integral_aux: forall f (r eps: posreal) a,
  CHolo_on (ball a r) f ->
  exists (del: posreal), 
  forall n: nat, 
  del < r /\
  (del ^ n) * norm (CInt (circC a del) (fun z => (f(z) - f(a))/ (pow_n (z-a) (S n))))  
    <= eps.
Proof.
  move => f r eps a holo.
  have: continuous f a. {
    case: holo => f' /(_ a (ball_center _ _)) [H ?].
    auto_cts.
  }
  move => /cts_topology_1 
          /cts_topology_2 
          /filterlim_locally /(_ (pos_div_2PI eps)) [del h].
  have ?:= cond_pos del.
  pose del2 := mkposreal (Rmin (pos_div_2 del) (pos_div_2PI r)) (
    ltac:( apply Rmin_pos; apply cond_pos)).
  have ?:= cond_pos eps.
  have ?:= cond_pos r.
  have ?:= cond_pos del2.
  have ?:= PI_RGT_0.
  have ?:= PI_4.
  have ?:= PI2_3_2.
  have ?: /(2*PI) < /1 by apply Rinv_lt_contravar; lra.
  have ?: (0 < 2*PI) by lra.
  have ?: (0 < /(2*PI)) by apply Rinv_0_lt_compat.
  have ?: (r / (2*PI) < r*1) by  apply Rmult_lt_compat_l; lra.
  have ?: (0 < r /(2*PI) ) by apply Rdiv_lt_0_compat; lra.
  have del2_lt_r: (del2 < r) by apply: Rle_lt_trans; first apply Rmin_r; simpl; lra.
  have ?: (del2 < del) by apply: Rle_lt_trans; first apply Rmin_l; simpl; lra.
  exists del2 => n.
  set m := S n.
  set p := norm _.

  `Begin Rle p. {rewrite /p.
  
  |  {(  scal ((eps/(2*PI))/(del2^m )%R) _ )%R} apply: CInt_abs_bound .
    {
      auto_cts.
      apply/continous_C_AbsRing.
      apply: continuous_mult.
      - apply: continuous_minus; last by auto_continuous_aux.
        eapply filterlim_filter_le_1.
        2: apply: ex_derive_continuous. 
        1: move => P; apply prod_c_topology_eq.
        move: holo => [f' holo].
        exists (f' (gamma (circC a del2) z)).
        apply/diff_topology_change .
        apply holo.
        unfold_alg.
        set q := (x in Cmod x).
        simplify_as_R2 e q.
        rewrite c_circle_norm.
        rewrite Rabs_pos_eq.
        + eapply Rle_lt_trans; first apply Rmin_r.
          lra.
        + left; 
          apply Rmin_pos; try lra.
      - apply /continous_C_AbsRing.
        apply: continuous_comp; first  
          (apply: (@continuous_comp _ _ _ _ (fun z:C => pow_n z m));
          [repeat auto_continuous_aux| apply pow_n_cts ]).
        apply: continuous_Cinv.
        simpl => H.
        set q := (_ + c_circle _ _ - _) in H.
        have: (Cmod (pow_n q (S n)) = 0) by
          rewrite -Cmod_0; f_equal.
        move {H}.
        simplify_as_R2 e q.
        rewrite pow_n_abs_C c_circle_norm.
        move => H. 
        contradict H.
        apply Rlt_0_neq_0.
        rewrite Rabs_pos_eq.
        2: left; apply: Rmin_pos; lra.
        rewrite pow_n_pow.
        apply: pow_lt.
        apply: cond_pos del2.
  }
  {
    move => t tbd.
    rewrite (@lock _ m).
    unfold_alg.
    rewrite Cmod_div;
    set q := a + _ - a;
    simplify_as_R2 e q.
    - rewrite pow_n_abs_C  ?c_circle_norm.
      rewrite Rabs_pos_eq; last by left.
      apply Rmult_le_compat_r; first by (
        left;
        (rewrite Rinv_pow; last by apply Rlt_0_neq_0);
        apply pow_lt; 
        apply Rinv_0_lt_compat).
      left.
      apply h.
      unfold_alg.
      set q := a + _ + _.
      simplify_as_R2 e q.
      rewrite c_circle_norm.
      rewrite Rabs_pos_eq; last by left.
      eapply Rle_lt_trans; first apply Rmin_l.
      lra.
    - apply/ Cmod_gt_0.
      rewrite pow_n_abs_C c_circle_norm.
      rewrite Rabs_pos_eq; last by left.
      apply pow_lt.
      apply Rmin_pos; lra.
  }
  | {( (eps/(2*PI) /del2^m) * (del2 * 2*PI)  )%R}  
                                                apply Rmult_le_compat_l.
    {

      left.
      apply Rmult_lt_0_compat. 
      - apply Rmult_lt_0_compat; lra.
      - apply Rinv_0_lt_compat; 
        apply pow_lt.
        auto.
    }
    {
      under RInt_ext => t do rewrite /norm //= c_circle'_norm.
      rewrite RInt_const.
      unfold_alg.
      rewrite Rabs_pos_eq; last by left.
      lra.
    }
  | {( pos eps/(del2^n) )%R} rewrite /m //=; field_simplify. 
    1: by apply Rlt_0_neq_0; apply pow_lt. 
    split;[|split].
    1-3: by apply Rlt_0_neq_0; try (apply pow_lt); try lra.
  `Done. }
  move =>H.
  split; first by [].
  apply (@Rle_trans _ (del2^n * (eps / del2 ^n))).
  - apply Rmult_le_compat_l; last by [].
    left; apply: pow_lt; lra.
  - field_simplify; first by reflexivity.
    apply: Rlt_0_neq_0. apply: pow_lt; lra.
Qed.

Lemma CInt_ext : forall f g gam, 
  (forall t, l_end gam <= t <= r_end gam -> f (gamma gam t) = g (gamma gam t)) ->
  CInt (gam) f = CInt (gam) g.
Proof.
  move => f g gam ext.
  rewrite /CInt.
  under RInt_ext => t tbd.
   rewrite ext.
  over.
  2: auto.
  rewrite Rmin_left in tbd.
  rewrite Rmax_right in tbd.
  lra.
  all: left; apply endpoint_interval.
Qed.

Lemma CInt_ext_global : forall f g gam, 
  (forall z,  f z = g z) ->
  CInt (gam) f = CInt (gam) g.
Proof.
  move => f g gam ext.
  under CInt_ext => t _ do rewrite ext.
  auto.
Qed.

Lemma CInt_plus : forall f g gam,
  cts_on_contour g gam -> 
  cts_on_contour f gam -> 
  CInt (gam) (fun z => f z + g z) = 
  CInt (gam) f + CInt ( gam) g.
Proof.
  move => f g ctsf ctsg gam.
  rewrite /CInt.
  under RInt_ext => t _ do rewrite Cmult_plus_distr_r.
  rewrite RInt_plus; first by [];
  apply ex_CInt_RInt, cts_CInt; auto.
Qed.

Lemma CInt_mult_Ci : forall f gam,
  cts_on_contour f gam -> 
  CInt (gam) (fun z => Ci * f z) = 
  Ci * CInt (gam) f .
Proof.
  move => f gam ctsf.
  rewrite /CInt split_cint /compose //=.
  under RInt_ext => t tbd do field_simplify.
  under [x in (_,x)]RInt_ext => t tbd do field_simplify.

  rewrite split_cint.
  set p := RHS.
  simplify_as_R2 e p.
  symmetry.
  rewrite /compose.
  simpl.
  f_equal.
  set p := (x in Ropp x).
  replace (-p)%R with (opp p); last by unfold_alg.
  rewrite /p.
  rewrite -RInt_opp.
  under RInt_ext => t _. 
    unfold_alg.
    field_simplify.
  over.
  auto.
  - apply ex_RInt_continuous => t tbd.
    rewrite Rmin_left in tbd.
    rewrite Rmax_right in tbd.
    2-3: left; apply endpoint_interval.
    repeat auto_continuous_aux; apply continuous_comp;
    try auto_continuous_aux.
    1,3: apply continuous_comp; last by apply ctsf.
    3,4: by apply cts_derive.
    1,2: apply: ex_derive_continuous; eexists; apply contour_derive; auto.
  - apply/ ex_CInt_RInt.
    apply: cts_CInt .
    auto.
  - apply (@ex_CInt_RInt (fun z => Ci * f z)).
    apply: cts_CInt .
    apply cts_on_contour_mult; last by auto.
    move => *. apply continuous_const.
Qed.

Lemma ReImSplit_plus : forall z, 
  z = Re z + Ci * Im z.
Proof.
  move => z.
  rewrite /Re /Ci/Im /Cmult.
  simpl.
  set p := RHS.
  simplify_as_R2 e p.
  rewrite -surjective_pairing.
  auto.
Qed.

Lemma CInt_mult : forall f k gam,
  cts_on_contour f gam -> 
  CInt (gam) (fun z => k * f z) = 
  k * CInt (gam) f .
Proof.
  move => f k gam cstf.
  rewrite (@ReImSplit_plus k).
  under CInt_ext_global => t do
    rewrite Cmult_plus_distr_r .
  rewrite CInt_plus. 
  2-3 : by
    apply: cts_on_contour_mult; last by [];
    move => *; apply: continuous_const.
  rewrite {1}/CInt. 
  under RInt_ext => t _ do
    rewrite -Cmult_assoc -scal_R_Cmult.
  rewrite RInt_scal; last by 
    apply/ ex_CInt_RInt;
    apply: cts_CInt .
  rewrite scal_R_Cmult.
  rewrite [RHS]Cmult_plus_distr_r.
  rewrite -/(CInt _).
  f_equal.
  rewrite {1}/CInt. 
  under RInt_ext => t _.
    set p := _ * _ * _ * _.
    replace p with (Im k * (Ci * f (gamma gam t) * gamma' gam t )); last by
      rewrite /p; field_simplify.
    rewrite -scal_R_Cmult.
  over.
  rewrite RInt_scal.
  - rewrite scal_R_Cmult.
    rewrite -/(CInt _ (fun z => Ci * f z)).
    rewrite CInt_mult_Ci; last by [].
    field_simplify.
    auto.
  - apply (@ex_CInt_RInt (fun z => Ci * f z)).
    apply cts_CInt .
    apply cts_on_contour_mult; last by [].
    move => *. apply continuous_const.
Qed.

Lemma holo_ball_contour: forall f a (r: posreal) D,
  (forall w, Cmod (a - w) <= r -> D w) ->
  CHolo_on D f ->
  cts_on_contour f (circC a r).
Proof.
  move => f a r D subset [f' holo] t tbd.
  apply/continous_C_AbsRing_1.
  apply: ex_derive_continuous.
  exists (f' (gamma (circC a r) t)).
  apply holo.
  apply subset.
  unfold_alg.
  
  set p := (x in Cmod x).
  replace p with (-c_circle r t); last by
    rewrite /p; field_simplify.
  rewrite Cmod_opp c_circle_norm_2 Rabs_pos_eq.
  reflexivity.
  left.
  apply cond_pos.
Qed.

Lemma Cmod_sym: forall z w, 
  Cmod( z-w) = Cmod (w - z).
Proof.
  move => z w .
  replace (z-w) with (-(w-z)). 
  - rewrite Cmod_opp //=.
  - field_simplify; auto.
Qed.

Lemma Cminus_0_eq : forall z w, 
  z - w = 0 <-> z = w.
Proof.
  move => z w.
  split. 
  - destruct z,w.
    rewrite /Cminus /Cplus /Copp //=.
    replace (RtoC 0) with (R0,R0); last by simpl.
    move => /pair_equal_spec [??].
    f_equal; lra.
  - move => ->.
    rewrite /Cminus Cplus_opp_r.
    auto.
Qed.

Lemma open_neq_C: forall a, 
  open (fun z:C => z <> a).
Proof.
  move => a z neq.
  apply/prod_c_topology_eq.
  have := Cmod_ge_0 (z-a).
  case. 
  - move => H.
    exists (mkposreal _ H).
    move => x xball.
    simpl in *.
    move => H'.
    subst.
    move: xball.
    unfold_alg.
    rewrite -/(Cminus _ _) Cmod_sym.
    lra.
  - move => H'. 
    contradict neq.
    symmetry in H'.
    move: H' => /Cmod_eq_0 ?.
    by apply/ Cminus_0_eq.
Qed.



Theorem cauchy_integral_formula_center: forall f (r:posreal) D a, 
  open D ->
  (forall w, Cmod (a - w) <= r -> D w) ->
  CHolo_on D f ->
  1/(2*PI* Ci) * CInt (circC a r) (fun z => f(z) / (z-a))
  = f(a).
Proof.
 move => f r D a openD subset holo. 

 
 `Begin eq (CInt (circC a r) (fun z => (f(z) - f(a))/ (z-a))). {

 | {( CInt 
        ( circC a r)  
        (fun z : C => ((f z)/(z-a)) + (-(f a) / (z - a))) 
   )}
    under CInt_ext_global => z do
      rewrite /Cdiv /Cminus Cmult_plus_distr_r
              -?/(Cdiv _ _)  -?/(Cminus _ _) .
 | {( CInt _  (fun z : C => (f z)/(z-a)) 
    + CInt _  (fun z : C => -(f a)/(z-a)) 
   )} rewrite CInt_plus.
   
   1,2: apply cts_on_contour_mult.
   1: move => *; apply continuous_const.
   1,3: apply: div_z_continuous_contour.
   1: apply: holo_ball_contour; eauto.

 | {( _ + (-f(a)) * CInt _  (fun z : C => /(z-a)))} 
   f_equal; rewrite CInt_mult .

   1: apply: div_z_continuous_contour.

 | {( _ + (-f(a)) * (2*PI*Ci) )} idtac.
   f_equal;f_equal; apply integral_div_z.
 `Done.
 }

 move => H.

 have ->: CInt (circC a r) (fun z : C => f z / (z - a)) = f a * (2 * PI * Ci) .
 - set p := LHS. 
   replace p with (p + (- f a*(2*PI*Ci)) + f a * 2 * PI * Ci); last by 
     field_simplify.
   rewrite /p -{}H.
   rewrite /zero //= /prod_zero /zero //=.
   field_simplify_eq.   
   rewrite -[RHS]Cplus_0_l.
   f_equal.
  apply: squeeze_le => eps.
  have := @cauchy_integral_aux f r eps a.
  case. {
    apply: CHolo_subset; last eauto.
    move => z zball.
    apply subset.
    left.
    rewrite Cmod_sym.
    apply zball.
  }
  move => del /(_ 0)%nat [delbd H].
  rewrite //= Rmult_1_l in H.
  apply: Rle_trans; last by apply H.
  right.
  f_equal.
  symmetry.
  under CInt_ext_global => t do rewrite mult_one_r.  
  pose D' := fun z => z<> a /\ D z.
  apply (@circ_independence _ _ _ _ D').
  1: left; apply cond_pos.
  1: apply open_and.
  2: auto.
  1: apply open_neq_C.
  1: auto.
  move => w bd. 
  have ?:= cond_pos del.
  split; last (apply subset; lra).
  move => ?; subst.
  move: bd.
  rewrite /Cminus Cplus_opp_r Cmod_0.
  lra.

  rewrite /Cdiv.
  apply CHolo_on_mult.
  {
    apply CHolo_on_minus; last by apply CHolo_on_const.
    apply: CHolo_subset; last by apply holo.
    move => z.
    rewrite /D'.
    tauto.
  }
  {
    apply: CHolo_on_div; first apply: CHolo_on_minus.
    - apply CHolo_on_id.
    - apply CHolo_on_const.
    - move => z [H' _]Q.
      contradict H'.
      apply/Cminus_0_eq.
      auto.
  }
  - field_simplify_eq; first by auto.
    repeat split; move => Q; inversion Q; try lra.
    have:= PI_RGT_0.
    lra.
Qed.

Lemma Cmod_cos_sin: forall t, Cmod (cos t, sin t) = 1.
Proof.
  move => t.
  rewrite /Cmod /fst /snd Rplus_comm -?Rsqr_pow2 sin2_cos2 sqrt_1 //=.
Qed.

Lemma Cmod_lt_neq: forall z w, 
  Cmod z < Cmod w -> z <> w.
Proof.
  move => z w + H.
  rewrite H.
  lra.
Qed.

Theorem cauchy_integral_formula: forall f (r: posreal) D a z, 
  open D ->
  CHolo_on D f ->
  (forall w, Cmod (a - w) <= r -> D w) ->
  @ball (AbsRing_UniformSpace C_AbsRing) a r z -> 
  1/(2*PI* Ci) * CInt (circC a r) (fun w => f(w) / (w-z)) = f(z).
Proof.
  move => f r D a z openD. 
  copy.
  move => [f' holo'] holo subset zball.
  have ? := cond_pos r.
  have ?:= @Cmod_ge_0 (z-a).
  pose delr' := (r - (Cmod (z -a)%C))%R.
  have delrpos: 0 < delr'. {
    move: zball.
    unfold_alg.
    rewrite -/(Cminus _ _).
    rewrite /delr'.
    lra.
  }
  pose delr := mkposreal _ delrpos.
  have?: delr <= r. {
    rewrite /delr /delr' /=.
    lra.
  }

  rewrite -[RHS](@cauchy_integral_formula_center f (delr) D z); simpl.
  2: move => *; apply prod_c_topology_eq; apply openD; auto.
  2: { 
    move => w H. 
    apply subset.
    `Begin Rle (Cmod (a - w)). {
    | {( Cmod ((a - z) + (z- w)) )} right; f_equal; field_simplify.

    | {( Rplus (Cmod (a - z)) (Cmod (z- w)) )} apply: Cmod_triangle.

    | {( Rplus _ (delr') )} apply: Rplus_le_compat_l; auto.

    | {( pos r )} rewrite Cmod_sym /delr'; field_simplify.
    `Done.
    }
    auto.
  }
  2: auto.
  f_equal.
  rewrite /CInt.
  pose h1 := (fun x' t' => (x' * z.1 + (1-x')*a.1 + (x'*delr' + (1-x')*r) * cos t'))%R.
  pose h2 := (fun x' t' => (x' * z.2 + (1-x')*a.2 + (x'*delr' + (1-x')*r) * sin t'))%R.
  simpl.
  evar ( dg : R -> R -> R*R).
  enough (forall t', c_circle' delr' t' = ?dg 1 t') as dg_eq1.
  enough (forall t', c_circle' r t' = ?dg 0 t') as dg_eq2.
  under RInt_ext.
    move => t _.
    replace (a + c_circle r t) with (h1 0 t, h2 0 t ).
    rewrite dg_eq2.
  over.
  rewrite /c_circle /h1 /h2.
  set p := RHS.
  simplify_as_R2 e p.
  set p := LHS.
  simplify_as_R2 e p.
  auto.
  symmetry.
  under RInt_ext.
    move => t _.
    replace (z + c_circle delr' t) with (h1 1 t, h2 1 t ).
    rewrite dg_eq1.
  over.
  rewrite /c_circle /h1 /h2.
  set p := RHS.
  simplify_as_R2 e p.
  set p := LHS.
  simplify_as_R2 e p.
  auto.
  symmetry.
  pose D' := fun w => w <> z /\ D w.
  have : CHolo_on D' (fun w : C => f w / (w - z)). {
    rewrite /Cdiv.
    apply: @CHolo_on_mult .
    - apply: CHolo_subset.
      2: apply holo.
      rewrite /D'.
      tauto.
    - apply: CHolo_on_div.
      apply CHolo_on_minus.
      apply CHolo_on_id.
      apply CHolo_on_const.
      rewrite /D'.
      move => w [wneqz _].
      rewrite Cminus_0_eq.
      auto.
  }
  move => [fz' holo_fz].
  apply : (@path_independence_loop
              0 (2*PI)
              0 1
              h1 h2
              _ _
              (fun w => f w / (w-z) ) 
              fz'
              ).
  - lra.
  - move => *; apply: smooth_translate_circ.
  - move => x t xbd tbd.
    apply (@holo_path_local _ _ _ _ D').
    1: apply open_and.
    3: split.
    + apply open_neq_C.
    + move => *; apply/prod_c_topology_eq; apply: openD; auto.
    + rewrite /h1/h2. 
      move => /Cminus_0_eq.
      set p := (y in y = _).
      replace p with ((x * ((z - a) + c_circle (delr' -r) t)) + 
                      (a - z) + c_circle r t ); last by (
        rewrite /p;
        set u := RHS;
        simplify_as_R2 e u;
        set v := LHS;
        simplify_as_R2 e v).
      clear p.
      rewrite Cplus_comm.
      set p := (_ * _ + _).
      replace p with (
         -(x * ((a - z) + c_circle (Cmod(a-z)) t) - (a-z))
                       ); last (
        rewrite /p /delr' Cmod_sym;
        set u := RHS;
        simplify_as_R2 e u;
        set v := LHS;
        simplify_as_R2 e v;
        f_equal; field_simplify; auto).
      move =>/Cminus_0_eq /esym.
      apply: Cmod_lt_neq.
      rewrite c_circle_norm_2 Rabs_pos_eq.
      2: left; apply cond_pos.
      clear p.
      set p := (x in Cmod x).
      replace p with ((1-x) * (z-a) + x * (c_circle (Cmod (z-a)) t)); last by
        rewrite Cmod_sym /p; field_simplify.
      apply: Rle_lt_trans.
      1: apply Cmod_triangle.
      rewrite ?Cmod_mult ?Cmod_R Cmod_cos_sin ?Rabs_pos_eq.
      2: apply Cmod_ge_0.
      have ->: (Cmod (1-x) = (1-x)%R). {
        rewrite/Cmod //= ?Rplus_0_l Ropp_0 Rmult_0_l Rplus_0_r Rmult_1_r
               -/(Rsqr _) sqrt_Rsqr_abs Rabs_pos_eq //=; 
        lra.
      }
      2: lra.
      move: zball.
      unfold_alg.
      rewrite -/(Cminus _ _).
      lra.
    + apply subset.
      rewrite /h1 /h2.
      set p := (x in Cmod x).
      replace p with (x*(a - z) + 
        (c_circle (x*Cmod (z-a) - r) t) ); last by (

        rewrite /p /delr' Cmod_sym;
        set u := RHS;
        simplify_as_R2 e u;
        set v := LHS;
        simplify_as_R2 e v;
        f_equal; field_simplify; auto).
      apply: Rle_trans; first apply Cmod_triangle.
      rewrite c_circle_norm_2 Rabs_minus_sym Rabs_pos_eq.
      * rewrite Cmod_mult Cmod_sym Cmod_R Rabs_pos_eq; last lra. 
        field_simplify.
        reflexivity.
      * rewrite -Rminus_le_0.
        apply (Rle_trans _ (1*Cmod (z-a))).
        apply: Rmult_le_compat_r.
        2: lra.
        1: apply Cmod_ge_0.
        left. 
        move: zball.
        unfold_alg.
        rewrite -/(Cminus _ _).
        lra.
    + move => *; apply smooth_translate_circ.
    + apply holo_fz.
  - move => x xbd.
    rewrite /h1/h2.
    split; first by 
      rewrite cos_0 sin_0 cos_2PI sin_2PI. 
    f_equal.
    + under Derive_ext => t do rewrite cos_0.
      symmetry.
      under Derive_ext => t do rewrite cos_2PI.
      auto.
    + under Derive_ext => t do rewrite sin_0.
      symmetry.
      under Derive_ext => t do rewrite sin_2PI.
      auto.
  - rewrite /c_circle' //= /Cmult //=.
    move => t'.
    f_equal.
    + symmetry. 
      apply: is_derive_unique. 
      auto_derive; auto.
      field_simplify.
      auto.
    + symmetry. 
      apply: is_derive_unique. 
      auto_derive; auto.
      field_simplify.
      auto.
  - rewrite /c_circle' //= /Cmult //=.
    move => t'.
    f_equal.
    + symmetry. 
      apply: is_derive_unique. 
      auto_derive; auto.
      field_simplify.
      auto.
    + symmetry. 
      apply: is_derive_unique. 
      auto_derive; auto.
      field_simplify.
      auto.
Qed.
End CauchyIntegral.