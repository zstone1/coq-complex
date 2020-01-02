
Require Import Reals Psatz Lra RelationClasses List.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex
  RInt RInt_analysis Derive_2d Compactness
  Series PSeries Lim_seq.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Require Import helpers complex_core path_independence cauchy_integral compact_convergence.

Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.

Definition contour_equiv g1 g2 := 
  (l_end g1 = l_end g2) /\
  (r_end g1 = r_end g2) /\ 
  (forall t, l_end g1 <= t <= r_end g1 -> 
    gamma g1 t = gamma g2 t) /\
  (forall t, l_end g1 <= t <= r_end g1 -> 
    gamma' g1 t = gamma' g2 t).

Lemma CInt_gamma_ext: forall g1 g2 f, 
  contour_equiv g1 g2 ->
  CInt g1 f = CInt g2 f.
Proof.
  move => g1 g2 f [lend [rend [ext ext']]].
  rewrite /CInt lend rend.
  under RInt_ext => t.
    rewrite Rmin_left; last by (left; apply endpoint_interval).
    rewrite Rmax_right; last by (left; apply endpoint_interval).
    move => bd.
    rewrite ext; last by lra.
    rewrite ext'; last by lra.
  over.
  auto.
Qed.

Lemma bounded_derive_contour: forall g1, exists g2,
  contour_equiv g1 g2 /\
  exists M : posreal, forall z, norm (gamma' g2 z) < M. 
Proof.
  move => g1. 
  pose gam2 := {|
    gamma := extension_C1 (gamma g1) (gamma' g1) (l_end g1) (r_end g1);
    gamma' := extension_C0 (gamma' g1) (l_end g1) (r_end g1);
    l_end := l_end g1;
    r_end := r_end g1;
    endpoint_interval := endpoint_interval g1;
    contour_derive := ltac:( move => *; apply:extension_C1_is_derive;
    [ rewrite /Rbar_le; left; apply: endpoint_interval
    | rewrite /Rbar_le; move => *; apply contour_derive; auto
    ]);
    cts_derive := ltac:(move => *; apply: extension_C0_continuous;
    [ rewrite /Rbar_le; left; apply: endpoint_interval
    | rewrite /Rbar_le; move => *; apply cts_derive; auto
    ])
      |}.
  exists gam2.
  repeat split.
  - move => * //=. symmetry. apply: extension_C1_ext; simpl; auto; lra.
  - move => * //=. symmetry. apply: extension_C0_ext; simpl; auto; lra.
  - have := bounded_continuity (gamma' g1) (l_end gam2) (r_end gam2).
    case. {
        move => t tbd.
        simpl.
        apply: cts_derive.
        auto.
    }
    move => M Mbd.
    have: (0 < M ). {
      apply: Rle_lt_trans.
      apply: norm_ge_0 (gamma' gam2 (l_end gam2)).
      simpl.
      rewrite extension_C0_ext; simpl; 
        [| reflexivity | left; apply: endpoint_interval].
      apply Mbd.
      split; [reflexivity | left; apply: endpoint_interval ].
    }
    move => Q.
    exists (mkposreal _ Q).
    simpl.
    move => z.
    rewrite /extension_C0.
      destruct_match.
      destruct_match.
      all: apply Mbd; auto.
      all: split; try reflexivity;
           try (left; apply: endpoint_interval).
Qed.

Definition contour_inside (g:Contour) D:= 
  forall t, l_end g <= t <= r_end g -> D (gamma g t).

Hint Extern 3 (continuous (gamma' _) _) => apply: cts_derive : teardown_leaf.

Section FilterlimFunc.

Context {T:Type} {F: (T -> Prop) -> Prop } {FF: Filter F}.

Open Scope C.
Import FunctionalExtensionality.
Context {FF': ProperFilter F}.
Open Scope C.
Lemma uniform_limits_CInt : forall 
  (f_: T -> C -> C)
  (flim : C -> C)
  (gam: Contour),
  filterlim (fun u z => f_ u (extension_C0 (gamma gam) (l_end gam) (r_end gam) z)) F
    (@locally (fct_UniformSpace _ _) 
    (fun z => flim (extension_C0 (gamma gam) (l_end gam) (r_end gam) z))) ->
  (forall u, cts_on_contour (f_ u) gam) ->
  filterlim (fun u => CInt gam (f_ u)) F (locally (CInt gam flim)).
Proof.
  move => f_ flim gam  unif cts.

  wlog: gam unif cts / 
    exists M : posreal, forall z : R_UniformSpace, norm (gamma' gam z) < M. {
      have:= bounded_derive_contour gam.
      move => [gam2 [eqv bdd]] H'.
      rewrite (@CInt_gamma_ext gam gam2); auto.
      eapply filterlim_ext.
        move => t.
        rewrite (@CInt_gamma_ext gam gam2); auto.
      reflexivity.
      move: eqv => [lends [rends[ext1 ext2]]].
      pose gamma_bar2 :=extension_C0 (gamma gam2) (l_end gam2) (r_end gam2).
      pose gamma_bar :=extension_C0 (gamma gam) (l_end gam) (r_end gam).
      have H: (forall t, gamma_bar2 t= gamma_bar t). {
        move => t.
        rewrite /gamma_bar /gamma_bar2 /extension_C0.
        rewrite -rends -lends.
        destruct_match.
        destruct_match.
        all: symmetry; apply ext1; auto; split; try reflexivity.
        all: left;apply endpoint_interval.
      }
      apply (@H' gam2).
      - apply: (@filterlim_ext _ _ _ _ _ (fun u z => (f_ u (gamma_bar z)))).
          move => x.
          apply functional_extensionality => t.
          f_equal.
          symmetry.
          apply H.
        set h := (x in locally x).
        have ->: (h = (fun z => flim (gamma_bar z))).
        2: auto.
        apply functional_extensionality => t.
        rewrite /h.
        f_equal.
        apply H.
      - move => u t tbd.
        rewrite -ext1; first apply cts.
        all: rewrite lends rends; lra.
      - auto.
  }
  move => bounded.
  have ? : l_end gam < r_end gam by apply endpoint_interval.

  rewrite /CInt.
  eapply filterlim_ext.
    move => x.
    eapply RInt_ext. move => t tbd.
      rewrite Rmin_left in tbd; last by left.
      rewrite Rmax_right in tbd; last by left.
      rewrite -(extension_C0_ext (gamma gam) (l_end gam) (r_end gam)).
      2,3: simpl; left; apply tbd.
  reflexivity.
  erewrite RInt_ext. 2: {
     move => t tbd.
    rewrite Rmin_left in tbd; last by left.
    rewrite Rmax_right in tbd; last by left.
    rewrite -(extension_C0_ext (gamma gam) (l_end gam) (r_end gam)).
    2,3: simpl; left; apply tbd.
    reflexivity.
  }
  pose gamma_bar :=extension_C0 (gamma gam) (l_end gam) (r_end gam).
  have := @filterlim_RInt T
          (C_R_CompleteNormedModule) 
          (fun u t => f_ u (
            (gamma_bar t)) * 
            gamma' gam t)
          (l_end gam)
          (r_end gam) 
          F
          (ltac:(auto))
          (fun t => flim (gamma_bar t) * gamma' gam t)
          (fun u =>  RInt (V:=C_R_CompleteNormedModule)
                     (fun t : R => f_ u (
                       gamma_bar t) * 
                       gamma' gam t)
                     (l_end gam) (r_end gam)  ).
  case. 
  - move => u. 
    apply: RInt_correct. 
    apply: ex_RInt_continuous. move => t tbd.
    rewrite Rmin_left in tbd; last by left.
    rewrite Rmax_right in tbd; last by left.
    auto_cts.
    apply continuous_comp.
    + rewrite /gamma_bar.
      apply: extension_C0_continuous; simpl; first by left.
      move => *. apply: is_derive_continuous.
      apply: contour_derive; auto.
    + rewrite /gamma_bar extension_C0_ext; simpl.
      2,3: apply tbd.
      apply/cts_topology_2.
      apply cts.
      auto.
  - apply: filterlim_filter_le_2.
    1: apply filter_uniformly_global_local.
    apply: uniformly_bounded_mult.
    move: bounded => [M H].
    exists M =>*;apply H.
    apply: filterlim_filter_le_2.
    1: apply filter_locally_le_uniformly.
    auto.
  - move => z [+ /is_RInt_unique ->].
    apply.
Qed.

Lemma compact_limit_contour: forall 
  (f_: T -> C -> C)
  (flim : C -> C)
  (gam: Contour)
  (D: C -> Prop),
  open D ->
  (forall u, D u \/ ~ D u) ->
  (exists u0, D u0) ->
  contour_inside gam D ->
  filterlim f_ F (compactly D flim) ->
  filterlim (fun u z => f_ u (extension_C0 (gamma gam) (l_end gam) (r_end gam) z)) F
    (@locally (fct_UniformSpace _ _) 
    (fun z => flim (extension_C0 (gamma gam) (l_end gam) (r_end gam) z))). 
Proof.
  move => f_ flim gam D openD decD nonempty gam_in_D compact_lim.

  pose gamma_bar :=extension_C0 (gamma gam) (l_end gam) (r_end gam).
  rewrite /filterlim.
  apply: (@filterlim_compose_fam).
    1: apply compactly_non_trivial; eauto.
    1: auto.
    have := @path_in_circles gamma_bar D (l_end gam) (r_end gam)
             openD (ltac:(auto)) (ltac:(auto)).
    rewrite path_independence.not_not_impl.
    have?:= endpoint_interval gam.
    case.
    + auto.
    + move => *. 
      rewrite /gamma_bar /extension_C0.
      destruct_match; last apply gam_in_D.
      destruct_match; apply gam_in_D.
      all: split; try reflexivity; auto; left; auto.
    + move => *. 
      apply: extension_C0_continuous; first by left.
      move => t tbd1 tbd2.
      apply: is_derive_continuous.
      apply contour_derive.
      auto.
    + move => cov [sqrs cover].
      exists (fun z => Exists (@^~ z) cov).
      split; first by (
        exists cov;
        split; auto;
        move => *; tauto
      ).
      move => t.
      rewrite /gamma_bar /extension_C0.
      have r_eq: gamma_bar (r_end gam) = gamma gam (r_end gam). {
        rewrite /gamma_bar /extension_C0.
        repeat destruct_match.
        1,2: auto.
        simpl in *.
        lra.
      }
      have l_eq: gamma_bar (l_end gam) = gamma gam (l_end gam). {
        rewrite /gamma_bar /extension_C0.
        repeat destruct_match.
        1,3: auto.
        simpl in *.
        lra.
      }
        
      repeat (destruct_match). 
      * rewrite -(extension_C0_ext _ (l_end gam) (r_end gam)); auto.
      * move: cover => /(_ (r_end gam) (ltac:(lra))).
        rewrite r_eq //=.
      * move: cover => /(_ (l_end gam) (ltac:(lra))).
        rewrite l_eq //=.
Qed.

Lemma compact_limit_CInt: forall 
  (f_: T -> C -> C)
  (flim : C -> C)
  (gam: Contour)
  (D: C -> Prop),
  open D ->
  (forall u, D u \/ ~ D u) ->
  (exists u0, D u0) ->
  contour_inside gam D ->
  filterlim f_ F (compactly D flim) ->
  (forall u, cts_on_contour (f_ u) gam) ->
  filterlim (fun u => CInt gam (f_ u)) F (locally (CInt gam flim)).
Proof.
  move => *.
  apply uniform_limits_CInt; auto.
  apply: compact_limit_contour; eauto.
Qed.
End FilterlimFunc.

Open Scope C.
Lemma C_sum_pow_n: forall (z : C) (n : nat),
  z <> 1 ->
  sum_n [eta pow_n z] n = ((1 - (pow_n z (S n))) / (1 - z)).
Proof.
  move => z + neq1.
  have?:(1 - z <> 0) by
    move => H; contradict neq1;
    rewrite -[LHS]Cplus_0_l -H;
    field_simplify_eq.
  elim.
  - simpl.
    rewrite sum_O.
    simpl.
    rewrite mult_one_r.
    rewrite /one /=.
    field_simplify_eq; auto.
  - move => n IH.
    simpl.
    rewrite sum_Sn /plus /= IH //= /mult/=.
    field_simplify_eq; last by auto.
    auto.
Qed.

Lemma Cmod_lt_1_neq_1: forall z, Cmod z < 1 -> z <> 1.
Proof.
  move => z lt1 H.
  rewrite H Cmod_1 in lt1.
  lra.
Qed.

Definition pos1: posreal := (mkposreal 1 (ltac:(lra))).
Lemma geometric_compact:
  filterlim (fun (n : nat) (z0 : C) => sum_n (pow_n z0) n) eventually
  (compactly (@ball (AbsRing_UniformSpace C_AbsRing) (0,0) pos1 ) (fun z0 : C => 1 / (1 - z0))).
Proof.
  apply filterlim_on_family.
  1: apply eventually_filter.
  move => E [sub [a[del Esqr]]].
  have ?:= cond_pos del.
  have ?:= Rlt_sqrt2_0.
  have: {p | forall z, E z -> Cmod z <= p < 1}.  {
    simpl in *.
    have {}sub: forall z, E z -> Cmod z < 1 by
      move => z Ez; rewrite -[z]Cplus_0_r -Copp_0; apply sub.
    wlog: E a Esqr sub/ 0 <= a.1 /\ 0 <= a.2. {
      destruct (Rle_dec 0 a.1); destruct (Rle_dec 0 a.2).
      - apply; eauto.
      - move => /(_ 
          (fun z =>  a.1 - del <= z.1 <= a.1 + del /\ 
                     (-a.2) - del <= z.2 <= (-a.2) + del) (a.1, -a.2))%R.
        
        case.
        + move => z /=. lra.
        + move => [z1 z2] H; rewrite Cmod_opp_imaginary;
          apply sub; apply /Esqr; simpl in *; lra.
        + simpl; lra.
        + move => r' rH; exists r'; move => [z1 z2] /Esqr Ez.
          rewrite Cmod_opp_imaginary; apply rH; simpl in *; lra.
      - move => /(_ 
          (fun z =>  (-a.1) - del <= z.1 <= (-a.1) + del /\ 
                     a.2 - del <= z.2 <= a.2 + del) (-a.1, a.2))%R.
        
        case.
        + move => z /=. lra.
        + move => [z1 z2] H; rewrite Cmod_opp_real;
          apply sub; apply /Esqr; simpl in *; lra.
        + simpl; lra.
        + move => r' rH; exists r'; move => [z1 z2] /Esqr Ez.
          rewrite Cmod_opp_real; apply rH; simpl in *; lra.
      - move => /(_ 
          (fun z =>  (-a.1) - del <= z.1 <= (-a.1) + del /\ 
                     (-a.2) - del <= z.2 <= (-a.2) + del) (-a.1, -a.2))%R.
        
        case.
        + move => z /=. lra.
        + move => [z1 z2] H; rewrite Cmod_opp_real Cmod_opp_imaginary;
          apply sub; apply /Esqr; simpl in *; lra.
        + simpl; lra.
        + move => r' rH; exists r'; move => [z1 z2] /Esqr Ez.
          rewrite Cmod_opp_real Cmod_opp_imaginary; apply rH; simpl in *; lra.
    }
    move => [??].
    exists (Cmod (a.1 + del, a.2+del))%R => z /Esqr Ez.
    split.
    - apply sqr_Cmod_bound; lra.
    - apply sub.
      apply/Esqr.
      simpl.
      lra.
  }
  move => [r rH].
  have rlt1 : r < 1 by move: (rH a); rewrite Esqr; move => /(_ (ltac: (lra))) [].
  have rpos : 0 <= r by
    move: (rH a); rewrite Esqr; move => /(_ (ltac: (lra)))[??];
    apply: Rle_trans; first (by apply Cmod_ge_0); eauto.

  apply/filterlim_uniformly_on => eps.


  have L: Rabs r < 1 by rewrite Rabs_pos_eq.
  pose eps' := (eps * (1-r)%R)%R.
  have?: 0 < eps by apply cond_pos.
  have eps'pos: 0 < eps' by rewrite /eps'; apply Rmult_lt_0_compat; try lra.
  have := @is_lim_seq_geom r L.
  move => /filterlim_locally /(_ (mkposreal _ eps'pos) ) [N nH].
  exists N => n nbd w Ew.
  apply: norm_compat1.
  unfold_alg.
  rewrite -/(Cminus _ _).
  have wneq: (w <> 1) by
    apply Cmod_lt_1_neq_1; apply: Rle_lt_trans;
    [ apply rH
    | apply rlt1
    ].
  rewrite C_sum_pow_n //. 
  set p := (x in Cmod x).
  replace p with (- (pow_n w (S n)/(1-w))).
  2: rewrite /p /mult /=; field_simplify; auto.
  2,3: apply/ Cminus_0_eq; apply nesym; auto.
  rewrite Cmod_opp Cmod_mult pow_n_abs_C.
  rewrite pow_n_pow.
  apply Rlt_div_r; rewrite Cmod_inv. 
  1: apply Rinv_0_lt_compat; apply Cmod_gt_0.
  1,2,4: apply/Cminus_0_eq; apply nesym; auto.
  have ?: ( 0 < Cmod (1-w)) by
    apply Cmod_gt_0; apply/ Cminus_0_eq; apply nesym.
  rewrite /Rdiv Rinv_involutive.
  2: move => /Cmod_eq_0 /Cminus_0_eq; contradict wneq; auto.
  have lt3: (1-r)%R <= Cmod (1-w). { 
    apply: Rle_trans.
    2: apply Cmod_triangle_inverse.
    rewrite Cmod_1.
    apply Rplus_le_compat_l.
    move: (rH w Ew); lra.
  }
  apply: (@Rlt_le_trans _ (eps * (1-r)%R)).
  2: apply Rmult_le_compat_l; auto; left;apply cond_pos.
  apply (@Rle_lt_trans _ (r ^(S n))).
  1: by apply pow_incr; split; [apply Cmod_ge_0| apply rH].
  rewrite -/eps'.
  move: (nH (S n) (ltac:(auto))).
  unfold_ball;unfold_alg.
  rewrite Rabs_pos_eq.
  lra.
  field_simplify.
  rewrite -/(pow _ (S n)).
  destruct rpos; subst.
  1: left; apply pow_lt; auto.
  rewrite pow_i. 
  1: lra.
  lia.
Qed.

Lemma Cplus_plus_complete: forall (z w:C_R_CompleteNormedModule), plus z w = z + w.
Proof.
  repeat unfold_alg; move => *.
  simplify_as_R2 RHS.
  auto.
Qed.
Lemma Cplus_plus_C: forall (z w:C), plus z w = z + w.
Proof.
  repeat unfold_alg; move => *.
  auto.
Qed.

Lemma cts_contour_sum: forall f gam n,
  (forall m, cts_on_contour (fun z => f m z) gam) ->
  cts_on_contour ( fun z => sum_n (fun n => f n z) n) gam.
Proof.
  move => f gam + cts.
  elim.
  - move => t tbd.
    apply: continuous_ext.
      move => x.
      rewrite sum_O.
    reflexivity.
    apply cts.
    auto.
  - move => n IH.
    move => t tbd.
    apply: continuous_ext.
      move => x.
      rewrite sum_Sn Cplus_plus_C. 
    reflexivity.
    apply: continuous_plus.
    1: apply IH; auto.
     apply: cts; auto.
Qed.

Lemma sum_n_CInt : forall f gam n, 
  (forall m, cts_on_contour (f m) gam) ->
  sum_n (fun m => CInt gam (fun z => f m z)) n = 
  CInt gam (fun z => sum_n (fun m => f m z) n).
Proof.
  move => f gam  + cts.
  elim.
  { rewrite sum_O.
    symmetry.
    under CInt_ext.
      move => t tbd.
      rewrite sum_O.
    over.
    auto.
  }
  move => n IH.
  rewrite sum_Sn.
  rewrite Cplus_plus_complete IH. 
  rewrite -CInt_plus.
  2: apply: cts.
  2: apply: cts_contour_sum; auto.
  rewrite (@CInt_ext _ (fun z:C => sum_n (f^~ z) (S n))); auto.
  move => t tbd.
  rewrite sum_Sn Cplus_plus_C.
  auto.
Qed.

Lemma contour_puncture: forall a (r:posreal) t z,
  @ball (AbsRing_UniformSpace C_AbsRing) a r z -> 
  a + c_circle r t <> z.
Proof.
  move => a r t z ball ?. 
  have H: (z-a = c_circle r t) by subst; field_simplify_eq; auto.
  contradict H.
  apply Cmod_lt_neq.
  rewrite c_circle_norm_2 Rabs_pos_eq.
  2: left; apply cond_pos.
  apply ball.
Qed.

Lemma CInt_puncuture_ext: forall f g a (r:posreal), 
  (forall z, z <> a -> f z = g z) -> 
  CInt (circC a r) f = CInt (circC a r) g.
Proof.
  move => f g a r ext.
  apply CInt_ext.
  move => t tbd.
  apply ext.
  apply contour_puncture.
  apply ball_center.
Qed.

Lemma pow_n_div: forall (z w:C) n , w <> (0,0) -> 
  pow_n z n /(pow_n w n) = pow_n (z/w) n.
Proof.
  move => z w + neq.
  elim.
  - simpl. 
    rewrite /one /=.
    field_simplify; auto.
    move => /pair_equal_spec [? _].
    lra.
  - move => n IH.
    simpl.
    rewrite -IH.
    rewrite /mult /=.
    field_simplify_eq; auto.
    split; [apply pow_n_neq_0; auto| auto].
Qed.

Lemma cts_puncture_contour: forall f a (r:posreal),
  (forall w, w <> a -> continuous f w) ->
  cts_on_contour f (circC a r).
Proof.
  move => f a r cts t _.
  apply cts.
  apply contour_puncture.
  apply ball_center.
Qed.

Definition PCoef := 1/(2*PI* Ci).

Theorem holo_analytic : forall (f:C -> C) (r: posreal) D a z, 
  open D ->
  CHolo_on D f ->
  (forall w, Cmod (a - w) <= r -> D w) ->
  @ball (AbsRing_UniformSpace C_AbsRing) a r z ->
  @is_pseries C_AbsRing C_NormedModule
    (fun n => PCoef * CInt (circC a r) 
      (fun w => f(w)/(pow_n (w-a) (S n)))
    ) (z-a) (f z).
Proof.
  move => f r D a z openD CHolo subset aball.
  have ?:= Rgt_2PI_0.
  rewrite -(@cauchy_integral_formula f r D a z ) -/PCoef; auto.
  rewrite /is_pseries /is_series.
  eapply filterlim_ext. 
    move => x.
    eapply sum_n_ext.
      move => n.
      set p := CInt _ _.
      set q := RHS.
      replace q with (PCoef * (scal (pow_n (z- a) n) p)); last by (
        rewrite /q; unfold_alg; field_simplify_eq;
        rewrite -Cmult_assoc [_*p]Cmult_comm Cmult_assoc).
        rewrite /p.
  reflexivity.
  eapply filterlim_ext.
    move => x.
    rewrite sum_n_mult_l.
  reflexivity.
  set p := (q in PCoef * q).
  replace (PCoef * p) with (mult PCoef p ); last by unfold_alg.
  apply: filterlim_comp_2.
  1: apply filterlim_const.
  2:{
    apply: filterlim_filter_le_2.
    2: apply: filterlim_filter_le_1.
    3: apply: @filterlim_mult C_AbsRing PCoef p.
    1: move => *; apply locally_C; auto.
    move => P [Q R F1 F2 impl].
    apply: Filter_prod .
    2: apply/locally_C; apply F2.
    1: apply/locally_C; apply F1.
    auto.
  }
  rewrite /p.
  eapply filterlim_ext. 
    move => x.
    eapply sum_n_ext. 
      move => n.
        rewrite /scal /=/mult /= -CInt_mult.
      eapply CInt_puncuture_ext => w neq.
      move =>{p}.
      set p := RHS.
      replace p with ( mult (pow_n ((z-a)/(w-a)) n)  (f(w) / (w-a)) ).
  reflexivity.
  have?: (w-a <> 0) by move => /Cminus_0_eq ?; contradict neq.
  2: {
    auto_cts_on_contour.
    apply cts_puncture_contour.
    move => w neq.
    have?: (w-a <> 0) by move => /Cminus_0_eq ?; contradict neq.
    apply continuous_comp.
    2: apply continuous_Cinv; apply Cmult_neq_0; auto; apply pow_n_neq_0; auto.
    auto_cts.
    apply/cts_topology_2.
    apply: (@continuous_comp _ _ _ (fun w => w - a) (fun w => pow_n w n));
    auto_cts.
  }
  1:{
    rewrite -pow_n_div /p; auto.
    unfold_alg.
    field_simplify_eq; auto.
    split; auto.
    apply pow_n_neq_0.
    auto.
  }
  eapply filterlim_ext. 
    move => x.
    rewrite [RHS]sum_n_CInt.
    eapply CInt_puncuture_ext.
      move => w neq.
      rewrite sum_n_mult_r.
      rewrite /mult /=.
  reflexivity.
  1: {
    move => n.
    rewrite {2}/Cdiv.
    auto_cts_on_contour.
    apply cts_puncture_contour => w neq.
    apply (@continuous_comp _ _ _ (fun w:C => (z-a)/(w - a))%C 
            (fun w:C => pow_n w n));
    auto_cts.
    apply/cts_topology_2.
    apply: continuous_Cinv.
    apply/ Cminus_0_eq; auto.
  }
  rewrite (@CInt_ext _ (fun w => 1/(1-((z-a)/(w-a))) * (f w /(w-a)))).
  2: {
    move => w neq.
    field_simplify_eq; auto.
    split.
    - apply/Cminus_0_eq.
      apply contour_puncture.
      apply ball_center.
    - move => H.
      field_simplify in H.
      contradict H.
      apply/ Cminus_0_eq.
      apply contour_puncture.
      auto.
  }
  pose h := extension_C0 (gamma (circC a r)) 0 (2*PI)%R.
  apply uniform_limits_CInt.
  all: rewrite -?/h.
  2:{
    move => n.
    rewrite {2}/Cdiv.
    auto_cts_on_contour. 
    apply cts_contour_sum => m.
    apply: cts_puncture_contour => w neq.
    apply: (@continuous_comp _ _ _ (fun w:C => (z-a)/(w - a))%C 
            (fun w:C => pow_n w m)); auto_cts.
    apply/cts_topology_2; apply: continuous_Cinv; apply/Cminus_0_eq; auto.
  }
  clear p.
  apply: filterlim_filter_le_2.
  1: apply filter_uniformly_global_local.
  apply: uniformly_bounded_mult.
  - destruct (@bounded_continuity (C_AbsRing) (C_NormedModule)
    (fun t => f (a + c_circle r t) / (a + c_circle r t - a)) 0 (2*PI)%R).
    + move => t tbd.
      rewrite -/(continuous _ _).
      auto_cts.
      1: apply: continuous_comp.
      1: auto_cts.
      1,3: rewrite /c_circle; auto_cts;
        apply: is_derive_continuous;
        auto_derive; auto.
      2: simplify_term (x in _ _ x); apply/cts_topology_2; apply: continuous_Cinv.
      2: apply nesym, Cmod_lt_neq; rewrite c_circle_norm_2 Cmod_0 Rabs_pos_eq.
      2: apply cond_pos.
      2: left; apply cond_pos.
      apply /cts_topology_2.
      have:= @holo_ball_contour f a r D subset CHolo.
      apply.
      simpl; lra.
    + have xpos: (0 < x). {
        apply: Rle_lt_trans.
        1: apply: norm_ge_0.
        2: apply (r0 0).
        split.
        1: lra.
        left.
        apply Rgt_2PI_0.
      }
      exists (mkposreal _ xpos).
      simpl.
      move => t.
      rewrite /h /extension_C0.
      repeat destruct_match; move => _.
      * apply (r0 t); split; auto; apply Rgt_2PI_0.
      * apply r0; split; [left; apply Rgt_2PI_0| reflexivity].
      * apply r0; split; [reflexivity | left; apply Rgt_2PI_0].
  - pose g t := (z-a)/(h t  -a).
    eapply filterlim_ext.
      move => x.
      apply functional_extensionality.
      move => x'.
      eapply sum_n_ext. 
      move => n.
      rewrite -/(g x').
    reflexivity.
    apply: filterlim_filter_le_2.
    1: apply: filter_locally_le_uniformly.
    rewrite [x in locally x](@functional_extensionality _ _ 
      _ (fun t => (1/(1-g t)))).
    2: move => *; rewrite /g //=.

    pose odisk := (@ball (AbsRing_UniformSpace C_AbsRing) (0,0) pos1).
    pose dom: Domain odisk := BallDom pos1 (0,0).
    apply: (@filterlim_compose_fam _ _ _ _
      _
      (fun n (z:C) => sum_n (pow_n z) n)
      (fun z => 1/(1-z))
         ).
    1: apply compactly_non_trivial.
    have:= open_dom dom.
    simpl; apply.
    1: exists(0,0);
       apply (@ball_center (AbsRing_UniformSpace C_AbsRing) (0,0) pos1 ).
    2: {
    have := @path_in_circles g odisk 0 (2*PI)
             (open_dom dom) (ltac: (lra)).
    rewrite path_independence.not_not_impl.
    case.
    + move => w. 
      apply excluded_middle.
    + move => t tbd.
      rewrite /odisk.
      unfold_ball; unfold_alg.
      rewrite /Cminus Copp_0 Cplus_0_r /g/h /Cdiv Cmod_mult.
      rewrite extension_C0_ext; simpl. 
      2,3:lra.
      set p := (a + _ - a).
      replace p with (c_circle r t).
      2: rewrite /p; field_simplify_eq; auto.
      rewrite Cmod_inv.
      2: move => H; symmetry in H; contradict H; apply Cmod_lt_neq;
         rewrite c_circle_norm_2 Cmod_0 Rabs_pos_eq;[|left]; apply cond_pos.
      rewrite c_circle_norm_2 Rabs_pos_eq;[|left]. 
      2:apply cond_pos.
      rewrite -Rdiv_lt_1.
      2: apply cond_pos.
      apply aball.
    + move => t tbd. rewrite /g /h. 
      auto_cts.
      1: apply: extension_C0_continuous.
      1: simpl; lra.
      1: move => *; apply: is_derive_continuous; apply contour_derive.
      1: simpl in *; lra.
      apply/cts_topology_2.
      apply: continuous_Cinv.
      simpl.
      rewrite /h extension_C0_ext.
      2,3: simpl; lra.
      simpl.
      apply nesym, Cmod_lt_neq.
      rewrite Cmod_0.
      set p := (a + _ -a).
      replace p with (c_circle r t).
      2: rewrite /p; field_simplify; auto.
      rewrite c_circle_norm_2 Rabs_pos_eq; [|left]; apply cond_pos.
    + move => cov [sqrs cover].
      exists (fun z => Exists (@^~ z) cov).
      split; first by (
        exists cov;
        split; auto;
        move => *; tauto
      ).
      move => t.
      rewrite /h /extension_C0.
      have r_eq: h 0 = gamma (circC a r) 0. {
        rewrite /h /extension_C0.
        repeat destruct_match.
        1,2: auto.
        simpl in *.
        lra.
        auto.
      }
      have l_eq: h (2*PI)%R = gamma(circC a r) (2*PI)%R. {
        rewrite /h /extension_C0.
        repeat destruct_match.
        1,3: auto.
        simpl in *.
        lra.
        auto.
      }
      rewrite /g/h/extension_C0.
      repeat destruct_match.
      * rewrite //= -(extension_C0_ext (fun t => a + c_circle r t)  0 (2*PI)%R); auto.
        apply: cover.
        auto.
      * rewrite -l_eq //=.
        apply: cover.
        lra.
      * rewrite -r_eq //=.
        apply: cover; lra.
    }
    apply geometric_compact.
Qed.
