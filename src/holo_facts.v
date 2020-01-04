
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
Import Logic.Classical_Prop.

Require Import helpers complex_core path_independence 
  cauchy_integral compact_convergence analytic.

  
Ltac case_assumption :=
    match goal with 
    | |- (?A -> ?B) -> ?G => 
      let H := fresh in 
      have: A; last (move => H /(_ H) {H})
    end.
Ltac case_assumptions := repeat case_assumption.

Definition PowCoef f a r n :=  PCoef * CInt (circC a r) 
      (fun w => f(w)/(pow_n (w-a) (S n))).

Definition abs_retract {K:AbsRing} {V : CompleteNormedModule K} (a_ : nat -> V):=
  fun r => PSeries (fun n => norm (a_ n)) r.
  
Lemma CHolo_on_continuous: forall f D z, 
  CHolo_on D f -> D z -> continuous f z.
Proof.
  move => f D z holo Dz.
  move: holo.
  case => f'.
  move => /(_ z Dz). 
  case.
  rewrite /Holo => H _.
  apply/cts_topology_1.
  apply: ex_derive_continuous.
  eexists.
  eapply H.
Qed.


  
Lemma holo_absolute_convergence: forall f D a (r r': posreal), 
  open D ->
  CHolo_on D f ->
  (forall z, (Cball a r z) -> D z) -> 
  r' < r ->
      ex_pseries (fun n => norm (PowCoef f a r n )) r'.
Proof.
  move => f D a r r' openD holo subset r'bd.
  rewrite /ex_pseries.
  unfold_alg.
  set h := (x in ex_series x).
  apply: ex_series_le.
  1: move => *; unfold_alg; right; reflexivity.
  rewrite {}/h.
  have:= @bounded_continuity _ _ (fun t => f (a + c_circle r t)) 0 (2*PI).
  case_assumptions.
  1: move => *. rewrite -/(continuous _ _); apply: continuous_comp.
  1: apply: ex_derive_continuous; eexists; apply: (@contour_derive (circC a r));
     simpl; auto.
  1: apply: CHolo_on_continuous; eauto; apply subset;
     rewrite /Cball; simplify_term (x in Cmod x);
     rewrite c_circle_norm_2 Rabs_pos_eq; first (right; auto);
     left; apply cond_pos.
  move => [M HM].
  have ?: 0 < r by apply cond_pos.
  have ?: 0 < r' by apply cond_pos.
  have ?: 0 <= r by left;apply cond_pos.
  have ?: 0 <= r' by left;apply cond_pos.
  apply: ex_series_le. {
    move => n.
    unfold_alg.
    rewrite 2!Rabs_mult 2!Rabs_Rabsolu [Rabs (Cmod _)] Rabs_pos_eq.
    2: apply Cmod_ge_0.
    rewrite /PowCoef Cmod_mult.
    apply Rmult_le_compat_l.
    1: apply Rabs_pos.
    apply Rmult_le_compat_l.
    1: apply Cmod_ge_0.
    rewrite Cmod_norm.
    apply: CInt_abs_bound.
    1: rewrite /Cdiv; auto_cts_on_contour.
    1: apply: holo_ball_contour; eauto; rewrite /Cball in subset. 
    1: move => w; rewrite Cmod_sym; apply subset.
    move => t tbd.
    set m := S n.
    rewrite [m]lock.
    unfold_alg.
    simplify_term (_ + _ - _).
    rewrite /Cdiv Cmod_mult Cmod_inv.
    2: apply Cmod_gt_0; rewrite pow_n_abs_C c_circle_norm_2 pow_n_pow;
       apply pow_lt; rewrite Rabs_pos_eq;[|left]; apply cond_pos.
    rewrite pow_n_abs_C c_circle_norm_2 pow_n_pow -lock /m Rabs_pos_eq.
    2: lra.
    apply Rmult_le_compat_r.
    1: left; apply Rinv_0_lt_compat; apply pow_lt; apply cond_pos.
    left.
    apply HM.
    simpl in *; auto.
  } 
  apply: ex_series_Rabs .
  apply: ex_series_DAlembert. 
  3: {
    eapply is_lim_seq_ext. {
      move => n.
      have?: (0 < r^n) by apply pow_lt; lra.
      have?: (0 < r'^n) by apply pow_lt; lra.
      have? := Rgt_2PI_0.
      set m := S n; rewrite [m]lock.
      rewrite ?(Rabs_mult, Rabs_Rinv) ?Rabs_Rabsolu. 
      1: field_simplify; rewrite -/(pow_n _ _).
      3,4: apply Rlt_0_neq_0; apply pow_lt; apply cond_pos.
      1:rewrite -lock {}/m /= Rabs_mult; unfold_alg; field_simplify. 
      reflexivity.
      all: repeat split.
      all: rewrite ?Rabs_pos_eq ?pow_n_pow; 
           rewrite -?lock ?/m //=;
           try left;
           repeat apply Rlt_0_neq_0;
           repeat apply Rmult_lt_0_compat;
           try apply: Rinv_0_lt_compat;
           repeat apply Rmult_lt_0_compat;
           try apply lt_pow; 
           try lra.
      all: try (apply (@Rle_lt_trans _ (norm (f (a + c_circle r 0)))); 
           try apply norm_ge_0;
           try apply: HM; lra).
      all: try (apply Cmod_gt_0; apply PCoef_neq_0).
      all: try (under RInt_ext => x _ do (unfold_alg; rewrite c_circle'_norm);
           rewrite RInt_const; unfold_alg;
           rewrite Rabs_pos_eq; try apply: Rmult_lt_0_compat; lra).
    }
    apply is_lim_seq_const.
  }
  - rewrite ?Rabs_pos_eq; try lra.
    rewrite -Rdiv_lt_1; lra.
  - move => n. 
      have?: (0 < r^n) by apply pow_lt; lra.
      have?: (0 < r'^n) by apply pow_lt; lra.
      have? := Rgt_2PI_0.
      all: rewrite ?Rabs_pos_eq ?pow_n_pow; 
           rewrite -?lock ?/m //=;
           try left;
           repeat apply Rlt_0_neq_0;
           repeat apply Rmult_lt_0_compat;
           try apply: Rinv_0_lt_compat;
           repeat apply Rmult_lt_0_compat;
           try apply lt_pow; 
           try lra.
      all: try (apply (@Rle_lt_trans _ (norm (f (a + c_circle r 0)))); 
           try apply norm_ge_0;
           try apply: HM; lra).
      all: try (apply Cmod_gt_0; apply PCoef_neq_0).
      all: try (under RInt_ext => x _ do (unfold_alg; rewrite c_circle'_norm);
           rewrite RInt_const; unfold_alg;
           rewrite Rabs_pos_eq; try apply: Rmult_lt_0_compat; lra).
Qed.

Lemma holo_pseries_compatly
    eapply is_lim_seq_ext. {
      move => n.
      simpl.
      unfold_alg.
      rewrite 
      rewrite /PowCoef 2!Cmod_mult.
      simpl.


    }
    rewrite/is_lim_seq.
    apply/filterlim_locally.
    move => eps.


  }





Lemma Ceq_dec: forall (z w: C), z = w \/ z<> w.
Proof. move => *. apply classic. Qed. 

Lemma holo_neq_0_locally: forall f D z,
  open D ->
  CHolo_on D f ->
  D z ->
  f z <> 0 ->
  locally z (fun w => f w <> 0).
Proof.
  move => f D z openD holo Dz neq.
  have ctsf: continuous f z. {
    apply/cts_topology_1.
    apply: ex_derive_continuous.
    move: holo => [? /(_ z Dz)[holo _] ].
    rewrite /Holo in holo.
    eexists.
    eapply holo.
  }
  apply/locally_C.
  apply: (ctsf (fun y:C => y <> 0)).
  apply open_neq_C.
  auto.
Qed.

Lemma sum_n_zero {G: AbelianGroup}: forall n, @sum_n G (fun=> zero) n = zero.
Proof.
  elim.
  - rewrite sum_O //=.
  - move => n IH; rewrite sum_Sn plus_zero_r //=.
Qed.

Lemma holo_const_0: forall f D (a:C) (x_: nat -> C), 
  Domain D -> 
  CHolo_on D f -> 
  filterlim x_ eventually (locally a) -> 
  (forall n , x_ n <> a /\ D (x_ n) /\ f (x_ n) = 0) ->
  D a -> 
  locally a (fun w => f w = 0).
Proof.
  move => f D a x_ domD holo conv seq.
  copy => /(open_dom domD)/locally_C [del circIn] Da.  
  have ?:= cond_pos del.
  have := (@holo_analytic f (pos_div_2 del) D a _).
  have suff: forall n, PowCoef f a (pos_div_2 del) n = 0. {
    move => c0 H.
    apply/locally_C.
    exists (pos_div_2 del) => w yball.
    move: H => /(_ w _ holo ).
    case_assumptions.
    - move => *; apply/locally_C; apply open_dom; auto.
    - move => *; apply circIn; unfold_ball;unfold_alg.
      rewrite Cmod_sym.
      apply: Rle_lt_trans; eauto.
      simpl.
      have:= cond_pos del.
      lra.
    - auto.
    - move => H. 
      symmetry.
      have: (filterlim (fun => (0,0)) eventually (locally (0,0))) by apply: filterlim_const.
      move => / filterlim_locally_unique.
      apply.
      

      eapply is_pseries_ext in H. 
      2: move => n; rewrite -/(PowCoef f a (pos_div_2 del) n) (c0 n); reflexivity.
      rewrite /is_pseries in H.
      eapply is_series_ext in H. 
      2: move => *; rewrite scal_zero_r; reflexivity.
      rewrite /is_series in H.
      eapply filterlim_ext in H. 
      2: move => *; rewrite sum_n_zero /zero /=; reflexivity.
      auto.
  }
  apply.

  have ctsF: (f a = RtoC 0). {
    symmetry.
    have: (filterlim (fun => (0,0)) eventually (locally (RtoC 0))) by apply: filterlim_const.
    move => / filterlim_locally_unique.
    apply.
    eapply filterlim_ext.
      move => m.
      rewrite -/(RtoC 0).
      have [_ [_ <-]] := seq m.
    reflexivity.
    apply: filterlim_comp; eauto.
    rewrite -/(continuous f a).
    apply/cts_topology_1.
    apply: ex_derive_continuous.
    move: holo => [? /(_ a Da)[holo _] ].
    eexists; apply holo.
  }

  wlog seq_in_gam: x_ seq conv / 
      (forall n, (@ball (AbsRing_UniformSpace C_AbsRing) a (pos_div_2 del) (x_ n))). {
    move: conv.
    have poseps: 0< (pos_div_2 del)/(sqrt 2). {
      simpl.
      have:= Rlt_sqrt2_0.
      do 2 apply Rdiv_lt_0_compat; lra.
    }
    copy => /(filterlim_locally) /(_ (mkposreal _ poseps) ) [N small] conv. 
    pose y_ n := x_ ((N+1) + n)%nat.
    move => /(_ y_).
    apply.
    - move => n; repeat split; apply seq.
    - apply /filterlim_locally => eps.
      move: conv => /filterlim_locally /(_ eps) [N' H].
      exists (N' + N)%nat => *.
      apply H.
      lia.
    - move => n. 
      move: (small (N + 1 + n)%nat). 
      case_assumptions; first lia.
      move => H.
      simpl in *.
      unfold_ball; unfold_alg.
      have -> : ((del/2)= (sqrt 2) * (del/2 / sqrt 2))%R.
      1: field_simplify; auto.
      1: apply Rlt_0_neq_0; apply Rlt_sqrt2_0.
      replace (y_ n - a) with (minus (y_ n) a); last by auto.
      rewrite -/(pos (mkposreal _ poseps)).
      apply C_NormedModule_mixin_compat2.
      auto.
  }
  move => n.
  rewrite /PowCoef.
  symmetry.
  have: (filterlim (fun => (0,0)) eventually (locally (RtoC 0))) by apply: filterlim_const.
  move => / filterlim_locally_unique.
  apply.
  eapply filterlim_ext.
    move => m.
    rewrite -/(RtoC 0).
    have [_ [_ <-]] := seq m.
    have <- := @cauchy_integral_formula_center f ( pos_div_2(pos_div_2 del)) D (x_ m); auto.
    rewrite -/PCoef.
  reflexivity.

  1: move => *; apply open_dom; auto.
  1: { 
     move => w H; apply circIn; unfold_ball;unfold_alg;
     rewrite Cmod_sym.
     have -> : (a - w = (a - (x_ m)) + ((x_ m) - w)) by field_simplify.
     apply: Rle_lt_trans.
     1: apply Cmod_triangle.
     simpl in *.
     have ?:= cond_pos del.
     have := (seq_in_gam m).
     unfold_ball;unfold_alg => ?.
     rewrite Cmod_sym.
     nra.
  }
  apply: filterlim_comp_2.
  1: apply filterlim_const.
.

     apply: Rle_lt_trans. eauto.
     simpl;
  }
     have:= cond_pos del.
     lra.
  reflexivity.


  }
    




  }
  elim; first by [].
  move => n IH.

  move => n.
  have fz0 : (f z = 0 ).
    apply: .
  SearchAbout continuous.
    

  





Lemma isolated_roots: forall f D z,
  Domain D ->
  CHolo_on D f ->
  D z ->
  f z = 0 ->
  locally' z (fun w => f w <> 0).
Proof.
  move => f D z openD holo Dz eq0.
  