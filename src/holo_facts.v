
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

Definition PowCoef f a r n :=  PCoef * CInt (circC a r) 
      (fun w => f(w)/(pow_n (w-a) (S n))).

Ltac case_assumption :=
    match goal with 
    | |- (?A -> ?B) -> ?G => 
      let H := fresh in 
      have: A; last (move => H /(_ H) {H})
    end.
Ltac case_assumptions := repeat case_assumption.

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
  