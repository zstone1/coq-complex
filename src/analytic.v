
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



Require Import domains ext_rewrite real_helpers.
Require Import domains cauchy_riemann path_independence cauchy_integral compact_convergence.

Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.


Section FilterlimFunc.

Context {T:UniformSpace} {F: (T -> Prop) -> Prop } {FF: ProperFilter F}.

Open Scope C.
Lemma filterlim_mult: forall {U:UniformSpace}
  (f: T -> U -> C) (g: U -> C) flim,
  (exists (M:posreal), forall z, norm(g z) < M  ) ->
  filterlim (fun u z=> f u z ) F (locally flim) ->
  filterlim (fun u z=> f u z * g z ) F 
    (@locally (fct_UniformSpace U C_UniformSpace) (fun z => flim z * g z)).

Proof.
  move => U f g flim [M bd] /filterlim_locally H.
  have?:= cond_pos M.
  apply/ filterlim_locally => eps.
  have?:= cond_pos eps.
  have delpos : 0 < eps/(2*M) by apply Rdiv_lt_0_compat;  lra.
  pose del := mkposreal _ delpos.
  move:H => /(_ (del )) H.
  apply: filter_imp H.
  move => t.
  unfold_alg.
  rewrite /fct_ball /= .
  move => H.
  move => z.
  move: H => /(_ z).
  rewrite /ball /= /prod_ball => H.
  case: H => [+ +].
  unfold_alg.
  rewrite -?/(Rminus _ _).
  Open Scope R.
  have bd1 : Rabs((g z).1) < M. {
    move: bd=> /(_ z).
    unfold_alg => bd.
    apply: Rle_lt_trans. 
    2: apply bd.
    case e: (g z).
    apply Cmod_Rabs_real.
  }
  have bd2 : Rabs((g z).2) < M. {
    move: bd=> /(_ z).
    unfold_alg => bd.
    apply: Rle_lt_trans. 
    2: apply bd.
    case e: (g z).
    apply Cmod_Rabs_imaginary.
  }
  move => H1 H2.
  replace (pos eps) with ((eps/(2*M)) *M + (eps/(2*M)) * M )%R; 
    last field_simplify_eq; auto.
  2: apply Rlt_0_neq_0; lra.
  split.
  - set p := ( x in Rabs x).
    replace p with (((f t z).1 - (flim z).1) * (g z).1 - 
                    ((f t z).2 - (flim z).2) * (g z).2).
    2: rewrite /p; field_simplify_eq;
       rewrite [(flim z).2*_]Rmult_comm;
       apply Rplus_eq_compat_r;
       rewrite [(flim z).1*_]Rmult_comm;
       auto.
    apply: Rle_lt_trans; first by apply Rabs_triang.
    rewrite Rabs_Ropp ?Rabs_mult;
    apply Rplus_lt_compat;
    apply Rmult_le_0_lt_compat; auto;
      try apply Rabs_pos.
  - set p := ( x in Rabs x).
    replace p with (((f t z).1 - (flim z).1) * (g z).2 + 
                    ((f t z).2 - (flim z).2) * (g z).1).
    2: rewrite /p; field_simplify_eq;
       rewrite [(flim z).2*_]Rmult_comm;
       apply Rplus_eq_compat_r;
       rewrite [(flim z).1*_]Rmult_comm;
       auto.
    apply: Rle_lt_trans; first by apply Rabs_triang.
    rewrite ?Rabs_mult;
    apply Rplus_lt_compat;
    apply Rmult_le_0_lt_compat; auto;
      try apply Rabs_pos.
Qed.

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
      clear l.
      destruct_match.
      all: apply Mbd; auto.
      all: split; try reflexivity;
           try (left; apply: endpoint_interval).
Qed.

Definition contour_inside (g:Contour) D:= 
  forall t, l_end g <= t <= r_end g -> D (gamma g t).

(**I need this to deal with some compactness issues. 
   very likely it can be removed by requring D to be decidable, so
   and because square_in becomes decidable.*)
Axiom classical: forall P:Prop, ~ ~P  <-> P.

Open Scope C.
Lemma uniform_limits_CInt : forall 
  (D: C -> Prop)
  (f_: T -> C -> C)
  (flim : C -> C)
  (gam: Contour),
  open D ->
  (forall z, D z \/ ~ D z) ->
  (exists z0, D z0) ->
  contour_inside gam D ->
  (forall u, cts_on_contour (f_ u) gam) ->
  filterlim f_ F (compactly D flim) -> 
  filterlim (fun u => CInt gam (f_ u)) F (locally (CInt gam flim)).
Proof.
  move => D f_ flim gam openD decD nonempty gam_in_D cts H.

  wlog: gam gam_in_D cts / 
    exists M : posreal, forall z : R_UniformSpace, norm (gamma' gam z) < M. {
      have:= bounded_derive_contour gam.
      move => [gam2 [eqv bdd]] H'.
      rewrite (@CInt_gamma_ext gam gam2); auto.
      eapply filterlim_ext.
        move => t.
        rewrite (@CInt_gamma_ext gam gam2); auto.
      reflexivity.
      move: eqv => [lends [rends[ext1 ext2]]].
      apply H'.
      - move => t tbd.
        rewrite -ext1; first apply gam_in_D.
        all: rewrite lends rends; lra.
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
  pose gamma_bar := extension_C0 (gamma gam) (l_end gam) (r_end gam) .
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
    apply/continous_C_NormedModule.
    apply: continuous_mult; last by
      apply/continous_C_NormedModule; apply: cts_derive; auto.
    apply continuous_comp.
    + apply: extension_C0_continuous; simpl; first by left.
      move => *. apply: is_derive_continuous.
      apply: contour_derive; auto.
    + rewrite /gamma_bar extension_C0_ext; simpl.
      2,3: apply tbd.
      apply/continous_C_NormedModule.
      apply cts.
      auto.
  - apply filterlim_mult; first by apply: bounded.
    apply: (filterlim_compose_fam).
    1: apply compactly_non_trivial; eauto.
    1: auto.
    have := @path_in_circles gamma_bar D (l_end gam) (r_end gam)
             openD (ltac:(auto)) (ltac:(auto)).
    rewrite classical.
    case.
    + move => *. 
      rewrite /gamma_bar /extension_C0.
      destruct_match; last apply gam_in_D.
      clear l.
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
        destruct_match; clear l; try destruct_match.
        1,2: auto.
        simpl in *.
        lra.
      }
      have l_eq: gamma_bar (l_end gam) = gamma gam (l_end gam). {
        rewrite /gamma_bar /extension_C0.
        destruct_match; clear l; try destruct_match.
        1,3: auto.
        simpl in *.
        lra.
      }
        
      (destruct_match); simpl in *.
      move: l => l'.
      destruct_match;
      move: l => l''.
      * rewrite -(extension_C0_ext _ (l_end gam) (r_end gam)); auto.
      * move: cover => /(_ (r_end gam) (ltac:(lra))).
        rewrite r_eq //=.
      * move: cover => /(_ (l_end gam) (ltac:(lra))).
        rewrite l_eq //=.
  - move => z [+ /is_RInt_unique ->].
    apply.
Qed.

Open Scope C.
Lemma C_sum_pow_n: forall (z : C) (n : nat),
  z <> 1 ->
  sum_n [eta Cpow z] n = ((1 - (Cpow z (S n))) / (1 - z)).
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
    field_simplify_eq; auto.
  - move => n IH.
    simpl.
    rewrite sum_Sn /plus /= IH //=.
    field_simplify_eq; last by auto.
    auto.
Qed.

Lemma Cmod_lt_1_neq_1: forall z, Cmod z < 1 -> z <> 1.
Proof.
  move => z lt1 H.
  rewrite H Cmod_1 in lt1.
  lra.
Qed.

Global Instance abs_locally_filter: forall z,
  Filter (@locally (AbsRing_UniformSpace C_AbsRing) z).
Proof.
  move => z.
  constructor.
  - apply/locally_C.
    apply filter_true.
  - move => P Q /locally_C H1 /locally_C H2.
    apply/locally_C.
    apply filter_and; auto.
  - move => P Q impl /locally_C H.
    apply: filter_imp.
    1: apply impl.
    apply/ locally_C.
    auto.
Qed.


Lemma is_series_geom_C: forall z, 
  Cmod z < 1 -> is_series (fun n => Cpow z n) (1/(1-z)).
Proof.
  move => z Hq.
  have?:(1 - z <> 0) by
    move: Hq => /Cmod_lt_1_neq_1 H1 H2; contradict H1;
    rewrite -[LHS]Cplus_0_l -H2;
    field_simplify_eq.
  apply filterlim_ext with (fun n => (1/(1-z))+ -(Cpow z (S n)) / (1-z)). {
    move => n.
    rewrite C_sum_pow_n.
    auto.
    field_simplify_eq; auto.
    apply Cmod_lt_1_neq_1. auto.
  }
  rewrite -[x in filterlim _ _ (locally x)]Cplus_0_r.
  apply: (filterlim_comp_2 ).
  1: apply filterlim_const.
  2: apply: (@filterlim_plus _ _ (1/(1-z))).
  apply: filterlim_comp_2.
  2: apply filterlim_const.
  2: rewrite /Cdiv; apply: filterlim_comp_2. 
  3: apply: filterlim_fst.
  3: apply: filterlim_comp.
  3: apply: filterlim_snd.
  4: apply: continuous_Cinv; auto.
  4: apply: filterlim_filter_le_2.
  5: apply: filterlim_filter_le_1.
  6: apply: Hierarchy.filterlim_mult.
  6: apply (RtoC 0).
  6: apply (/(1-z)).
  4: rewrite /mult //= Cmult_0_l //=.
  4: move => P H; apply/ prod_c_topology_eq; auto.
  4: { move => P [Q R F1 F2 impl].
       apply: Filter_prod .
       2: apply/prod_c_topology_eq; apply F2.
       1: apply F1.
       auto.
  }
  2: apply: filter_prod_filter .
  2: apply: abs_locally_filter.
  apply: filterlim_comp.
  2: apply: filterlim_filter_le_2. 
  3: apply: filterlim_opp. 
  3: apply zero.
  2: rewrite /opp /zero //= Copp_0; move => P H; 
     apply/ prod_c_topology_eq; auto.
  apply filterlim_norm_zero .
  rewrite /norm /=. 
  eapply filterlim_ext. {
    move => x.
    rewrite Cmod_mult Cpow_cmod.
    reflexivity.
  }
  have Hq' : Cmod z = Rabs (Cmod z) by
    rewrite Rabs_pos_eq;[ auto | apply Cmod_ge_0] .
  rewrite Hq' in Hq.
  apply: filterlim_comp_2.
  1: apply filterlim_const.
  1: apply: is_lim_seq_geom _ Hq.
  replace (locally 0) with (locally (Cmod z * 0)%R).
  2: f_equal; lra.
  apply: Hierarchy.filterlim_mult.
Qed.

Definition PCoef := 1/(2*PI* Ci).

Theorem holo_analytic : forall (f:C -> C) (r r': posreal ) z, 
  r' < r ->
  CHolo_on (ball z r) f ->
  forall a, ball z r' a ->
  
  @is_pseries 
    C_AbsRing
    C_NormedModule
    (fun n => PCoef * CInt (circC a r') 
      (fun w => f(w)/(Cpow (w-a) n))
    ) a (f a).
Proof.
  move => f r r' z r'ler CHolo a aball.

  `Begin eq (f(z)). {

  | {( PCoef * CInt (circC z r') ( fun w => (f w)/(w-z)) )} 
    rewrite (@cauchy_integral_formula f r); auto.

  | {( PCoef * CInt _ (fun w => (f w)/((w-a) - (z-a))) )} idtac.
    rewrite (@cauchy_integral_formula f r); auto.

  }

