
Require Import Reals Psatz Lra RelationClasses List.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex
  RInt RInt_analysis Derive_2d Compactness.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Require Import domains ext_rewrite real_helpers.
Require Import domains cauchy_riemann path_independence cauchy_integral .

Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.
Section LocallyUniform.

Context {U V:UniformSpace}.

Definition locally_uniform_sub  (D: U -> Prop) f (P: (U -> V) -> Prop) : Prop := 
  exists (eps:posreal) x (del:posreal), D x /\ forall g, 
      (forall x', ball x del x' -> ball (f x') eps (g x')) -> 
      P g
  .

Inductive locally_uniform (D: U -> Prop) f (P: (U -> V) -> Prop) : Prop :=
  | Single: locally_uniform_sub D f P  -> locally_uniform D f P
  | Intersect: forall Q1 Q2, 
    (forall z, Q1 z /\ Q2 z -> P z) -> 
    locally_uniform D f Q1 -> 
    locally_uniform D f Q2 -> 
    locally_uniform D f P. 
  

Global Instance locally_uniform_filter: forall D f,
  (exists z0, D z0) ->
  ProperFilter (locally_uniform D f).
Proof.
  move => D f [z0 z0D].
  constructor;[| constructor].
  - move => P cpt. exists f.
    elim: cpt.
    + move => ? [eps [x [del [Dx +]]]].
      apply.
      move => *.
      apply: ball_center.
    + move => P0 Q R pand _ ? _ ?.
      apply pand; tauto.
  - constructor. 
    exists pos_half.
    exists z0.
    exists pos_half.
    split; first by auto.
    move => * //=.
  - move => P Q lP lQ.
    apply: Intersect. 
    + move => z. apply.
    + auto.
    + auto.

  - move => P + + H. 
    case: H.
    + move => [eps [u [del[Du H]]]] Q Qimpl. 
      constructor.
      exists eps, u, del. 
      split; first by auto.
      move => y yball.
      apply Qimpl.
      apply H.
      auto.
    + move => Q1 Q2 impl lQ1 lQ2 Q Qimpl.
      apply: Intersect.
      3: apply lQ2.
      2: apply lQ1.
      firstorder.
Qed.

Definition contour_inside (g:Contour) D:= 
  forall t, l_end g <= t <= r_end g -> D (gamma g t).
  
Definition OnPaths (D: C -> Prop) f (P: (C -> C) -> Prop) : Prop := 
  forall (gam:Contour), 
    contour_inside gam D ->
  (exists (del:posreal), forall g,
     (forall t, l_end gam <= t <= r_end gam -> 
     Cmod (g (gamma gam t) - f (gamma gam t)) < del) -> 
   P g
  ).

Lemma locally_uniform_le_uniform: forall D f,
  (exists z0, D z0) ->
  filter_le (locally f) (locally_uniform D f).
Proof.
  move => D f [z0 Dz0] ?. 
  elim. 
  + move => P [eps[x[del [Dx H']]]].
    exists eps => g gball.
    apply H'.
    move => z _.
    apply gball.
  + move => P Q1 Q2 impl unifQ1 lQ1 unifQ2 lQ2.
    have:=  @filter_and _ _ _ _ _ lQ1 lQ2.
    move => /(_ ltac:(apply locally_filter)) H.
    apply: filter_imp H; auto.
Qed.

End LocallyUniform.

Section LocallyConverge.

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

Lemma CInt_gamma_ext: forall g1 g2 f, 
  (l_end g1 = l_end g2) -> 
  (r_end g1 = r_end g2) -> 
  (forall t, l_end g1 <= t <= r_end g1 -> 
    gamma g1 t = gamma g2 t) ->
  (forall t, l_end g1 <= t <= r_end g1 -> 
    gamma' g1 t = gamma' g2 t) ->
  CInt g1 f = CInt g2 f.
Proof.
  move => g1 g2 f lend rend ext ext'.
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
Open Scope C.
Lemma uniform_limits_CInt : forall 
  (D: C -> Prop)
  (f_: T -> C -> C)
  (flim : C -> C)
  (gam: Contour),
  open D ->
  contour_inside gam D ->
  (forall u, cts_on_contour (f_ u) gam) ->
  filterlim f_ F (locally_uniform D flim) -> 
  filterlim (fun u => CInt gam (f_ u)) F (locally (CInt gam flim)).
Proof.
  move => D f_ flim gam openD gam_in_D cts H.

  wlog: gam gam_in_D cts / 
    exists M : posreal, forall z : R_UniformSpace, norm (gamma' gam z) < M. {
      pose gam2 := {|
        gamma := extension_C1 (gamma gam) (gamma' gam) (l_end gam) (r_end gam);
        gamma' := extension_C0 (gamma' gam) (l_end gam) (r_end gam);
        l_end := l_end gam;
        r_end := r_end gam;
        endpoint_interval := endpoint_interval gam;
        contour_derive := ltac:( move => *; apply:extension_C1_is_derive;
        [ rewrite /Rbar_le; left; apply: endpoint_interval
        | rewrite /Rbar_le; move => *; apply contour_derive; auto
        ]);
        cts_derive := ltac:(move => *; apply: extension_C0_continuous;
        [ rewrite /Rbar_le; left; apply: endpoint_interval
        | rewrite /Rbar_le; move => *; apply cts_derive; auto
        ])
      |}.
      move => /(_ (gam2)) H'.
      rewrite (@CInt_gamma_ext gam gam2); auto.
      eapply filterlim_ext.
        move => t.
        rewrite (@CInt_gamma_ext gam gam2); auto.
      reflexivity.
      all: simpl. 
      1,4: move => *;symmetry; apply extension_C1_ext; simpl; lra.
      1,3: move => *;symmetry; apply extension_C0_ext; simpl; lra.
      apply H'.
      - rewrite /contour_inside //=.
        move => t tbd.
        rewrite extension_C1_ext; simpl; auto.
        all: simpl; lra.
      - rewrite /cts_on_contour //=.
        move => u t tbd.
        rewrite extension_C1_ext; simpl; auto.
        apply: cts; lra.
        all: lra.
      - have := bounded_continuity (gamma' gam) (l_end gam2) (r_end gam2).
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
          apply Mbd.
          split; [reflexivity | left; apply endpoint_interval ].
        }
        move => Q.
        exists (mkposreal _ Q).
        simpl.
        move => z.
        case: (Rle_dec (l_end gam) z ) => zbd1;
        case: (Rle_dec z (r_end gam) ) => zbd2.
        + apply Mbd; split; auto.
        + rewrite /extension_C0.
          destruct_match.
          clear l.
          destruct_match.
          all: apply Mbd.



      m
      move => H2.
      destruct H2.
      case.

  }

  rewrite /CInt.
  have := @filterlim_RInt T
          (C_R_CompleteNormedModule) 
          (fun u t => f_ u (gamma gam t) * gamma' gam t)
          (l_end gam)
          (r_end gam) 
          F
          (ltac:(auto))
          (fun t => flim (gamma gam t) * gamma' gam t)
          (fun u =>  RInt (V:=C_R_CompleteNormedModule)
                     (fun t : R => f_ u (gamma gam t) * gamma' gam t) 
                     (l_end gam) (r_end gam)  ).
  case. 
  - move => u. 
    apply RInt_correct. 

    apply ex_CInt_RInt, cts_CInt; auto.
  - apply filterlim_mult.
    1: admit.
    move => P [del L].
    move: H => /(_ (fun h => P(fun t => h (gamma gam t) ))).
    apply.
    case (sqr_dec a b c d (gamma gam t)) => sqr;[split|].
    + set z := (gamma gam t).
      set z' := (gamma' gam t).
      set p := (x in Rabs x).
      Open Scope R.
      replace p with ((((h z).1 - (flim z).1) * z'.1) - 
                      (((h z).2 - (flim z).2) * z'.2)).
      
      2: rewrite /p; field_simplify. 
      2: apply Rplus_eq_compat_l.

      simplify_R p.
      admit.
    + rewrite hball_out; last by auto.
      set p := (x in Rabs x). 
      simplify_R p.
      rewrite Rabs_R0.
      set p := (x in Rabs x). 
      simplify_R p.
      rewrite Rabs_R0.
      split; apply cond_pos.
  - move => z [+ /is_RInt_unique ->].
    apply.
Admitted.

  apply/ filterlim_locally => eps.

  rewrite /filterlim /filter_le /filtermap in H.
  move:H.
  move => /(_ (fun t => 
    ball (CInt gam flim) eps (CInt gam t ))).
  apply.
  move => 
  eexists ?[del].
  move => g gbd.
  rewrite (@lock _ CInt).
  unfold_alg.
  rewrite -lock.
  Check ().





  True.
  wlog ext : f_ flim H cts / 
    (forall z, ~( exists t, l_end gam <= t <= r_end gam  -> z = gamma gam t)
                   -> forall u, f_ u z = flim z).
  admit.

  (* need to pull back open balls from C to R.
     Should be able to use open_comp to get this*)
(* 
  pose delta := (fun t => 
      match Rlt_dec t (l_end g) with 
      | left _ => pos_div_2
          (proj1_sig (locally_ex_dec 
            (gamma g (l_end g)) D 
            (decD) 
            (ltac:(apply openD; apply inD; split;
                   [ reflexivity
                   | left; apply endpoint_interval 
                   ]
                   ))))
      | right pf1 => 
        match Rlt_dec (r_end g) t with 
        | left pf2 => pos_div_2
            (proj1_sig (locally_ex_dec 
               (gamma g (r_end g)) D 
               (decD) 
               (ltac:(apply openD; apply inD; split;
                    [ left; apply endpoint_interval 
                    | reflexivity
                    ]
                    ))))
        | right pf2 => pos_div_2
            (proj1_sig (locally_ex_dec 
              (gamma g t) D 
              (decD) 
              (ltac:(apply openD; apply inD; lra))))
        end
      end).
  have := (compactness_list 1 (l_end g,tt) (r_end g,tt) 
    (fun t => delta (fst t))).
  rewrite /bounded_n.
  have := (compactness_value_1d (l_end g) (r_end g) 
    (delta)). move  => [del H].
  move => /NNPP [l H].
  induction l.
  - move: H => /( _ (l_end g,tt)).
    case.
    + rewrite /bounded_n; auto.
  set comp := (x in not(not x)) in H.
  move 
  have: comp. { 
    apply/negPn.  Decidable

    case: H.  
    contradict H.
    apply H.  

  }

  move => H.
  

  rewrite /delta in n.

  Locate proj1_sig. (locally_ex_dec x _ (H0 x) (H x))).
  pose: 


  
Axiom classic : forall P:Prop, P \/ ~ P.

Lemma NNPP : forall p:Prop, ~ ~ p -> p.
Proof.
unfold not in |- *; intros; elim (classic p); auto.
intro NP; elim (H NP).
Qed. *)