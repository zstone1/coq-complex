
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

Context {U:UniformSpace}.

Definition locally_uniform_sub  (D: U -> Prop) f (P: (U -> U) -> Prop) : Prop := 
  exists (del:posreal) x, D x /\ locally x (fun x' => D x' /\
    (forall g, (ball (f x') del (g x')) -> P g)
  ).

Inductive locally_uniform (D: U -> Prop) f (P: (U -> U) -> Prop) : Prop :=
  | Single: locally_uniform_sub D f P  -> locally_uniform D f P
  | Intersect: forall Q1 Q2, 
    (forall z, Q1 z /\ Q2 z -> P z) -> 
    locally_uniform D f Q1 -> 
    locally_uniform D f Q2 -> 
    locally_uniform D f P. 
  

Global Instance locally_uniform_filter: forall D f,
  open D -> 
  (exists z0, D z0) ->
  ProperFilter (locally_uniform D f).
Proof.
  move => D f openD [z0 z0D].
  constructor;[| constructor].
  - move => P cpt. exists f.
    elim: cpt.
    + move => Q [del [x [_ [del2 /(_ x) ]]]].
      case; first by apply: ball_center.
      move => _.
      apply. 
      apply: ball_center.
    + move => P0 Q R pand _ ? _ ?.
      apply pand; tauto.
  - constructor. 
    exists pos_half.
    exists z0.
    split; first by auto.
    apply (filter_imp (D)) .
    + move => x Dx; split; auto.
    + apply: locally_open; eauto.
  - move => P Q lP lQ.
    apply: Intersect. 
    + move => z. apply.
    + auto.
    + auto.

  - move => P + + H. 
    case: H.
    + move => [eps [u [Du [del H]]]] Q Qimpl. 
      constructor.
      exists eps, u. 
      split; first by auto.
      exists del => y yball.
      split; first by apply H.
      move => g gball.
      apply Qimpl.
      move:H => /(_ y yball ) [_ H].
      apply H.
      auto.
    + move => Q1 Q2 impl lQ1 lQ2 Q Qimpl.
      apply: Intersect.
      3: apply lQ2.
      2: apply lQ1.
      firstorder.
Qed.


      move => lQ1 Q1impl lQ2 Q2impl Qimpl.
      apply Q1impl; move => 
      


      


    + move => P0.
    
    elim: cpt.
    case.
    + move => z [r1 r2] [r3 r4]. 
      apply z0D.
      unfold_alg.
      rewrite -!/(Rminus _ _).
      rewrite ?Rabs_lt_between'. 
      do 2 split;
      [ apply: (@Rlt_le_trans _ (z0.1 - del/2))
      | apply: (@Rlt_le_trans _ (z0.1 + del/2))
      | apply: (@Rlt_le_trans _ (z0.2 - del/2))
      | apply: (@Rlt_le_trans _ (z0.2 + del/2))
      ]; 
      try (apply Rplus_lt_compat_l); 
      try (apply Rplus_le_compat_l); 
      try lra.
    + move => x. 
      have xge0:= cond_pos x.
      apply => *.
      unfold_alg.
      rewrite -?/(Rminus _ _).
      rewrite !Rminus_eq_0 ?Rabs_R0 //=.
      reflexivity.
  - move => *. exists pos_half; auto.
  - move => P Q C1 C2.
    move => a b c d sqr_in.
    move: C1 => /(_ a b c d sqr_in) [del1 H1].
    move: C2 => /(_ a b c d sqr_in) [del2 H2].
    pose del := (Rmin del1 del2).
    exists (mkposreal _ (@Rmin_stable_in_posreal del1 del2)).
    move => g gbd_in gbd_out.
    split; [apply H1| apply H2] => z. 
    2,4: auto.
    1,2: move => zbd1 zbd2; apply: ball_le.
    1: apply Rmin_l. 
    2: apply Rmin_r.
    all: apply gbd_in; eauto.
  - move => P Q impl C.
    move => a b c d sqr_in.
    move :C  => /(_ a b c d sqr_in) [del H].
    exists del => g gbd_in gbd_out.
    apply impl.
    apply H.
    auto.
    auto.
Qed.

Fixpoint in_patch (l: list (R*R*R*R)):  C -> Prop := 
  match l with 
  | nil => fun => False
  | s :: l' => fun z => 
    let: (a,b,c,d) := s in 
      (a <= z.1 <= b /\ c <= z.2 <= d) \/ (in_patch l' z)
  end.
  
 Definition OnPatches (D: C -> Prop) f (P: (C -> C) -> Prop) : Prop := 
  forall (l: list (R *R * R*R)), 
    l <> [] -> 
    (forall z, in_patch l z -> D z) ->
  (exists (del:posreal), forall g,
     (forall z, in_patch l z -> Cmod (g z - f z) < del) -> 
     (forall z, ~(in_patch l z) -> f z = g z) -> 
   P g
  ).

 Lemma squares_implies_patches: forall D f P, 
  Compactly_on D f P -> OnPatches D f P.
Proof.
  move => D f P com.
  elim; first by auto.
  move => [[[a b] c ] d].
  case. { move => _ _ sqr.
    move:com => /(_ a b c d).
    case.
    - move => z xbd ybd.
      apply sqr.
      rewrite /in_patch. left.
      tauto.
    - move => del H. 
      exists del.
      move => g gbd_in gbd_out.
      apply H.
      + move => ???. apply gbd_in.
        rewrite /in_patch. tauto.
      + move => ??. apply gbd_out; 
        rewrite /in_patch. tauto.
  }
  move => q l H1 _ zbd.
  move :H1.
  case; first by auto. {
    
    move => z patch . 
    apply zbd.
    rewrite {1}/in_patch.
    right.
    auto.
  }
  move => del1 H1.
  exists del1 .
  move => g gbd_in gbd_out.
  apply H1 => z H.
  + apply gbd_in.
    right.
    auto.
  + apply gbd_out.
    rewrite /in_patch   .
    admit.
Admitted.  *)

(* Lemma patches_iff_squares: forall D f P, 
  Compactly_on D f P <-> OnPatches D f P.
Proof.
  move => D f P.
  split; first by apply: squares_implies_patches.
  move => patches a b c d.
  move => zbd.
  move: patches => /(_ [(a,b,c,d)]).
  case; first by auto.
  - rewrite /in_patch => *; apply zbd; tauto.
  - move => del H.
    exists del => g gbd.
    apply H => z' z'bd.
    apply gbd;
    rewrite /in_patch in z'bd;
    tauto.
Qed. *)


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

Lemma compact_le_uniform: forall D f,
  filter_le (Compactly_on D f) (locally f).
Proof.
  move => D f P [del loc].
  move => a b c d sqr.
  exists (del).
  move => g gbd_in gbd_out.
  apply loc.
  rewrite /ball //= /fct_ball.
  move => z.
  destruct (sqr_dec a b c d z) .
  - apply: gbd_in; tauto.
  - rewrite gbd_out; auto.
    apply ball_center.
Qed.
  

  
  

Lemma uniform_limits_CInt : forall {T: UniformSpace} 
  (D: C -> Prop)
  F
  (f_: T -> C -> C)
  (flim : C -> C)
  (gam: Contour),
  open D ->
  contour_inside gam D ->
  (forall u, cts_on_contour (f_ u) gam) ->
  ProperFilter F ->
  filterlim f_ F (Compactly_on D flim) -> 
  filterlim (fun u => CInt gam (f_ u)) F (locally (CInt gam flim)).
Proof.
  move => T D F f_ flim gam openD gam_in_D cts FF H.
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
  - Set Printing Implicit.
    rewrite /filterlim /filtermap /filter_le.
    move => P [del L].
    move: H => /(_ (fun h => P(fun t => h (gamma gam t) * gamma' gam t ))).
    apply.
    move => a b c d sqrbd.
    exists del => h hball_in hball_out.
    apply L.
    unfold_alg.
    rewrite /fct_ball /ball //= /prod_ball .
    unfold_alg => t.

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