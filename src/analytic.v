
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

(*The topology of compact convergence*)

Definition Compactly_on (D: C -> Prop) f (P: (C -> C) -> Prop) : Prop := 
  forall a b c d, 
  (forall z, a <= z.1 <= b -> c <= z.2 <= d -> D z) -> 
  (exists (del:posreal), forall g,
     (forall z, a <= z.1 <= b -> c <= z.2 <= d -> Cmod (g z - f z) < del) -> 
     (forall z, ~(a <= z.1 <= b -> c <= z.2 <= d ) -> f z = g z) ->
   P g
  ).

Lemma sqr_dec : forall a b c d z,
  (a <= z.1 <= b -> c <= z.2 <= d ) \/ ~(a <= z.1 <= b -> c <= z.2 <= d ).
Proof.
  move => a b c d z.
  case (Rle_dec a z.1); 
  case (Rle_dec z.1 b); 
  case (Rle_dec c z.2); 
  case (Rle_dec z.2 d);
  tauto.
Qed.

Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.

Global Instance compactly_filter: forall D f,
  open D -> 
  (exists z0, D z0) ->
  ProperFilter (Compactly_on D f).
Proof.
  move => D f openD [z0 z0D].
  repeat constructor.
  - move => P cpt; exists f.
    eapply locally_open in z0D; eauto.
    move: z0D => [del z0D].
    have?:= cond_pos del.
    have?: 0 < del/2 by lra.
    move: cpt => /(_ 
      (z0.1 - del/4) 
      (z0.1 + del/4) 
      (z0.2 - del/4) 
      (z0.2 + del/4) )%R.
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
      rewrite Cminus_eq_0 Cmod_0 //=.
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
    1,2: move => zbd1 zbd2; apply: Rlt_le_trans. 
    2: apply Rmin_l. 
    3: apply Rmin_r.
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

(* Lemma squares_implies_patches: forall D f P, 
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
Qed. *)

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
  exists del.
  move => g gbd_in gbd_out.
  apply loc.
  rewrite /ball //= /fct_ball.
  move => z.
  destruct (sqr_dec a b c d z) .
  - unfold_alg. 
    rewrite -?/(Rminus _ _).
    apply gbd_in.

  
  

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
    have : ( 
          @filterlim T (R -> C_R_CompleteNormedModule)
            (fun (u : T) (t : R) => f_ u (gamma gam t)) F
            (@locally (fct_UniformSpace R C_R_CompleteNormedModule)
            (fun t : R => flim (gamma gam t)))). 
    {  
        eapply (@filterlim_comp T (C -> C) (R -> C)
          _ (fun h t => h(gamma gam t)) ) in H.
        apply H.
        apply: (@filterlim_filter_le_1 _ _ (locally flim)).
        admit.  
        apply/filterlim_locally => eps.
        exists eps => y.
        unfold_alg.
        rewrite /fct_ball /ball //= /prod_ball .
   }
   admit.

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