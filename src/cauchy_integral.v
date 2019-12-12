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


Require Import domains cauchy_riemann path_independence.

Open Scope program_scope.
Open Scope general_if_scope.
Require Import domains ext_rewrite real_helpers.

Section CauchyIntegral.
Open Scope C.
Definition c_circle (r: R) (t:R):C := r * (cos t, sin t).
Definition c_circle' (r: R) (t:R):C := r * (-sin t, cos t)%R.

Open Scope R.

Lemma c_circle_norm: forall r t,
  Cmod( (r*cos t, r * sin t)) = Rabs r.
Proof.
  move => r t.
  elim_norms.
  - nra.
  - field_simplify_eq. 
    rewrite -Rmult_plus_distr_l Rplus_comm 
            -?Rsqr_pow2 sin2_cos2.
    lra.
Qed.
Lemma differentiable_pt_scal: forall f x y,
  ex_derive f y -> 
  differentiable_pt (fun p q => p * f q) x y.
Proof.
  move => f x y Ex.
  eexists; eexists.
  apply/filterdiff_differentiable_pt_lim. 
  apply: (@is_derive_filterdiff (fun p q => p * f q)). 
  - apply global_local => x'; auto_derive; eauto; field_simplify;
      instantiate (1:= fun _ q => f q); auto.
  - auto_derive; auto. 
  - apply continuous_comp; simpl; try auto_continuous_aux.
    apply: ex_derive_continuous.
    auto_derive; auto.
Qed.
Lemma differentiable_pt_proj2: forall f x y,
  ex_derive f y -> 
  differentiable_pt (fun p q => f q) x y.
Proof.
  move => f x y Ex.
  eexists; eexists.
  apply/filterdiff_differentiable_pt_lim. 
  apply: (@is_derive_filterdiff (fun p q =>  f q)). 
  - apply global_local => x'; auto_derive; eauto.
      instantiate (1:= fun _ _ => 0); auto.
  - auto_derive; auto. 
  - apply continuous_const. 
Qed.

Lemma differentiable_pt_ext: forall f g x y,
  (forall p q, f p q = g p q) -> 
  differentiable_pt f x y <-> differentiable_pt g x y.
Proof.
  split; move => [? [? G]]; eexists; eexists; 
  eapply differentiable_pt_lim_ext.
  - exists pos_half => *. apply H.
  - eauto.
  - exists pos_half => *. symmetry. apply H.
  - eauto.
Qed.
    
Lemma differentiable_pt_plus: forall f k x y,
  differentiable_pt f x y -> differentiable_pt (fun p q => k + f p q) x y.
Proof.
  move => f k x y [d1 [d2 D]].
  apply differentiable_pt_comp.
  - exists 1. exists 1. apply filterdiff_differentiable_pt_lim. 
    eapply filterdiff_ext_lin.
    apply filterdiff_linear.
    apply: is_linear_plus.
    move => *; simpl; lra.
  - exists 0. exists 0; apply filterdiff_differentiable_pt_lim. 
    eapply filterdiff_ext_lin.
    apply: filterdiff_const.
    move => * //=.
    rewrite /zero //=; lra.
  - exists d1; exists d2; auto.
Qed.


Lemma smooth_circ: forall z r t, 
  SmoothPath (fun r t => z.1 + r * cos t)%R ( fun r t => z.2 + r * sin t)%R r t.
Proof.

  Ltac rerwite_under f := 
    let l := fresh in 
    under differentiable_pt_ext => p q do (
      set l := Derive _ _;
      replace l with f
    )
    ;
    rewrite /l; symmetry;
    apply: is_derive_unique;
    auto_derive; auto; field_simplify; auto;
    apply: differentiable_pt_scal;
    auto_derive; auto.
  Ltac replace_Derive := 
    eapply continuity_2d_pt_ext;[ move => x y;
      eapply Derive_ext => z;
        symmetry;
        apply is_derive_unique;
        auto_derive; auto;
        field_simplify; auto | ];
    eapply continuity_2d_pt_ext;[ move => x y;
        symmetry;
        apply is_derive_unique;
        auto_derive; auto;
        field_simplify; auto | ].
  move => r t; repeat split; [exists pos_half | exists pos_half | .. ]; repeat split.
  7-10: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply: differentiable_pt_plus.
    apply differentiable_pt_scal; auto_derive; auto.
  - apply (@differentiable_pt_ext _ (fun p q => (p * (- sin q))));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_scal; auto_derive; auto
    ].
  - apply (@differentiable_pt_ext _ (fun p q => cos q));
    [ move => *; apply: is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_proj2; auto_derive; auto
    ].
    
  - apply differentiable_pt_plus.
    apply differentiable_pt_scal; auto_derive; auto.
  - apply (@differentiable_pt_ext _ (fun p q => (p * (cos q))));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_scal; auto_derive; auto
    ].
  - apply (@differentiable_pt_ext _ (fun p q => sin q));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_proj2; auto_derive; auto
    ].
Qed.

Open Scope C.
Definition CHolo f f' z := 
  Holo f f' z /\ continuous f' z.
Definition CHolo_on D f := exists f',
  forall z, D z -> CHolo f f' z.

Lemma circ_independence : forall (f: C -> C) z (r:posreal) (r' r'': R),
  CHolo_on (ball z r) f ->
   r' < r'' ->
  -r < r' < r ->
  -r < r'' < r ->
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f (z + c_circle r' t0) * c_circle' r' t0) 0 (2 * PI) =
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f(z + c_circle r'' t0) * c_circle' r'' t0) 0 (2 * PI).
Proof.
  move => f z r r' r'' [f' holo] ? [? ?] [? ?].
  
  have indep := @path_independence_part_4 
                (-PI)%R (3*PI) 0 (2*PI)
                (-r) r r' r''
                f f' 
                (fun r t => z.1 + r * cos t)%R
                (fun r t => z.2 + r * sin t)%R.
  have pig0 := PI_RGT_0.
  have rpos := cond_pos r.
  case: indep.
  2-5: rewrite Rmin_left; last (by lra); rewrite Rmax_right; lra.
  - auto.
  - move => r0 t r0bd tbd.
    rewrite Rmax_right in r0bd; last by lra.
    rewrite Rmin_left in r0bd; last by lra.
    move : r0bd => [??].
    rewrite -and_assoc.
    split.
    + move: holo => /(_ ( z + c_circle r0 t)).
      case. {
        unfold_alg ; rewrite /AbsRing_ball; unfold_alg.
        set p := _ + _.
        simplify_as_R2 e p.
        rewrite c_circle_norm. 
        destruct (Rlt_dec r0 0).
        - rewrite Rabs_left; lra.
        - rewrite Rabs_pos_eq; lra.
      }
      set p := z + _.
      simplify_as_R2 e p.
      auto.
    + have:= smooth_circ z r0 t. apply.
  - move => r0 r0bd.
    rewrite Rmax_right in r0bd; last by lra.
    rewrite Rmin_left in r0bd; last by lra.
    move : r0bd => [??].
    split;
    rewrite cos_0 sin_0 cos_2PI sin_2PI; auto.
  - move => I1 [I2 H].
    under RInt_ext => t0 _.
      set p := z + _.
      simplify_as_R2 e p.
      rewrite /c_circle'.
      set p := r' * _.
      simplify_as_R2 e p.
      replace (-r'* sin t0)%R with (Derive (fun t : R => (z.1 + r' * cos t)%R) t0).
      2: apply is_derive_unique; auto_derive; auto; lra.
      replace (r'* cos t0)%R with (Derive (fun t : R => (z.2 + r' * sin t)%R) t0) at 2.
      2: apply is_derive_unique; auto_derive; auto; lra.
    over.
    rewrite H.
    symmetry.
    under RInt_ext => t0 _.
      set p := z + _.
      simplify_as_R2 e p.
      rewrite /c_circle'.
      set p := r'' * _.
      simplify_as_R2 e p.
      replace (-r''* sin t0)%R with (Derive (fun t : R => (z.1 + r'' * cos t)%R) t0).
      2: apply is_derive_unique; auto_derive; auto; lra.
      replace (r''* cos t0)%R with (Derive (fun t : R => (z.2 + r'' * sin t)%R) t0) at 2.
      2: apply is_derive_unique; auto_derive; auto; lra.
    over.
    auto.
Qed.
      
      
Lemma cauchy_integral_theorem_circ : forall (f: C -> C) z (r r':posreal),
  r' < r ->
  CHolo_on (ball z r) f ->
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f (z + c_circle r' t0) * c_circle' r' t0) 0 (2 * PI) = zero.
Proof.
  move => f z r r' ? holo .
  have? := cond_pos r.
  have? := cond_pos r'.
  rewrite -(@circ_independence f z r 0 r').
  3-5: lra.
  2: auto.
  under RInt_ext => t _.
    rewrite /c_circle'.
    set p := _ * _.
    simplify_as_R2 e p.
    replace (0,0) with (zero (G:= C_AbelianGroup)); last by auto.
  over.
  rewrite RInt_const.
  rewrite scal_zero_r.
  auto.
Qed.
  
Record Contour := mkContour {
  gamma: R -> C; 
  gamma': R -> C;
  l_end: R;
  r_end: R;
  endpoint_interval: l_end < r_end;
  contour_derive: forall t, l_end < t < r_end -> is_derive gamma t (gamma' t);
}.
Open Scope C. 
Definition is_CInt (g: Contour) (f: C -> C) (z:C) :=
  is_RInt (fun t => f (gamma g t) * (gamma' g t)) (l_end g) (r_end g) z.
Definition CInt {g: Contour } f := 
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t => f (gamma g t) * (gamma' g t)) (l_end g) (r_end g) .

Program Definition circC (z:C) (r: posreal) := {|
  gamma := fun t => z + c_circle r t;
  gamma' := c_circle' r;
  l_end := 0;
  r_end := 2*PI;
|}.
Obligation 1. 
Proof. have:= PI_RGT_0; lra. Qed.
Obligation 2. 
Proof. 
  rewrite /c_circle /c_circle'.
  under ext_is_derive_glo => y.
    set p := _ + _.
    simplify_as_R2 e p.
  over.
  set p := _ * _.
  simplify_as_R2  e p.
  apply (is_derive_pair 
    (f := fun q => z.1 + r * cos q) 
    (g := fun q => z.2 + r * sin q)
    (f' := fun q => -r * sin q)
    (g' := fun q => r * cos q)
  )%R; auto_derive_all. 
Qed.

Theorem cauchy_integral_theorem: forall (f: C -> C) z (r r':posreal),
  r' < r ->
  CHolo_on (ball z r) f ->
  CInt (g:= circC z r') f = zero.
Proof.
  move => f z r r' r'bd holo.
  rewrite /CInt //=.
  rewrite (@cauchy_integral_theorem_circ f z r r'); auto.
Qed.

Lemma rmult_scal : forall (r:R) (z:C),
  (RtoC r) * z = scal r z.
Proof.
  move => r [z1 z2]. unfold_alg; rewrite /prod_scal /Cmult.
  simpl.
  set p := LHS.
  simplify_as_R2 e p.
  set p := RHS.
  simplify_as_R2 e p.
Qed.
