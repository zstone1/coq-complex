
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

Open Scope C.
Definition c_circle (r: R) (t:R):C := r * (cos t, sin t).
Definition c_circle' (r: R) (t:R):C := r * (-sin t, cos t)%R.

Open Scope R.

Definition SmoothPath' g r t:= 
  differentiable_pt g r t /\
  differentiable_pt (fun p q => Derive (g p) q) r t /\
  differentiable_pt (fun p q => Derive (g ^~ q) p) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g z t) v) u) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g t z) u) v) r t
.

Lemma smoothpath'_smoothpath : forall g1 g2 r t, 
  locally_2d (SmoothPath' g1) r t ->
  locally_2d (SmoothPath' g2) r t -> 
  SmoothPath g1 g2 r t.
Proof.
  move => g1 g2 r t H1 H2.
  split;[|split].
  - apply: locally_2d_impl H1.
    apply: locally_2d_forall.
    move => >. rewrite /SmoothPath'. tauto.
  - apply: locally_2d_impl H2.
    apply: locally_2d_forall.
    move => >. rewrite /SmoothPath'. tauto.
  - move: H1 => /locally_2d_singleton.
    move: H2 => /locally_2d_singleton.
    rewrite /SmoothPath'.
    tauto.
Qed.

 
  

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
Lemma differentiable_pt_proj1: forall f x y,
  ex_derive f x -> 
  differentiable_pt (fun p q => f p) x y.
Proof.
  move => f x y [??].
  eexists; eexists.
  apply: differentiable_pt_lim_proj1_0 .
  apply/ is_derive_Reals.
  eauto.
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

Lemma differentiable_pt_ext_loc: forall f g x y,
  locally_2d (fun p q => f p q = g p q) x y -> 
  differentiable_pt f x y <-> differentiable_pt g x y.
Proof.
  move => f g x y /locally_2d_locally loc_eq.
  split; move => [? [? /filterdiff_differentiable_pt_lim G]]; eexists; eexists;
  apply/ filterdiff_differentiable_pt_lim;
  [ |
  have {}loc_eq: locally (x,y) (fun z => g z.1 z.2 = f z.1 z.2) by
      apply: filter_imp loc_eq;
      move => *; congruence
  ];
  apply: (filterdiff_ext_loc _ _ _ loc_eq).
  - apply locally_filter.
  - move => p /is_filter_lim_locally_unique <- //=.
    move: loc_eq => /locally_singleton //=.
  - eauto.
  - apply locally_filter.
  - move => p /is_filter_lim_locally_unique <- //=.
    move: loc_eq => /locally_singleton //=.
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
Lemma smooth_cos: forall r t, 
  SmoothPath' (fun r t => r * cos t) r t.
Proof.
  move => r t; repeat split. 
  4,5: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply differentiable_pt_scal; auto_derive; auto.
  - apply (@differentiable_pt_ext _ (fun p q => (p * (- sin q))));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_scal; auto_derive; auto
    ].
  - apply (@differentiable_pt_ext _ (fun p q => cos q));
    [ move => *; apply: is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_proj2; auto_derive; auto
    ].
Qed.
    
Lemma smooth_sin: forall r t, 
  SmoothPath' (fun r t => r * sin t) r t.
Proof.
  move => r t; repeat split. 
  4,5: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply differentiable_pt_scal; auto_derive; auto.
  - apply (@differentiable_pt_ext _ (fun p q => (p * (cos q))));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_scal; auto_derive; auto
    ].
  - apply (@differentiable_pt_ext _ (fun p q =>sin q));
    [ move => *; apply: is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_proj2; auto_derive; auto
    ].
Qed.

Lemma smooth_line: forall z w r t, 
  SmoothPath' (fun r t => r * z + (1-r) * w ) r t.
Proof.
  move => r t; repeat split.
  4,5: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply: differentiable_pt_proj1.
    auto_derive. 
    auto.
  - eapply differentiable_pt_ext.
    move => *.
    apply Derive_const.
    apply: differentiable_pt_proj1.
    auto_derive.
    auto.
  - apply: differentiable_pt_proj1.
    eapply ex_derive_ext.
    symmetry.
    apply is_derive_unique.
    auto_derive; auto.
    reflexivity.
    auto_derive.
    auto.
Qed.

Lemma differentiable_pt_rplus : forall x y, differentiable_pt Rplus x y .
Proof.
  move => x y.
  exists 1; exists 1.
  apply/ filterdiff_differentiable_pt_lim.
  apply: filterdiff_ext_lin.
  2: move => z; rewrite ?Rmult_1_r; reflexivity.
  apply: filterdiff_plus.
Qed.

Lemma smooth_path_plus: forall g h r t, 
  locally_2d (SmoothPath' g) r t -> 
  locally_2d (SmoothPath' h) r t -> 
  locally_2d (SmoothPath' (fun r' t' => g r' t' + h r' t')) r t.
Proof.
  move => g h r t Sg Sh.
  have Sgh := locally_2d_and _ _ _ _ Sg Sh.
  apply: locally_2d_impl_strong Sgh.
  apply locally_2d_forall.
  rewrite /SmoothPath'.
  move => u v H.
  repeat split.
  - apply: differentiable_pt_comp.
    1: apply differentiable_pt_rplus.
    all: move: H => /locally_2d_singleton; tauto.
  - eapply differentiable_pt_ext_loc.
     apply: locally_2d_impl H;
     apply locally_2d_forall => p q H;
     rewrite Derive_plus;[
           reflexivity
           | apply: (@differentiable_pt_ex_right g); tauto 
           | apply: (@differentiable_pt_ex_right h); tauto 
         ].
    apply: differentiable_pt_comp.
    1: apply differentiable_pt_rplus.
    all: move: H => /locally_2d_singleton; tauto.
  - eapply differentiable_pt_ext_loc.
    1: apply: locally_2d_impl H;
       apply locally_2d_forall => p q H;
       rewrite Derive_plus;[
         reflexivity
         | apply: (@differentiable_pt_ex_left g); tauto 
         | apply: (@differentiable_pt_ex_left h); tauto 
       ].
    apply: differentiable_pt_comp.
    1: apply: differentiable_pt_rplus.
    all: move: H => /locally_2d_singleton; tauto.
  - apply: continuity_2d_pt_ext_loc.
      apply: locally_2d_impl_strong H.
      apply locally_2d_forall => p q /locally_2d_1d_const_y H.
      apply: Derive_ext_loc.
      apply: filter_imp H => p' H.
      rewrite Derive_plus;
      [ reflexivity
      | apply: (@differentiable_pt_ex_right g); tauto 
      | apply: (@differentiable_pt_ex_right h); tauto 
      ].
      apply: continuity_2d_pt_ext_loc.
      apply: locally_2d_impl H.
      apply locally_2d_forall => p q H.
      rewrite Derive_plus;
      [ reflexivity
      | apply: (@differentiable_pt_ex_left (fun p => Derive (g p))); tauto
      | apply: (@differentiable_pt_ex_left (fun p => Derive (h p))); tauto
      ].
      move: H => /locally_2d_singleton H.
      apply continuity_2d_pt_plus; tauto.
  - apply: continuity_2d_pt_ext_loc.
    apply: locally_2d_impl_strong H.
    apply locally_2d_forall => p q /locally_2d_1d_const_x H.
    apply: Derive_ext_loc.
    apply: filter_imp H => p' H.
    rewrite Derive_plus;
    [ reflexivity
    | apply: (@differentiable_pt_ex_left g); tauto 
    | apply: (@differentiable_pt_ex_left h); tauto 
    ].
    apply: continuity_2d_pt_ext_loc.
    apply: locally_2d_impl H.
    apply locally_2d_forall => p q H.
    rewrite Derive_plus;
    [ reflexivity
    | apply: (@differentiable_pt_ex_right (fun x y => Derive (g ^~ y) x)); tauto
    | apply: (@differentiable_pt_ex_right (fun x y => Derive (h ^~ y) x)); tauto
    ].
    move: H => /locally_2d_singleton H.
    apply continuity_2d_pt_plus; tauto.
Qed.

Lemma SmoothPath'_ext: forall f g r t, 
  (forall x y , f x y = g x y) -> 
  SmoothPath' f r t -> SmoothPath' g r t.
Proof.
  move => f g r t ext H.
  rewrite /SmoothPath' in H.
  repeat split.
  - eapply differentiable_pt_ext.
    move => *.
    symmetry.
    apply ext.
    tauto.
  - eapply differentiable_pt_ext.
      move => *.
      eapply Derive_ext.
        move => *.
        symmetry.
        apply ext.
    tauto.

  - eapply differentiable_pt_ext.
      move => *.
      eapply Derive_ext.
        move => *.
        symmetry.
        apply ext.
    tauto.
  - eapply continuity_2d_pt_ext.
      move => *.
      eapply Derive_ext.
        move => *.
        eapply Derive_ext.
          move => *.
        apply ext.
    tauto.
  - eapply continuity_2d_pt_ext.
      move => *.
      eapply Derive_ext.
        move => *.
        eapply Derive_ext.
          move => *.
        apply ext.
    tauto.
Qed.

Lemma smooth_path_const : forall z r t,
  SmoothPath' (fun _ _ => z) r t.
Proof.
  move => z r t.
  apply (@SmoothPath'_ext (fun x y => x*z + (1-x)*z)).  
  move => *.
  field_simplify; auto.
  apply smooth_line.
Qed.

Lemma smooth_translate: forall z g r t, 
  locally_2d (SmoothPath' g) r t ->
  SmoothPath' (fun r' t' => z + g r' t') r t.
Proof.
  move => z g r t H.
  apply locally_2d_singleton.
  have := smooth_path_const z.
  move => /(locally_2d_forall _ r t) H'.
  have := smooth_path_plus H' H.
  auto.
Qed.

Lemma smooth_circ: forall z r t, 
  SmoothPath (fun r t => z.1 + r * cos t)
             (fun r t => z.2 + r * sin t) r t.
Proof.
  move => z r t.
  apply: smoothpath'_smoothpath.
  - apply locally_2d_forall.
    move => u v.
    apply smooth_translate.
    apply locally_2d_forall.
    move => *.
    apply smooth_cos.
  - apply locally_2d_forall.
    move => u v.
    apply smooth_translate.
    apply locally_2d_forall.
    move => *.
    apply smooth_sin.
Qed.