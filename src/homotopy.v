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


Require Import domains cauchy_riemann.

Open Scope program_scope.
Open Scope general_if_scope.
Require Import domains ext_rewrite real_helpers.

Open Scope C.
Definition c_circle (r: R) (t:R):C := r * (cos t, sin t).
Definition c_circle' (r: R) (t:R):C := r * (-sin t, cos t)%R.

Open Scope R.

Lemma differentiable_pt_unique (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  differentiable_pt_lim f x y  
    (Derive (fun x => f x y) x) 
    (Derive (fun y => f x y) y).
Proof. 
  move => [l1 [l2]].
  copy.
  by move => /differentiable_pt_lim_unique [-> ->].
Qed.

Lemma differentiable_pt_ex_derive (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  ex_derive [eta f x] y /\
  ex_derive (f ^~ y) x. 
Proof. 
  move => [l1 [l2]] /differentiable_pt_lim_is_derive [H1 H2].
  split; [exists l2 | exists l1]; auto.
Qed.
Lemma differentiable_pt_ex_left (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  ex_derive (f ^~ y) x. 
Proof. apply differentiable_pt_ex_derive. Qed.

Lemma differentiable_pt_ex_right (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  ex_derive [eta f x] y.
Proof. apply differentiable_pt_ex_derive. Qed.

Lemma continuity_2d_pt_comp: 
  forall f g h x y,
  continuity_2d_pt f (g x y) (h x y) -> 
  continuity_2d_pt g x y -> 
  continuity_2d_pt h x y -> 
  continuity_2d_pt (fun x' y' => f (g x' y') (h x' y')) x y.
Proof.
  move => f g h x y 
    /continuity_2d_pt_filterlim Cf
    /continuity_2d_pt_filterlim Cg 
    /continuity_2d_pt_filterlim Ch. 
  apply/ continuity_2d_pt_filterlim. 
  apply: filterlim_comp_2; eauto.
  apply: filterlim_filter_le_1 Cf.
  move => P [del +].
  rewrite /ball //= /prod_ball //= => H.
  eapply Filter_prod. 
  - exists del => x0; instantiate(1 := ball (g x y) del); auto. 
  - exists del => y0; instantiate(1 := ball (h x y) del); auto.
  - move => x0 y0 b1 b2. apply H; simpl; tauto.
Qed.

Lemma continuity_2d_pt_continuous: 
  forall f x y,
  continuity_2d_pt f x y <-> 
  continuous (fun z => f z.1 z.2) (x,y).
Proof.
  move => f x y.
  rewrite continuity_2d_pt_filterlim /continuous //=.
Qed.

Lemma continuity_2d_pt_continuous_right: 
  forall f x y,
  continuity_2d_pt f x y -> 
  continuous (fun z => f x z) y.
Proof.
  move => f x y.
  rewrite continuity_2d_pt_continuous //=. 
  move => /(continuous_comp (fun z => (x, z.2))).
  move => /(_ ltac:(repeat auto_continuous_aux)) //=.
  rewrite /continuous /filtermap //= /filterlim /filtermap /filter_le => H.
  move => P lP.
  move:H => /(_ P lP) [eps H].
  exists eps => y' xball. 
  apply (H (x,y')).
  move: xball. unfold_alg.
  rewrite /AbsRing_ball //= -/(Rminus _ _); split; auto. 
  unfold_alg.
  have ->: (x+-x=0) by lra.
  rewrite Rabs_R0.
  apply cond_pos.
Qed.

Section DifferentiablePtComp.
  Variables (f g h : R -> R -> R).
  Variables (x y : R).
  Hypothesis (df: differentiable_pt f (g x y) (h x y)).
  Hypothesis (dg: differentiable_pt g x y ).
  Hypothesis (dh: differentiable_pt h x y ).
  Lemma differentiable_pt_comp   :
    differentiable_pt (fun x' y'  => f (g x' y') (h x' y')) x y .
  Proof.
    move: df dg dh=> [? [? ?]] [? [? ?]] [? [? ?]]. 
    eexists; eexists.
    apply differentiable_pt_lim_comp; eauto.
  Qed.
  
  Lemma differentiable_pt_comp_ex_derive  :
    ex_derive (fun x' => f (g x' y) (h x' y)) x /\
    ex_derive (fun y' => f (g x y') (h x y')) y 
  .
  Proof.
    have := differentiable_pt_comp.
    move => /differentiable_pt_ex_derive; tauto.
  Qed.
  
  Lemma differentiable_pt_comp_ex_derive_right:
    ex_derive (fun y' => f (g x y') (h x y')) y .
  Proof. apply differentiable_pt_comp_ex_derive. Qed.
  Lemma differentiable_pt_comp_ex_derive_left:
    ex_derive (fun x' => f (g x' y) (h x' y)) x.
  Proof.
    apply differentiable_pt_comp_ex_derive.
  Qed.

  Lemma Derive_comp_2_left: 
    Derive (fun z => f (g z y) (h z y)) x = 
    Derive (f ^~ (h x y)) (g x y) * Derive (g ^~ y) x + 
    Derive [eta (f (g x y))] (h x y) * Derive (h ^~ y) x.
  Proof.
    move: df => /differentiable_pt_unique => Df.
    move: dg => /differentiable_pt_unique => Dg.
    move: dh => /differentiable_pt_unique => Dh.
    have := (differentiable_pt_lim_comp f g h x y _ _ _ _ _ _ Df Dg Dh). 
    move=>  /differentiable_pt_lim_unique; tauto.
  Qed.
  Lemma Derive_comp_2_right: 
    Derive (fun z => f (g x z) (h x z)) y = 
    Derive (f ^~ (h x y)) (g x y) * Derive (g x) y + 
    Derive [eta (f (g x y))] (h x y) * Derive (h x) y.
  Proof.
    move: df => /differentiable_pt_unique => Df.
    move: dg => /differentiable_pt_unique => Dg.
    move: dh => /differentiable_pt_unique => Dh.
    have := (differentiable_pt_lim_comp f g h x y _ _ _ _ _ _ Df Dg Dh). 
    move=>  /differentiable_pt_lim_unique; tauto.
  Qed.

End DifferentiablePtComp.

Definition SmoothFun g r t:= 
  differentiable_pt g r t /\
  differentiable_pt (fun p q => Derive (g p) q) r t /\
  differentiable_pt (fun p q => Derive (g ^~ q) p) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g z t) v) u) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g t z) u) v) r t
.

Definition SmoothPath g1 g2 r t:= 
  locally_2d (SmoothFun g1) r t /\
  locally_2d (SmoothFun g2) r t.

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

Lemma differentiable_pt_mult: forall x y,
  differentiable_pt Rmult x y .
Proof.
  move => x y.
  exists y; exists x.
  apply/ filterdiff_differentiable_pt_lim.
  apply: filterdiff_ext_lin.
  2: move => z; rewrite [x in _ + x]Rmult_comm; reflexivity.
  apply: filterdiff_mult_fct.
  1: unfold_alg; move => *; field_simplify; auto.

  - split; first by apply is_linear_fst.
    move => p /is_filter_lim_locally_unique <- //= eps.
    exists pos_half => *.
    unfold_alg.
    set q := (x in Rabs x).
    simplify_R q.
    rewrite Rabs_R0.
    apply Rmult_le_pos.
    1: left; apply cond_pos.
    apply Cmod_ge_0.

  - split; first by apply is_linear_snd.
    move => p /is_filter_lim_locally_unique <- //= eps.
    exists pos_half => *.
    unfold_alg.
    set q := (x in Rabs x).
    simplify_R q.
    rewrite Rabs_R0.
    apply Rmult_le_pos.
    1: left; apply cond_pos.
    apply Cmod_ge_0.
Qed.

Lemma differentiable_pt_minus: forall x y,
  differentiable_pt Rminus x y .
Proof.
  move => x y.
  exists 1; exists (-1).
  apply/ filterdiff_differentiable_pt_lim.
  apply: (@filterdiff_ext_lin _ _ _ _ _ _ ( fun z => z.1 - z.2)).
  2: move => *; field_simplify; auto.
  apply: filterdiff_minus.
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
Lemma smooth_cos_between: forall r1 r2 r t, 
  SmoothFun (fun r' t' => (r' * r1 + (1 - r') * r2) * cos t') r t.
Proof.
  move => r t; repeat split. 
  4,5: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply differentiable_pt_comp. 
    3: apply differentiable_pt_proj2; auto_derive; auto.
    2: apply differentiable_pt_proj1; auto_derive; auto.
    1: apply differentiable_pt_mult.
  
  - eapply differentiable_pt_ext. 
    move => *.
      rewrite Derive_mult.
      2,3: auto_derive; auto.
      rewrite Derive_const.
      rewrite Rmult_0_l Rplus_0_l.
    reflexivity.
    apply differentiable_pt_comp.
    1: apply differentiable_pt_mult.
    1: apply differentiable_pt_proj1; auto_derive; auto.
    apply differentiable_pt_proj2; auto_derive; auto.
    eapply ex_derive_ext => [t'|].
      symmetry.
      apply is_derive_unique;
      auto_derive; auto.
    reflexivity.
    auto_derive.
    auto.
  - eapply differentiable_pt_ext. 
    move => *.
      rewrite Derive_mult.
      2,3: auto_derive; auto.
      rewrite Derive_const.
      rewrite Rmult_0_r Rplus_0_r.
    reflexivity.
    apply differentiable_pt_comp.
    1: apply differentiable_pt_mult.
    2: apply differentiable_pt_proj2; auto_derive; auto.

    apply differentiable_pt_proj1; auto_derive; auto.
    eapply ex_derive_ext => [t'|].
      symmetry.
      apply is_derive_unique;
      auto_derive; auto.
    reflexivity.
    auto_derive.
    auto.
Qed.
    
Lemma smooth_sin_between: forall r1 r2 r t, 
  SmoothFun (fun r' t' => (r' * r1 + (1 - r') * r2) * sin t') r t.
Proof.
  move => r t; repeat split. 
  4,5: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply differentiable_pt_comp. 
    3: apply differentiable_pt_proj2; auto_derive; auto.
    2: apply differentiable_pt_proj1; auto_derive; auto.
    1: apply differentiable_pt_mult.
  
  - eapply differentiable_pt_ext. 
    move => *.
      rewrite Derive_mult.
      2,3: auto_derive; auto.
      rewrite Derive_const.
      rewrite Rmult_0_l Rplus_0_l.
    reflexivity.
    apply differentiable_pt_comp.
    1: apply differentiable_pt_mult.
    1: apply differentiable_pt_proj1; auto_derive; auto.
    apply differentiable_pt_proj2; auto_derive; auto.
    eapply ex_derive_ext => [t'|].
      symmetry.
      apply is_derive_unique;
      auto_derive; auto.
    reflexivity.
    auto_derive.
    auto.
  - eapply differentiable_pt_ext. 
    move => *.
      rewrite Derive_mult.
      2,3: auto_derive; auto.
      rewrite Derive_const.
      rewrite Rmult_0_r Rplus_0_r.
    reflexivity.
    apply differentiable_pt_comp.
    1: apply differentiable_pt_mult.
    2: apply differentiable_pt_proj2; auto_derive; auto.

    apply differentiable_pt_proj1; auto_derive; auto.
    eapply ex_derive_ext => [t'|].
      symmetry.
      apply is_derive_unique;
      auto_derive; auto.
    reflexivity.
    auto_derive.
    auto.
Qed.


Lemma smooth_cos: forall r t, 
  SmoothFun (fun r t => r * cos t) r t.
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
  SmoothFun (fun r t => r * sin t) r t.
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
  SmoothFun (fun r t => r * z + (1-r) * w ) r t.
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
Lemma smooth_path_plus: forall g h r t, 
  locally_2d (SmoothFun g) r t -> 
  locally_2d (SmoothFun h) r t -> 
  locally_2d (SmoothFun (fun r' t' => g r' t' + h r' t')) r t.
Proof.
  move => g h r t Sg Sh.
  have Sgh := locally_2d_and _ _ _ _ Sg Sh.
  apply: locally_2d_impl_strong Sgh.
  apply locally_2d_forall.
  rewrite /SmoothFun.
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
  SmoothFun f r t -> SmoothFun g r t.
Proof.
  move => f g r t ext H.
  rewrite /SmoothFun in H.
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
  SmoothFun (fun _ _ => z) r t.
Proof.
  move => z r t.
  apply (@SmoothPath'_ext (fun x y => x*z + (1-x)*z)).  
  move => *.
  field_simplify; auto.
  apply smooth_line.
Qed.

Lemma smooth_translate: forall z g r t, 
  locally_2d (SmoothFun g) r t ->
  SmoothFun (fun r' t' => z + g r' t') r t.
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
  split.
  - apply locally_2d_forall.
    move => u v.
    apply smooth_translate.
    apply locally_2d_forall.
    move => *.
    apply: smooth_cos.
  - apply locally_2d_forall.
    move => u v.
    apply smooth_translate.
    apply locally_2d_forall.
    move => *.
    apply smooth_sin.
Qed.

Lemma smooth_translate_circ: forall z w r1 r2 r t,
  SmoothPath (fun r' t' => (r' * z.1 + (1-r')*w.1 + (r'*r1 + (1-r')*r2) * cos t'))
             (fun r' t' => (r' * z.2 + (1-r')*w.2 + (r'*r1 + (1-r')*r2) * sin t')) 
             r t.
Proof.
  move => z w r1 r2 r t.
  split.
  - have := smooth_line z.1 w.1.
    move => /(locally_2d_forall _ r t) H'.
    have := smooth_cos_between r1 r2. 
    move => /(locally_2d_forall _ r t) H''.
    apply: smooth_path_plus H' H''.
  - have := smooth_line z.2 w.2.
    move => /(locally_2d_forall _ r t) H'.
    have := smooth_sin_between r1 r2. 
    move => /(locally_2d_forall _ r t) H''.
    apply: smooth_path_plus H' H''.
Qed.