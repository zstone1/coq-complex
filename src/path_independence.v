Require Import Reals Psatz Lra RelationClasses.
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


Require Import helpers complex_core.

Open Scope program_scope.
Open Scope general_if_scope.

Open Scope R.

Section Homotopy.

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

Ltac differentiable_pt_compute_derive:=
  eapply differentiable_pt_ext; 
         first ( move => p q; replace_Derive; reflexivity).
Ltac continuity_2d_compute_derive:=
  eapply continuity_2d_pt_ext; first (
    move => *;
      eapply Derive_ext; first (
        move => *; replace_Derive; reflexivity
      )
  );
  eapply continuity_2d_pt_ext; 
         first ( move => p q; replace_Derive; reflexivity).

Ltac compute_smooth:= 
  move => r t; repeat split;
  try continuity_2d_compute_derive;
  try differentiable_pt_compute_derive;
  try apply: differentiable_continuity_pt; 
  auto_differentiable_pt; auto_derive; auto.

Lemma smooth_cos_between: forall r1 r2 r t, 
  SmoothFun (fun r' t' => (r' * r1 + (1 - r') * r2) * cos t') r t.
Proof. compute_smooth. Qed.
    
Lemma smooth_sin_between: forall r1 r2 r t, 
  SmoothFun (fun r' t' => (r' * r1 + (1 - r') * r2) * sin t') r t.
Proof. compute_smooth. Qed.


Lemma smooth_cos: forall r t, 
  SmoothFun (fun r t => r * cos t) r t.
Proof. compute_smooth. Qed.
    
Lemma smooth_sin: forall r t, 
  SmoothFun (fun r t => r * sin t) r t.
Proof. compute_smooth. Qed.


Lemma smooth_line: forall z w r t, 
  SmoothFun (fun r t => r * z + (1-r) * w ) r t.
Proof. compute_smooth. Qed.

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
  move: H.
  copy => /locally_2d_singleton H_loc H.

  Tactic Notation "ext_Derive_plus" hyp(H) tactic(ext) tactic(t1) tactic(t2):=
    ext; first (
     apply: locally_2d_impl H;
     apply locally_2d_forall => p q H;
     rewrite Derive_plus;[
           reflexivity
           | t1; tauto 
           | t2; tauto 
    ]).

  Tactic Notation "ext_Derive_Derive_plus" hyp(H) constr(v)
     tactic(t1) tactic(t2):=
    apply: continuity_2d_pt_ext_loc; first(
      apply: locally_2d_impl_strong H;
      apply locally_2d_forall => p q /v H;
      apply: Derive_ext_loc;
      apply: filter_imp H => p' H;
      rewrite Derive_plus;
      [ reflexivity
      | t1; tauto 
      | t2; tauto 
      ]).
  
  repeat split.
  1: auto_differentiable_pt; tauto.
  - ext_Derive_plus H (eapply differentiable_pt_ext_loc)
      (apply: (@differentiable_pt_ex_right g))
      (apply: (@differentiable_pt_ex_right h)).
      auto_differentiable_pt; tauto.
  - ext_Derive_plus H (eapply differentiable_pt_ext_loc)
      (apply: (@differentiable_pt_ex_left g))
      (apply: (@differentiable_pt_ex_left h)).
      auto_differentiable_pt; tauto.
  - ext_Derive_Derive_plus H (locally_2d_1d_const_y)
      (apply: (@differentiable_pt_ex_right g))
      (apply: (@differentiable_pt_ex_right h))
      .
    ext_Derive_plus H (eapply continuity_2d_pt_ext_loc)
      (apply: (@differentiable_pt_ex_left (fun p => Derive (g p))))
      (apply: (@differentiable_pt_ex_left (fun p => Derive (h p)))).
      apply continuity_2d_pt_plus; tauto.
  - ext_Derive_Derive_plus H (locally_2d_1d_const_x)
      (apply: (@differentiable_pt_ex_left g))
      (apply: (@differentiable_pt_ex_left h)).
    ext_Derive_plus H (eapply continuity_2d_pt_ext_loc)
      (apply: (@differentiable_pt_ex_right (fun p p' => Derive (g ^~ p')p)))
      (apply: (@differentiable_pt_ex_right (fun p p' => Derive (h ^~ p')p))).
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
End Homotopy.

Ltac diff_help_old :=
  match goal with 
  | |- ex_derive (fun _ => ?u (_ _ _) (_ _ _)) _ => 
    first[ apply: (@differentiable_pt_comp_ex_derive_left u )|
           apply: (@differentiable_pt_comp_ex_derive_right u)]
  | H: differentiable_pt_lim ?f ?x ?y _ _ |- differentiable_pt ?f ?x ?y => 
    eexists; eexists; eapply H
  | H: differentiable_pt ?f ?x ?y |- differentiable_pt_lim ?f ?x ?y _ _ => 
    move: H => [h1 [h2 +]]
  | H: differentiable_pt ?f ?x ?y |- ex_derive ?g ?y =>  
     move:H => /differentiable_pt_ex_derive; tauto
  | H: differentiable_pt ?f ?x ?y |- ex_derive ?g ?x =>  
     move:H => /differentiable_pt_ex_derive; tauto
  end.

Ltac diff_help_ex_derive :=
  match goal with 
  | H: differentiable_pt_lim (fun _ _ => ?f _ _) ?x _ _ _
    |- ex_derive (fun _ => ?f _ _) ?x =>  
      apply (differentiable_pt_lim_left H)
  | H: differentiable_pt_lim ?f ?x _ _ _
    |- ex_derive (fun _ => ?f _ _) ?x =>  
      apply (differentiable_pt_lim_left H)
  | H: differentiable_pt_lim ?f ?x _ _ _
    |- ex_derive (?f _) ?x =>  
      apply (differentiable_pt_lim_left H)

  | H: differentiable_pt_lim (fun _ _ => ?f _ _) _ ?y _ _
    |- ex_derive (fun _ => ?f _ _) ?y =>  
      apply (differentiable_pt_lim_right H)
  | H: differentiable_pt_lim ?f _ ?y _ _
    |- ex_derive (fun _ => ?f _ _) ?y =>  
      apply (differentiable_pt_lim_right H)
  | H: differentiable_pt_lim ?f _ ?y _ _
    |- ex_derive (?f _) ?y =>  
      apply (differentiable_pt_lim_right H)
  end.
Ltac auto_derive_teardown :=
  rewrite /Rdiv /Cdiv;
  repeat (teardown 
          (apply/diff_topology_change) 
          (apply: ex_derive_plus) 
          (apply: ex_derive_scal) 
          (apply: ex_derive_mult)
          (apply: ex_derive_minus)
          (apply: ex_derive_opp)
          (apply: ex_derive_inv)
          (apply: derive_ex_derive; apply/is_derive_pair));
  auto with teardown_leaf.

Hint Extern 4 (ex_derive _ _) => (by diff_help_ex_derive) : teardown_leaf.
Hint Extern 4 (ex_derive id _) => (by apply: ex_derive_id) : teardown_leaf.
Hint Extern 2 (differentiable_pt _ _ _)  => 
  (match goal with 
  | H: differentiable_pt_lim ?f ?x ?y _ _ |- (differentiable_pt ?f ?x ?y) =>
    try (now (eexists; eexists; eauto))
  end) : teardown_leaf.

Hint Extern 5 (ex_derive _ _ ) => (
  match goal with 
  | H: differentiable_pt ?f ?x ?y |- ex_derive ?g ?y =>  
     move:H => /differentiable_pt_ex_derive; tauto
  | H: differentiable_pt ?f ?x ?y |- ex_derive ?g ?x =>  
     move:H => /differentiable_pt_ex_derive; tauto
  end
  ) : teardown_leaf.

Lemma path_independence_part_1: forall
    (u v: R -> R -> R) udx udy vdx vdy
    (g1 g2: R -> R -> R) g2_r g2_t g1_r g1_t r t,
  differentiable_pt_lim u (g1 r t) (g2 r t) udx udy ->
  differentiable_pt_lim v (g1 r t) (g2 r t) vdx vdy ->
  differentiable_pt_lim g1 r t (g1_r r t) (g1_t r t) ->
  differentiable_pt_lim g2 r t (g2_r r t) (g2_t r t) ->
  differentiable_pt g1_t r t  ->
  differentiable_pt g1_r r t  ->
  differentiable_pt g2_t r t  ->
  differentiable_pt g2_r r t  ->
  Derive (g1_t ^~ t) r = Derive (g1_r r) t ->
  Derive (g2_t ^~ t) r = Derive (g2_r r) t ->
  vdx = - udy ->
  Derive(fun t0 =>
   (u (g1 r t0) (g2 r t0) * g1_r r t0) - v (g1 r t0) (g2 r t0) * (g2_r r t0)) t
  = 
  Derive
  (fun r0  =>
   (u (g1 r0 t) (g2 r0 t) * g1_t r0 t - (v (g1 r0 t) (g2 r0 t) * g2_t r0 t))%R) r.
Proof.
  move => u v udx udy vdx vdy g1 g2 g2_r g2_t g1_r g1_t r t.
  move => du dv dg1 dg2 dg1t dg1r dg2t dg2r swapdiff1 swapdiff2 CR_eq//=.
  move: dg1t => [? [? dg1t]].
  move: dg1r => [? [? dg1r]].
  move: dg2t => [? [? dg2t]].
  move: dg2r => [? [? dg2r]].
  set p := RHS.
  have ug : ( differentiable_pt_lim (fun r t => u (g1 r t) (g2 r t)) 
                r t (udx * (g1_r r t) + udy * (g2_r r t))
                    (udx * (g1_t r t) + udy * (g2_t r t))
            )by
    apply differentiable_pt_lim_comp; auto.
  have vg : ( differentiable_pt_lim (fun r t => v (g1 r t) (g2 r t)) 
                r t (vdx * (g1_r r t) + vdy * (g2_r r t))
                    (vdx * (g1_t r t) + vdy * (g2_t r t))
            )by
    apply differentiable_pt_lim_comp; auto.
  
  `Begin eq p. { rewrite {}/p.

  | {(   Derive _ _ - Derive _ _   )} 

    rewrite ?Derive_minus; auto_derive_teardown.

  | {(   Derive _ r * _ + _ * Derive _ r - (Derive _ r * _ + _ * Derive _ r))}  
    rewrite ?Derive_mult; auto_derive_teardown.

  | {(  (udx * (g1_r r t) + udy * (g2_r r t)) * _ + _ - _ )%R}
    do 2 apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r.
    pose hu := fun r' t' => u (g1 r' t') (g2 r' t').
    rewrite -/(hu ^~ t).
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  | {(  _ - ((vdx * g1_r r t + vdy * (g2_r r t)) * _ + _) )%R}
    rewrite ?Rplus_assoc;
    apply Rplus_eq_compat_l;
    apply Ropp_eq_compat;
    apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r;
    idtac .
    pose hv := fun r' t' => v (g1 r' t') (g2 r' t').
    rewrite -/(hv ^~ t).
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  `Done.
  }
  move ->.
  set q := LHS.
  `Begin eq q. { rewrite {}/q.

  | {(   Derive _ _ - Derive _ _   )} 
    rewrite ?Derive_minus; auto_derive_teardown.

  | {(   Derive _ _ * _ + _ * Derive _ _ - (Derive _ _ * _ + _ * Derive _ _))}  
     rewrite ?Derive_mult; auto_derive_teardown.

  | {(  (udx * (g1_t r t) + udy * (g2_t r t)) * _ + _ - _ )%R}
    do 2 apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r.
    pose hu := fun r' t' => u (g1 r' t') (g2 r' t').
    rewrite -/(hu r).
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  | {(  _ - ((vdx * g1_t r t + vdy * (g2_t r t)) * _ + _) )%R}
    rewrite ?Rplus_assoc;
    apply Rplus_eq_compat_l;
    apply Ropp_eq_compat;
    apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r;
    idtac .
    pose hv := fun r' t' => v (g1 r' t') (g2 r' t').
    rewrite -/(hv r).
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  `Done.
  } 
  move ->.
  rewrite swapdiff1 swapdiff2 ?CR_eq.
  lra.
Unshelve.
2: apply ug.
2: apply vg.
2: apply ug.
2: apply vg.
Qed.


Lemma path_independence_part_2_real:
  forall (u v u' v': R -> R -> R) r t g1 g2, 
  let g:= fun p q => (g1 p q, g2 p q) in
  let f:= fun z => (u z.1 z.2, v z.1 z.2) in
  let f':= fun z => (u' z.1 z.2, v' z.1 z.2) in
  SmoothPath g1 g2 r t -> 
  Holo f f' (g r t) -> 
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
  Derive ( fun t0 => Re (f (g r t0) * g_r r t0 ))%C t =
  Derive ( fun r0 => Re (f (g r0 t) * g_t r0 t ))%C r  
.
Proof.
  move => u v u' v' r t g1 g2 g f f' [g1_smooth g2_smooth] .
  move => holo.
  move => g_t g_r.
  simpl.
  pose g1_r p q := Derive (g1 ^~ q) p.
  pose g2_r p q := Derive (g2 ^~ q) p.
  pose g1_t p q := Derive (g1 p) q .
  pose g2_t p q := Derive (g2 p) q .
  under Derive_ext => t0.
    set p := Derive _ _ .
    replace p with (g1_r r t0). 
    set q := Derive _ _ .
    replace q with (g2_r r t0). 
  over.
  rewrite /p  //= .
  rewrite /p  //= .
  symmetry.
  under Derive_ext => r0.
    set p := Derive _ _ .
    replace p with (g1_t r0 t). 
    set q := Derive _ _ .
    replace q with (g2_t r0 t). 
  over.
  rewrite /p  //= .
  rewrite /p  //= .
  symmetry.
  move: g1_smooth; copy => /locally_2d_singleton [? [?[?[??]]]] g1_smooth.
  move: g2_smooth; copy => /locally_2d_singleton [? [?[?[??]]]] g2_smooth.
  move: holo; copy => /holo_differentiable_pt_lim_real ?
                      /holo_differentiable_pt_lim_imaginary ?.
  simpl in *.
  
  eapply (@path_independence_part_1 u v _ _ _ _ g1 g2 _ _ _ _ r t);
    try apply Schwarz;
    try eauto;
    try apply: differentiable_pt_unique; eauto.

  3: lra.
  1: apply: locally_2d_impl g1_smooth.
  2: apply: locally_2d_impl g2_smooth.
  all: apply locally_2d_forall => x y 
    [/differentiable_pt_ex_derive ?
    [/differentiable_pt_ex_derive ?
    [/differentiable_pt_ex_derive ? ?]]];
    tauto.
Qed.

Open Scope C.

Lemma ReImSplit : forall z, 
  (Re z, Im z) = z.
Proof.
  move => z.
  rewrite /Re /Im /Cplus //=.
  set p := LHS.
  simplify_as_R2 LHS.
  rewrite -surjective_pairing //=.
Qed.
  
Lemma split_cint : forall (f: R -> C) a b, 
  ex_RInt f a b -> 
  RInt (V:=C_R_CompleteNormedModule) f a b = 
  (RInt (compose Re f) a b, RInt (compose Im f) a b).
Proof.
  move => f a b [l isR]. 
  rewrite /Re /Im /compose.
  apply: is_RInt_unique.
  apply: is_RInt_fct_extend_pair.
  - move: isR.
    copy => /is_RInt_fct_extend_fst /is_RInt_unique ->.
    apply is_RInt_fct_extend_fst.
  - move: isR.
    copy => /is_RInt_fct_extend_snd /is_RInt_unique ->.
    apply is_RInt_fct_extend_snd.
Qed.
      
(* I suspect that the proposition I'm working with 
are actually decidable anyway, so this is probably overkill*)
Axiom excluded_middle: forall P:Prop, P \/ ~P.

Ltac expand_nice := 
    move => [[+ +] [ [?[?[?[??]]]] [?[?[?[??]]]]]];
    copy => /holo_differentiable_pt_lim_imaginary ?
            /holo_differentiable_pt_lim_real ?;
    copy => /(continuous_comp _ fst) /= Cu';
    move => /(continuous_comp _ snd) /= Cv'.
Lemma not_not_impl: forall (P:Prop), ~ ~ P <-> P.
Proof.
  move => P. tauto.
Qed.

Section PathIndependence .
  Variables (a b c d:R).
  Variables (g1 g2 : R -> R -> R ).

  Hypothesis cled: c < d.

  Let g:= fun p q => (g1 p q, g2 p q).
  Let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q).
  Let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p).

  Hypothesis smooth: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
    SmoothPath g1 g2 r t.

  Lemma unif_r: forall (P: R -> R -> Prop) r, c <= r <= d -> 
    (forall r' t', c <= r' <= d -> Rmin a b <= t' <= Rmax a b ->
      locally_2d P r' t') ->
    locally r ( fun r0 => 
        forall t0, Rmin a b <= t0 <= Rmax a b -> 
        P r0 t0).
  Proof.
    move => P r rbd pH.
    move : pH => /(_ r) => {}nicer.
    pose delta := fun t => 
      match (Rle_dec (Rmin a b) t, Rle_dec t (Rmax a b) ) with 
      | (left p1, left p2) => proj1_sig (@locally_2d_ex_dec 
          _ r t
          (ltac:(move => *; apply (@excluded_middle _ ) )) 
          (@nicer t rbd (conj p1 p2) ))
      
      | _ => pos_half
      end.
    destruct (@compactness_value_1d (Rmin a b) (Rmax a b) delta).
    exists x.
    move => r' r'bd t tbd.
    move: n => /(_ t tbd).
    rewrite not_not_impl.
    case => t0 [t0bd [+ xdel]].
    move: xdel.
    rewrite /delta.
    destruct_match; try lra.
    destruct_match; try lra.
    set del' := locally_2d_ex_dec _ _ _ _ _ .
    move: del' => [del' dH] /= tballt0.
    apply dH.
    apply: Rlt_le_trans.
    2: apply tballt0.
    apply r'bd.
  Qed.

  Section DeriveHomotopy.

  Variables (u v u' v': R -> R -> R).
  Let f:= fun z => (u z.1 z.2, v z.1 z.2).
  Let f':= fun z => (u' z.1 z.2, v' z.1 z.2).

  Hypothesis holo_loc: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  Holo f f' (g r0 t0)) r t.

  Hypothesis cts_derive: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  continuous f' (g r0 t0)) r t.

  Ltac decompose_u_v :=
    match goal with 
    | |- ex_derive (fun _ => u (_ _ _) (_ _ _)) _ => 
      first[ apply: (@differentiable_pt_comp_ex_derive_left u )|
             apply: (@differentiable_pt_comp_ex_derive_right u)]
    | |- ex_derive (fun _ => v (_ _ _) (_ _ _)) _ => 
      first[ apply: (@differentiable_pt_comp_ex_derive_left v )|
             apply: (@differentiable_pt_comp_ex_derive_right v)]
    end.

  Let nice r0 t0 :=
    CHolo f f' (g r0 t0) /\
    SmoothFun g1 r0 t0 /\
    SmoothFun g2 r0 t0.

  Lemma locally_nice: forall r t, 
    c <= r <= d -> 
    Rmin a b <= t <= Rmax a b ->locally_2d nice r t.
  Proof.
    move => r t tbd rbd.
    move: holo_loc => /(_ r t tbd rbd ).
    move: cts_derive => /(_ r t tbd rbd ).
    move: smooth => /(_ r t tbd rbd ) [].
    move => H.
    move => {}H'; have {}H:= locally_2d_and _ _ r t H H'. 
    move => {}H'; have {}H:= locally_2d_and _ _ r t H H'. 
    move => {}H'; have {}H:= locally_2d_and _ _ r t H H'. 
    apply: locally_2d_impl H.
    apply locally_2d_forall.
    move => *.
    rewrite /nice /CHolo.
    tauto. 
  Qed.

  Lemma diff_integrand_t: forall r t,
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
    locally_2d (
        differentiable_pt (fun r0 t0 => Re(f (g r0 t0) * g_t r0 t0))) r t.
  Proof.
    move => r t rbd tbd.
    apply: locally_2d_impl (locally_nice  rbd tbd).
    apply locally_2d_forall.
    move => r0 t0 [[+ _] [[?[?[?[??]]]] [?[?[?[??]]]]]]. 
    copy => /holo_differentiable_pt_lim_real Du 
            /holo_differentiable_pt_lim_imaginary Dv /=.
    simpl in *.
    auto_differentiable_pt.
    all: apply: differentiable_pt_comp.
    all: auto_differentiable_pt.
    all: eexists;eexists; now eauto.
  Qed.

  Lemma diff_integrand_r: forall r t,
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
    locally_2d (
        differentiable_pt (fun r0 t0 => Re(f (g r0 t0) * g_r r0 t0))) r t.
  Proof.
    move => r t rbd tbd.
    apply: locally_2d_impl (locally_nice  rbd tbd).
    apply locally_2d_forall.
    move => r0 t0 [[+ _] [[?[?[?[??]]]] [?[?[?[??]]]]]]. 
    copy => /holo_differentiable_pt_lim_real Du 
            /holo_differentiable_pt_lim_imaginary Dv /=.
    simpl in *.
    auto_differentiable_pt.
    all: apply: differentiable_pt_comp.
    all: auto_differentiable_pt.
    all: eexists;eexists; now eauto.
  Qed.
  Local Ltac foo x y := 
    let smooth := fresh in 
      move => /(_ x y)[+ smooth];
      copy => /holo_differentiable_pt_lim_real ? 
              /holo_differentiable_pt_lim_imaginary ?;
      case: smooth => /locally_2d_singleton [? [H Q]] [/locally_2d_singleton [?[??]] c];
      simpl in *.

  Ltac auto_2d_continuous :=
    repeat ( teardown 
      (fail "no topology shenanigans")
      (apply: continuity_2d_pt_plus)
      (unfold_alg; apply: continuity_2d_pt_mult)
      (apply: continuity_2d_pt_mult)
      (apply: continuity_2d_pt_minus)
      (apply: continuity_2d_pt_opp)
      (fail "inv doesn't matter")
      (fail "pair doesn't matter"));
  auto with teardown_leaf.


  Lemma D: forall r, 
    c <= r <= d ->  
      is_derive (fun r0 => RInt (fun t0 => Re(f (g r0 t0) * g_t r0 t0 ))%C a b) r 
      (RInt (fun t0 => Derive (fun r0 => Re(f (g r0 t0) * g_t r0 t0 )%C) r) a b). 
  Proof.
    move => r rbd.
    apply is_derive_RInt_param.
    - apply: unif_r; auto.
      move => r' t' r'bd t'bd.
      apply: locally_2d_impl (diff_integrand_t r'bd t'bd).
      apply: locally_2d_forall.
      move => r0 t0 /differentiable_pt_ex_derive [_ H].
      tauto.
    - move => t tbd.
      move: locally_nice => /(_ _ _ rbd tbd) nice'.
      eapply continuity_2d_pt_ext_loc. {
        apply: locally_2d_impl nice'.
        apply: locally_2d_forall => r0 t0. 
        copy.
        expand_nice.
        move => [[+ _] _].
        copy => /holo_differentiable_pt_lim_real
                /differentiable_pt_lim_unique [Du'1 Du'2]
                /holo_differentiable_pt_lim_imaginary
                /differentiable_pt_lim_unique [Dv'1 Dv'2].
        simpl in *.
        rewrite Derive_minus ?Derive_mult ?Derive_plus /=.
        rewrite (@Derive_comp_2_left u g1 g2).
        rewrite (@Derive_comp_2_left v g1 g2).
        rewrite Du'1 Du'2 Dv'1 Dv'2.
        reflexivity.
        all: try decompose_u_v.
        all: auto_differentiable_pt; auto_derive_teardown.
        1: apply differentiable_pt_comp_ex_derive_left.
        4: apply differentiable_pt_comp_ex_derive_left.
        all: auto_differentiable_pt; auto_derive_teardown.
      }
      move: nice' => /locally_2d_singleton.
      expand_nice.
      simpl in *.
      Hint Extern 1 (continuity_2d_pt _ _ _) => 
        (match goal with 
        | H : differentiable_pt ?f ?x ?y |- continuity_2d_pt ?f ?x ?y =>
          apply: differentiable_continuity_pt
        end) : teardown_leaf.
      auto_2d_continuous.
      all: apply: continuity_2d_pt_comp.
      all: auto_2d_continuous.
      3,6: apply: differentiable_continuity_pt; eexists; eexists ;eauto.
      all: apply/continuity_2d_pt_continuous; simpl;
        first [apply Cu' | apply Cv']; auto_cts.
    - apply: filter_imp.
      1: move => r' H; 
         apply: ex_RInt_continuous; 
         exact H.
      apply: unif_r; auto.
      move => r' t' r'bd t'bd.
      apply: locally_2d_impl (diff_integrand_t r'bd t'bd).
      apply locally_2d_forall.
      move => r0 t0 /differentiable_pt_ex_derive H.
      apply: ex_derive_continuous.
      tauto.
  Qed.

  Lemma path_independence_part_3_real:
    forall r, c <= r <= d ->
      is_derive (fun r0 => RInt (fun t0 : R => Re (f (g r0 t0) * g_t r0 t0)) a b) r 
     (Re(f (g r b) * g_r r b - f (g r a) * g_r r a )%C).
  Proof.
    move => r rbd.
    have D := D rbd.
    erewrite RInt_ext in D. 
    2:{ move => x xbd.
      rewrite -(@path_independence_part_2_real u v u' v').
      reflexivity.
      apply smooth; lra.
      move: (@holo_loc r x rbd (ltac:(lra))) => /locally_2d_singleton. 
      auto.
    }
    rewrite RInt_Derive in D. 
    - apply: D.
    - move => t0 t0bd. 
      move: (diff_integrand_r rbd t0bd) => 
        /locally_2d_singleton /differentiable_pt_ex_derive.
        tauto.
    - simpl. 
      move => t tbd.
      eapply continuous_ext_loc. {
        move : (locally_nice rbd tbd) => /locally_2d_1d_const_x H.
        apply: filter_imp H => t'.
        copy.
        expand_nice.

        move => [[+ _] _].
        copy => /holo_differentiable_pt_lim_real
                /differentiable_pt_lim_unique [Du'1 Du'2]
                /holo_differentiable_pt_lim_imaginary
                /differentiable_pt_lim_unique [Dv'1 Dv'2].
        simpl in *.
        rewrite Derive_minus ?Derive_mult ?Derive_plus /=.
        rewrite (@Derive_comp_2_right u g1 g2).
        rewrite (@Derive_comp_2_right v g1 g2).
        rewrite Du'1 Du'2 Dv'1 Dv'2.
        reflexivity.
        all: auto_derive_teardown.
        all: apply differentiable_pt_comp_ex_derive_right.
        all: auto_derive_teardown.
      }
      move: (locally_nice rbd tbd) => /locally_2d_singleton.
      expand_nice.
      simpl in *.
      auto_cts.
      1,3,8,10: apply continuous_comp_2.
      all: auto_cts.
      all: try now (apply: ex_derive_continuous; auto_derive_teardown).
      1,3: apply: ex_derive_continuous;
           apply differentiable_pt_comp_ex_derive_right.
      all: auto_differentiable_pt.
      2: repeat match goal with 
      | H: continuity_2d_pt _ _ _ |- _ => move: H
      end;
      move => _ _ _ ;
      move /continuity_2d_pt_continuous_right; auto.
      repeat match goal with 
      | H: continuity_2d_pt _ _ _ |- _ => move: H
      end;
      move => _ + _ _ ;
      move /continuity_2d_pt_continuous_right; auto.
  Qed.
  End DeriveHomotopy.

  Variables (f f': C -> C).

  Hypothesis holo_loc: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  CHolo f f' (g r0 t0)) r t.


  Let nice r0 t0 :=
    CHolo f f' (g r0 t0) /\
    SmoothFun g1 r0 t0 /\
    SmoothFun g2 r0 t0.

  Lemma locally_nice': forall r t, 
    c <= r <= d -> 
    Rmin a b <= t <= Rmax a b ->locally_2d nice r t.
  Proof.
    move => r t tbd rbd.
    move: holo_loc => /(_ r t tbd rbd ).
    move: smooth => /(_ r t tbd rbd ) [].
    move => H.
    rewrite /CHolo.
    move => {}H'; have {}H:= locally_2d_and _ _ r t H H'. 
    move => {}H'; have {}H:= locally_2d_and _ _ r t H H'. 
    apply: locally_2d_impl H.
    apply locally_2d_forall.
    move => *.
    rewrite /nice /CHolo.
    tauto. 
  Qed.
  Lemma integrand_cts:
      (forall r t, c <= r <= d ->
                  Rmin a b <= t <= Rmax a b ->
      locally_2d (fun r' t' => 
        continuous (fun t0 => f (g r' t0) * g_t r' t0) t') r t).
  Proof.
    move => r t rbd tbd.
    move: (locally_nice' rbd tbd) => H.
    apply: locally_2d_impl H.
    apply: locally_2d_forall.
    move => u v.
    copy.
    move => [[/is_derive_continuous ? _] _]. 
    expand_nice.
    rewrite /g /g_t.
    auto_cts.
    - apply continuous_comp; auto_cts; 
      apply: ex_derive_continuous; auto_derive_teardown.
    - apply: (@continuity_2d_pt_continuous_right 
        (fun r' t' => (Derive (g1 r') t'))).
      apply: differentiable_continuity_pt.
      auto.
    - apply: (@continuity_2d_pt_continuous_right 
        (fun r' t' => (Derive (g2 r') t'))).
      apply: differentiable_continuity_pt.
      auto.
  Qed.
  Local Ltac prod_int := 
      rewrite -?ex_RInt_prod;
      apply ex_RInt_continuous => z /(inside a'bd b'bd) zbd;
      apply: integrand_cts; eauto.

  Lemma path_independence_part_4:
    forall r, c <= r <= d ->
    is_derive (fun r0 => 
      RInt (V:=C_R_CompleteNormedModule)
        (fun t0 : R => f (g r0 t0) * g_t r0 t0) a b) r 
      (f (g r b) * g_r r b - f (g r a) * g_r r a )%C.
  Proof.
    move => r rbd.
    eapply is_derive_ext_loc.
      move: (unif_r rbd integrand_cts) => H.
      apply: filter_imp H.
      move => r' *.
      rewrite [RHS]split_cint /compose; last by
        rewrite -ex_RInt_prod; apply ex_RInt_continuous => * //=; auto.
    reflexivity.
    rewrite -[x in is_derive _ _ x]ReImSplit.
    apply/is_derive_pair; split.
    - pose u := fun p q => (f (p,q)).1.
      pose v := fun p q => (f (p,q)).2.
      pose u' := fun p q => (f' (p,q)).1.
      pose v' := fun p q => (f' (p,q)).2.
      apply (@path_independence_part_3_real u v u' v' ); auto.
      + move => r' t' r'bd t'bd.
        apply: locally_2d_impl (holo_loc  r'bd t'bd).
        apply locally_2d_forall.
        rewrite /CHolo.
        move => r0 t0 [H _].
        eapply is_derive_ext with (f0:=f).
          move => t.
          rewrite /u /v -?surjective_pairing //=.
        rewrite /u' /v' -?surjective_pairing //=.
      + move => r' t' r'bd t'bd.
        apply: locally_2d_impl (holo_loc  r'bd t'bd).
        apply locally_2d_forall.
        move => r0 t0 [_ H].
        eapply continuous_ext with (f0:=f').
          move => t.
          rewrite /u' /v' -?surjective_pairing //=.
        auto.
    - pose u := fun p q => Ropp (f (p,q)).2.
      pose v := fun p q => (f (p,q)).1.
      pose u' := fun p q => Ropp (f' (p,q)).2.
      pose v' := fun p q => (f' (p,q)).1.
      pose h := fun z => (u z.1 z.2, v z.1 z.2).
      pose h' := fun z => (u' z.1 z.2, v' z.1 z.2).
      have hf : forall z, h z = Ci * f z by 
        move => z; rewrite /h/u/v //=/Cmult;
        simplify_as_R2 LHS;
        simplify_as_R2 RHS;
        rewrite -?surjective_pairing.
      have hf' : forall z, h' z = Ci * f' z by 
        move => z; rewrite /h'/u'/v' //=/Cmult;
        simplify_as_R2 LHS;
        simplify_as_R2 RHS;
        rewrite -?surjective_pairing.
      have toRe: forall r t, Im ( f (g r t) * g_t r t) = Ropp (Re (h (g r t) * g_t r t)). {
        move => r' t'. 
        rewrite /h /u/v /g//=.
        simpl.
        field_simplify_eq; auto.
      }
      eapply is_derive_ext_loc.
        move : (unif_r rbd locally_nice') => H. 
        apply: filter_imp H.
        move => r' nice'.
        under RInt_ext => x _.
          rewrite toRe.
        over.
        rewrite RInt_opp.
      reflexivity.
      1: {
        apply ex_RInt_continuous.
        move => z zbd.
        simpl.
        move: (nice' z zbd).
        copy => [[[holo _] _]].
        copy => [[[/is_derive_continuous ? _] _]].
        expand_nice.
        auto_cts.
        2-4: apply: ex_derive_continuous.
        3: apply differentiable_pt_comp_ex_derive_right.
        all: auto_derive_teardown.
        rewrite /u.
        auto_cts.
        apply: continuous_comp; last auto_cts.
        apply (@continuous_comp_2 _ _ _ _ _ _ (fun x y => f (x,y))) .
        Set Printing Implicit.
        1,2: apply: ex_derive_continuous; auto_derive_teardown.
        apply/ cts_topology_1. 
        apply: ex_derive_continuous.
        eapply ex_derive_ext.
          move => t; rewrite -surjective_pairing.
        reflexivity.
        eexists.
        apply holo.
      }
      have ->: (Im (f (g r b) * g_r r b - f (g r a) * g_r r a)) =
                 (opp (Re(h (g r b) * g_r r b - h (g r a) * g_r r a))) by
        rewrite /opp /=/g/h/u/v; field_simplify_eq. 
      apply: is_derive_opp.
      
      apply: (@path_independence_part_3_real u v u' v' ); auto.
      + move => r0 t0 r0bd t0bd.
        apply: locally_2d_impl (holo_loc r0bd t0bd).
        apply locally_2d_forall.
        move => r' t' [H _].
        eapply is_derive_ext. 
          move => t.
          rewrite -/(h t) hf.
        reflexivity.
        rewrite -/(h' (g r' t')) hf'.
        apply: Holo_mult.
        auto.
      + move => r0 t0 r0bd t0bd.
        apply: locally_2d_impl (holo_loc r0bd t0bd).
        apply locally_2d_forall.
        move => r' t' [_ H].
        rewrite -/h'.
        eapply continuous_ext. 
          move => x. 
          rewrite hf'. 
         reflexivity. 
        simpl.
        auto_cts.
  Qed.


  Lemma path_independence_line:
    (forall r1 r2, 
      (g r1 a = g r2 a) /\ 
      (g r1 b = g r2 b)) ->
    RInt (V:=C_R_CompleteNormedModule) 
      (fun t0 : R => (f (g c t0) * g_t c t0)) a b =
    RInt (V:=C_R_CompleteNormedModule)
      (fun t0 : R => (f (g d t0) * g_t d t0)) a b .
  Proof.
    move => loop.
    pose h := fun r => RInt (V:=C_R_CompleteNormedModule)
       (fun t0 : R => f (g r t0) * g_t r t0) a b.
    change (h c = h d).
    apply:eq_is_derive; last by [].
    move => r tbd.
    evar_last.
    apply: path_independence_part_4; first by [].
    rewrite /g_r.
    under Derive_ext => r'.
      move: (loop c r') =>  [_ /pair_equal_spec [<- _]].
    over.
    rewrite Derive_const.
    under Derive_ext => r'.
      move: (loop c r') =>  [_ /pair_equal_spec [_ <-]].
    over.
    rewrite Derive_const.
    under Derive_ext => r'.
      move: (loop c r') =>  [/pair_equal_spec [<- _] _].
    over.
    rewrite Derive_const.
    under Derive_ext => r'.
      move: (loop c r') =>  [/pair_equal_spec [_ <-] _].
    over.
    rewrite Derive_const.
    rewrite /zero /= /prod_zero /zero /= ?Cmult_0_r.
    field_simplify_eq.
    auto.
  Qed.

  Lemma path_independence_loop:
      (forall r,  c <= r <= d -> 
                  (g r a = g r b) /\ 
                  (g_r r a = g_r r b)) ->
    RInt (V:=C_R_CompleteNormedModule) 
      (fun t0 : R => (f (g c t0) * g_t c t0)) a b =
    RInt (V:=C_R_CompleteNormedModule)
      (fun t0 : R => (f (g d t0) * g_t d t0)) a b .
  Proof.
    move => loop.
    pose h := fun r => RInt (V:=C_R_CompleteNormedModule)
       (fun t0 : R => f (g r t0) * g_t r t0) a b.
    change (h c = h d).
    apply:eq_is_derive; last by [].
    move => r rbd.
    evar_last.
    apply: path_independence_part_4; first by [].
    move: (loop _ rbd) => [-> ->].
    field_simplify_eq.
    auto.
  Qed.
End PathIndependence.