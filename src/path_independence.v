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


Require Import domains cauchy_riemann real_helpers homotopy.

Open Scope program_scope.
Open Scope general_if_scope.
Require Import domains ext_rewrite real_helpers.

Open Scope R.

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

  | {(   Derive _ _ - Derive _ _   )} rewrite ?Derive_minus.
    apply ex_derive_mult.
    apply (differentiable_pt_lim_left ug).
    apply (differentiable_pt_lim_left dg1t).
    apply ex_derive_mult.
    apply (differentiable_pt_lim_left vg).
    apply (differentiable_pt_lim_left dg2t).
  | {(   Derive _ r * _ + _ * Derive _ r 
         - (Derive _ r * _ + _ * Derive _ r)
    )}  rewrite ?Derive_mult.
    apply (differentiable_pt_lim_left vg).
    apply (differentiable_pt_lim_left dg2t).
    apply (differentiable_pt_lim_left ug).
    apply (differentiable_pt_lim_left dg1t).
  | {(  (udx * (g1_r r t) + udy * (g2_r r t)) * _ + _ - _ )%R}
    do 2 apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r.
    pose hu := fun r' t' => u (g1 r' t') (g2 r' t').
    under Derive_ext => r'.
      rewrite (_: u _ _ = hu r' t); auto.
    over.
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  | {(  _ - ((vdx * g1_r r t + vdy * (g2_r r t)) * _ + _) )%R}
    rewrite ?Rplus_assoc;
    apply Rplus_eq_compat_l;
    apply Ropp_eq_compat;
    apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r;
    idtac .
    pose hv := fun r' t' => v (g1 r' t') (g2 r' t').
    under Derive_ext => r'.
      rewrite (_: v _ _ = hv r' t); auto.
    over.
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  `Done.
  }
  move ->.
  set q := LHS.
  `Begin eq q. { rewrite {}/q.

  | {(   Derive _ _ - Derive _ _   )} rewrite ?Derive_minus.
    apply ex_derive_mult.
    apply (differentiable_pt_lim_right ug).
    apply (differentiable_pt_lim_right dg1r).
    apply ex_derive_mult.
    apply (differentiable_pt_lim_right vg).
    apply (differentiable_pt_lim_right dg2r).
  | {(   Derive _ _ * _ + _ * Derive _ _ 
         - (Derive _ _ * _ + _ * Derive _ _)
    )}  rewrite ?Derive_mult.
    apply (differentiable_pt_lim_right vg).
    apply (differentiable_pt_lim_right dg2r).
    apply (differentiable_pt_lim_right ug).
    apply (differentiable_pt_lim_right dg1r).
  | {(  (udx * (g1_t r t) + udy * (g2_t r t)) * _ + _ - _ )%R}
    do 2 apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r.
    pose hu := fun r' t' => u (g1 r' t') (g2 r' t').
    under Derive_ext => t'.
      rewrite (_: u _ _ = hu r t'); auto.
    over.
    eapply (differentiable_pt_lim_unique _ _ _ _ _ _).
  | {(  _ - ((vdx * g1_t r t + vdy * (g2_t r t)) * _ + _) )%R}
    rewrite ?Rplus_assoc;
    apply Rplus_eq_compat_l;
    apply Ropp_eq_compat;
    apply Rplus_eq_compat_r;
    apply Rmult_eq_compat_r;
    idtac .
    pose hv := fun r' t' => v (g1 r' t') (g2 r' t').
    under Derive_ext => t'.
      rewrite (_: v _ _ = hv r t'); auto.
    over.
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
Lemma Holo_mult: forall f g z k,
  Holo f g z -> Holo (fun q => k * (f q)) (fun q => k * (g q)) z.
Proof.
  move => f g z k.
  move => /(filterdiff_scal_r_fct k ). 
  have H := Cmult_comm.
  move /(_ H).
  under ext_filterdiff_d => t.
    rewrite scal_assoc.
    have ->: (mult k t = mult t k) by unfold_alg.
    rewrite -scal_assoc.
  over.
  rewrite -/(is_derive _ _ _).
  unfold_alg.
Qed.

Ltac diff_help := timeout 1 
  match goal with 
  | |- ex_derive (fun _ => _ - _)%R _ => apply: ex_derive_minus
  | |- ex_derive (fun _ => _ * _)%R _ => apply: ex_derive_mult 
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

Lemma inside_internal: forall a b t' t, 
  Rabs(t' -t) < Rmin (Rabs(t -a)) (Rabs(t-b)) -> 
  Rmin a b < t < Rmax a b -> 
  Rmin a b < t' < Rmax a b.
Proof.
  move => a b . 
  wlog: a b / (a < b). {
    move => H t' t t'bd tbd.
    destruct (Rle_lt_dec a b).
    inversion r.
    - apply: H; eauto.
    - subst. 
      rewrite Rmin_left in tbd; auto.
      rewrite Rmax_left in tbd; auto.
      lra.
    - rewrite Rmin_comm Rmax_comm.
      rewrite Rmin_comm in t'bd.
      rewrite Rmin_comm Rmax_comm in tbd. apply: H; eauto.
  }
  move => R t' t t'bd tbd.
  split.
  + rewrite Rmin_left in tbd *; last by lra.
    eapply (Rlt_le_trans) in t'bd; last by apply Rmin_l.
    rewrite [x in _ < x]Rabs_pos_eq in t'bd; last by lra.
    move : t'bd => /Rabs_lt_between => ?.
    lra.
  + rewrite Rmax_right in tbd *;last by lra.
    eapply (Rlt_le_trans) in t'bd; last by apply Rmin_r.
    rewrite [x in _ < x]Rabs_minus_sym 
            [x in _ < x]Rabs_pos_eq in t'bd; last by lra.
    move : t'bd => /Rabs_lt_between => ?.
    lra.
Qed.

(* I suspect that the proposition I'm working with 
are actually decidable anyway, so this is probably overkill*)
Axiom excluded_middle: forall P:Prop, P \/ ~P.

Lemma not_not_impl: forall (P:Prop), ~ ~ P <-> P.
Proof.
  move => P. tauto.
Qed.

Section DeriveHomotopy .
  Variables (u v u' v': R -> R -> R) (a b c d:R).
  Variables (g1 g2 : R -> R -> R ).

  Local Definition g:= fun p q => (g1 p q, g2 p q).
  Local Definition f:= fun z => (u z.1 z.2, v z.1 z.2).
  Local Definition f':= fun z => (u' z.1 z.2, v' z.1 z.2).
  Local Definition g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q).
  Local Definition g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p).

  Lemma inside': forall t, Rmin a b < t < Rmax a b -> 
    0 < Rmin (Rabs(t-a)) (Rabs(t-b)).
  Proof.
    move => t tbd.
      apply Rmin_glb_lt; apply Rabs_pos_lt;
      eapply Rminus_eq_contra; move => ?; subst;
      destruct (Rle_dec a b);
      try (rewrite Rmin_left in tbd; auto; lra);
      try (rewrite Rmax_left in tbd; auto; lra);
      try (rewrite Rmax_right in tbd; auto; lra);
      try (rewrite Rmin_right in tbd; auto; lra).
  Qed.

  Hypothesis cled: c < d.
  Hypothesis holo_loc: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  Holo f f' (g r0 t0)) r t.

  Hypothesis cts_derive: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  continuous f' (g r0 t0)) r t.

  Hypothesis smooth: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
    SmoothPath g1 g2 r t.

  Definition nice r0 t0 :=
    Holo f f' (g r0 t0) /\
    SmoothFun g1 r0 t0 /\
    SmoothFun g2 r0 t0 /\
    continuous f' (g r0 t0).

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
    rewrite /nice.
    tauto. 
  Qed.

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
    clear l.
    destruct_match; try lra.
    set del' := locally_2d_ex_dec _ _ _ _ _ .
    move: del' => [del' dH] /= tballt0.
    apply dH.
    apply: Rlt_le_trans.
    2: apply tballt0.
    apply r'bd.
  Qed.


  Lemma diff_integrand: forall r t,
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
    locally_2d (
        differentiable_pt (fun r0 t0 => Re(f (g r0 t0) * g_t r0 t0))) r t.
  Proof.
    move => r t rbd tbd.
    apply: locally_2d_impl (locally_nice  rbd tbd).
    apply locally_2d_forall.
    move => r0 t0 [+  
      [[?[?[?[??]]]] [[?[?[?[??]]]]] _] ].
    copy => /holo_differentiable_pt_lim_real Du 
            /holo_differentiable_pt_lim_imaginary Dv.
    apply differentiable_pt_comp;
    simpl in *.
    1: apply differentiable_pt_minus.
    all: apply: differentiable_pt_comp.
    1,4: apply differentiable_pt_mult.
    1: apply differentiable_pt_comp.
    2,3,4,6: now auto.
    all: apply differentiable_pt_comp.
    5,6: now auto.
    1,4: eexists;eexists; now eauto.
    1: apply differentiable_pt_proj1; apply ex_derive_id.
    1: apply differentiable_pt_proj2; apply ex_derive_id.
  Qed.

  Local Ltac foo x y := 
    let smooth := fresh in 
      move => /(_ x y)[+ smooth];
      copy => /holo_differentiable_pt_lim_real ? 
              /holo_differentiable_pt_lim_imaginary ?;
      case: smooth => /locally_2d_singleton [? [H Q]] [/locally_2d_singleton [?[??]] c];
      simpl in *;
      repeat diff_help; auto.

  Ltac auto_2d_continuous :=
    repeat (
    try apply continuity_2d_pt_minus;
    try apply continuity_2d_pt_plus;
    try apply continuity_2d_pt_mult;
    try apply continuity_2d_pt_opp;
    simpl in *; auto).

  Lemma D: forall r, 
    c <= r <= d ->  
      is_derive (fun r0 => RInt (fun t0 => Re(f (g r0 t0) * g_t r0 t0 ))%C a b) r 
      (RInt (fun t0 => Derive (fun r0 => Re(f (g r0 t0) * g_t r0 t0 )%C) r) a b). 
  Proof.
    move => r rbd.
    apply is_derive_RInt_param.
    - apply: unif_r; auto.
      move => r' t' r'bd t'bd.
      apply: locally_2d_impl (diff_integrand r'bd t'bd).
      apply: locally_2d_forall.
      move => r0 t0 /differentiable_pt_ex_derive [_ H].
      tauto.
    - move => t tbd.
      move: locally_nice => /(_ _ _ rbd tbd) nice.
      eapply continuity_2d_pt_ext_loc. {
        apply: locally_2d_impl nice.
        apply: locally_2d_forall => r0 t0 [holo [
           [?[?[?[??]]]] [
           [?[?[?[??]]]] _]]].
        move: holo.
        copy => /holo_differentiable_pt_lim_imaginary ?.
        copy => /holo_differentiable_pt_lim_real ?.
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
        all: repeat diff_help; auto.
      }
      move: nice => /locally_2d_singleton
      [holo [
         [?[?[?[??]]]] [
         [?[?[?[??]]]] +]]].
      copy => /(continuous_comp _ fst) //= Cu'.
      move => /(continuous_comp _ snd) //= Cv'.
      move: holo.
      copy => /holo_differentiable_pt_lim_imaginary ?
              /holo_differentiable_pt_lim_real ?.
      simpl in *.
      auto_2d_continuous.
      1,3,7,9: apply continuity_2d_pt_comp.
      all: try now (
        apply: differentiable_continuity_pt; repeat diff_help; auto;
        apply: (differentiable_pt_comp); try diff_help; eauto).
      all: apply/continuity_2d_pt_continuous;
        first [apply Cu' | apply Cv']; auto_continuous_aux.
  
    - apply: filter_imp.
      1: move => r' H; 
         apply: ex_RInt_continuous; 
         exact H.
      apply: unif_r; auto.
      move => r' t' r'bd t'bd.
      apply: locally_2d_impl (diff_integrand r'bd t'bd).
      apply locally_2d_forall.
      move => r0 t0 /differentiable_pt_ex_derive H.
      apply: ex_derive_continuous.
      tauto.
  Qed.

  Lemma path_independence_part_3_real:
      is_derive (fun r0 => RInt (fun t0 => Re(f (g r0 t0) * g_t r0 t0 ))%C a' b') r 
     (Re(f (g r b') * g_r r b' - f (g r a') * g_r r a' )%C).
  Proof.
    have D := D.
    erewrite RInt_ext in D. 
    2:{ move => x xbd.
      rewrite -(@path_independence_part_2_real u v u' v').
      reflexivity.
      all: move: locally_nice => [del /(_ r (ball_center _ _) x)];
      move => H; apply H; apply: inside; split; left; apply xbd.
    }
    rewrite RInt_Derive in D. 
    - apply: D.
    - move => ? /inside ?.
      apply: diff_t; 
      first by (move: holo => /locally_singleton; apply).
      by (move: smooth => /locally_singleton; apply).
    - simpl. 
      move : locally_nice => [del H] t /inside  tbd.
      eapply continuous_ext_loc. {
      pose del2 := (Rmin del (Rmin (Rabs(t-a)) (Rabs(t-b)))).
      have del2ge: 0 < del2 by
        apply Rmin_glb_lt; first (by apply: cond_pos);
        apply Rmin_glb_lt; apply Rabs_pos_lt;
        eapply Rminus_eq_contra; move => ?; subst;
        destruct (Rle_dec a b);
        try (rewrite Rmin_left in tbd; auto; lra);
        try (rewrite Rmax_left in tbd; auto; lra);
        try (rewrite Rmax_right in tbd; auto; lra);
        try (rewrite Rmin_right in tbd; auto; lra).
      pose del2pos := mkposreal del2 del2ge. 
      exists del2pos => t' t'ball.
      rewrite /ball /= /AbsRing_ball /= /ball /abs /= /minus /= 
        /plus /= /opp /= -/(Rminus _ _) in t'ball.
      move: t'ball => /(Rlt_le_trans _ _ _) /(_ (Rmin_r _ _)) t'bd.
      have {}t'bd: (Rmin a b < t' < Rmax a b) 
          by apply: (inside_internal (t:=t)).
      move: H => /(_ r (ball_center _ _)); copy => H.
      move => /(_ t' t'bd) [+ _].
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
      all: move: H; foo t' t'bd. 
      }
      move: H => /(_ r (ball_center _ _)).
      foo t tbd.
      move:c => [? [?[??]]].
      move: cts => /(_ t tbd) .
      copy.
      rewrite /f'.
      move => /(continuous_comp _ fst) //= Cu'.
      move => /(continuous_comp _ snd) //= Cv'.
      repeat auto_continuous_aux; simpl.
  
      1,3,6,8,10,13: apply continuous_comp_2.
      all: try now (apply: ex_derive_continuous; repeat diff_help; auto).
      all: try now (first [apply Cu' | apply Cv']; auto_continuous_aux).
      1,2: apply/continuity_2d_pt_continuous; 
           apply differentiable_continuity_pt; diff_help.
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

  End DeriveInterior.
  Variables (c d: R).
  Hypothesis holo: 
    forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
                Holo f f' (g r t).
  Hypothesis cts: 
    forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
                continuous f' (g r t) .
  Hypothesis smooth:
    forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b -> 
                SmoothPath g1 g2 r t .

  Definition I q := RInt (fun t0 : R => Re (f (g q t0) * g_t q t0)) a' b'.

  Lemma path_mvt_aux:
    a' < b' ->
    (forall r t, Rmin a b < t < Rmax a b ->
                continuous (g1 r) t /\ 
                continuous (g2 r) t /\ 
                continuous (Derive (g1 r)) t /\ 
                continuous (Derive (g2 r)) t /\ 
                continuous (fun q => u q.1 q.2) (g1 r t, g2 r t) /\
                continuous (fun q => v q.1 q.2) (g1 r t, g2 r t)) ->
    (forall (eps: posreal) r, Rmin c d <= r <= Rmax c d -> 
      locally r ( fun r' => forall t, a' <= t <= b' ->  
        ball (f (g r t) * g_t r t) eps (f (g r' t) * g_t r' t) )) ->
    exists xi, Rmin c d <= xi <= Rmax c d /\
               (I d - I c)%R = 
      ((Re (f (g xi b') * g_r xi b' - f (g xi a') * g_r xi a'))%C * (d-c))%R.
  Proof.
   move => ? ctsf unif_cts.
    have open_r: (open (fun z => Rmin c d < z < Rmax c d)) 
      by apply: open_and; [apply: open_gt | apply: open_lt].
     
    apply (@MVT_gen I c d); 
    [ move => r rbd; apply: path_independence_part_3_real | ].
    - apply: @locally_open rbd; first by apply: open_r.
      move => ? ? ? ?. apply: holo; auto.
    - move => *; by apply: cts.
    - apply: @locally_open rbd; first by apply: open_r.
      move => ? ? ? ?. by apply: smooth.
    - move => r rbd. 
      rewrite /I continuity_pt_filterlim.
      rewrite filterlim_locally => eps.
      pose delv := (eps/(b' - a') /2)%R.
      have epspos := cond_pos eps.
      have delpos: 0 < delv by 
        apply: Rdiv_lt_0_compat; last lra; 
        apply Rdiv_lt_0_compat; lra.
      pose del := mkposreal delv delpos.
      move: unif_cts => /(_ (del) r rbd) H.
      apply: filter_imp H => r'.
      move => H.
      rewrite /ball //= /AbsRing_ball.

      rewrite -!RInt_minus /abs //=.
      eapply (Rle_lt_trans).  
      eapply abs_RInt_le_const; first by left;auto.
      1,4,5: apply: ex_RInt_continuous; 
             move => t' /inside t'bd;
             move: ctsf;
             copy => /(_ r t' t'bd) [?[?[?[?[??]]]]];
             move => /(_ r' t' t'bd) [?[?[?[?[??]]]]];
             repeat auto_continuous_aux;
             try apply: continuous_comp_2; 
             try apply: continuous_pair; 
             auto.
      + left. rewrite /abs //= in H. apply (H t H0).
      + rewrite /delv; field_simplify; lra.
  Qed.
End DeriveHomotopy.

Lemma is_derive_continuous: forall 
  {K: AbsRing} {V : NormedModule K} f f' x,
  is_derive (K:=K) (V:=V) f x f' -> continuous f x.
Proof.
 move => *.
 apply ex_derive_continuous; eexists;  eauto.
Qed.

Lemma path_independence_part_4_real:
  forall (a b a' b' c d c' d' :R) (f f' : C -> C) (g1 g2: R -> R -> R),
  let g := fun r t => (g1 r t, g2 r t) in
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in 
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
    c' < d' ->
    Rmin a b < a' < Rmax a b -> 
    Rmin a b < b' < Rmax a b -> 
    Rmin c d < c' < Rmax c d -> 
    Rmin c d < d' < Rmax c d -> 
    (forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
                  Holo f f' (g r t) /\
                  continuous f' (g r t) /\
                  SmoothPath g1 g2 r t) ->
    (forall r, Rmin c d < r < Rmax c d -> 
                (g r a' = g r b') /\ 
                (g_r r a' = g_r r b')) ->
    RInt (fun t0 : R => Re (f (g c' t0) * g_t c' t0)) a' b' =
    RInt (fun t0 : R => Re (f (g d' t0) * g_t d' t0)) a' b' .
  Proof.
    move => a b a' b' c d c' d' f f' g1 g2 g g_t g_r.
    move => c'led' a'bd b'bd c'bd d'bd nice loop.
    pose u := fun p q => (f (p,q)).1.
    pose v := fun p q => (f (p,q)).2.
    pose u' := fun p q => (f' (p,q)).1.
    pose v' := fun p q => (f' (p,q)).2.
    pose ff := fun z => (u z.1 z.2, v z.1 z.2).
    pose ff' := fun z => (u' z.1 z.2, v' z.1 z.2).
    pose h := fun r0 => RInt (fun t0 : R => Re (ff (g r0 t0) * g_t r0 t0)) a' b'.

    change (h c' = h d').
    apply:eq_is_derive ; last by [].
    move => r rbd.
    have ->: (zero = Re(f (g r b') * g_r r b' - f (g r a') * g_r r a' )%C) by
      case : (loop r); first lra;
      move => -> -> //=; 
      rewrite /zero //=;
      lra.
    rewrite /h.
    have open_r: (open (fun z => Rmin c d < z < Rmax c d)) 
      by apply: open_and; [apply: open_gt | apply: open_lt].
    apply (@path_independence_part_3_real u v u' v' a' b' a b g1 g2).
    - lra.
    - lra.
    - eapply locally_open; first by apply: open_r.
      + move => r' r'bd t' t'bd //=.
        rewrite /path_independence.f 
                /path_independence.f' 
                /path_independence.g.
        eapply (is_derive_ext f). {
          move => ?.
          by rewrite -!surjective_pairing.
        }
        rewrite -!surjective_pairing.
        apply nice; lra.
      + simpl; lra.
    - rewrite /path_independence.f' /path_independence.g => t' t'bd.
      eapply (continuous_ext f'). {
        move => ?.
        by rewrite -!surjective_pairing.
      }
      apply nice; lra.
    - eapply locally_open; first by apply: open_r.
      + move => *; apply nice; lra.
      + simpl. lra.
  Qed.

Lemma integrand_cts:
  forall (a b a' b' c d c' d' :R) (f f' : C -> C) (g1 g2: R -> R -> R),
  let g := fun r t => (g1 r t, g2 r t) in
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in 
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
    c' < d' ->
    Rmin a b < a' < Rmax a b -> 
    Rmin a b < b' < Rmax a b -> 
    Rmin c d < c' < Rmax c d -> 
    Rmin c d < d' < Rmax c d -> 
    (forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
                  Holo f f' (g r t) /\
                  continuous f' (g r t) /\
                  SmoothPath g1 g2 r t) ->
    (forall r, Rmin c d < r < Rmax c d -> 
                (g r a' = g r b') /\ 
                (g_r r a' = g_r r b')) ->
    (forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
    continuous (fun t0 => f (g r t0) * g_t r t0) t).
Proof.
  move => a b a' b' c d c' d' f f' g1 g2 g g_t g_r.
  move => c'led' a'bd b'bd c'bd d'bd nice loop.
  move => r t rbd tbd.
  move: nice => /( _ r t rbd tbd) [/is_derive_continuous holo [_ smooth]].
  case: smooth => /locally_2d_singleton [? [H Q]] [/locally_2d_singleton [?[??]] ?];
    apply/continous_C_AbsRing.
    apply: continuous_mult.
    + apply continuous_comp.
      * rewrite /g. auto_continuous_aux; apply: ex_derive_continuous; diff_help.
      * apply/continous_C_NormedModule. 
        apply: filterlim_filter_le_1; last exact holo.
        move => P; apply prod_c_topology_eq.
    + rewrite /g_t //=. apply continuous_comp_2.
      1,2: apply: ex_derive_continuous; diff_help.
      Set Printing Implicit.
      eapply continuous_ext. move => ?.
        rewrite -surjective_pairing.
      reflexivity.
      apply: filterlim_filter_le_2;
      move => P. 
      apply prod_c_topology_eq.
      auto.
Qed.
Lemma path_independence_part_4_imaginary:
  forall (a b a' b' c d c' d' :R) (f f' : C -> C) (g1 g2: R -> R -> R),
  let g := fun r t => (g1 r t, g2 r t) in
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in 
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
    c' < d' ->
    Rmin a b < a' < Rmax a b -> 
    Rmin a b < b' < Rmax a b -> 
    Rmin c d < c' < Rmax c d -> 
    Rmin c d < d' < Rmax c d -> 
    (forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
                  Holo f f' (g r t) /\
                  continuous f' (g r t) /\
                  SmoothPath g1 g2 r t) ->
    (forall r, Rmin c d < r < Rmax c d -> 
                (g r a' = g r b') /\ 
                (g_r r a' = g_r r b')) ->
    RInt (fun t0 : R => Im (f (g c' t0) * g_t c' t0)) a' b' =
    RInt (fun t0 : R => Im (f (g d' t0) * g_t d' t0)) a' b' .
Proof.
  move => a b a' b' c d c' d' f f' g1 g2 g g_t g_r.
  move => c'led' a'bd b'bd c'bd d'bd nice loop.
  pose h := fun q => Ci * f q.
  have toRe: forall r t, Im ( f (g r t) * g_t r t) = Ropp (Re (h (g r t) * g_t r t)). {
    move => r t. 
    rewrite /h //=.
    field_simplify_eq; auto.
  }
  under RInt_ext => x _ do rewrite toRe.
  rewrite RInt_opp.
  symmetry.
  under RInt_ext => x _ do rewrite toRe.
  rewrite RInt_opp.
  f_equal. 
  symmetry.
  apply: path_independence_part_4_real; eauto.
  - move => r t ? ?; split; [| split]. 
    + apply: Holo_mult; apply nice; auto.
    + apply/continous_C_AbsRing.
      apply: continuous_mult; first by auto_continuous_aux.
      apply/continous_C_AbsRing.
      apply nice; auto.
    + apply nice; auto.
  - apply ex_RInt_continuous => z /(inside a'bd b'bd) zbd.
    eapply continuous_ext. move => t.
      rewrite -[RHS]Ropp_involutive -toRe.
    reflexivity.
    apply: continuous_opp.
    apply continuous_comp; last by apply: continuous_snd.
    apply: integrand_cts; eauto.
  - apply ex_RInt_continuous => z /(inside a'bd b'bd) zbd.
    eapply continuous_ext. move => t.
      rewrite -[RHS]Ropp_involutive -toRe.
    reflexivity.
    apply: continuous_opp.
    apply continuous_comp; last by apply: continuous_snd.
    apply: integrand_cts; eauto.
Qed.
    
Lemma ReImSplit : forall z, 
  Re z + Ci*Im z = z.
Proof.
  move => z.
  rewrite /Re /Im /Cplus //=.
  set p := LHS.
  simplify_as_R2 e p.
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
    

Theorem path_independence:
  forall (a b a' b' c d c' d' :R) (f f' : C -> C) (g1 g2: R -> R -> R),
  let g := fun r t => (g1 r t, g2 r t) in
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in 
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
    c' < d' ->
    Rmin a b < a' < Rmax a b -> 
    Rmin a b < b' < Rmax a b -> 
    Rmin c d < c' < Rmax c d -> 
    Rmin c d < d' < Rmax c d -> 
    (forall r t, Rmin c d < r < Rmax c d ->
                Rmin a b < t < Rmax a b ->
                  Holo f f' (g r t) /\
                  continuous f' (g r t) /\
                  SmoothPath g1 g2 r t) ->
    (forall r, Rmin c d < r < Rmax c d -> 
                (g r a' = g r b') /\ 
                (g_r r a' = g_r r b')) ->
    ex_RInt (fun t0 : R => f (g c' t0) * g_t c' t0) a' b' /\
    ex_RInt (fun t0 : R => f (g d' t0) * g_t d' t0) a' b' /\
    RInt (V:=C_R_CompleteNormedModule) 
      (fun t0 : R => f (g c' t0) * g_t c' t0) a' b' =
    RInt (V:=C_R_CompleteNormedModule)
      (fun t0 : R => f (g d' t0) * g_t d' t0) a' b'.
  Proof.

    Local Ltac prod_int := 
       rewrite -?ex_RInt_prod;
       apply ex_RInt_continuous => z /(inside a'bd b'bd) zbd;
       apply: integrand_cts; eauto.
    move => a b a' b' c d c' d' f f' g1 g2 g g_t g_r.
    move => c'led' a'bd b'bd c'bd d'bd nice loop.
    split; [|split].
    1,2: prod_int.
    apply: is_RInt_unique.
    rewrite split_cint /compose.
    rewrite -(@path_independence_part_4_real a b a' b' c d c' d' f f'); auto.
    rewrite -(@path_independence_part_4_imaginary a b a' b' c d c' d' f f'); auto.
    rewrite -split_cint.
    apply RInt_correct.
    all: prod_int.
Qed.