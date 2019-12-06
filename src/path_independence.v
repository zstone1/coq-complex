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

Section CauchyIntegral.
  Record Contour := mkContour {
    gamma: R -> C; 
    l: R;
    r: R;
    l_to_r: l < r;
    gamma' : R -> C;
    diff: forall t, l < t < r -> is_derive gamma t (gamma' t);
  }.
  Open Scope C. 
  Definition CInt {g: Contour } f := 
    RInt (V:=C_R_CompleteNormedModule) 
      (fun t => f (gamma g t) * (gamma' g t)) (l g) (r g) .
  Definition is_CInt (g: Contour) (f: C -> C) (z:C) :=
    is_RInt (fun t => f (gamma g t) * (gamma' g t)) (l g) (r g) z.
  
(**Strategy for path independence 
1: prove 

  soo.... this proof is broken somewhere. 
  (f(g(r,t)) * g_t(r,t))_r = 
  f'(g(r,t)) * g_r(r,t) * g_t(r,t) + f(g(r,t)) *g_tr(r,t)  = 
  f'(g(r,t)) * g_t(r,t) * g_r(r,t) + f(g(r,t)) *g_rt(r,t)  = 
  (f(g(r,t)))_t * g_r(r,t) + f(g(r,t)) * (g_r(r,t))_t  = 
  (f(g(r,t))* g_r(r,t))_t
  something about convservative fields. The important thing
  is that holomorphic functions have cauchy riemann equations,
  which magically finish the proof.


2: apply is_derive_RInt_param_bound_comp.
   this pushes the d/dr into the integral.

3: show (Rint_a^b f(g(r,t))*g_t(r,t))_r = 0

4: apply fn_eq_Derive_eq
*)

Open Scope R.
(** A stupid issue with the existing proof in Coquelicot.
they prove Derives = _, but that's not strong enough.
So I copy pasted the entire proof, minus one rewrite at the beginning*)
Lemma differentiable_pt_lim_is_derive (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> is_derive (fun x => f x y) x lx /\ is_derive (fun y => f x y) y ly.
Proof.
  move => Df ; split ; apply is_derive_Reals => e He ;
  case: (Df (pos_div_2 (mkposreal e He))) => {Df} delta /= Df ;
  exists delta => h Hh0 Hh.


  replace ((f (x + h) y - f x y) / h - lx)
    with ((f (x+h) y - f x y - (lx * ((x+h) - x) + ly * (y - y))) / h)
    by (by field).
  rewrite Rabs_div.
  apply Rlt_div_l.
  by apply Rabs_pos_lt.
  apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x + h - x)) (Rabs (y - y))).
  apply (Df (x+h) y).
  by (ring_simplify (x + h - x)).
  rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
  ring_simplify (x + h - x).
  rewrite Rmax_left.
  apply Rmult_lt_compat_r.
  by apply Rabs_pos_lt.
  lra.
  rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
  by [].

  replace ((f x (y + h) - f x y) / h - ly)
    with ((f x (y + h) - f x y - (lx * (x - x) + ly * ((y + h) - y))) / h)
    by (by field).
  rewrite Rabs_div.
  apply Rlt_div_l.
  by apply Rabs_pos_lt.
  apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x - x)) (Rabs (y + h - y))).
  apply (Df x (y + h)).
  rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
  by (ring_simplify (y + h - y)).
  ring_simplify (y + h - y).
  rewrite Rmax_right.
  apply Rmult_lt_compat_r.
  by apply Rabs_pos_lt.
  lra.
  rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
  by [].
Qed.

Lemma differentiable_pt_lim_left (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> ex_derive (fun x => f x y) x.
Proof.
  move => df.
  have := (differentiable_pt_lim_is_derive df).
  case => H _.
  exists lx; auto.
Qed.

Lemma differentiable_pt_lim_right (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> ex_derive (fun y => f x y) y.
Proof.
  move => df.
  have := (differentiable_pt_lim_is_derive df).
  case => _ H.
  exists ly; auto.
Qed.


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

  | {(   Derive _ r - Derive _ r   )} rewrite ?Derive_minus.
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

Lemma holo_differentiable_pt_lim_imaginary: forall (f:C -> C) x y g,
  is_derive (K:=C_AbsRing) f (x,y) g-> 
  differentiable_pt_lim (fun x y => (f (x,y)).2) x y g.2 g.1 .
Proof.
  move => f x y g.
  rewrite /is_derive /filterdiff.
  move => [_ /(_ (x,y))] .
  move => /(_ (@is_filter_lim_locally (AbsRing_UniformSpace C_AbsRing) (x,y) )).
  move => + eps.
  have erpos : ( 0 < eps /(sqrt 2)) by apply Rdiv_lt_0_compat;
    [apply (cond_pos eps) | apply Rlt_sqrt2_0 ]. 
  pose epsr2 := mkposreal (eps/ (sqrt 2)) erpos .
  move => /(_ epsr2) /prod_c_topology_eq [del H].
  exists del => u v uball vball.
  move :H => /(_ (u,v)).
  unfold_alg; rewrite /AbsRing_ball. unfold_alg .
  have Q: (Rabs (u-x) < del /\ Rabs (v-y) < del) by auto.
  move => /(_ Q) {Q}.
  set p := (x in Cmod x <= _).
  simplify_as_R2 e p.
  set p := (x in Cmod (x,_)).
  set q := (x in Cmod (_,x)).
  set l := (x in Rabs x).
  set dz := ((u,v) + _)%C.
  simplify_as_R2 e dz.
  have ->: (l = q) by rewrite /l /q; field_simplify_eq.
  move => H.
  apply: Rle_trans.
  apply: Cmod_Rabs_imaginary p _.
  apply: Rle_trans.
  apply H.
  apply (Rle_trans _ (eps * Rmax (Rabs (u-x)) (Rabs (v-y)))); last by reflexivity.
  rewrite /Rdiv.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l; first by left; apply: cond_pos.
  field_simplify .
  apply/ Rle_div_l; first by apply Rlt_sqrt2_0.
  rewrite Rmult_comm.
  apply Cmod_2Rmax.
  apply Rsqr_gt_0_0.
  rewrite Rsqr_sqrt; lra.
Qed.

Lemma holo_differentiable_pt_lim_real: forall (f:C -> C) x y g,
  is_derive (K:=C_AbsRing) f (x,y) g-> 
  differentiable_pt_lim (fun x y => (f (x,y)).1) x y g.1 (-g)%C.2 .
Proof.
  Open Scope C.
  move => f x y g.
  move => /(filterdiff_scal_r_fct Ci ). 
  have H := Cmult_comm.
  move /(_ H).
  under ext_filterdiff_d => t.
    rewrite scal_assoc.
    have ->: (mult Ci t = mult t Ci) by unfold_alg.
    rewrite -scal_assoc.
  over.
  move /holo_differentiable_pt_lim_imaginary.
  simpl in *.
  set p := (x in differentiable_pt_lim _ _ _ x _).
  simplify_R e p.
  set p := (x in differentiable_pt_lim _ _ _ _ x).
  simplify_R e p.
  eapply differentiable_pt_lim_ext.
  exists pos_half => u v _ _ . field_simplify_eq; auto.
Qed.

Definition SmoothPath g1 g2 r t:= 
  locally_2d (fun r' t' =>
    differentiable_pt g1 r' t' /\
    differentiable_pt (fun p q => Derive (g1 p) q) r' t' /\
    differentiable_pt (fun p q => Derive (g1 ^~ q) p) r' t') r t /\
  locally_2d (fun r' t' =>
    differentiable_pt g2 r' t' /\
    differentiable_pt (fun p q => Derive (g2 p) q) r' t' /\
    differentiable_pt (fun p q => Derive (g2 ^~ q) p) r' t') r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g1 z t) v) u) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g1 t z) u) v) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g2 z t) v) u) r t /\
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g2 t z) u) v) r t 
.
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
  move => u v u' v' r t g1 g2 g f f' [g1_smooth [g2_smooth +]] .
  move => [g1_rt_cts [g1_tt_cts [g2_rt_cts g2_tr_cts]]] holo.
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
  eapply (@path_independence_part_1 u v _ _ _ _ g1 g2 _ _ _ _ r t).
  9, 10:  apply Schwarz.
  - apply: differentiable_pt_unique. 
    move: holo => / holo_differentiable_pt_lim_real holo.
    simpl in *.
    eexists. eexists.
    eapply holo.
  - apply differentiable_pt_unique. 
    move: holo => /holo_differentiable_pt_lim_imaginary holo.
    simpl in *.
    eexists. eexists.
    eapply holo.
  - apply locally_2d_singleton in g1_smooth.
    apply differentiable_pt_unique; auto.
    by case: g1_smooth => H _.
  - apply locally_2d_singleton in g2_smooth.
    apply differentiable_pt_unique; auto.
    by case: g2_smooth => H _.
  - apply locally_2d_singleton in g1_smooth.
    move: g1_smooth => [_ [H _]].
    apply H.
  - apply locally_2d_singleton in g1_smooth.
    move: g1_smooth => [_ [_ H]].
    apply H.
  - apply locally_2d_singleton in g2_smooth.
    move: g2_smooth => [_ [H _]].
    apply H.
  - apply locally_2d_singleton in g2_smooth.
    move: g2_smooth => [_ [_ H]].
    apply H.
  - move: g1_smooth => [eps H1].
    exists eps => p q pbd qbd.
    move: H1 => /(_ p q pbd qbd). 
    case => /differentiable_pt_ex_derive [H1 H2]. 
    case => /differentiable_pt_ex_derive [H3 H4]
            /differentiable_pt_ex_derive [H5 H6].
    repeat split; auto.
  - auto.
  - auto.
  - move: g2_smooth => [eps H1].
    exists eps => p q pbd qbd.
    move: H1 => /(_ p q pbd qbd). 
    case => /differentiable_pt_ex_derive [H1 H2]. 
    case => /differentiable_pt_ex_derive [H3 H4]
            /differentiable_pt_ex_derive [H5 H6].
    repeat split; auto.
  - auto.
  - auto.
  - rewrite /f in holo. 
    rewrite -[LHS]Ropp_involutive.
    apply Ropp_eq_compat.
    symmetry.
    move: holo => /CauchyRiemann_Easy.
    simpl in *.
    tauto.
Qed.

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


Lemma path_independence_part_2_imaginary:
  forall (u v u' v': R -> R -> R) r t g1 g2, 
  let g:= fun p q => (g1 p q, g2 p q) in
  let f:= fun z => (u z.1 z.2, v z.1 z.2) in
  let f':= fun z => (u' z.1 z.2, v' z.1 z.2) in
  SmoothPath g1 g2 r t -> 
  Holo f f' (g r t) -> 
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
  Derive ( fun t0 => Im (f (g r t0) * g_r r t0 ))%C t =
  Derive ( fun r0 => Im (f (g r0 t) * g_t r0 t ))%C r  
.
Proof. 
  move => u v u' v' r t g1 g2 g f f' smooth.
  move => /(Holo_mult Ci).
  move => + g_t g_r.
  rewrite /Holo /is_derive.
  under ext_filterdiff_glo => z.
    set p := _ * _.
    simplify_as_R2 e p.
  over.
  under ext_filterdiff_d => z.
    set p := _ * _.
    simplify_as_R2 e p.
  over.
  move => holo.
  rewrite -/(is_derive _ _ _) in holo.
  have := @path_independence_part_2_real 
    (fun x y => -v x y)%R
    (fun x y => u x y)
    (fun x y => -v' x y)%R
    (fun x y => u' x y)
    r t g1 g2
    smooth
    holo
  .
  move => H.
  rewrite -[LHS]Ropp_involutive -[RHS]Ropp_involutive. 
  apply Ropp_eq_compat. 
  rewrite -2!Derive_opp.
  simpl in *.
  under Derive_ext => t0 do 
    rewrite Rplus_comm Ropp_plus_minus_distr Ropp_mult_distr_l.
  symmetry.
  under Derive_ext => r0 do 
    rewrite Rplus_comm Ropp_plus_minus_distr Ropp_mult_distr_l.
  auto.
Qed.

Ltac combine_local := 
match goal with 
| H1: @locally ?T _ _, H2: @locally ?T _ _  |- _ => 
  have:= filter_and _ _ H1 H2;
  try move /(_ ltac:(apply locally_filter)) {H1 H2}

end.




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
    inversion r0.
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

Lemma path_independence_part_3: forall u v u' v' r g1 g2 a b, 
  let g:= fun p q => (g1 p q, g2 p q) in
  let f:= fun z => (u z.1 z.2, v z.1 z.2) in
  let f':= fun z => (u' z.1 z.2, v' z.1 z.2) in
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
  a <> b ->
  locally r (fun r0 => forall t, Rmin a b < t < Rmax a b -> Holo f f' (g r0 t)) ->
  (forall t, Rmin a b < t < Rmax a b -> continuous f' (g r t)) ->
  locally r (fun r0 => forall t, Rmin a b < t < Rmax a b -> SmoothPath g1 g2 r0 t) -> 
  forall a' b', 
    (*Wierd issues with coquelicot with differentiability at the endpoints.*)
    (Rmin a b < a' < Rmax a b) ->
    (Rmin a b < b' < Rmax a b) ->
    is_derive (fun r0 => RInt (fun t0 => Re(f (g r0 t0) * g_t r0 t0 ))%C a' b') r 
   (Re(f (g r b') * g_r r b' )%C - (Re(f (g r a') * g_r r a' )%C))%R.
Proof.
  move => u v u' v' r g1 g2 a b g f f' g_t g_r altb holo cts smooth a' b' a'bd b'bd.
  combine_local.
  move => H.
  have inside: forall t, Rmin a' b' <= t <= Rmax a' b' -> Rmin a b < t < Rmax a b. {
    split.
    - apply: (@Rlt_le_trans _ (Rmin a' b') t). 
      apply: Rmin_glb_lt; [apply a'bd | apply b'bd].
      apply H0.
    - apply: (@Rle_lt_trans _ (Rmax a' b') _). 
      apply H0.
      apply: Rmax_lub_lt; [apply a'bd | apply b'bd].
  }
  Local Ltac foo x y := 
    let smooth := fresh in 
      move => [/(_ x y) + /(_ x y) smooth];
      copy => /holo_differentiable_pt_lim_real ? 
              /holo_differentiable_pt_lim_imaginary ?;
      case: smooth => /locally_2d_singleton [? [H Q]] [/locally_2d_singleton [?[??]] c];
      simpl in *;
      repeat diff_help; auto.
  have diff_t: (locally r( fun r0 => forall t, Rmin a' b' <= t <= Rmax a' b' -> 
    ex_derive (fun t0 => Re(f (g r0 t0) * g_r r0 t0)) t)). {
      apply: filter_imp H => r0 + t /inside tbd; foo t tbd.
  }
  have diff_r: (locally r( fun r0 => forall t, Rmin a' b' <= t <= Rmax a' b' -> 
    ex_derive (fun t0 => Re(f (g r0 t0) * g_t r0 t0)) t)). {
      apply: filter_imp H => r0 + t /inside tbd; foo t tbd.
  }
  have D: is_derive (fun r0 => RInt (fun t0 => Re(f (g r0 t0) * g_t r0 t0 ))%C a' b') r 
   (RInt (fun t0 => Derive (fun r0 => Re(f (g r0 t0) * g_t r0 t0 )%C) r) a' b'). {
   apply is_derive_RInt_param .
  - apply: filter_imp H => r0 + t /inside tbd; foo t tbd.
  - move :H => [del H] t /inside  tbd.
    eapply continuity_2d_pt_ext_loc. {
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
      exists del2pos => r' t' 
        /(Rlt_le_trans _ _ del) /(_ (Rmin_l _ _)) r'bd
        /(Rlt_le_trans _ _ _) /(_ (Rmin_r _ _)) t'bd.
      have {}t'bd: (Rmin a b < t' < Rmax a b) 
        by apply: (inside_internal (t:=t)).
      move: H => /(_ r' r'bd).
      copy.
      move => [/(_ t' t'bd) + _].
      copy => /holo_differentiable_pt_lim_real 
              /differentiable_pt_lim_unique [Du'1 Du'2]
              /holo_differentiable_pt_lim_imaginary
              /differentiable_pt_lim_unique [Dv'1 Dv'2].
      move => H.
      simpl in *.
      rewrite Derive_minus ?Derive_mult ?Derive_plus /=.
      rewrite (@Derive_comp_2_left u g1 g2).
      rewrite (@Derive_comp_2_left v g1 g2).
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
    repeat (
    try apply continuity_2d_pt_minus;
    try apply continuity_2d_pt_plus;
    try apply continuity_2d_pt_mult;
    try apply continuity_2d_pt_opp;
    simpl in *; auto).
    1,3,7,9: apply continuity_2d_pt_comp.
    all: try now (
      apply: differentiable_continuity_pt; repeat diff_help; auto;
      apply: (differentiable_pt_comp); try diff_help; eauto).
    all: apply/continuity_2d_pt_continuous;
      first [apply Cu' | apply Cv']; auto_continuous_aux.
  - apply: filter_imp diff_r => r0 D. 
    apply: ex_RInt_continuous => ??.
    apply: ex_derive_continuous .
    by apply: D.
  }
  erewrite RInt_ext in D. 
  2:{ move => x xbd.
    rewrite -(@path_independence_part_2_real u v u' v').
    reflexivity.
    all: move: H => [del /(_ r (ball_center _ _))].
    - case => _ +; apply; apply inside; split; left; apply xbd.
    - case => + _; apply; apply inside; split; left; apply xbd.
  }
  rewrite RInt_Derive in D. 
  - apply: D.
  - move:diff_t. 
    move => [? /(_ r (ball_center _ _))]. auto. 
  - simpl. 
    move :H => [del H] t /inside  tbd.
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
    move: H => /(_ r (ball_center _ _)).
    copy.
    simpl.
    move => [/(_ t' t'bd) + _].
    copy => /holo_differentiable_pt_lim_real 
            /differentiable_pt_lim_unique [Du'1 Du'2]
              /holo_differentiable_pt_lim_imaginary
              /differentiable_pt_lim_unique [Dv'1 Dv'2].
    move => H.
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
    3: apply: continuous_opp.

    1,3,6,8,10,13: apply continuous_comp_2.
    all: try now (apply: ex_derive_continuous; repeat diff_help; auto).
    all: try now (first [apply Cu' | apply Cv']; auto_continuous_aux).
    1,2: apply/continuity_2d_pt_continuous; 
         apply differentiable_continuity_pt; diff_help.

     //=.
    apply: continuity_2d_pt_comp.
Qed.

  Definition c_circle (t:R):C := (cos t, sin t).
  Definition c_circle' (t:R):C := (-sin t, cos t)%R.
  
  Lemma c_circle_deriv: forall x, is_derive c_circle x (c_circle' x).
  Proof.
    rewrite /c_circle /c_circle'.
    move => x.
    apply (is_derive_pair (f' := fun q => -_ _)%R); auto_derive_all. 
  Qed.
  Hint Resolve c_circle_deriv : derive_compute.

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

  Program Definition Circ_Contour (r:R) := {|
    l:= 0;
    r:= 1;
    l_to_r:= _;
    gamma := fun q => r * c_circle q;
    gamma' := fun q => r * c_circle' q;
  |}. 
  Obligation 1. lra. Qed.
  Obligation 2. 
    under ext_is_derive_glo => y do rewrite rmult_scal.
    rewrite rmult_scal.
    have := (c_circle_deriv t).
    move => /filterdiff_scal_r_fct //= /(_ r0 Rmult_comm).
    rewrite /is_derive.
    under ext_filterdiff_d => y. 
      rewrite scal_assoc.
      have ->: (mult r0 y = mult y r0 ) by  unfold_alg; lra.
      rewrite -scal_assoc.
    over.
    auto.
  Qed.

  Open Scope R.
  Lemma fubini: forall (a b c d: R) (f: C -> R), 
    c <= d -> a <= b ->
    (forall x y, a <= x <= b -> c <= y <= d -> continuous f (x,y)) ->
    RInt (fun x => RInt (fun y => f(x,y)) c d) a b =
    RInt (fun y => RInt (fun x => f(x,y)) a b) c d.
  Proof.
    move => a b c d f c_le_d a_le_b cts.
    pose h := fun z => RInt (fun v => f(z.1,v)) c z.2. 

    pose F := fun y => RInt (fun x => h (x, y)) a b.
    pose G := fun y => RInt (fun v => RInt (fun u => h (u, b)) a b) c y.

    have: (exists C, forall x, c <= x <= d -> F x = G x + C)%R. {
      apply fn_eq_Derive_eq.
      - apply/continuity_pt_filterlim.  
        


    }
    move => [C FeqG].
    have: (C = 0). {
      admit.
    }
    move => ?. subst.

    set p := LHS.
    replace p with (F d).
    set p' := RHS.
    replace p' with (G d).
    rewrite -[RHS]Rplus_0_r.
    apply: FeqG.
    split; auto using reflexivity.
  Admitted.
    


      have: continuous F
      have: continuous G
      have: (forall y, Derive F y = Derive G y).
      have: (F c = 0)
      have: (G c = 0)
    apply: F d = G d.
    (*1st apply some uniform continuity to prove h is continuous*)

    (*2st pove *)

    rewrite /RInt /iota.
    RInt_comp


    
(*utline of proof for cauchy integral theorem on a square. 
Note key usage of fubini.

    0 
    = RInt (fun x => (RInt (fun y => udy(x,y) - vdx (x,y) ) 0 r)) 0 r 
    
    = RInt (fun x => (RInt (fun y => udx(x,y)) 0 r)) 0 r 
      - RInt (fun x => (RInt (fun y => vdy (x,y)))) 0 r

    = RInt (fun y => (RInt (fun x => udx(x,y)) 0 r)) 0 r 
      - RInt (fun x => (RInt (fun y => vdy (x,y)))) 0 r

    =   RInt (fun y => u(r, y)) 0 r
      + RInt (fun y => u(0, y)) r 0
      + RInt (fun x => u(x,0)) 0 r 
      + RInt (fun x => u(x,r)) r 0 

    =   RInt (fun x => u(x,0)) 0 r 
      + RInt (fun y => u(r, y)) 0 r
      + RInt (fun x => u(x,r)) r 0 
      + RInt (fun y => u(0, y)) r 0
*)
  Definition SquareInt (r: R) (f: C -> R ) := 
    RInt (fun x => f (x, 0)) 0 r +
    RInt (fun y => f (r, y)) 0 r +
    RInt (fun x => f (x, r)) r 0 +
    RInt (fun y => f (0, y)) r 0 .
  Lemma CauchyIntegral_Squares: 
    forall (r: R) (u v: C -> R) g, 
      (forall z, 0 <= z.1 <= r -> 
                 0 <= z.2 <= r ->  
        Holo (fun q => (u q, v q)) g z) -> 
        
    SquareInt r u = 0.
  .
      


Print RInt_analysis.
Locate "eta".


Lemma fubini: forall (a b c d: R) (f: C -> R), 
  c <= d -> a <= b ->
  (forall x y, a <= x <= b -> c <= y <= d -> continuous f (x,y)) ->
  RInt (fun x => RInt (fun y => f(x,y)) c d) a b =
  RInt (fun y => RInt (fun x => f(x,y)) a b) c d.
Proof.
  move => a b c d f c_le_d a_le_b cts.
  pose h := fun x y => RInt (fun v => f(x,v)) c y. 

  pose F := fun y => RInt (fun x => h x y) a b.
  pose G := fun y => RInt (fun v => RInt (fun u => h u b) a b) c y.

  have ? : (forall x y, a<=x<=b -> c<=y<=d -> 
         continuous (fun z => h z.1 z.2) (x,y) ). {
    simpl in *.
    move => x y xbd ybd.
    have h_Rint: (is_RInt (fun v => f(x,v)) c y (h x y )). {
      apply: RInt_correct.
      apply: ex_RInt_continuous.
      rewrite Rmin_left; [ | case: ybd; auto ].
      rewrite Rmax_right; [ | case: ybd; auto ].
      move => z zbd.
      apply continuous_comp.
      - repeat auto_continuous_aux.
      - apply cts; auto.
        case:zbd; split; auto.
        apply: transitivity. 
        apply b0. 
        apply ybd.
    }
    rewrite /h.
  }
  have: (exists C, forall x, c <= x <= d -> F x = G x + C)%R. {
    apply fn_eq_Derive_eq.
    - rewrite continuity_pt_filterlim -/(continuous F c).
      rewrite /F.
      rewrite /continuous.
      apply: filterlim_RInt .


  }
  move => [C FeqG].
  have: (C = 0). {
    admit.
  }
  move => ?. subst.

  set p := LHS.
  replace p with (F d).
  set p' := RHS.
  replace p' with (G d).
  rewrite -[RHS]Rplus_0_r.
  apply: FeqG.
  split; auto using reflexivity.
Admitted.
Locate Schwarz.
Check filterdiff_comp.