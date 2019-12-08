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
  move: g1_smooth; copy => /locally_2d_singleton [? [??]] g1_smooth.
  move: g2_smooth; copy => /locally_2d_singleton [? [??]] g2_smooth.
  move: holo; copy => /holo_differentiable_pt_lim_real ?
                      /holo_differentiable_pt_lim_imaginary ?.
  simpl in *.
  
  eapply (@path_independence_part_1 u v _ _ _ _ g1 g2 _ _ _ _ r t);
    try apply Schwarz;
    try eauto;
    try apply: differentiable_pt_unique; eauto.

  3: lra.
  1: move: g1_smooth. 
  2: move: g2_smooth.
  all: move => [eps H1] ;
    exists eps => p q pbd qbd;
    move: H1 => /(_ p q pbd qbd);
    case => /differentiable_pt_ex_derive [H1 H2];
    by case => /differentiable_pt_ex_derive [H3 H4]
           /differentiable_pt_ex_derive [H5 H6].
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

Section DeriveHomotopy .
  Variables (u v u' v': R -> R -> R) (a' b' a b :R).
  Variables (g1 g2 : R -> R -> R ).

  Definition g:= fun p q => (g1 p q, g2 p q).
  Definition f:= fun z => (u z.1 z.2, v z.1 z.2).
  Definition f':= fun z => (u' z.1 z.2, v' z.1 z.2).
  Definition g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q).
  Definition g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p).
  Hypothesis a'bd: (Rmin a b < a' < Rmax a b).
  Hypothesis b'bd: (Rmin a b < b' < Rmax a b).

  Lemma inside: forall t, Rmin a' b' <= t <= Rmax a' b' -> Rmin a b < t < Rmax a b.
  Proof.
    split.
    - apply: (@Rlt_le_trans _ (Rmin a' b') t). 
      apply: Rmin_glb_lt; [apply a'bd | apply b'bd].
      apply H.
    - apply: (@Rle_lt_trans _ (Rmax a' b') _). 
      apply H.
      apply: Rmax_lub_lt; [apply a'bd | apply b'bd].
  Qed.

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

  Lemma inside'': forall t, Rmin a' b' <= t <= Rmax a' b' -> Rmin a b <= t <= Rmax a b.
  Proof.
    split; left; apply inside; auto.
  Qed.

  Section DeriveInterior.
  Variables (r: R).
  Hypothesis holo: 
    locally r (fun r0 => forall t, Rmin a b < t < Rmax a b -> Holo f f' (g r0 t)).
  Hypothesis cts: 
    (forall t, Rmin a b < t < Rmax a b -> continuous f' (g r t)) .
  Hypothesis smooth:
  locally r (fun r0 => forall t, Rmin a b < t < Rmax a b -> SmoothPath g1 g2 r0 t) .

  Lemma locally_nice: locally r (fun r0 => forall t, Rmin a b < t < Rmax a b -> 
    Holo f f' (g r0 t)/\ SmoothPath g1 g2 r0 t).
  Proof.
    combine_local => /(_ ltac:(apply locally_filter)) H. 
    apply: filter_imp H => r0 [H1 H2]; split;
    [apply H1 | apply H2]; auto.
  Qed.
  Local Ltac foo x y := 
    let smooth := fresh in 
      move => /(_ x y)[+ smooth];
      copy => /holo_differentiable_pt_lim_real ? 
              /holo_differentiable_pt_lim_imaginary ?;
      case: smooth => /locally_2d_singleton [? [H Q]] [/locally_2d_singleton [?[??]] c];
      simpl in *;
      repeat diff_help; auto.

  Lemma diff_t: (locally r( fun r0 => forall t, Rmin a' b' <= t <= Rmax a' b' -> 
    ex_derive (fun t0 => Re(f (g r0 t0) * g_r r0 t0)) t)).
  Proof.
      apply: filter_imp locally_nice => r0 + t /inside tbd. foo t tbd.
  Qed.
  Lemma diff_r: (locally r( fun r0 => forall t, Rmin a' b' <= t <= Rmax a' b' -> 
    ex_derive (fun t0 => Re(f (g r0 t0) * g_t r0 t0)) t)).
  Proof.
      apply: filter_imp locally_nice => r0 + t /inside tbd. foo t tbd.
  Qed.
  Ltac auto_2d_continuous :=
    repeat (
    try apply continuity_2d_pt_minus;
    try apply continuity_2d_pt_plus;
    try apply continuity_2d_pt_mult;
    try apply continuity_2d_pt_opp;
    simpl in *; auto).

  Lemma D: is_derive (fun r0 => RInt (fun t0 => Re(f (g r0 t0) * g_t r0 t0 ))%C a' b') r 
   (RInt (fun t0 => Derive (fun r0 => Re(f (g r0 t0) * g_t r0 t0 )%C) r) a' b'). 
  Proof.
     apply is_derive_RInt_param .
    3: apply: filter_imp diff_r => r0 D;
       apply: ex_RInt_continuous => ??;
       apply: ex_derive_continuous ;
       by apply: D.
    1: apply: filter_imp locally_nice => r0 + t /inside tbd; foo t tbd.
  
    move :locally_nice => [del H] t /inside  tbd.
    eapply continuity_2d_pt_ext_loc. {
      pose del2 := (Rmin del (Rmin (Rabs(t-a)) (Rabs(t-b)))).
      have del2ge: 0 < del2 by
        apply Rmin_glb_lt; [by apply: cond_pos| by apply: inside'].
      pose del2pos := mkposreal del2 del2ge. 
      exists del2pos => r' t' 
        /(Rlt_le_trans _ _ del) /(_ (Rmin_l _ _)) r'bd
        /(Rlt_le_trans _ _ _) /(_ (Rmin_r _ _)) t'bd.
      have {}t'bd: (Rmin a b < t' < Rmax a b) 
        by apply: (inside_internal (t:=t)).
      move: H; copy => H.
      move => /(_ r' r'bd t' t'bd)  [+ _].
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
      all: move: H => /(_ r' r'bd); foo t' t'bd. 
    }
    move: H => /(_ r (ball_center _ _)).
    foo t tbd.
    move:c => [? [?[??]]].
    move: cts => /(_ t tbd) .
    copy.
    rewrite /f'.
    move => /(continuous_comp _ fst) //= Cu'.
    move => /(continuous_comp _ snd) //= Cv'.
    auto_2d_continuous.
    1,3,7,9: apply continuity_2d_pt_comp.
    all: try now (
      apply: differentiable_continuity_pt; repeat diff_help; auto;
      apply: (differentiable_pt_comp); try diff_help; eauto).
    
    all: apply/continuity_2d_pt_continuous;
      first [apply Cu' | apply Cv']; auto_continuous_aux.
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
    - move:diff_t. 
      move => [? /(_ r (ball_center _ _))]. auto. 
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
      unfold_alg; rewrite /AbsRing_ball //=.
      move => H.
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

Lemma path_independence_part_4:
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
    apply eq_is_derive; last by [].
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
        rewrite /CauchyIntegral.f /CauchyIntegral.f' /CauchyIntegral.g.
        eapply (is_derive_ext f). {
          move => ?.
          by rewrite -!surjective_pairing.
        }
        rewrite -!surjective_pairing.
        apply nice; lra.
      + simpl; lra.
    - rewrite /CauchyIntegral.f' /CauchyIntegral.g => t' t'bd.
      eapply (continuous_ext f'). {
        move => ?.
        by rewrite -!surjective_pairing.
      }
      apply nice; lra.
    - eapply locally_open; first by apply: open_r.
      + move => *; apply nice; lra.
      + simpl. lra.
  Qed.

  Definition c_circle (r: R) (t:R):C := r * (cos t, sin t).
  Definition c_circle' (r: R) (t:R):C := r* (-sin t, cos t)%R.
  
  Lemma c_circle_deriv: forall r x, is_derive (c_circle r) x ((c_circle' r) x).
  Proof.
    rewrite /c_circle /c_circle'.
    move => r x.
    under ext_is_derive_glo => y.
      set p := _ * _.
      simplify_as_R2 e p.
    over.
    set p := _ * _.
    simplify_as_R2  e p.
    apply (is_derive_pair 
      (f := fun q => r * cos q) 
      (g := fun q => r * sin q)
      (f' := fun q => -r * sin q)
      (g' := fun q => r * cos q)
    )%R; auto_derive_all. 
  Qed.

  Open Scope R.
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
      


  Lemma smooth_circ: forall r t, 
    SmoothPath (fun r t => r * cos t)%R ( fun r t => r * sin t)%R r t.
  Proof.

    Ltac rerwite_under f := 
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
    move => r t; repeat split; [exists pos_half | exists pos_half | .. ]; repeat split.
    - apply differentiable_pt_scal; auto_derive; auto.
    - apply (@differentiable_pt_ext _ (fun p q => (p * (- sin q))));
      [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
      | apply: differentiable_pt_scal; auto_derive; auto
      ].
    - apply (@differentiable_pt_ext _ (fun p q => cos q));
      [ move => *; apply: is_derive_unique; auto_derive; auto; field_simplify; auto
      | idtac
      ].
      eexists; eexists.
      apply/filterdiff_differentiable_pt_lim. 
      apply: (@is_derive_filterdiff (fun p q => cos q)).
      + apply global_local => x. auto_derive; eauto. 
        instantiate (1:= fun _ _ => 0); auto.
      + auto_derive; eauto.
      + apply continuous_const.
    - apply differentiable_pt_scal; auto_derive; auto.
    - apply (@differentiable_pt_ext _ (fun p q => (p * (cos q))));
      [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
      | apply: differentiable_pt_scal; auto_derive; auto
      ].
    - apply (@differentiable_pt_ext _ (fun p q => sin q));
      [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
      | idtac
      ].
      eexists; eexists.
      apply/filterdiff_differentiable_pt_lim. 
      apply: (@is_derive_filterdiff (fun p q => _ q)).
      + apply global_local => x. auto_derive; eauto. 
        instantiate (1:= fun _ _ => 0); auto.
      + auto_derive; eauto.
      + apply continuous_const.
    - 
      
      


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

