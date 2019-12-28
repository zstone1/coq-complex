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


Lemma is_derive_continuous: forall 
  {K: AbsRing} {V : NormedModule K} f f' x,
  is_derive (K:=K) (V:=V) f x f' -> continuous f x.
Proof.
 move => *.
 apply ex_derive_continuous; eexists;  eauto.
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

Lemma ReImSplit : forall z, 
  (Re z, Im z) = z.
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
      
Lemma is_derive_pair' {K : AbsRing} {M : NormedModule K} :
  forall (f g: K -> M) (x: K) f' g', 
  is_derive f x (f') ->
  is_derive g x (g') ->
  is_derive (fun q => (f q, g q)) x (f', g').
Proof.
  pose h (p q:M) := (p,q).
  move => *.
  apply: (filterdiff_comp_2 _ _ h).
  - auto_derive_all. 
  - auto_derive_all. 
  - under (ext_filterdiff_d) => x.
      have e: ((x.1, x.2)=x); first by case: x. 
      rewrite e.
    over.
    rewrite /h //=.
    under ext_filterdiff_loc.
      { apply global_local; 
        instantiate (1:= id); 
        auto.
      }
      move => x _. 
      have ->: ((x.1, x.2)=x); first by case: x.
    over.
    auto_derive_all.
Qed.
(* I suspect that the proposition I'm working with 
are actually decidable anyway, so this is probably overkill*)
Axiom excluded_middle: forall P:Prop, P \/ ~P.

Ltac expand_nice := 
  let holo := fresh in 
    move => [holo [
       [?[?[?[??]]]] [
       [?[?[?[??]]]] +]]];
    copy => /(continuous_comp _ fst) /= Cu';
    move => /(continuous_comp _ snd) /= Cv';
    move: holo;
    copy => /holo_differentiable_pt_lim_imaginary ?
            /holo_differentiable_pt_lim_real ?.
Lemma not_not_impl: forall (P:Prop), ~ ~ P <-> P.
Proof.
  move => P. tauto.
Qed.

Section PathIndependence .
  Variables (a b c d:R).
  Variables (g1 g2 : R -> R -> R ).

  Hypothesis cled: c < d.

  Local Definition g:= fun p q => (g1 p q, g2 p q).
  Local Definition g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q).
  Local Definition g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p).

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
    clear l.
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
  Local Definition f:= fun z => (u z.1 z.2, v z.1 z.2).
  Local Definition f':= fun z => (u' z.1 z.2, v' z.1 z.2).

  Hypothesis holo_loc: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  Holo f f' (g r0 t0)) r t.

  Hypothesis cts_derive: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  continuous f' (g r0 t0)) r t.


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

  Lemma diff_integrand_t: forall r t,
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

  Lemma diff_integrand_r: forall r t,
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
    locally_2d (
        differentiable_pt (fun r0 t0 => Re(f (g r0 t0) * g_r r0 t0))) r t.
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
      apply: locally_2d_impl (diff_integrand_t r'bd t'bd).
      apply: locally_2d_forall.
      move => r0 t0 /differentiable_pt_ex_derive [_ H].
      tauto.
    - move => t tbd.
      move: locally_nice => /(_ _ _ rbd tbd) nice.
      eapply continuity_2d_pt_ext_loc. {
        apply: locally_2d_impl nice.
        apply: locally_2d_forall => r0 t0. 
        copy.
        expand_nice.
        
        move => [+ _].
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
      move: nice => /locally_2d_singleton.
      expand_nice.
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

        move => [+ _].
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
        all: repeat diff_help; auto.
      }
      move: (locally_nice rbd tbd) => /locally_2d_singleton.
      expand_nice.
      simpl in *.
      repeat auto_continuous_aux.
      1,3,8,10: apply continuous_comp_2.
      all: try now (apply: ex_derive_continuous; repeat diff_help; auto).
      all: try now (first [apply Cu' | apply Cv']; auto_continuous_aux).
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
      locally_2d ( fun r0 t0 =>  Holo f f' (g r0 t0)) r t.

  Hypothesis cts_derive: forall r t, 
    c <= r <= d ->
    Rmin a b <= t <= Rmax a b ->
      locally_2d ( fun r0 t0 =>  continuous f' (g r0 t0)) r t.

  Definition nice' r0 t0 :=
    Holo f f' (g r0 t0) /\
    SmoothFun g1 r0 t0 /\
    SmoothFun g2 r0 t0 /\
    continuous f' (g r0 t0).

  Lemma locally_nice': forall r t, 
    c <= r <= d -> 
    Rmin a b <= t <= Rmax a b ->locally_2d nice' r t.
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
    rewrite /nice'.
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
    move => [+ _]=> /is_derive_continuous ?.
    expand_nice.
      apply/continous_C_AbsRing.
      apply: continuous_mult.
      + apply continuous_comp.
        * rewrite /g. auto_continuous_aux; apply: ex_derive_continuous; diff_help.
        * apply/continous_C_NormedModule. 
          apply: filterlim_filter_le_1; last auto.
          move => P; apply prod_c_topology_eq.
          auto.
      + rewrite /g_t.
        change_topology.
        apply: continuous_pair.
        apply: (@continuity_2d_pt_continuous_right 
          (fun r' t' => (Derive (g1 r') t'))).
        apply: differentiable_continuity_pt.
        auto.
        apply: (@continuity_2d_pt_continuous_right 
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
    apply: is_derive_pair'.
    - pose u := fun p q => (f (p,q)).1.
      pose v := fun p q => (f (p,q)).2.
      pose u' := fun p q => (f' (p,q)).1.
      pose v' := fun p q => (f' (p,q)).2.
      apply (@path_independence_part_3_real u v u' v' ); auto.
      + move => r' t' r'bd t'bd.
        apply: locally_2d_impl (holo_loc  r'bd t'bd).
        apply locally_2d_forall.
        move => r0 t0 H.
        eapply is_derive_ext with (f0:=f).
          move => t.
          rewrite /PathIndependence.f /u /v -?surjective_pairing //=.
        rewrite /PathIndependence.f' /u' /v' -?surjective_pairing //=.
      + move => r' t' r'bd t'bd.
        apply: locally_2d_impl (cts_derive  r'bd t'bd).
        apply locally_2d_forall.
        move => r0 t0 H.
        eapply continuous_ext with (f0:=f').
          move => t.
          rewrite /PathIndependence.f' /u' /v' -?surjective_pairing //=.
        auto.
    - pose u := fun p q => Ropp (f (p,q)).2.
      pose v := fun p q => (f (p,q)).1.
      pose u' := fun p q => Ropp (f' (p,q)).2.
      pose v' := fun p q => (f' (p,q)).1.
      pose h := fun z => (u z.1 z.2, v z.1 z.2).
      pose h' := fun z => (u' z.1 z.2, v' z.1 z.2).
      have hf : forall z, h z = Ci * f z by 
        move => z; rewrite /h/u/v //=/Cmult;
        set l := LHS;
        simplify_as_R2 e l;
        set p := RHS;
        simplify_as_R2 e p;
        rewrite -?surjective_pairing.
      have hf' : forall z, h' z = Ci * f' z by 
        move => z; rewrite /h'/u'/v' //=/Cmult;
        set l := LHS;
        simplify_as_R2 e l;
        set p := RHS;
        simplify_as_R2 e p;
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
        copy.
        move => [/is_derive_continuous holo _].
        expand_nice.
        repeat auto_continuous_aux.
        1,3: apply continuous_comp.
        2,4: auto_continuous_aux.
        1,2: apply continuous_comp.
        5,6: apply: ex_derive_continuous; try diff_help. 
        2,4: apply/ continous_C_NormedModule. 
        Set Printing Implicit.
        2,3: apply/ continous_C_NormedModule; apply: filterlim_filter_le_1; last 
               apply holo.
        2,3: move => *; apply prod_c_topology_eq; auto.
        all: rewrite /g;  apply continuous_comp_2.
        all: try now (apply: ex_derive_continuous; repeat diff_help; auto).
        all: repeat auto_continuous_aux.
      }
      have ->: (Im (f (g r b) * g_r r b - f (g r a) * g_r r a)) =
                 (opp (Re(h (g r b) * g_r r b - h (g r a) * g_r r a))) by
        rewrite /opp /=/g/h/u/v; field_simplify_eq. 
      apply: is_derive_opp.
      
      apply: (@path_independence_part_3_real u v u' v' ); auto.
      + move => r0 t0 r0bd t0bd.
        apply: locally_2d_impl (holo_loc r0bd t0bd).
        apply locally_2d_forall.
        move => r' t' H.
        rewrite /PathIndependence.f /PathIndependence.f'.
        eapply is_derive_ext. 
          move => t.
          rewrite -/(h t) hf.
        reflexivity.
        rewrite -/(h' (g r' t')) hf'.
        apply: Holo_mult.
        auto.
      + move => r0 t0 r0bd t0bd.
        apply: locally_2d_impl (cts_derive r0bd t0bd).
        apply locally_2d_forall.
        move => r' t' H.
        rewrite /PathIndependence.f' -/h'.
        eapply continuous_ext. 
          move => x. 
          rewrite hf'. 
         reflexivity. 
        simpl.
        apply: continuous_comp_2; auto.
        auto_continuous_aux.
        apply/continous_C_AbsRing.
        apply: continuous_mult;
        apply/continous_C_AbsRing; auto_continuous_aux.
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