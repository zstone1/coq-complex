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

Lemma circ_independence : forall (f: C -> C) z (r:posreal) (l r' r'': R),
  CHolo_on (fun z' => l < Cmod (z'-z) < r) f ->
   -r <= l ->
   r' < r'' ->
   l < r' < r ->
   l < r'' < r ->
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f (z + c_circle r' t0) * c_circle' r' t0) 0 (2 * PI) =
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f(z + c_circle r'' t0) * c_circle' r'' t0) 0 (2 * PI).
Proof.
  move => f z r l r' r'' [f' holo] ? ? [? ?] [? ?].
  
  have indep := @path_independence
                (-PI)%R (3*PI) 0 (2*PI)
                (l) r r' r''
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
        set p := _ - _.
        simplify_as_R2 e p.
        rewrite c_circle_norm.
        split.
        - destruct (Rlt_dec l 0).
          + eapply Rlt_le_trans. 
            apply r1.
            apply Rabs_pos.
          + rewrite Rabs_right; lra.
        - destruct (Rlt_dec r0 0).
          + rewrite Rabs_left; lra.
          + rewrite Rabs_pos_eq; lra.
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
  rewrite -(@circ_independence f z r (-r) 0 r').
  3-6: lra.
  2: { 
    move: holo => [f' h].
    exists f' => z0 [? ?].
    apply h.
    unfold_alg.
  }
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
  contour_derive: forall t, l_end <= t <= r_end -> is_derive gamma t (gamma' t);
  cts_derive: forall t, l_end <= t <= r_end -> continuous gamma' t;
}.
Open Scope C. 
Definition is_CInt (g: Contour) (f: C -> C) (z:C) :=
  is_RInt (fun t => f (gamma g t) * (gamma' g t)) (l_end g) (r_end g) z.
Definition ex_CInt (g: Contour) (f: C -> C) :=
  exists z, is_CInt g f z. 
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
Obligation 3.
Proof.
rewrite /c_circle'.
auto_continuous_aux; simpl; apply: ex_derive_continuous;
auto_derive; auto.
Qed.

Lemma circ_independence_C : forall (f: C -> C) z (r' r'' :posreal) l r,
  CHolo_on (fun z' => l < Cmod (z'-z) < r) f ->
   0 <= l -> 
   l < r' < r ->
   l < r'' < r ->
  CInt (g:= circC z r') f = 
  CInt (g:= circC z r'') f.
Proof.
  move => f z r' r''.
  wlog: r' r'' / r' < r''. {
    move => H.
    destruct (Rtotal_order r' r'');[ | destruct H0].
    - apply: H; auto.
    - move => *. rewrite /CInt //= H0 //=.
    - move => *; symmetry; apply: H; eauto.
  }
  move => ? l r holo r'bd r''bd.
  rewrite /CInt.
  apply: (@circ_independence _ _ (mkposreal r _) l); eauto.
  - have?:= cond_pos r'; lra.
  - move => ?; simpl. lra.
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

Definition cts_on_contour (f: C -> C) g := 
  forall t, l_end g <= t <= r_end g -> continuous f (gamma g t).

Lemma ex_CInt_RInt: forall f g, 
  ex_RInt (fun t => f (gamma g t) * (gamma' g t)) (l_end g) (r_end g) <-> 
  ex_CInt g f.
Proof.
  move => f g; split;
  move => [l H]; exists l; apply H.
Qed.

Lemma cts_CInt: forall (f: C -> C) g, 
  cts_on_contour f g -> ex_CInt g f.
Proof.
  move => f g cts.
  rewrite -ex_CInt_RInt -ex_RInt_prod.
  apply: ex_RInt_continuous => t tbd.
  rewrite Rmin_left in tbd.
  rewrite Rmax_right in tbd.
  2-3: left; apply endpoint_interval.
  change_topology.
  apply: continuous_mult; first apply continuous_comp.
  - eapply filterlim_filter_le_2.
    2: apply ex_derive_continuous; eexists; eapply (contour_derive tbd)  .
    move => P. auto.
  - move: cts => /(_ t tbd) => H.
    eapply filterlim_filter_le_2.
    2: apply H.
    move => P. 
    rewrite prod_c_topology_eq //=.
  - eapply filterlim_filter_le_2.
    2: apply (cts_derive); auto.
    move => *; rewrite prod_c_topology_eq //=.
Qed.
       

  
Lemma Rlt_0_neq_0: forall a,
  0 < a -> a <> 0.
Proof.
  move => *; lra.
Qed.
Open Scope R.
Lemma continuous_Cinv: forall (z:C), 
  z <> 0 -> continuous (Cdiv 1) z.
Proof.
  move => z z_neq_0.
  have ?: (z.1 * z.1 + z.2 * z.2 <> 0). {
    contradict z_neq_0.
    field_simplify.
    rewrite [LHS]surjective_pairing.
    f_equal; nra.
  }

  apply: continuous_pair; simpl;
  rewrite/continuous; 
  rewrite [x in _ _ (_ x) _]surjective_pairing;
  set p := (x in _ x _ _);
  pose h := fun a b => p (a,b);
  rewrite -(@continuity_2d_pt_filterlim h);
  rewrite /h /p;
  eapply continuity_2d_pt_ext. 
  1,3: move => x y;
      rewrite ?Rmult_0_l ?Rminus_0_l ?Rmult_1_l 
              ?Rmult_1_r ?Rminus_0_r ?Rplus_0_r //=.
  1: apply: continuity_2d_pt_mult; first by 
      apply continuity_2d_pt_id1.
  2: apply: continuity_2d_pt_mult; first by 
      apply: continuity_2d_pt_opp;
      apply continuity_2d_pt_id2.
  all:
    apply: continuity_2d_pt_inv; last (by auto);
    apply continuity_2d_pt_plus;
    apply continuity_2d_pt_mult;
    (try apply: continuity_2d_pt_id2);
    apply: continuity_2d_pt_id1.
Qed.
    

      
  
Open Scope C.

Lemma div_z_continuous_contour: forall a r , 
  cts_on_contour (fun q : C => 1 / (q - a)) (circC a r).
Proof.
  move => a r.
  move => t tbd; simpl in *.
  have ?:= cond_pos r.
  apply continuous_comp; first repeat auto_continuous_aux.
  apply: continuous_Cinv.
  set p := (x in x <> _).
  simplify_as_R2 e p.
  rewrite Cmod_gt_0 c_circle_norm Rabs_pos_eq; nra.
Qed.

Lemma cts_on_contour_mult: forall f g gam, 
  cts_on_contour f gam ->
  cts_on_contour g gam -> 
  cts_on_contour (fun z => f z * g z) gam.
Proof.
  move => f g gam ctsf ctsg t tbd.
  change_topology.
  apply: continuous_mult; change_topology.
  - apply: ctsf; auto.
  - apply: ctsg; auto.
Qed.


Open Scope R.
Lemma holo_inv : forall (z: C), 
  (z <> 0)%C -> (Holo (fun q => 1/q) (fun q => -1/(q * q)) z)%C.
Proof.
  move => z neq_0.
  have zb : 0 < Rmax (Rabs z.1) (Rabs z.2). {
    destruct z; simpl.
    destruct (Req_dec 0 r);
    destruct (Req_dec 0 r0).
    - contradict neq_0; subst; auto.
    - subst. rewrite Rmax_right.
      + apply Rabs_pos_lt; auto. 
      + rewrite Rabs_R0; apply Rabs_pos.
    - subst. rewrite Rmax_left.
      + apply Rabs_pos_lt; auto. 
      + rewrite Rabs_R0; apply Rabs_pos.
    - apply (@Rmax_case (Rabs r) (Rabs r0) (fun q => 0 < q));
        apply Rabs_pos_lt; auto.
  }
  pose del := (mkposreal _ zb).
  have ball_neq_0: forall y, ball z del y -> y.1 * y.1 + y.2 * y.2 <> 0. {
    move => y ybd H.
    move: H.
    copy => /Rplus_sqr_eq_0_l y1. 
    rewrite Rplus_comm.
    move => /Rplus_sqr_eq_0_l y2.
    have: y = (0,0); first by rewrite [LHS]surjective_pairing y1 y2.
    move => ?; subst.
    move: ybd.
    unfold_alg.
    SearchAbout Rmax.
    destruct (Rlt_dec (Rabs z.1) (Rabs z.2)).
    - rewrite ?Rmax_right; last by left; auto.
      rewrite ?Rplus_0_l ?Rabs_Ropp; lra.
    - rewrite ?Rmax_left; last by lra .
      rewrite ?Rplus_0_l ?Rabs_Ropp; lra.
  }
  have ball_pows_0: forall y, ball z del y -> 
       ( 0 < y.1 ^ 4 + 2 * y.1 ^ 2 * y.2 ^ 2 + y.2 ^ 4)%R . {
    move => y zbd.
    set p := (x in _ < x).
    replace p with ((y.1 * y.1 + y.2 * y.2)^2); last by
      rewrite /p; lra. 
    apply pow2_gt_0.
    apply ball_neq_0.
    auto.
  }
  apply: CauchyRieman_Hard; simpl. 
  1:{ rewrite /LocallyPartials. repeat split;
    ( exists del => y yb;
      simpl in *;
      auto_derive; 
      rewrite ?Rmult_0_l ?Rminus_0_l ?Rmult_1_l 
              ?Rmult_1_r ?Rminus_0_r ?Rplus_0_r //=;
      repeat split; try by apply: ball_neq_0);
      field_simplify_eq; auto; repeat split;
      try by apply: ball_neq_0.
    + apply: Rlt_0_neq_0. field_simplify. apply ball_pows_0; auto.
    + apply: Rlt_0_neq_0. field_simplify. apply ball_pows_0; auto.
  }
  1,2: simpl; field_simplify_eq; auto;
    split;
    [ (apply: Rlt_0_neq_0; field_simplify);
      apply ball_pows_0; apply ball_center
    |  apply: ball_neq_0; apply ball_center
    ].
  all: repeat auto_continuous_aux;
    apply continuous_comp; repeat auto_continuous_aux;
    apply: ex_derive_continuous; auto_derive;
    try (now apply ball_neq_0; apply ball_center);
    try (now apply: Rlt_0_neq_0; field_simplify; apply ball_pows_0;
             apply ball_center).
Qed.

Open Scope C.

Lemma integral_div_z: forall a r, 
  CInt (g:= circC a r) (fun z => 1/(z-a)) = 2 * PI * Ci.
Proof.
  move => a r.
  have? := cond_pos r. 
  rewrite /CInt split_cint.
  2: shelve.
  simpl.
  set p := RHS.
  simplify_as_R2 e p.
  rewrite /c_circle /c_circle' //=.
  f_equal.
  - rewrite /compose //=.
    under RInt_ext => t _.
      field_simplify.
    over.
    apply Rlt_0_neq_0.
    field_simplify.
    rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2 /Rsqr.
    field_simplify.
    nra.

    under RInt_ext => t _.
      rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2.
      set p := (0 / _)%R.
      replace p with (0)%R;
      rewrite {}/p.
    over.
    lra.
    rewrite RInt_const /scal //= /mult //=. lra.
  - rewrite /compose //=.
    under RInt_ext => t _.
      field_simplify.
    over.
    apply Rlt_0_neq_0.
    field_simplify.
    rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2 /Rsqr.
    field_simplify.
    nra.
    under RInt_ext => t _.
      set p := (_ / _)%R.
      replace p with (1)%R;
      rewrite {}/p.
    over.
    field_simplify_eq; auto.

    apply Rlt_0_neq_0.
    field_simplify.
    rewrite -Rmult_plus_distr_l -?Rsqr_pow2 Rplus_comm sin2_cos2 /Rsqr.
    field_simplify.
    nra.

    rewrite RInt_const /scal //= /mult //=. lra.
  Unshelve.
  apply/(@ex_CInt_RInt (fun q =>1/ (q - a)) _).
  apply cts_CInt.
  apply: div_z_continuous_contour.
Qed.

Lemma squeeze: forall {K: AbsRing} {T: NormedModule K} (x:T),
   (forall (eps: posreal), norm x < eps) -> x = zero.
Proof.
  move => ? ? x sqz.
  destruct (Rle_dec 0 (norm x)).
  destruct r. 
  - move: sqz => /(_ (mkposreal _ H)) Q.
    simpl in *.
    lra.
  - apply norm_eq_zero; auto.
  - contradict n. 
    apply norm_ge_0.
Qed.

Lemma CInt_abs_bound: forall f g M, 
  cts_on_contour f g -> 
  (forall t, l_end g <= t <= r_end g -> abs (f (gamma g t)) <= M) ->
  norm (CInt (g:=g) f) <= scal M (RInt (fun t => norm (gamma' g t)) (l_end g) (r_end g)).
Proof.
  move => f g M cts fbd.
  rewrite /CInt.
  apply: norm_RInt_le.
  3: apply: RInt_correct; apply/ ex_CInt_RInt; apply/ cts_CInt; auto.
  1: left; apply: endpoint_interval.
  2: { 
     rewrite -RInt_scal.
     instantiate(1:= fun x => scal M (norm (gamma' g x))).
     apply: RInt_correct. 
     all: apply ex_RInt_continuous => t tbd.
     rewrite Rmin_left in tbd.
     rewrite Rmax_right in tbd.
     2,3: left; by apply endpoint_interval.
     1: apply: continuous_scal; first by auto_continuous_aux.
     all: apply continuous_comp.
     1,3: apply cts_derive; auto.
     rewrite Rmin_left in tbd.
     rewrite Rmax_right in tbd.
     2,3: left; by apply endpoint_interval.
     by auto.
     all: apply filterlim_norm.
  }
  move => t tbd.
  simpl.
  set p := norm _.
  `Begin Rle p. { rewrite /p.

  | {( norm( scal (f (gamma g t)) (gamma' g t)) )}   unfold_alg.

  | {( (abs (f (gamma g t)) * norm _) )%R}  apply: norm_scal.

  | {( (M * norm _) )%R}  idtac.
    apply: Rmult_le_compat_r; first (by apply: norm_ge_0).
    by apply: fbd.
  `Done.
  }
  unfold_alg.
Qed.

Program Definition pos_div_2PI (r: posreal): posreal := 
  mkposreal (r / (2 * PI))%R _.
Obligation 1.
Proof.
  apply: RIneq.Rdiv_lt_0_compat.
  - apply: cond_pos.
  - have ?:= PI_RGT_0; lra.
Qed.

Lemma cauchy_integral_aux: forall f (r r': posreal) a, 
  r' < r ->
  CHolo_on (ball a r) f ->
  CInt (g:=circC a r') (fun z => (f(z) - f(a))/ (z-a))
  = zero.
Proof.
  move => f r r' a rbd holo.
  apply: squeeze => eps.
  have: continuous f a. {
    eapply filterlim_filter_le_1.
    2: apply: ex_derive_continuous. 
    1: move => P. apply prod_c_topology_eq.
    case: holo => f' /(_ a (ball_center _ _)) H.
    exists (f' a).
    apply H.
  }
  move => /filterlim_locally /(_ (pos_div_2PI eps)) [del h].
  set p := norm _.

  `Begin Rle p. {rewrite /p.
  
  | {( norm (CInt (g:= circC a (pos_div_2 del)) _ ))} apply_.
    {(  scal (eps/(r' * 2*PI)) _ )%R} apply: CInt_abs_bound .
  
  }
