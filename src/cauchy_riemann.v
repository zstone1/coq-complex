
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


Require Import domains.

Open Scope program_scope.
Open Scope general_if_scope.
Require Import domains ext_rewrite real_helpers.


Lemma scal_one_r {K:Ring}: forall z: K ,
  scal z one = z.
Proof.
rewrite /scal //=.
apply mult_one_r.
Qed.

Lemma is_filter_lim_locally: forall {T:UniformSpace} (z:T),
  is_filter_lim (locally z) z.
Proof.
  move => T z. rewrite //=.
Qed.
  

Lemma Cmod_Rabs_imaginary: forall (x y:R), 
  Rabs y <= Cmod (x,y).
Proof.
  move => x y.
  apply: transitivity; last by apply sqrt_plus_sqr.
  simpl.
  apply Rmax_r.
Qed.

  
Definition Holo (f g: C -> C) z := 
  is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z (g z).

Definition is_Holo (f: C -> C) z := 
  exists g, Holo f g z.

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

Lemma holo_differentiable_pt_lim_imaginary: forall (f:C -> C) x y g,
  Holo f g (x,y) -> 
  differentiable_pt_lim (fun x y => (f (x,y)).2) x y (g (x,y)).2 (g (x,y)).1 .
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
  Holo f g (x,y) -> 
  differentiable_pt_lim (fun x y => (f (x,y)).1) x y (g (x,y)).1 (-g (x,y))%C.2 .
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
  simpl.
  rewrite -/(is_derive _ _ _).
  rewrite -/(Holo _ (fun z => scal Ci (g z) ) _).
  move /holo_differentiable_pt_lim_imaginary.
  simpl in *.
  set p := (x in differentiable_pt_lim _ _ _ x _).
  simplify_R p.
  set p := (x in differentiable_pt_lim _ _ _ _ x).
  simplify_R p.
  eapply differentiable_pt_lim_ext.
  exists pos_half => u v _ _ . field_simplify_eq; auto.
Qed.


Lemma is_derive_scal_C: forall z k,
  is_derive (K:=C_AbsRing) (fun q => scal k q) z k.
Proof.
  move => z k. 
  rewrite /is_derive.
  under ext_filterdiff_glo => x.
    rewrite /scal //= /mult //= Cmult_comm.
  over.
  apply filterdiff_linear . 
  apply is_linear_scal_l.
Qed.


Ltac copy := 
  let h := fresh in 
  let j := fresh in
   move => h; pose proof h as j; move: h j.

Section Holo.

  Definition CauchyRiemann (udx udy vdx vdy: C -> R) z:=
    udx z = vdy z /\ 
    udy z = (- vdx z)%R
  .

  Theorem CauchyRiemann_Easy: forall u v g1 g2 z,
    Holo (fun p => (u p, v p)) (fun p => (g1 p, g2 p)) z ->
    Derive (fun t => u (t,z.2)) z.1 = Derive (fun t => v (z.1,t)) z.2 /\ 
    Derive (fun t => u (z.1,t)) z.2 = Ropp(Derive (fun t => v (t,z.2)) z.1) /\
    g1 z = Derive (fun t => v (z.1,t)) z.2  /\
    g2 z = Derive (fun t => v (t,z.2)) z.1
    .
  Proof.
    move => u v g1 g2 z.
    rewrite [x in Holo _ _ x]surjective_pairing.
    copy.
    move => /holo_differentiable_pt_lim_imaginary /differentiable_pt_lim_is_derive [+ +]
            /holo_differentiable_pt_lim_real /differentiable_pt_lim_is_derive [+ +].
    do 4 move => /is_derive_unique ->. 
    rewrite -?surjective_pairing; auto.
    
  Qed.

  Lemma Rabs_lt_between_min_max: 
     forall x y z : R, Rmin x y < z < Rmax x y -> Rabs (z - y) < Rabs (x - y).
  Proof.
    move => x y z.
    rewrite /Rmin /Rmax.
    set p := (Rle_dec _ _).
    case: p.
    - move => _ ord.
      rewrite ?Rabs_left; lra.
    - move => _ ord.
      rewrite ?Rabs_right; lra.
  Qed.
  Lemma Rabs_le_between_min_max_2: 
     forall x y z : R, Rmin x y <= z <= Rmax x y -> Rabs (z - x) <= Rabs (y - x).
  Proof.
    move => x y z.
    rewrite Rmin_comm Rmax_comm => *.
    apply (Rabs_le_between_min_max y x z).
    auto.
  Qed.

  Ltac combine_local H := 
  match goal with 
  | J: locally _ _ |- _ => pose proof (filter_and _ _ J H) as H
  end.
  Open Scope R.
  Theorem MVT_along_axis: forall u udx udy z,
    locally z ( fun q =>
      is_derive (fun t => u (t,q.2)) q.1 (udx q)) ->
    locally z ( fun q =>
      is_derive (fun t => u (q.1,t)) q.2 (udy q)) ->
    locally z (fun a => 
      exists c1 c2, 
      Rabs(c1 - z.1) <= Rabs (a.1 - z.1) /\
      Rabs(c2 - z.2) <= Rabs (a.2 - z.2) /\
      (u a - u z = udx (c1,z.2) * (a.1 - z.1) + 
                   udy (a.1,c2) * (a.2 - z.2)))
  .
  Proof.
    move => u udx udy z.
    move => loc.
    move => {loc} /(filter_and _ _ loc) => loc.
     
    case: loc => eps_safe safe.

    eexists ?[del] => a [aballz1 aballz2].

    have H': (?del <= eps_safe) by shelve.
    have H: (ball z eps_safe a) by
      split;
      apply: (Rlt_le_trans _ ?del); auto.
    simpl in *.
    
    (** the key lemma. Hard to factor due to epsilons and deltas.*)
    have axis_mvt: 
      forall (f df :R -> R) bd1 bd2 (extend: R -> C),
      let l0 := Rmin bd1 bd2 in
      let r0 := Rmax bd1 bd2 in
      (forall x, Rabs(x-bd1) <= Rabs(bd2-bd1) -> 
        Rabs ((extend x).1 - z.1) < eps_safe /\
        Rabs ((extend x).2 - z.2) < eps_safe) ->
      (forall x, ball z eps_safe (extend x) -> is_derive f x (df x)) ->
      exists c:R, l0 <= c <= r0 /\ (f bd2 - f bd1 = df(c)*(bd2 - bd1))%R.
    { move {safe} => f df bd1 bd2 extend l0 r0 ext_lem diffin.
      have: (forall x, l0 <= x <= r0 -> is_derive f x (df x)).
      - simpl in *. move => x /Rabs_le_between_min_max_2 bds.
        apply: (diffin x).
        apply ext_lem.
        auto.
      - rewrite /r0 /l0 => diff_all.
        apply: MVT_gen => x bds.
        + apply diff_all.
          lra.
        + rewrite continuity_pt_filterlim -/(continuous _ _).
          apply: ex_derive_continuous.
          exists (df x).
          by apply diff_all.
    }

    have := axis_mvt (fun q => u(q,z.2)) (fun q => udx(q,z.2))
      z.1 a.1 (fun q => (q,z.2)).
    case.
    { move => ? bds.
      case: H => H1 H2 //=.
      split.
      + rewrite -!/(Rminus _ _) in bds H1 H2 *. 
        apply: (Rle_lt_trans _ _ _ bds); auto.
      + set p := (x in Rabs x). simplify_R p.
        rewrite Rabs_R0; apply cond_pos.
    }
    {
        move => x.
        move: (safe ) => /(_ (x,z.2)) //=.
        tauto.
    }
    move => xi_udx [/Rabs_le_between_min_max_2 xi_udx_bds mvt_udx].

    have := axis_mvt (fun q => u(a.1,q)) (fun q => udy(a.1,q))
      z.2 a.2 (fun q => (a.1,q)).
    case. 
    {
        move => ? bds.
        case: H => H1 H2 //=.
        simpl in *; split.
        + rewrite -!/(Rminus _ _) in bds H1 H2 *; auto.
        + set p := (x in Rabs x). simplify_R p.
          apply: (Rle_lt_trans _ _ _ bds); auto.
    }
    {
        move => y yball.
        move: (safe ) => /(_ (a.1,y)) //=.
        case; first by exact yball.
        tauto.
    }
    move => xi_udy [/Rabs_le_between_min_max_2 xi_udy_bds mvt_udy].

    exists xi_udx, xi_udy; repeat split; auto.
     
    `Begin eq (u a - u z). {
    | {( u (a.1, a.2) - u (z.1,z.2) )}  
      rewrite -!surjective_pairing.
    | {( (_ - u(a.1,z.2)) + (u(a.1,z.2) - _ ) )}
      field_simplify_eq.
    | {( _ + udx (_,z.2) * (a.1 - z.1) )}
      rewrite mvt_udx.
    | {( udy (a.1, _) * (a.2 - z.2) + _ )}
      rewrite mvt_udy.
    `Done.
    }
    lra.

    Grab Existential Variables.
    apply eps_safe.
    reflexivity.
  Qed.

  Lemma filter_apply: forall 
    {T: UniformSpace} 
    {F: ((T-> Prop) -> Prop)}
    {FF: Filter F} 
    {P Q : T -> Prop},
    F P -> F (fun x => (P x -> Q x)) -> F Q.
  Proof.
    move => ? F FF P Q FP FPQ. 
    have H := filter_and _ _ FP FPQ. 
    move: H => /(_ FF).
    apply: filter_imp => x.
    tauto.
  Qed.

  Lemma Cmod_Rabs_plus: forall (x y:R), 
    Cmod (x,y) <= Rabs x + Rabs y.
  Proof.
    move => x y.
    elim_norms.
    - rewrite 2!pow2_abs. 
      apply Rplus_le_compat_r.
      rewrite -[x in x <= _]Rplus_0_r.
      apply Rplus_le_compat_l.
      apply Rmult_le_pos; last apply Rabs_pos.
      apply Rmult_le_pos; last apply Rabs_pos.
      lra.
    - nra.
    - apply Rplus_le_le_0_compat; apply Rabs_pos.
  Qed.

  Lemma Cmod_Rabs_real: forall (x y:R), 
    Rabs x <= Cmod (x,y).
  Proof.
    move => x y.
    apply: transitivity; last by apply sqrt_plus_sqr.
    simpl.
    apply Rmax_l.
  Qed.
  
  Definition LocallyPartials (u v udx udy vdx vdy: C -> R)  z := 
    locally z ( fun q =>
      is_derive (fun t => u (t,q.2)) q.1 (udx q)) /\
    locally z ( fun q =>
      is_derive (fun t => u (q.1,t)) q.2 (udy q)) /\
    locally z ( fun q =>
      is_derive (fun t => v (t,q.2)) q.1 (vdx q)) /\
    locally z ( fun q =>
      is_derive (fun t => v (q.1,t)) q.2 (vdy q))
    .

    
  Open Scope C.
  Theorem CauchyRieman_Hard: forall u v udx udy vdx vdy z,
    LocallyPartials u v udx udy vdx vdy z -> 
    udx z = vdy z ->
    (udy z = - vdx z)%R ->
    continuous udx z ->  
    continuous udy z ->  
    continuous vdx z ->  
    continuous vdy z ->  
      Holo (fun q => (u q, v q)) (fun q => (vdy q, vdx q)) z
  .
  Proof.
    move => u v udx udy vdx vdy z CR_diffs cr1 cr2.
    move => /filterlim_locally c_udx.
    move => /filterlim_locally c_udy.
    move => /filterlim_locally c_vdx.
    move => /filterlim_locally c_vdy.
    simpl in *.
    case CR_diffs => d_udx.
    case => d_udy.
    case => d_vdx.
    move => d_vdy.
    rewrite /Holo /is_derive /filterdiff.
    split; first by apply is_linear_scal_l.
    move => + /is_filter_lim_locally_unique <- eps.
    move => _.
    simpl in *.
    rewrite -prod_c_topology_eq.
    apply: (filter_apply (MVT_along_axis d_udx d_udy)).
    apply: (filter_apply (MVT_along_axis d_vdx d_vdy)).
    pose eps4 := pos_div_2 (pos_div_2 eps).
    move => {d_udx d_udy d_vdx d_vdy }.
    move: c_udx => /(_ eps4).
    move: c_udy => /(_ eps4).
    move: c_vdx => /(_ eps4).
    move: c_vdy => /(_ eps4).
    move => cts.
    do 3 move => {cts} /(filter_and _ _ cts) => cts.
    move: cts => [del] .
    copy.
    move => cr_eqs cts.
    
    exists del => a aballz .
    set p := (x in norm (minus x _ ) ).
    simplify_as_R2 e p.
    move => [c1 [c2 [c1_bd [c2_bd -> ]]]].
    move => [c3 [c4 [c3_bd [c4_bd -> ]]]].
  
    Open Scope R.
    rewrite /ball //= /prod_ball //= /ball //= /AbsRing_ball /abs //= 
    /minus //= /opp /plus //= -2!/(Rminus _ _) in aballz.
    case: aballz => dx_del dy_del.
    set p := (x in norm (minus x _ ) ).
    set dx := (a.1 - z.1) in p c1_bd c3_bd dx_del *.
    set dy := (a.2 - z.2) in p c2_bd c4_bd dy_del *.
    set dz := minus a z in p *.
    `Begin eq p. { rewrite /p.
  
    | {( ((udx z*dx + udy z*dy + (udx (c3,z.2) - udx z) *dx + 
           (udy (a.1,c4) - udy z) *dy) ,_)  )} 
      f_equal; field_simplify;
      rewrite {1}Rmult_comm; f_equal;
      rewrite Rmult_comm.
  
    | {( (_, (vdx z*dx + vdy z*dy + (vdx (c1,z.2) - vdx z) *dx + 
           (vdy (a.1,c2) - vdy z) *dy))  )} 
      f_equal; field_simplify; 
      rewrite {1}Rmult_comm; f_equal;
      rewrite Rmult_comm. 
    | {( Cplus (udx z *dx + udy z * dy, vdx z * dx + vdy z * dy) (_,_) )}
      rewrite /Cplus;
      simpl;
      f_equal;
      rewrite 3!Rplus_assoc;
      do 2 apply (Rplus_eq_compat_l).
  
    | {( Cplus (vdy z * dx + (-vdx z * dy), _) (_,_) )}
      rewrite {1}cr1 {1}cr2.
  
    | {( dz * (vdy z , vdx z)%R + (_,_) )%C}
      f_equal; rewrite /dz /dx /dy;
      set p' := LHS;
      simplify_as_R2 e p';
      set p' := RHS;
      simplify_as_R2 e p';
      unfold_alg;
      f_equal;
      field_simplify.
    `Done.
    }
    move => -> {p}.
    unfold_alg.
    rewrite Cplus_comm.
    rewrite Cplus_assoc /dz.
    unfold_alg.
    set p := (-(_) + _)%C.
    simplify_as_R2 e p.
    rewrite Cplus_0_l.
  
    set p := (x in x <= _).
    `Begin Rle p. { rewrite /p.
    | {(  Rabs _ + Rabs _ )}          
      apply Cmod_Rabs_plus.
    | {(  (Rabs _ + Rabs _) + _ )}   
      apply Rplus_le_compat_r;
      apply Rabs_triang.
    | {(  _ + _ + Rabs _ + Rabs _ )}
       rewrite !Rplus_assoc;
       do 2 apply Rplus_le_compat_l;
       apply Rabs_triang.
    | {(  _ * _ dx + _ * _ dy + _ * _ dx + _ * _ dy  )}         
      rewrite !Rabs_mult.
    | {(  _ + _ + _ + _ * Cmod dz   )} 
       apply Rplus_le_compat_l;
       apply Rmult_le_compat_l; first (by apply Rabs_pos);
       apply Cmod_Rabs_imaginary.
    | {(  _ + _ + _ * Cmod dz + _   )} 
       apply Rplus_le_compat_r.
       rewrite !Rplus_assoc.
       do 2 apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; first (by apply Rabs_pos).
       apply Cmod_Rabs_real.
    | {(  _ + _ * Cmod dz + _ + _   )} 
       do 2 apply Rplus_le_compat_r.  
       apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; first (by apply Rabs_pos).
       apply Cmod_Rabs_imaginary.
    | {(   _ * Cmod dz + _ + _ + _  )} 
       do 3 apply Rplus_le_compat_r.  
       apply Rmult_le_compat_l; first (by apply Rabs_pos).
       apply Cmod_Rabs_real.
    | {(   (_ + _ + _ + _)* Cmod dz )} 
      idtac;
      field_simplify;
      rewrite Rmult_comm. 
    `Done.
    }
    move => H.
    apply: (transitivity H).
    apply Rmult_le_compat_r; first by apply Cmod_ge_0.
  
    move: cts; do 3 copy; 
    rewrite /ball //= 
      /AbsRing_ball //= /abs //= /prod_ball
      /ball//= /AbsRing_ball / abs //=.
    unfold_alg.
    move => 
    /(_ (c3,z.2)) cts_udx
    /(_ (a.1,c4)) cts_udy
    /(_ (c1,z.2)) cts_vdx
    /(_ (a.1,c2)) cts_vdy.
    rewrite -!/(Rminus _ _) in cts_udx cts_udy cts_vdx cts_vdy.
    simpl in *.
    rewrite {H}/p {p}.
    set p := (x in x <= _).
    `Begin Rle p. { rewrite /p.
    | {(  _ + _ + _ + eps/2/2   )} 
      apply Rplus_le_compat_l;
      left;
      apply cts_vdy;
      split; [ | apply: (Rle_lt_trans _ _ _ c2_bd)]; auto.
    | {(  _ + _ + eps/2/2 + _   )} 
      apply Rplus_le_compat_r;
      apply Rplus_le_compat_l;
      left;
      apply cts_vdx;
      split; [ apply: (Rle_lt_trans _ _ _ c1_bd); auto | ];
      rewrite Rminus_eq_0 Rabs_R0; apply: cond_pos.
    | {(  _ + eps/2/2 + _ + _   )} 
      do 2 apply Rplus_le_compat_r;
      apply Rplus_le_compat_l.
      left.
      apply cts_udy;
      split; [ apply: dx_del | apply: (Rle_lt_trans _ _ _ c4_bd); auto ].
    | {(  eps/2/2 + _ + _ + _   )} 
      do 3 apply Rplus_le_compat_r.
      left.
      apply cts_udx.
      split; [ apply: (Rle_lt_trans _ _ _ c3_bd); auto | ].
      rewrite Rminus_eq_0 Rabs_R0; apply: cond_pos.
    `Done.
    }
    move => H.
    apply: (transitivity H).
    field_simplify.
    lra.
  Qed.
End Holo.