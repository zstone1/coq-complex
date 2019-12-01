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

Ltac nrapp := 
  match goal with 
  | |- context [Rabs ?y] => pose proof (Rabs_pos y)
  end.
Open Scope C.

Lemma Cmod_prod_norm: forall x1 x2,
  Cmod (x1,x2) = prod_norm (K:= R_AbsRing) (x1,x2).
Proof.
  move => x y.
  rewrite /Cmod //= /prod_norm //= /norm //= /abs //=.
  f_equal.
  field_simplify.
  rewrite ? pow2_abs.
  auto.
Qed.

Ltac unfold_alg := do ! rewrite 
  ? /norm //= -?Cmod_prod_norm //= 
  ? /minus //= ? /plus //= ? /opp //= ? /scal //=
  ? /mult //= ? /abs //= ?/prod_ball //= ? /ball //= 
  ? /prod_plus //= /prod_opp //=
.

Ltac elim_norms := do !
  match goal with 
  | |- context[Cmod] => rewrite !/Cmod
  | |- sqrt _ = sqrt _ => f_equal
  | |- (?x * _ = ?x * _)%R => f_equal
  | |- (?x + _ = ?x + _)%R => f_equal
  | |- (?x * _ = ?x * _)%C => f_equal
  | |- (?x + _ = ?x + _)%C => f_equal
  | |- sqrt _ = _ => apply sqrt_lem_1
  | |- sqrt _ < sqrt _ => apply sqrt_lt_1
  | |- Rabs _ <= Rabs _ => apply Rsqr_eq_abs_0
  | |- 0 <= Rabs _ => by apply Rabs_pos
  | |- 0 <= ?x^2 - 2 * ?x * ?y + ?y ^2 => apply diff_sqr
  | _ => rewrite ? (sqrt_le_left, abs_sqr, sqrt_Rsqr, sqrt_square, sqrt_pow2, Rsqr_abs);
         (simpl; field_simplify)
end.

Lemma is_filter_lim_locally: forall {T:UniformSpace} (z:T),
  is_filter_lim (locally z) z.
Proof.
  move => T z. rewrite //=.
Qed.
  


  Lemma diff_topology_equiv: forall f z v,
    is_derive (K:=C_AbsRing) (V:= AbsRing_NormedModule C_AbsRing) f z v <->
    is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z v.
  Proof.
    move => f z v.
    rewrite /is_derive /filterdiff //= /Equiv.is_domin.
    do 2 split.
    1,3: apply is_linear_scal_l.
    all: destruct H; auto.
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

  Lemma R_opp_1: forall x, (-(1) * x) = -x.
  Proof. move => x. field_simplify_eq. auto. Qed.

  Ltac simplify_R e p := 
    let H := fresh in 
    (have H: (p=p) by auto);
    rewrite {1}/p in H;
    field_simplify in H;
    rewrite -{}H {p}
  .
  Ltac split_as_R2 e p := 
    let H := fresh in 
    let H' := fresh in 
    case e: p;
    rewrite /p /Cmult /Copp /Cplus //= in e;
    case: e => H H';
    rewrite -{}H -{}H' {p}
  .
  Ltac simplify_as_R2 e p := 
    let H := fresh in 
    let H' := fresh in 
    case e: p;
    rewrite /p /Cmult /Copp /Cplus //= in e;
    case: e => H H';
    field_simplify in H;
    field_simplify in H';
    rewrite -{}H -{}H' {p}
  .

Ltac copy := 
  let h := fresh in 
  let j := fresh in
   move => h; pose proof h as j; move: h j.
Section Holo.
  Definition CR_eqs (u v udx udy vdx vdy: C -> R)  z := 
    locally z ( fun q =>
      is_derive (fun t => u (t,q.2)) q.1 (udx q)) /\
    locally z ( fun q =>
      is_derive (fun t => u (q.1,t)) q.2 (udy q)) /\
    locally z ( fun q =>
      is_derive (fun t => v (t,q.2)) q.1 (vdx q)) /\
    locally z ( fun q =>
      is_derive (fun t => v (q.1,t)) q.2 (vdy q))
    .

  Definition CauchyRieman (u v udx udy vdx vdy: C -> R) z:=
    udx z = vdy z /\ 
    udy z = (- vdx z)%R
    .
  
  Definition Holo (f g: C -> C) z := 
    is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z (g z).

  Definition is_Holo (f: C -> C) z := 
    exists g, Holo f g z.


  Lemma local_c_reals:
    forall (z:C) P,
      (within (fun q => q.2 = z.2) (locally (T:=C_UniformSpace) z)) P ->
      (locally (T:= R_UniformSpace) z.1 (fun q => (P (q,z.2)))).
  Proof.
    move => z P lz //=.
    case lz => eps clim.
    exists eps => y byz.
    apply clim; last by simpl; auto.
    unfold_alg.
    auto using AbsRing_ball_center.
  Qed.

  Lemma local_c_imags:
    forall (z:C) P,
        (within (fun q => q.1 = z.1) (locally (T:=C_UniformSpace) z)) P ->
        (locally (T:= R_UniformSpace) z.2 (fun q => (P (z.1,q)))).
  Proof.
    move => z P.
    pose h (z:C) := (z.2,z.1) .
    auto_continuous h (z.2, z.1) => H {} /H ?.
    apply (local_c_reals (z:=(z.2, _)) (P:= fun q => _ (q.2, q.1))).
    auto.
  Qed.

  Hint View for move /is_filter_lim_locally_unique.

  Hint Rewrite prod_c_topology_eq.
  Lemma c_diff_imaginary_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (z.1, q)) z.2 ((-v.2,v.1)%R).
  Proof.
    rewrite /is_derive /filterdiff => f z v.
    case => _ //= /(_ z) b. split;
    first by apply (is_linear_scal_l (K:=R_AbsRing) ((-v.2,v.1)%R)).
    move => o /is_filter_lim_locally_unique <-.
    rewrite /Equiv.is_domin //=  in b * => eps.
    pose r_normeq := 
      fun z' => norm (K:=R_AbsRing)
          (minus (minus (f (z'.1, z'.2)) (f (z.1, z.2))) 
                 (scal (minus z'.2 z.2) ((-v.2,v.1)%R))) <=
        eps * norm (minus z'.2 z.2) .
    under ext_filter => p do rewrite -/(r_normeq (z.1, p)).
    apply local_c_imags.
    set c_normeq := fun x: C =>
      norm  (minus (minus (f x) (f z)) (scal (minus x z) v)) <=
       eps * norm (minus x z) in b.

    pose h := fun q:C => (z.1,q.2).
    auto_continuous h z => hcts.
    rewrite /within; 
    apply: (filter_imp (fun q => c_normeq (h q))).
    - case => q1 q2; simpl => + ->.
      rewrite /c_normeq /r_normeq /h //=.
      case eq: z.
      (have H : 
        (forall a b c d, a = b -> c = d -> a <= c -> b <= d) 
        by congruence).
      apply H;
      (unfold_alg;
      by elim_norms).
    - auto_continuous h z.
      apply. 
      rewrite -surjective_pairing prod_c_topology_eq.
      apply b.
      rewrite //=.
  Qed.

  Lemma c_diff_real_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (q,z.2)) z.1 (v.1,v.2).
  Proof.
    move => f z v.
    pose h := fun z => scal Ci z.
    have {1}->: (z = -Ci * (Ci * z) ) by
      set p := (X in _ = X);
      simplify_as_R2 e p;
      rewrite -surjective_pairing.
    move /(is_derive_comp _ _) 
         /(_ (is_derive_scal_C _ _))
         /c_diff_imaginary_axis.
    rewrite //=. 
    under ext_is_derive_glo => x.
      set p := (X in f X).
      simplify_as_R2 e p.
    over.
    set p := (X in is_derive _ _ X).
    simplify_as_R2 e p.
    set p := (X in is_derive _ X).
    simplify_R e p.
    auto.
  Qed.

  Lemma diff_split_coords: forall 
    {K: AbsRing}
    {V1 V2: NormedModule K} 
    (u: K -> V1)
    (v: K -> V2) x u' v', 
    is_derive (K:= K) (fun t => (u t, v t)) x (u', v') -> 
    is_derive (K:= K) u x u' /\
    is_derive (K:= K) v x v'
    .
  Proof.
    move => K V1 V2 u v x u' v' diff; split;
    [ apply (filterdiff_comp _ fst _ fst) in diff; simpl in *
    | apply (filterdiff_comp _ snd _ snd) in diff; simpl in *
    ];
    [auto | apply filterdiff_fst | auto | apply filterdiff_snd].
  Qed.

  Lemma holo_partials: forall u v g z, 
    locally z (Holo (fun q => (u q, v q)) g) -> exists udx udy vdx vdy,
      CR_eqs u v udx udy vdx vdy z . 
  Proof.
    move => u v g z [eps H].
    eexists ?[udx].
    eexists ?[udy].
    eexists ?[vdx].
    eexists ?[vdy].
    rewrite /CR_eqs.
    rewrite 4!prod_c_topology_eq.
    repeat split.
    - 
    
    
    exists eps => y byz.
    - apply c_diff_real_axis.
    

    rewrite -is_derive_pair_iff.

  Theorem CauchyRieman_Easy: forall u v udx udy vdx vdy g z,
    CR_eqs u v udx udy vdx vdy z -> 
    Holo (fun p => (u p, v p)) g z ->
    (CauchyRieman u v udx udy vdx vdy z /\ (g z).1 = (vdy z) /\ (g z).2 = vdx z)
    .
  Proof.
    move => u v udx udy vdx vdy g z .
    rewrite /Holo /CauchyRieman => cr_eqs .
    copy.
    case /c_diff_imaginary_axis /diff_split_coords .
    move /is_derive_unique => + /is_derive_unique => h1 h2.
    
    case /c_diff_real_axis /diff_split_coords .
    move /is_derive_unique => + /is_derive_unique => h3 h4.
    move: h1 h2 h3 h4.
    
    move: cr_eqs; rewrite /CR_eqs.
    do 3 (case; move /locally_singleton/is_derive_unique ->) .
    move /locally_singleton /is_derive_unique ->.
    move => *.
    repeat split; congruence.
  Qed.
  Notation "[| x |]" := (norm x) (at level 100).
  Infix "[+]" := plus (at level 199).
  Infix "[-]" := minus (at level 199).
  Infix "[.]" := scal (at level 10).

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
  Ltac ssrautoprop := try tauto; trivial.
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
      + set p := (x in Rabs x). simplify_R e p.
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
        + set p := (x in Rabs x). simplify_R e p.
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

  Lemma Cmod_Rabs_imaginary: forall (x y:R), 
    Rabs y <= Cmod (x,y).
  Proof.
    move => x y.
    apply: transitivity; last by apply sqrt_plus_sqr.
    simpl.
    apply Rmax_r.
  Qed.
  
    
  Open Scope C.
  Theorem CauchyRieman_Hard: forall u v udx udy vdx vdy z,
    CR_eqs u v udx udy vdx vdy z -> 
    (CauchyRieman u v udx udy vdx vdy z) -> 
    continuous udx z ->  
    continuous udy z ->  
    continuous vdx z ->  
    continuous vdy z ->  
      Holo (fun q => (u q, v q)) (fun q => (vdy q, vdx q)) z
  .
  Proof.
    move => u v udx udy vdx vdy z CR_diffs CR_eqs.
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
    move: cts => [del] cts.
    
    exists del => a aballz .
    set p := (x in norm (x [-] _ ) ).
    simplify_as_R2 e p.
    move => [c1 [c2 [c1_bd [c2_bd -> ]]]].
    move => [c3 [c4 [c3_bd [c4_bd -> ]]]].
  
    Open Scope R.
    rewrite /ball //= /prod_ball //= /ball //= /AbsRing_ball /abs //= 
    /minus //= /opp /plus //= -2!/(Rminus _ _) in aballz.
    case: aballz => dx_del dy_del.
    set p := (x in norm (x [-] _ ) ).
    set dx := (a.1 - z.1) in p c1_bd c3_bd dx_del *.
    set dy := (a.2 - z.2) in p c2_bd c4_bd dy_del *.
    set dz := a [-] z in p *.
    rewrite /CauchyRieman in CR_eqs.
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
      move: CR_eqs => [cr_eq1 cr_eq2];
      rewrite {1}cr_eq1 {1}cr_eq2.
  
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
  Print Complex.
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

Lemma path_independence_part_2:
  forall (u v: R -> R -> R) r t g1 g2, 
  let g:= fun p q => (g1 p q, g2 p q) in
  let f:= fun z => (u z.1 z.2, v z.1 z.2) in

  (*smooth path*)
  locally_2d (fun r' t' =>
    ex_derive (fun z : R => g1 z t') r' /\
    ex_derive (fun z : R => g1 r' z) t' /\
    ex_derive (fun z : R => Derive (fun q => g1 z q) t') r' /\
    ex_derive (fun z : R => Derive (fun q => g1 q z) r') t') r t ->
  locally_2d (fun r' t' =>
    ex_derive (fun z : R => g2 z t') r' /\
    ex_derive (fun z : R => g2 r' z) t' /\
    ex_derive (fun z : R => Derive (fun q => g2 z q) t') r' /\
    ex_derive (fun z : R => Derive (fun q => g2 q z) r') t') r t ->
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g1 z t) v) u) r t ->
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g1 t z) u) v) r t ->
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g2 z t) v) u) r t ->
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => g2 t z) u) v) r t ->
  
  is_Holo f (g r t) -> 
  let g_t := fun p q => (Derive (g1 p) q, Derive (g2 p) q) in
  let g_r := fun p q => (Derive (g1 ^~ q) p, Derive (g2 ^~ q) p) in
  Derive ( fun t0 => Re (f (g r t0) * g_r r t0 ))%C t =
  Derive ( fun r0 => Re (f (g r0 t) * g_t r0 t ))%C r  
.
Proof.
  move => u v r t g1 g2 g f g1_smooth g2_smooth .
  move => g1_rt_cts g1_tt_cts g2_rt_cts g2_tr_cts.
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
  9: rewrite /g1_t /g1_r; apply Schwarz; auto.
  9: rewrite /g2_t /g2_r; apply Schwarz; auto.
  
  
  

  Locally_

Proof.



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