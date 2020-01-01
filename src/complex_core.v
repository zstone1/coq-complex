Require Import Reals Psatz Lra Bool.
From Coquelicot Require Import Continuity 
  Derive Hierarchy AutoDerive Rbar Complex RInt Derive_2d Rcomplements.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope program_scope.
Open Scope general_if_scope.
Require Import helpers.


Section PathConnected .
  Program Definition path_connected {T: UniformSpace} (D: T -> Prop) := 
    forall x y : T,
    D x ->
    D y ->
    exists f : R -> T,
    f 0 = x /\ filterlim f (at_right 0) (locally x) /\ 
    f 1 = y /\ filterlim f (at_left  1) (locally y) /\ 
    (forall t, 0 < t < 1 -> continuous f t) /\
    forall t : { t: R | 0 <= t <= 1 }, D (f t).
  Program Definition convex  {T: NormedModule R_AbsRing} (D: T -> Prop) := 
    forall (x y : T) (t : R),
      D x -> 
      D y -> 
      0 <= t <= 1 -> 
    D (plus (scal (1-t) x) ( scal t  y)).
   
  Lemma convex_ext: forall (T: NormedModule R_AbsRing) (D1 D2: T -> Prop),
    (forall x, D1 x <-> D2 x) -> convex D1 <-> convex D2.
  Proof.
    move => ? D1 D2 ext.
    split; move => H ???;
    [rewrite -!ext | rewrite ! ext]; apply H.
  Qed.

  Lemma cts_all_cts_on:  
    forall {T: NormedModule R_AbsRing} (f:R -> T) x y,
    f 0 = x -> 
    f 1 = y ->
    (forall t, continuous f t) ->
    filterlim f (at_right 0) (locally x) /\ 
    filterlim f (at_left  1) (locally y) /\ 
    (forall t, 0 < t < 1 -> continuous f t).
  Proof.        
    move => T f x y f0 f1 cts.
    repeat split; auto.
    - apply: filterlim_filter_le_1.
      apply: filter_le_within.
      rewrite -f0.
      apply cts.
    - apply: filterlim_filter_le_1.
      apply: filter_le_within.
      rewrite -f1.
      apply cts.
  Qed.

  Lemma convex_path_connected {T: NormedModule R_AbsRing} (D: T -> Prop):
    convex D -> path_connected D.
  Proof.
    rewrite /convex /path_connected. 
    move => pathD x y Dx Dy. 
    pose f := fun t => (plus (scal (1 - t) x) (scal t y)).
    exists f.
    have f0: (f 0 = x) by
      rewrite /f !Rminus_0_r scal_zero_l scal_one plus_zero_r.
    have f1: (f 1 = y) by
      rewrite /f !Rcomplements.Rminus_eq_0 scal_zero_l scal_one plus_zero_l.

    repeat split; auto.
    - apply: filterlim_filter_le_1; first by apply: filter_le_within.
      rewrite -[x in filterlim _ _ (locally x)] f0.
      rewrite -/(continuous _ _) /f.
      auto_cts.
    - apply: filterlim_filter_le_1; first by apply: filter_le_within.
      rewrite -[x in filterlim _ _ (locally x)] f1.
      rewrite -/(continuous _ _) /f.
      auto_cts.
    - move => t _. rewrite /f. auto_cts.
    - move => t. apply pathD; auto.
      case: t; auto.
  Qed.
End PathConnected.

Open Scope fun_scope.
Definition NtoC (n: nat) := RtoC (INR n).

Section Domain.
              
  Record Domain (D:C -> Prop) := dom {
    open_dom: open D;
    connected_dom: path_connected D;
    dec_D : C -> bool;
    dec_DP : forall z, reflect (D z) (dec_D z);
  }.

  Definition mkDomain D (_:Domain D): Type := {z:C | D z}.

  Coercion mkDomain : Domain >-> Sortclass.
  (** need Program definition here to help coq understand that 
      f only occurs in the (D z) case.*)
  Program Definition const_extend {T:Type} {D_set : C -> Prop} 
    {D: Domain D_set} (x:T) (f: D -> T) (z: C): T := 
      if dec (dec_D D z)
      then f z
      else x.
  Obligation 1.
    (move => * //=; apply /(dec_DP); eauto).
  Qed.

  Definition dom_irr {T} {D_set} {D:Domain D_set}  (f: D -> T) := 
    forall z h1 h2, f (exist D_set z h1) = f (exist D_set z h2).
  Program Definition const_extend_id_def := 
    forall T D_set (D: Domain D_set) (f: D -> T) (x:T) z (Dz: D_set z) ,
    dom_irr f ->
    const_extend x f z = f z.

  Lemma const_extend_id: const_extend_id_def.
  Proof.
    rewrite /const_extend_id_def /const_extend. 
    move => T Ds D f x z + irr.
    case dec => [ eqt | fls Dz].
    - apply irr. 
    - contradict fls. move: Dz => /(dec_DP D) => q; rewrite q //=. 
  Qed.

  Lemma ODisk_convex: forall r, (0 < r) -> convex (fun z => Cmod z < r).
  Proof.
    rewrite /convex => r rpos x y t Dx Dy tbd.
    case: tbd. 
    case => teq1; case => teq2.
    - apply (Rle_lt_trans _ (Cmod (scal (1-t) x) + Cmod (scal t y)) _); 
      first by apply Cmod_triangle.
      rewrite ?scal_R_Cmult ?Cmod_mult ?Cmod_R ?Rabs_pos_eq.
      all: nra.
    - rewrite teq2 scal_one Rcomplements.Rminus_eq_0 scal_zero_l plus_zero_l //=.
    - rewrite -teq1 scal_zero_l plus_zero_r Rminus_0_r scal_one //=.
    - rewrite teq2 in teq1. contradict teq1. auto.
  Qed.

  Lemma convex_translate: forall D z, 
    convex D -> convex (fun q => D(z - q)%C ).
  Proof.
    move => D z + x y t Dzx Dzy tbd.
    move => /(_ (z - x)%C (z-y)%C t Dzx Dzy tbd).
    set p := (x in D x).
    set q := (x in _ ->  D x).
    have: p = q; last by congruence.
    rewrite {}/p {}/q.
    do 2 unfold_alg.
    simplify_as_R2 RHS.
    simplify_as_R2 LHS.
    f_equal; field_simplify_eq; auto.
  Qed.

  Program Definition BallDom (r: posreal) z: 
    Domain (ball_circ z r) :=  
  {|
    open_dom := _;
    connected_dom := _ ;
    dec_D := fun z0 => Rlt_dec (Cmod (z0 - z)%C) r;
    dec_DP := _;
  |}.

  Lemma ball_reduce_eps : forall {T: AbsRing} r (x y:T), 
    ball x r y -> ball x ((abs (minus y x)+r)/2) y.
  Proof.
    move => T r x y Br.
    rewrite /ball //= /AbsRing_ball //= in Br *.
    lra.
  Qed.
    
  Obligation 1. 
  Proof.
    move => x /ball_reduce_eps Bx.
    have ?:= cond_pos r.
    apply/locally_C.
    pose del := (r - ((abs(minus x z ) + r)/2)).
    have delpos : 0 < del. { 
      rewrite /ball //= /AbsRing_ball //= Rplus_comm in Bx. 
      rewrite -> Rcomplements.Rminus_lt_0 in Bx.
      rewrite /del.
      field_simplify.
      field_simplify in Bx.
      exact Bx.
    }
    exists (mkposreal del delpos) => y By.
    have -> : pos r = ((abs (minus x z) +r)/2 + del)%R by
      rewrite /del; lra.
    apply: UniformSpace.ax3; rewrite //= .
    - apply: Bx.
    - apply: By.
  Qed.

  Obligation 2. 
    apply: convex_path_connected. 
    have ?:= cond_pos r.
    have := ODisk_convex (cond_pos r).
    move => /(@convex_translate _ z) //=.
    rewrite /ball //= /AbsRing_ball /abs //= /minus /plus /opp //=.
    under convex_ext => q. 
      replace (Cmod (z -q)%C) with (Cmod (q - z)%C).  
    over.
    2: auto.
    
    rewrite /Cmod. 
    f_equal.
    simpl.
    nra.
  Qed.

  Obligation 3. 
  Proof.
    apply iff_reflect. 
    unfold_alg.
    rewrite -/(Cminus _ _).
    split; case (Rlt_dec (Cmod (z0 - z) %C) r) => x; by auto.
  Qed.

End Domain.

Section Holomorphism.

(** the main definition we care about. 
    It will turn out this is much stronger than 
    just differentiable in two dimensions
    *)
Definition Holo (f g: C -> C) z := 
  is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z (g z).

Definition is_Holo (f: C -> C) z := 
  exists g, Holo f g z.

(** Assuming the derivative is continuous dramatically simplifies 
    this whole project. It turns out Holo -> CHolo, but we don't
    prove that here *)
Definition CHolo f f' z := 
  Holo f f' z /\ continuous f' z.

Definition CHolo_on D f := exists f',
  forall z, D z -> CHolo f f' z.

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

Lemma continuous_Cinv: forall (z:C), 
  z <> 0 -> continuous (Cinv) z.
Proof.
  move => z z_neq_0.
  have ?: (z.1 * z.1 + z.2 * z.2 <> 0)%R. {
    contradict z_neq_0.
    field_simplify.
    rewrite [LHS]surjective_pairing.
    f_equal; nra.
  }
  rewrite /Cinv /=.
  auto_cts;
  rewrite /Rdiv;
  auto_cts.
  all: try apply: continuous_fst.
  all: try apply: continuous_snd.
  all: try apply: continuous_Rinv.
  all: lra. 
Qed.

End Holomorphism.

Section CauchyRiemann.

Definition CauchyRiemann (udx udy vdx vdy: C -> R) z:=
  udx z = vdy z /\ 
  udy z = (- vdx z)%R
.

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
  move => /(_ epsr2) /locally_C [del H].
  exists del => u v uball vball.
  move :H => /(_ (u,v)).
  unfold_alg; rewrite /AbsRing_ball. unfold_alg .
  have Q: (Rabs (u-x) < del /\ Rabs (v-y) < del) by auto.
  move => /(_ Q) {Q}.
  simplify_as_R2 (x in Cmod x <= _).
  set p := (x in Cmod (x,_)).
  set q := (x in Cmod (_,x)).
  set l := (x in Rabs x).
  simplify_as_R2 (x in Rmult _ (Cmod x)).
  have ->: (l = q) by rewrite /l /q; field_simplify_eq.
  move => H.
  apply: Rle_trans.
  apply: Cmod_Rabs_imaginary p _.
  apply: Rle_trans.
  apply H.
  apply (Rle_trans _ (eps * Rmax (Rabs (u-x)) (Rabs (v-y)))); last by right; auto.
  rewrite /Rdiv.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l; first by left; apply: cond_pos.
  field_simplify .
  apply/Rcomplements.Rle_div_l; first by apply Rlt_sqrt2_0.
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
  simplify_term (x in differentiable_pt_lim _ _ _ x _).
  simplify_term (x in differentiable_pt_lim _ _ _ _ x).
  eapply differentiable_pt_lim_ext.
  exists pos_half => u v _ _ . field_simplify_eq; auto.
Qed.
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
      + simplify_term (x in Rabs x).
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
        + simplify_term (x in Rabs x).
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

  Local Lemma filter_apply: forall 
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
  Theorem CauchyRiemann_Hard: forall u v udx udy vdx vdy z,
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
    apply/locally_C.
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
    simplify_as_R2 (x in norm (minus x _ ) ); simpl.
    rewrite -?/(Rminus _ _).
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
      simplify_as_R2 LHS;
      simplify_as_R2 RHS;
      unfold_alg;
      f_equal;
      field_simplify.
    `Done.
    }
    move => -> {p}.
    unfold_alg.
    rewrite -?/(Cminus _ _).
    rewrite Cplus_comm /dz.
    do 2 unfold_alg.
    simplify_as_R2 (x in Cmod x).
  
    set p := (x in x <= _).
    `Begin Rle p. { rewrite /p.
    | {(  Rabs _ + Rabs _ )}          
      apply Cmod_Rabs_plus.
    | {(  (Rabs (_ - _) + Rabs ( _ - _)) + _ )}   
      apply Rplus_le_compat_r;
      apply: Rle_trans;last (by apply Rabs_triang);
      rewrite -[x in _ <= Rabs x]Rplus_assoc -/(Rminus _ _).

    | {(  _ + _ + Rabs (_ - _) + Rabs (_ - _) )}
       rewrite !Rplus_assoc;
       do 2 apply Rplus_le_compat_l;
       rewrite -Rplus_assoc;
       apply: Rle_trans;last (by apply Rabs_triang);
       rewrite /Rminus -[x in _ <= Rabs x ]Rplus_assoc.

    | {(  _ * _ dx + _ * _ dy + _ * _ dx + _ * _ dy  )}         
      rewrite -?Rmult_minus_distr_r !Rabs_mult.
    | {(  _ + _ + _ + _ * Cmod dz   )} 
       apply Rplus_le_compat_l;
       apply Rmult_le_compat_l; first (by apply Rabs_pos);
       apply Cmod_Rabs_imaginary.
    | {(  _ + _ + _ * Cmod dz + _   )} 
       apply Rplus_le_compat_r;
       rewrite !Rplus_assoc;
       do 2 apply Rplus_le_compat_l;
       apply Rmult_le_compat_l; first (by apply Rabs_pos);
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
    apply: Rle_trans; first apply H.
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
    lra.
  Qed.
End CauchyRiemann.

Section CHoloTeardown.
(** Surprisingly, this is the Cauchy riemann equations are 
    the easist way to prove Cinv is holomorphic right now *)
Lemma holo_inv : forall (z: C), 
  (z <> 0)%C -> (Holo Cinv (fun q => -1/(q * q)) z)%C.
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
  have ball_neq_0: forall y, ball z del y -> (y.1 * y.1 + y.2 * y.2 <> 0)%R. {
    move => y ybd.
    copy => /Rplus_sqr_eq_0_l y1. 
    rewrite Rplus_comm.
    move => /Rplus_sqr_eq_0_l y2.
    have: y = (0,0); first by rewrite [LHS]surjective_pairing y1 y2.
    move => ?; subst.
    move: ybd.
    do 2 rewrite /ball /= /prod_ball /= /AbsRing_ball /= .
    unfold_alg.
    rewrite ?Rminus_0_l ?Rabs_Ropp.
    destruct (Rlt_dec (Rabs z.1) (Rabs z.2));
    [rewrite ?Rmax_right| rewrite ?Rmax_left]; lra.

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
  apply: CauchyRiemann_Hard; simpl. 
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
  all: auto_cts.
  all: apply: continuous_Rinv.
  all: try (now apply ball_neq_0; apply ball_center);
    try (now apply: Rlt_0_neq_0; field_simplify; apply ball_pows_0;
             apply ball_center).
Qed.

Lemma CHolo_subset: forall P Q f, 
  (forall z, P z -> Q z) -> 
  CHolo_on Q f ->
  CHolo_on P f.
Proof.
  move => P Q f sub [f' holo].
  exists f' => z Pz.
  apply holo.
  apply sub.
  auto.
Qed.

Open Scope C.
Lemma CHolo_on_plus: forall D f g, 
  CHolo_on D f ->
  CHolo_on D g -> 
  CHolo_on D (fun z => f z + g z )  
.
Proof.
  move => D f g [f' fholo] [g' gholo].
  exists (fun z => f' z  + g' z) => z Dz.
  split.
  - apply: is_derive_plus.
    + apply fholo; auto. 
    + apply gholo; auto.
  - auto_cts.
    + apply fholo; auto. 
    + apply gholo; auto.
Qed.

Lemma CHolo_on_minus: forall D f g, 
  CHolo_on D f ->
  CHolo_on D g -> 
  CHolo_on D (fun z => f z - g z )  
.
Proof.
  move => D f g [f' fholo] [g' gholo].
  exists (fun z => f' z  - g' z) => z Dz.
  split.
  - apply: is_derive_minus.
    + apply fholo; auto. 
    + apply gholo; auto.
  - auto_cts.
    + apply fholo; auto. 
    + apply gholo; auto.
Qed.

Lemma CHolo_on_opp: forall D f, 
  CHolo_on D f ->
  CHolo_on D (fun z => - f z)  
.
Proof.
  move => D f [f' fholo].
  exists (fun z => - f' z) => z Dz.
  split.
  - apply: is_derive_opp.
    apply fholo; auto. 
  - auto_cts.
    apply fholo; auto. 
Qed.

Lemma diff_topology_change: forall f f' z, 
 
 @is_derive C_AbsRing (C_NormedModule) f z f' <-> 
 @is_derive C_AbsRing (AbsRing_NormedModule C_AbsRing) f z f'.
Proof.
  move => f f' z.
  rewrite /is_derive /filterdiff.
  split;
  move => [_ Hf]; (split; first by apply is_linear_scal_l);
  move => + /is_filter_lim_locally_unique <- eps => _;
  move: Hf => /(_ z);
  [ move => /(_ (@is_filter_lim_locally (AbsRing_UniformSpace C_AbsRing) z ))
  | move => /(_ (@is_filter_lim_locally (AbsRing_UniformSpace C_AbsRing) z ))
  ];
  move => /(_ eps); auto.
Qed.

Hint Extern 5 (continuous _ _) => (apply/cts_topology_2) : teardown_leaf. 

Lemma CHolo_on_mult: forall D f g, 
  CHolo_on D f ->
  CHolo_on D g -> 
  CHolo_on D (fun z => f z * g z )  
.
Proof.
  move => D f g [f' fholo] [g' gholo].
  exists (fun q => f' q * g q + f q * g' q) => z Dz.
  split.
  - move: fholo => /(_ z Dz) [/diff_topology_change fholo _].
    move: gholo => /(_ z Dz) [/diff_topology_change gholo _].
    rewrite /Holo /is_derive in fholo gholo.
    have:= (@filterdiff_mult_fct 
      C_AbsRing 
      (AbsRing_NormedModule C_AbsRing) 
      f g z _ _ Cmult_comm fholo gholo ).
    move => H.
    apply/diff_topology_change.
    rewrite /is_derive.
    move: H => //=.
    unfold_alg => H.
    under ext_filterdiff_d => t.
      set p := _ * _. 
      replace p with (t * f' z * g z + f z * (t * g' z)).
    over.
    rewrite /p; field_simplify_eq; auto.
    auto.
  - move: (fholo z Dz) => [/is_derive_continuous df cf'].
    move: (gholo z Dz) => [/is_derive_continuous dg cg'].
    auto_cts. 
Qed.

Lemma Cmult_zero : forall z, 
  z * z = 0 -> z = 0.
Proof.
  move => z H.
  apply Cmod_eq_0.
  have: (Cmod z * Cmod z = 0)%R.
  2: by nra.
  rewrite -Cmod_mult -Cmod_0.
  by f_equal.
Qed.

Lemma CHolo_on_const: forall D k, 
  CHolo_on D (fun => k).
Proof.
  move => D k.
  exists (fun => 0) => z Dz.
  split.
  - apply: is_derive_const.
  - auto_cts.
Qed.

Lemma CHolo_on_id: forall D, 
  CHolo_on D id.
Proof.
  move => D.
  exists (fun => one) => z Dz.
  split.
  - apply/diff_topology_change; apply: is_derive_id.
  - auto_cts.
Qed.


Lemma CHolo_on_div: forall D f, 
  CHolo_on D f ->
  (forall z, D z -> f z <> 0) ->
  CHolo_on D (fun z => / (f z) )  
.
Proof.
  move => D f [f' fholo].
  exists (fun q => f' q * (-1/((f q * f q)))) => z Dz.
  split.
  - move: fholo => /(_ z Dz) [/diff_topology_change fholo _].
    rewrite /Holo /is_derive in fholo.
    apply: is_derive_comp; last by apply: fholo.
    apply holo_inv; auto.
  - move: (fholo z Dz) => [/is_derive_continuous df cf'].
    have Q:= @holo_inv (f z * f z).
    auto_cts.
    apply/cts_topology_1/cts_topology_2.
    apply: is_derive_continuous.
    apply: Q.
    move => /Cmult_zero.
    apply H.
    auto.
Qed.

End CHoloTeardown.

Hint Extern 1 (CHolo_on _ id _) => (apply: CHolo_on_id) : teardown_leaf.
Hint Extern 1 (CHolo_on _ (fun =>_) _) => (apply: CHolo_on_const) : teardown_leaf.
Ltac auto_CHolo_on := 
  rewrite /Rdiv /Cdiv; 
  repeat (teardown
          (fail "no topology change for CHolo") 
          (apply: CHolo_on_plus) 
          (unfold_alg; apply: CHolo_on_mult) 
          (apply: CHolo_on_mult)
          (apply: CHolo_on_plus)
          (apply: CHolo_on_opp)
          (apply: CHolo_on_div)
          (fail "no CHolo for pairs"));
 auto with teardown_leaf.


Section Contours.
  Open Scope C.
  
  Definition c_circle (r: R) (t:R):C := r * (cos t, sin t).
  Definition c_circle' (r: R) (t:R):C := r * (-sin t, cos t)%R.
  
  Record Contour := mkContour {
    gamma: R -> C; 
    gamma': R -> C;
    l_end: R;
    r_end: R;
    endpoint_interval: l_end < r_end;
    contour_derive: forall t, l_end <= t <= r_end -> is_derive gamma t (gamma' t);
    cts_derive: forall t, l_end <= t <= r_end -> continuous gamma' t;
  }.
  
  Definition is_CInt (g: Contour) (f: C -> C) (z:C) :=
    is_RInt (fun t => f (gamma g t) * (gamma' g t)) (l_end g) (r_end g) z.
  
  Definition ex_CInt (g: Contour) (f: C -> C) :=
    exists z, is_CInt g f z. 
  
  Definition CInt (g: Contour ) f := 
    RInt (V:=C_R_CompleteNormedModule) 
      (fun t => f (gamma g t) * (gamma' g t)) (l_end g) (r_end g) .
  
  Program Definition circC (z:C) (r: R) := {|
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
      simplify_as_R2 (_ + _) .
    over.
    simplify_as_R2 (x in is_derive _ _ x).
    apply/ is_derive_pair; split; auto_derive; auto; field_simplify; auto.
  Qed.
  
  Definition Cmult_Abs z1 z2: C_AbsRing := Cmult z1 z2.
  
  Obligation 3.
  Proof.
    rewrite /c_circle'.
    auto_cts.
    1,2: apply: ex_derive_continuous; auto_derive; auto.
  Qed.

End Contours.

