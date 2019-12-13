Require Import Reals Psatz Lra Bool.
From Coquelicot Require Import Continuity 
  Derive Hierarchy AutoDerive Rbar Complex RInt.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope program_scope.
Open Scope general_if_scope.
Require Import real_helpers ext_rewrite.


Lemma prod_c_topology_eq: forall z P,
  locally (T:=prod_UniformSpace R_UniformSpace R_UniformSpace) z P <->
  locally (T:=AbsRing_UniformSpace C_AbsRing) z P.
Proof.
  move => z P.
  rewrite /locally //=.
  split; case => eps H;
  have ?:= cond_pos eps;
  [eexists eps | eexists (mkposreal (eps/2) _)] => y bz;
  apply H;
  rewrite ? /ball //= /prod_ball /ball //= /AbsRing_ball /abs //=
            /Cmod sqrt_lt_left in bz *.
  2,3,5,6: nra.
  - rewrite -{2 3}(Rabs_right eps) /minus /opp //= /plus //=; 
    last by pose proof cond_pos eps; nra.
    rewrite ? Rmult_1_r.
    split; apply Rsqr_lt_abs_0;
    [rewrite /Rsqr | rewrite Rplus_comm in H0];
    eapply (Rplus_lt_reg_pos_r _ _ _ _ H0).
  - rewrite /minus /opp //= /plus //=
            -{1 2}(Rabs_right (eps/2)) /minus /opp //= /plus //=; 
    last by pose proof cond_pos eps; nra.
    case => /Rsqr_lt_abs_1 r1 /Rsqr_lt_abs_1 r2.
    have H0 := (Rplus_lt_compat _ _ _ _ r1 r2).
    rewrite /Rsqr in H0.
    nra.
  Unshelve.
  1: nra.
  all: rewrite -? /(Rsqr _); apply Rle_0_sqr.
Qed.

Ltac change_topology := 
  (apply: filterlim_filter_le_2;
  [ move => P; apply prod_c_topology_eq
  | auto
  ]).

Lemma continous_C_AbsRing: forall U f z, 
  @continuous U (AbsRing_UniformSpace C_AbsRing) f z <-> 
  @continuous U C_UniformSpace f z.
Proof.
  move => *; split => ?; change_topology.
Qed.

Lemma continous_C_NormedModule: forall U f z, 
  
  @continuous U (AbsRing_UniformSpace C_AbsRing) f z <-> 
  @continuous U C_NormedModule f z.
Proof.
  move => *; split => ?; change_topology.
Qed.

Lemma continous_R_Complete: forall f z, 
  
  @continuous R_UniformSpace R_UniformSpace f z <-> 
  @continuous R_UniformSpace 
    (CompleteNormedModule.UniformSpace R_AbsRing R_CompleteNormedModule)
 f z.
Proof.
  move => *; split =>?; eapply filterlim_filter_le_2.
  1,3: instantiate (1:= @locally _ _) => ?; apply: filter_imp; auto.
  all: auto.
Qed.

Lemma ex_RInt_prod: forall f a b,
  @ex_RInt C_R_CompleteNormedModule f a b <->
  @ex_RInt (prod_NormedModule R_AbsRing R_NormedModule R_NormedModule) f a b.
Proof.
  move => f a b; split; move=> [l ?]; exists l.
  - apply: filterlim_filter_le_2; first (by 
      (instantiate (1:= @locally _ l) => P)).
      auto.
  - apply: filterlim_filter_le_2; first (by 
      (instantiate (1:= @locally _ l) => P)).
      auto.
Qed.

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
    - auto_continuous f 0 => cts. 
      apply: filterlim_filter_le_1; first by apply: filter_le_within.
      rewrite -[x in filterlim _ _ (locally x)] f0.
      apply cts.
    - auto_continuous f 1 => cts. 
      apply: filterlim_filter_le_1; first by apply: filter_le_within.
      rewrite -[x in filterlim _ _ (locally x)] f1.
      apply cts.
    - move => t _; auto_continuous f t; auto.
    - move => t. apply pathD; auto.
      case: t; auto.
  Qed.
End PathConnected.

Open Scope fun_scope.
Open Scope type_scope.
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
    unfold_alg.
    set p := LHS.
    simplify_as_R2 e p.
    set p := RHS.
    simplify_as_R2 e p.
    f_equal; lra.
  Qed.
  Program Definition BallDom (r: posreal) z: 
    Domain (ball (M:= AbsRing_UniformSpace C_AbsRing) z r) :=  
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
    apply/prod_c_topology_eq.
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