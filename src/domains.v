Require Import Reals Psatz Lra Bool.
From Coquelicot Require Import Continuity 
  Derive Hierarchy AutoDerive Rbar Complex .
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope program_scope.
Open Scope general_if_scope.
Lemma sqrt_lt_left : forall x y, 0 <= x -> 0 <= y -> sqrt x < y <-> x < y^2.
Proof.
  move => x y xge yge; split; move => H.
  - apply sqrt_lt_0_alt.
    rewrite /pow. 
    rewrite Rmult_1_r.
    rewrite sqrt_square; auto.
  - pose z := y * y.
    rewrite -(sqrt_lem_1 z y) /z.
    2-4: nra.
    apply sqrt_lt_1_alt; split; nra.
Qed.

Lemma rabs_rewrite : forall x y, Rabs x < y <-> (x < y /\ -y < x).
Proof.
  move => x y; split => H.
  -  apply Rabs_def2. auto.
  - apply Rabs_def1; tauto.
Qed.

Lemma le_square : forall x y, 0 <= x -> 0 <= y ->  x < y <-> (x * x < y * y).
Proof.
  move => *; split => H; nra.
Qed.

Lemma abs_sqr: forall x, Rabs x * Rabs x = x * x.
Proof.
  move => x. rewrite -[_ * _]/(Rsqr _). rewrite -Rsqr_abs; auto.
Qed.

Lemma square_in_circle: forall x1 x2 y1 y2 e,
  0 < e -> 
  abs (y1 - x1) < e ->
  abs (y2 - x2) < e ->
  sqrt((y1 - x1)^2 + (y2 - x2)^2) < 2*e.
Proof.
  move => x1 x2 y1 y2 e epos U V.
  apply sqrt_lt_left.
  2: lra.
  { apply Rplus_le_le_0_compat; apply pow2_ge_0. }
  move: U V.
  rewrite le_square //=. 
  3: nra.
  2: apply abs_ge_0.
  move => H1.
  rewrite le_square //=. 
  3: nra.
  2: apply abs_ge_0.
  move: H1.
  rewrite /abs //= abs_sqr abs_sqr.
  nra.
Qed.

Lemma prod_c_topolog_eq: forall z P,
  locally (T:=prod_UniformSpace R_UniformSpace R_UniformSpace) z P <->
  locally (T:=AbsRing_UniformSpace C_AbsRing) z P.
Proof.
  move => z P.
  rewrite /locally //=.
  SearchAbout posreal.
  split => H; move: H; case => eps H;
  [eexists eps | eexists (mkposreal (eps/2) _)] => y bz;
  apply H;
  move: bz;
  rewrite ? /ball //= /prod_ball /ball //= /AbsRing_ball /abs //=;
  rewrite /Cmod sqrt_lt_left.
  3,6: pose proof cond_pos eps; nra.
  2,5: nra.
  - rewrite -{2 3}(Rabs_right eps) /minus /opp //= /plus //=; 
    last by pose proof cond_pos eps; nra.

    simpl in *.
    rewrite ? Rmult_1_r.
    split; apply Rsqr_lt_abs_0.
    rewrite /Rsqr; first by eapply (Rplus_lt_reg_pos_r _ _ _ _ H0).
    rewrite Rplus_comm in H0.
    eapply (Rplus_lt_reg_pos_r _ _ _ _ H0).
  - rewrite /minus /opp //= /plus //=.
    rewrite -{1 2}(Rabs_right (eps/2)) /minus /opp //= /plus //=; 
    last by pose proof cond_pos eps; nra.
    case => r1 r2.
    apply Rsqr_lt_abs_1 in r1.
    apply Rsqr_lt_abs_1 in r2.
    SearchAbout (_ < _ -> _ < _ -> _ + _ < _ + _).
    pose proof (Rplus_lt_compat _ _ _ _ r1 r2).
    rewrite /Rsqr in H0.
    nra.
  - nra.

  Unshelve.
  1: pose proof cond_pos eps; nra.
  all: rewrite -? /(Rsqr _); apply Rle_0_sqr.
Qed.

Section PathConnected .
  Program Definition path_connected {T: UniformSpace} (D: T -> Prop) := 
    forall x y : T,
    D x ->
    D y ->
    exists f : { t : R  | 0 <= t <= 1 } -> T,
    f 0 = x /\ 
    f 1 = y /\ 
    forall t : { t: R | 0 <= t <= 1 }, D (f t).
  Obligation 1.
  nra.
  Qed.
  Obligation 2.
  nra.
  Qed.

  Program Definition convex  {T: NormedModule R_AbsRing} (D: T -> Prop) := 
    forall (x y : T) (t : R),
      D x -> 
      D y -> 
      0 <= t <= 1 -> 
    D (plus (scal (1-t) x) ( scal t  y)).
   
  Lemma convex_path_connected {T: NormedModule R_AbsRing} (D: T -> Prop):
    convex D -> path_connected D.
  Proof.
    rewrite /convex /path_connected. 
    move => pathD x y.
    exists (fun t: {t: R | 0 <= t <= 1} => 
      (plus (scal (1 - proj1_sig t) x) (scal (proj1_sig t) y))).
    simpl.
    rewrite Rcomplements.Rminus_eq_0.
    rewrite Rminus_0_r.
    rewrite 2!scal_zero_l.
    rewrite 2!scal_one.
    rewrite plus_zero_l.
    rewrite plus_zero_r.
    repeat split; auto.
    case => t tle.
    apply pathD; simpl; auto.
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

  Lemma ODisk_open: forall r, (0 < r) -> open (fun z => Cmod z < r).
  Proof.
    rewrite /open /locally => r rpos x zle.
    rewrite /ball //= /prod_ball //= /ball //= /AbsRing_ball //= .
    pose proof zle.
    eexists ?[eps].
    move => y; case => b1 b2.
    move: b1 b2 H.
    have tri: (Cmod y <= Cmod (minus y x) + Cmod (x) ).
    { have q: (y = plus (minus y x) x); 
        last by rewrite {1} q; eapply Cmod_triangle.
      rewrite /minus -plus_assoc plus_opp_l plus_zero_r //=.
    }
    move => H1 H2 H3.
    have to_circ:(Cmod (minus y x) < 2 * ?eps).
    { apply square_in_circle. 1: shelve. all: auto. }
    have epslt: (2*?eps < r - Cmod x); first shelve.
    nra.


    Grab Existential Variables.
    - set e:= (r -Cmod x) / 4.
      have epos: (e > 0) by (rewrite /e; nra).
      set e' := mkposreal e epos.
      instantiate (1 := mkposreal ((r -Cmod x)/4) _ ).
      simpl.
      nra.
    - simpl. nra.
    Unshelve.
    nra.
  Qed.

  Lemma ODisk_convex: forall r, (0 < r) -> convex (fun z => Cmod z < r).
  Proof.
    rewrite /convex => r rpos x y t Dx Dy tbd.
    case: tbd. 
    case => teq1; case => teq2.
    - apply (Rle_lt_trans _ (Cmod (scal (1-t) x) + Cmod (scal t y)) _); 
      first by apply Cmod_triangle.
      repeat rewrite scal_R_Cmult.
      repeat rewrite Cmod_mult.
      repeat rewrite Cmod_R.
      repeat rewrite Rabs_pos_eq.
      all: nra.
    - rewrite teq2. 
      rewrite scal_one.
      rewrite Rcomplements.Rminus_eq_0.
      rewrite scal_zero_l.
      rewrite plus_zero_l.
      auto.
    - rewrite -teq1.
      rewrite scal_zero_l.
      rewrite plus_zero_r.
      rewrite Rminus_0_r.
      rewrite scal_one.
      auto.
    - rewrite teq2 in teq1. contradict teq1. auto.
  Qed.

  Definition ODisk_dec (r: R) (z:C) := Rlt_dec (Cmod z) r.


  Program Definition ODisk (r: {r : R | r > 0}):  Domain (fun z => Cmod z < r) := {|
    open_dom := _;
    connected_dom := _ ;
    dec_D := (ODisk_dec r);
    dec_DP := _;
  |}.
  Obligation 1. apply ODisk_open. nra. Qed.
  Obligation 2. apply convex_path_connected. apply ODisk_convex. nra. Qed.
  Obligation 3. 
    apply iff_reflect; split; case (ODisk_dec); by auto.
  Qed.

End Domain.