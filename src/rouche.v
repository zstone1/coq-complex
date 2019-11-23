Require Import Reals Psatz Lra.
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

Create HintDb derive_compute.

Ltac auto_derive_all_aux := 
  first [progress eauto with derive_compute | auto_derive]; 
  lra.

(** Gets a diff into a is_derive form, then tries a computation. Or it fails.*)
Ltac auto_derive_all :=
  match goal with 
  | |- is_derive _ _ _ => auto_derive_all_aux
  | |- filterdiff id _ ?y => by auto
  | |- filterdiff _ (locally _) _ =>
      (progress rewrite -/(is_derive _ _ _)); auto_derive_all_aux
  | |- filterdiff _ ?F _ => 
       progress rewrite [F]/(within _ (locally _));
       eapply (filterdiff_locally _ _);
       first apply filter_le_within;
       auto_derive_all_aux
    
  | |- ex_derive _ _ => auto_derive_all_aux
  | |- ex_filterdiff id _ => by auto
  | |- ex_filterdiff _ (locally _) =>
      (progress rewrite -/(ex_derive _ _)); auto_derive_all_aux
  | |- ex_filterdiff _ ?F => 
       progress rewrite [F]/(within _ (locally _));
       eapply (ex_filterdiff_locally _);
       first apply filter_le_within;
       apply ex_derive_filterdiff;
       auto_derive_all_aux
    
  end.


Hint Immediate filterdiff_id.
Hint Immediate ex_filterdiff_id.
Lemma global_local {A: UniformSpace} (P: A -> Prop):
  (forall x, P x) -> (forall x, locally x P).
Proof.
rewrite /locally.
move => glob x.
exists pos_half.
move => y _  //=.
Qed.

Lemma filterdiff_ex_filterdiff: forall {K:AbsRing} {U V:NormedModule K} f F g,
   filterdiff f F g -> ex_filterdiff (K:=K) (V:=V) (U:=U) f F.
Proof.
move => K V f F g d.
eexists.
eauto.
Qed.

Lemma derive_ex_derive: forall {K:AbsRing} {V:NormedModule K} f x g,
   is_derive f x g -> ex_derive (K:=K) (V:=V) f x.
Proof.
move => K V f F g d.
eexists.
eauto.
Qed.

Lemma ext_filter: 
  forall {T} (F: (T-> Prop) -> Prop) {FF: Filter F} P Q,
    (forall x, P x <-> Q x) -> F P <-> F Q.
Proof.
  move=> ? F ? P Q ext.
  split; apply filter_imp; apply ext.
Qed.

Lemma flip_filter {T V}:
  forall  (F: (T-> Prop) -> Prop) {FF: Filter F} (f g: T -> V),
    F (fun x => f x = g x) <-> F (fun x => g x = f x). 
Proof.
  move=> F FF f g ; split; move => fl.
  eapply (filter_imp (fun x => f x = g x)); first by congruence.
  auto.
  eapply (filter_imp (fun x => g x = f x)); first by congruence.
  congruence.
Qed.

Lemma ext_filterdiff_d {K : AbsRing} {U : NormedModule K} {V : NormedModule K}:
   forall l1 l2: U -> V, 
   (forall (x: U), l1 x = l2 x) ->   
   forall f F {FF: Filter F}, 
   filterdiff f F l1 <-> filterdiff f F l2.
Proof.
  move=> l1 l2 *.
  split; move => ?.
  - apply (filterdiff_ext_lin _ l1); auto.
  - apply (filterdiff_ext_lin _ l2); auto.
Qed.


Lemma ext_filterlim_loc:
  forall {T U F G} {FF : Filter F} (f g : T -> U),
  F (fun x => f x = g x) ->
  filterlim f F G <-> filterlim g F G.
Proof.
  move => ? ? F G ? f g ext; split;
  apply filterlim_ext_loc; auto.
  apply flip_filter; auto.
Qed.

Lemma ext_filterdiff_loc {K : AbsRing} {U : NormedModule K} {V : NormedModule K}:
   forall {F} {FF: Filter F} (f1 f2 l: U -> V),
   (F (fun q => f1 q = f2 q)) ->   
   (forall x, is_filter_lim F x -> f1 x = f2 x) ->
   filterdiff f1 F l <-> filterdiff f2 F l.
Proof.
  move => F FF f1 f2 l ext.
  split; move => ?.
  - eapply (filterdiff_ext_loc _ f2); auto. 
    auto.
  - eapply (filterdiff_ext_loc f2 _); auto.
    apply flip_filter; auto.
    symmetry.
    auto.
Qed.

Lemma ext_filterdiff_glo {K : AbsRing} {U : NormedModule K} {V : NormedModule K}:
   forall {F} {FF: Filter F} (f1 f2 l: U -> V),
   (forall x, f1 x = f2 x) ->
   filterdiff f1 F l <-> filterdiff f2 F l.
Proof.
  move => F FF f1 f2 l ext.
  apply ext_filterdiff_loc; last by auto.
  under ext_filter => x do by rewrite ext over.
  apply flip_filter; auto.
  apply filter_forall; auto.
Qed.

Lemma ext_is_derive_loc {K : AbsRing} {V : NormedModule K}:
   forall (f1 f2: K -> V) x l,
   (locally x (fun y => f1 y = f2 y)) ->
   is_derive f1 x l <-> is_derive f2 x l.
Proof.
  move => f1 f2 x l ext; split; move => drv //=; simpl in *.
  - apply (is_derive_ext_loc f1 _); auto.
  - apply (is_derive_ext_loc f2 ); auto.
    apply (filter_imp (fun y => f1 y = f2 y)); congruence.
Qed.

Lemma ext_is_derive_glo {K : AbsRing} {V : NormedModule K}:
   forall (f1 f2: K -> V) x l,
   (forall y,  f1 y = f2 y) ->
   is_derive f1 x l <-> is_derive f2 x l.
Proof.
  move => f1 f2 x l ext. 
  apply ext_is_derive_loc.
  apply global_local; auto.
Qed.

Lemma is_derive_pair {K : AbsRing} {M : NormedModule K} :
  forall (f g f' g': K -> M) (x: K), 
  is_derive f x (f' x) ->
  is_derive g x (g' x) ->
  is_derive (fun q => (f q, g q)) x (f' x, g' x).
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

Hint Resolve is_derive_pair : derive_compute.
Hint Resolve derive_ex_derive : derive_compute.
Hint Resolve filterdiff_ex_filterdiff : derive_compute.
Hint Resolve ex_derive_filterdiff : derive_compute.

Record Path (M: NormedModule R_AbsRing) := MkPath {
  l: R;
  r: R;
  f: R -> M
}.

Definition c_circle (t:R):C := (cos t, sin t).
Definition c_circle' (t:R):C := (-sin t, cos t).

Lemma c_circle_deriv: forall x, is_derive c_circle x (c_circle' x).
Proof.
  rewrite /c_circle /c_circle'.
  move => x.
  apply (is_derive_pair (f' := fun q => -_ _)); auto_derive_all. 
Qed.
Hint Resolve c_circle_deriv : derive_compute.

Lemma scal_one_r {K:Ring}: forall z: K ,
  scal z one = z.
Proof.
rewrite /scal //=.
apply mult_one_r.
Qed.

Open Scope fun_scope.
Open Scope type_scope.
Definition NtoC (n: nat) := RtoC (INR n).

Section Domain.
  Definition connected (D: C -> Prop) := 
    forall U V : C -> Prop, 
      (forall z, U z \/ V z <-> D z) -> 
      open U -> 
      open V -> 
      (exists z, U z /\ V z) \/ 
      (forall z, U z <-> False) \/
      (forall z, V z <-> False)
    .
              
  Record Domain (D:C -> Prop) := dom {
    open_dom: open D;
    connected_dom: connected D;
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
  Print Rtotal_order.
  SearchAbout ( _ < _ -> bool).
  Program Definition ODisk (r: {r : R | r > 0}):  Domain (fun z => Cmod z < r) := {|
    open_dom := _;
    connected_dom := _ ;
    dec_D := _ ;
    dec_DP := _;
  |}.

  Lemma sqrt_lt_left : forall x y, 0 <= x -> 0 <= y -> sqrt x < y <-> x < y^2.
  Proof.
    move => x y xge yge; split; move => H.
    - apply sqrt_lt_0_alt.
      rewrite /pow. 
      rewrite Rmult_1_r.
      rewrite sqrt_square; auto.
    - pose z := (y * y)%R.
      rewrite -(sqrt_lem_1 z y) /z.
      2-4: nra.
      apply sqrt_lt_1_alt; split; nra.
  Qed.

  Lemma rbs_rewrite : forall x y, Rabs x < y <-> (x < y /\ -x < y).
  Proof.
    move => x y; split => H.
    - apply Rabs_def2.

  Obligation 1.
  Proof.
    rewrite /open /locally => x zle.
    set eps := ((r0 - Cmod x)/ 2).
    have epspos: ( 0 < eps);first by (unfold eps; lra).
    exists (mkposreal eps epspos).
    rewrite /ball //= /prod_ball //= /ball //= /AbsRing_ball //= .
    rewrite /epspos /eps {epspos eps}.
    move => y; case => b1 b2.
    move: b1 b2 zle.
    rewrite /Cmod.
    rewrite /abs /AbsRing.abs //=.
    rewrite /minus //= /opp //=.
    rewrite /plus //= /opp //=.
    destruct x.
    destruct y.
    simpl.
    repeat rewrite Rmult_1_r.
    repeat rewrite sqrt_lt_left.
    2-5: nra.
    SearchAbout (Rabs _ < _).
    apply Rabs_def1.

    nra.


    move => H2; case => H3 H4.
    have H5: (r1 * r1 + r2 * r2 < r0^2); first by apply sqrt_lt_left; nra.
    apply sqrt_lt_left.
 
    nra.
    case => H4 H5.
    nra.
    case: x.
    move => x1 x2 y1 y2.
    
    lra.


    have (ball x )

    


  Definition bowl (z: )
End Domain.

Section Holo.

  Context {D_set: C -> Prop} {D: Domain D_set}.

  Context {V: NormedModule C_AbsRing}.
  
  Definition holo (f: D -> V) (z:D) (l:V) := 
    filterdiff (K:= C_AbsRing) (V:=V) f (locally z) (fun y => scal y l).  
  Proof.
    rewrite /holo => z Dz //=.
    apply holo_id_aux.
    under ext_filterdiff_d => x do by rewrite scal_one_r over.
    apply (filterdiff_id _).
  Qed.

Lemma holo_pow: forall n, 
  holo (pow_n ^~ (S n)) 
  (fun x => mult (NtoC (S n)) (pow_n x n)).
Proof.
  elim => [| n IHn] //=; rewrite /holo /is_derive => z Dz.
  - under ext_filterdiff_glo => x 
      do by rewrite mult_one_r over.
    under ext_filterdiff_d => x.
      rewrite mult_one_r /NtoC /scal //=.
      rewrite mult_one_r.
    over.
    auto.
    apply (filterdiff_id ).
    auto_derive_all.
  - rewrite /holo => z Dz.
    apply (filterdiff_comp _ (mult x)).
    under ext_filterdiff_glo => x.
      rewrite -/pow_n.
      field_simplify.

      
  under ext_filterdiff_loc. 
  





  
  






