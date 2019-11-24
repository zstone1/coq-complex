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