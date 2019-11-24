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

Require Import domains.

Open Scope program_scope.
Open Scope general_if_scope.

Create HintDb derive_compute.

  Open Scope R.
Lemma diff_sqr : forall x y, 0 <= x^2 - 2 * x * y + y ^2.
Proof.
  move => x y.
  have <-: (x-y)^2 = x ^ 2 - 2*x*y + y^2.
  - nra.
  - rewrite -Rsqr_pow2; apply Rle_0_sqr.
Qed.

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

Ltac proj_proof eps := 
   apply (filter_imp (fun _ => True)); 
   [
   move => z _;
   rewrite {2}/minus;
   rewrite minus_eq_zero;
   rewrite norm_zero;
   apply Rmult_le_pos;
     [ pose proof cond_pos eps; nra
     | apply norm_ge_0 ]
   |by apply filter_true]
  .
Lemma filterdiff_fst: forall 
  {K: AbsRing}
  {V1 V2: NormedModule K} 
  (F: (V1*V2 -> Prop) -> Prop)
  {FF : Filter F},
  filterdiff (K:=K) fst F fst.
Proof.
  rewrite /filterdiff; split; first by apply is_linear_fst.
  move => y flim;
  rewrite /Equiv.is_domin => eps.
  proj_proof eps.
Qed.
Lemma filterdiff_snd: forall 
  {K: AbsRing}
  {V1 V2: NormedModule K} 
  (F: (V1*V2 -> Prop) -> Prop)
  {FF : Filter F},
  filterdiff (K:=K) snd F snd.
Proof.
  rewrite /filterdiff; split; first by apply is_linear_snd.
  move => y flim.
  rewrite /Equiv.is_domin => eps.
  proj_proof eps.
Qed.

Hint Resolve is_derive_pair : derive_compute.
Hint Resolve derive_ex_derive : derive_compute.
Hint Resolve filterdiff_ex_filterdiff : derive_compute.
Hint Resolve ex_derive_filterdiff : derive_compute.
Hint Immediate filterdiff_fst : derive_compute.
Hint Immediate filterdiff_snd : derive_compute.

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

Open Scope C.

Lemma continous_pair {T U1 U2: UniformSpace}:
  forall (f: T -> U1) (g: T -> U2) t, 
  continuous f t ->
  continuous g t ->
  continuous (fun q => (f q, g q)) t.
Proof.
  move => f g t ctsf ctsg.
  rewrite /continuous.
  eapply filterlim_filter_le_2 .
  2: eapply filterlim_pair.
  2: apply ctsf.
  2: apply ctsg.
  rewrite /filter_le => P.
  case => eps //=.
  rewrite /ball //= /prod_ball //=.
  move => H.
  eapply Filter_prod.
  - eapply locally_ball .
  - eapply locally_ball.
  - move => a b bf bg. 
    apply H.
    eauto.
Qed.
Section Holo.
  Definition CR_eqs (u v udx udy vdx vdy: C -> R) := 
      (forall x y, is_derive (fun t => u (t,y)) x (udx (x,y))) /\
      (forall x y, is_derive (fun t => u (x,t)) y (udy (x,y))) /\
      (forall x y, is_derive (fun t => v (t,y)) x (vdx (x,y))) /\
      (forall x y, is_derive (fun t => v (x,t)) y (vdy (x,y)))
      .

  Definition CauchyRieman (u v udx udy vdx vdy: C -> R) z:=
    udx z = vdy z /\ 
    udy z = (- vdx z)%R
    .
  
  Definition Holo (f g: C -> C) z := 
    is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z (g z).

  Ltac auto_continuous_aux :=
    try apply continuous_id;
    try apply continuous_const;
    try eapply continous_pair; 
    try apply continuous_fst; 
    try apply continuous_snd.
  Ltac auto_continuous x z := 
    have: continuous x z;
    rewrite /x;
    repeat auto_continuous_aux.

  Lemma local_c_reals:
    forall (z:C) P,
      (within (fun q => q.2 = z.2) (locally (T:=C_UniformSpace) z)) P ->
      (locally (T:= R_UniformSpace) z.1 (fun q => (P (q,z.2)))).
  Proof.
    move => z P lz //=.
    pose h (q:R) := (q, z.2).
    auto_continuous h z.1 => ctsh.
    apply (ext_filter ( Q:= fun q => P (h q))); first by rewrite/h; auto.
    have ->: (locally z.1 (fun q => P (h q)) = filtermap h (locally z.1) P);
    first by rewrite /filtermap; auto.
    have q: (filterlim h 
      (locally z.1) 
      (within (fun q => q.2 = z.2) (locally z))).
    - rewrite /within /filterlim /filtermap /filter_le.
      move {lz P} => P.
      rewrite ? /locally => c_lim.
      case: c_lim => eps c_lim.
      eexists eps => y byz.
      apply c_lim .
      + move: byz.
        rewrite /h ? /ball //= /prod_ball //= /ball //=.
        move => byz; split; first by auto.
        apply AbsRing_ball_center.
      + rewrite /h //=.
    - rewrite /filterlim /filter_le in q.
      specialize q with P.
      apply q.
      auto.
  Qed.

  Lemma local_c_imags:
    forall (z:C) P,
        (within (fun q => q.1 = z.1) (locally (T:=C_UniformSpace) z)) P ->
        (locally (T:= R_UniformSpace) z.2 (fun q => (P (z.1,q)))).
  Proof.
    move => z P lzP.
    pose h (z:C) := (z.2,z.1) .
    apply (local_c_reals (z:=(z.2,z.1)) (P:= fun q => P (q.2, q.1))).
    simpl.
    under ext_filter => x.
      have <-: (h x = (x.2,x.1)) by rewrite /h; auto.
    over.
    auto_continuous h (z.2, z.1) => H.
    rewrite /within in lzP *.
    apply H in lzP.
    rewrite /filtermap //= in lzP.
  Qed.

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

  Hint Rewrite prod_c_topolog_eq.
  Lemma c_diff_imaginary_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (z.1, q)) z.2 ((-v.2,v.1)%R).
  Proof.
    rewrite /is_derive /filterdiff => f z v.
    case => _ //=; split;
    first by apply (is_linear_scal_l (K:=R_AbsRing) ((-v.2,v.1)%R)).
    move => o xlim .
    have eqn: (z.2 = o) by apply is_filter_lim_locally_unique; auto.
    subst.
    rewrite /Equiv.is_domin //= in b *.
    move => eps.
    pose r_normeq := 
      fun z' => norm (K:=R_AbsRing)
          (minus (minus (f (z'.1, z'.2)) (f (z.1, z.2))) 
                 (scal (minus z'.2 z.2) ((-v.2,v.1)%R))) <=
        eps * norm (minus z'.2 z.2) .
    under ext_filter => p.
       rewrite -/(r_normeq (z.1, p)).
    over.
    apply local_c_imags.
    specialize b with z eps.
    pose h := fun q:C => (z.1,q.2).
    auto_continuous h z => hcts.
    set c_normeq := fun x: C =>
      norm  (minus (minus (f x) (f z)) (scal (minus x z) v)) <=
       eps * norm (minus x z) in b.
    have H': (forall q, q.1 = z.1 -> c_normeq (h q) = r_normeq q ).
    - case => q1 q2.
      simpl.
      move => ?.
      subst.
      rewrite /c_normeq /r_normeq /h //=.
      rewrite ? /norm //= -Cmod_prod_norm //=.
      rewrite ? /minus //= ? /plus //= ? /opp //= ? /scal //=
              ? /mult //= ? /abs //=.
      destruct z.
      simpl.
      repeat f_equal.
      + field_simplify.
        rewrite ? /Cplus ? /Cminus ? /Cmult ? /Copp //=.
        f_equal; field_simplify; auto.
      + rewrite /Cmod //=.
        apply sqrt_lem_1.
        * field_simplify. apply diff_sqr.
        * apply Rabs_pos.
        * field_simplify. rewrite pow2_abs. field_simplify.
          auto.

    - rewrite /within. 
      eapply (filter_imp (fun q => c_normeq (h q)));
      first by move => x cn eq; rewrite -H' //=.
      apply hcts.
      rewrite -surjective_pairing.
      rewrite prod_c_topolog_eq.
      apply b.
      rewrite /is_filter_lim //=.
    Qed.
  (** copy paste horror show!, but it's fine for now*)
  Lemma c_diff_real_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (q,z.2)) z.1 (v.1,v.2).
  Proof.
    rewrite /filterdiff => f z v.
    case => _ //=; split;
    first by apply (is_linear_scal_l (K:=R_AbsRing) (v.1,v.2)).
    move => o xlim .
    have eqn: (z.1 = o) by apply is_filter_lim_locally_unique; auto.
    subst.
    rewrite /Equiv.is_domin //= in b *.
    move => eps.
    pose r_normeq := 
      fun z' => norm (K:=R_AbsRing)
          (minus (minus (f (z'.1, z'.2)) (f (z.1, z.2))) 
                 (scal (minus z'.1 z.1) (v.1,v.2))) <=
        eps * norm (minus z'.1 z.1) .
    under ext_filter => p.
       rewrite -/(r_normeq (p, z.2)).
    over.
    apply local_c_reals.
    set c_normeq := fun x: C =>
      norm  (minus (minus (f x) (f z)) (scal (minus x z) v)) <=
       eps * norm (minus x z).

    pose h := fun q:C => (q.1,z.2).
    auto_continuous h z => hcts.

    have H': (forall q, q.2 = z.2 -> c_normeq (h q) = r_normeq q ).
    - case => q1 q2.
      simpl.
      move => ?.
      subst.
      rewrite /c_normeq /r_normeq /h //=.
      rewrite ? /norm //= -Cmod_prod_norm //=.
      rewrite ? /minus //= ? /plus //= ? /opp //= ? /scal //=
              ? /mult //= ? /abs //=.
      destruct z.
      simpl.
      repeat f_equal.
      + field_simplify.
        rewrite ? /Cplus ? /Cminus ? /Cmult ? /Copp //=.
        f_equal; field_simplify; auto.
      + rewrite /Cmod //=.
        apply sqrt_lem_1.
        * field_simplify. apply diff_sqr.
        * apply Rabs_pos.
        * field_simplify. rewrite pow2_abs. field_simplify.
          auto.

    - rewrite /within. 
      eapply (filter_imp (fun q => c_normeq (h q)));
      first by move => x cn eq; rewrite -H' //=.
      apply hcts.
      rewrite -surjective_pairing.
      rewrite prod_c_topolog_eq.

      apply (b z).
      rewrite /is_filter_lim //=.
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
    move => K V1 V2 u v x u' v' diff;split.
    - rewrite /is_derive in diff.
      apply (filterdiff_comp _ fst _ fst) in diff; simpl in *.
      + rewrite /is_derive //=.
      + rewrite /filtermap //=. apply filterdiff_fst.
    - rewrite /is_derive in diff.
      apply (filterdiff_comp _ snd _ snd) in diff; simpl in *.
      + rewrite /is_derive //=.
      + rewrite /filtermap //=. apply filterdiff_snd.
  Qed.

  Theorem CauchyRieman_Easy: forall u v udx udy vdx vdy g z,
    CR_eqs u v udx udy vdx vdy -> 
    Holo (fun p => (u p, v p)) g z ->
    (CauchyRieman u v udx udy vdx vdy z /\ (g z).1 = (vdy z) /\ (g z).2 = vdx z)
    .
  Proof.
    move => u v udx udy vdx vdy g z. 
    rewrite /Holo /CauchyRieman => cr_eqs holo.
    pose proof holo as holo2.
    pose proof holo as holo3.
    apply c_diff_imaginary_axis in holo.
    apply diff_split_coords in holo.
    destruct holo.
    apply c_diff_real_axis in holo2.
    apply diff_split_coords in holo2.
    destruct holo2.
    apply is_derive_unique in H1.
    apply is_derive_unique in H2.
    apply is_derive_unique in H.
    apply is_derive_unique in H0.
    rewrite -H0 in H1.
    rewrite -H2 in H.
    rewrite /CR_eqs in cr_eqs.
    move: cr_eqs.

    repeat (
    (first [case => Q | move => Q]);
    specialize Q with z.1 z.2;
    apply is_derive_unique in Q;
    rewrite ? Q in H1, H, H0, H2;
    move {Q}).
    rewrite -surjective_pairing in H1,H, H0 H2.
    auto.
  Qed.


