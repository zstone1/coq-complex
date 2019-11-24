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
Require Import domains ext_rewrite real_helpers.

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
End Holo.

