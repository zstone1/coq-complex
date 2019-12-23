Require Import Reals Psatz Lra RelationClasses List.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex
  RInt RInt_analysis Derive_2d Compactness.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import domains ext_rewrite real_helpers.
Require Import domains cauchy_riemann path_independence cauchy_integral .

Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.



Section UniformOn.

Context {U V:UniformSpace}.

Definition uniformly_on (E: U -> Prop) f (P: (U -> V) -> Prop) := 
  exists (del: posreal), forall g, 
    (forall x, E x -> (ball (f x) del (g x))) -> 
    P g.
Lemma uniformly_on_self: forall E f P, 
  uniformly_on E f P -> P f.
Proof.
  move => E f P [del H].
  apply H.
  move =>*. 
  apply: ball_center.
Qed.


Global Instance uniformly_on_filter: forall E f,
  ProperFilter (uniformly_on E f).
Proof.
  move => D f .
  constructor;[| constructor].
  - move => *.
    exists f.
    apply: uniformly_on_self.
    eauto.
  - move => *.
    exists pos_half.
    auto.
  - move => P Q [del1 H1] [del2 H2].
    exists (mkposreal _ (Rmin_stable_in_posreal del1 del2 )).
    move => g gbd.
    split.
    + apply: H1 => x Dx.
      apply: ball_le; last apply gbd; simpl; auto.
      apply: Rmin_l.
    + apply: H2 => x Dx.
      apply: ball_le; last apply gbd; simpl; auto.
      apply: Rmin_r.
  - move => P Q impl [del H].
    exists del => g gbd.
    apply: impl.
    apply H.
    auto.
Qed.

Lemma uniformly_on_subset : forall (E1 E2: U -> Prop) f ,
  (forall z, E1 z -> E2 z) ->
  filter_le (uniformly_on E2 f) (uniformly_on E1 f).
Proof.
  move => E1 E2 f sub P [del H].
  exists del => g gbd.
  apply: H.
  move => x E1x.
  apply gbd.
  apply sub.
  auto.
Qed.

Lemma global_le_local : forall (E: U -> Prop) f ,
  filter_le (locally f) (uniformly_on E f).
Proof.
  move => E1 f P [del H].
  exists del => g gbd.
  rewrite /ball /= /fct_ball in gbd.
  apply: H => *.
  apply gbd.
Qed.

Lemma uniformly_on_union : forall (E1 E2: U -> Prop) f P Q,
  uniformly_on E1 f P -> 
  uniformly_on E2 f Q -> 
  uniformly_on (fun q => E1 q \/ E2 q) f (fun g => P g /\ Q g).
Proof.
  move => E1 E2 f P Q [del1 UE1] [del2 UE2].

  exists (mkposreal _ (Rmin_stable_in_posreal del1 del2 )).
  move => g gbd.
  split.
  + apply UE1 => *.
    apply: ball_le; last apply gbd; simpl; auto.
    apply: Rmin_l.
  + apply UE2 => *.
    apply: ball_le; last apply gbd; simpl; auto.
    apply: Rmin_r.
Qed.

Definition uniformly_on_family 
  (Fam: ((U -> Prop) -> Prop)) f (P:(U -> V) -> Prop): Prop :=
  exists (l: list ({ (E, P):(_ * _) | 
            Fam E /\ (uniformly_on E f P) } )),
    forall g,
      List.Forall (fun z => (snd (proj1_sig z)) g ) l -> P g.

Instance uniformly_on_family_filter: forall (Fam: (U -> Prop) -> Prop) f,
  (exists E, Fam E) ->
  ProperFilter (uniformly_on_family Fam f).
Proof.
  move => Fam f [E0 FamE0].
  constructor;[|constructor].
  - move => P //= [l H] .
    exists f.
    apply H.
    apply/ Forall_forall.
    case => [[??][??]] *.
    apply: uniformly_on_self.
    eauto.
  - have H: Fam E0 /\ (uniformly_on E0 f (fun => True)) by
      split; [apply FamE0| apply filter_true ].
    exists [exist _ (E0,(fun => True)) H] .
    auto.
  - move => P Q [lP Hp] [lQ Hq].
    exists (lP ++ lQ).
    move => g /Forall_forall Hg.
    split.
    + apply Hp.
      apply/Forall_forall => x xIn.
      apply Hg.
      apply in_or_app.
      auto.
    + apply Hq.
      apply/Forall_forall => x xIn.
      apply Hg.
      apply in_or_app.
      auto.
  - move => P Q impl [l H].
    exists l.
    move => *.
    apply impl.
    auto.
Qed.

Lemma family_le_on_one : forall E f (Fam:(U -> Prop) -> Prop), Fam E ->
  filter_le (uniformly_on_family Fam f) (uniformly_on E f).
Proof.
  move => E f Fam FamE P H.
  have H': Fam E /\ uniformly_on E f P by split; auto.
  exists [exist _ (E,P) H'].
  move => g /Forall_forall.
  move => /(_ (exist _ (E,P) H')).
  apply.
  constructor.
  auto.
Qed.

Lemma filterlim_on_family {T: UniformSpace}: 
  forall (Fam: (U -> Prop) -> Prop) (f_: T -> U -> V) flim F {FF: Filter F},
  (forall (E: U -> Prop), Fam E -> filterlim (f_) F (uniformly_on E flim)) <-> 
  filterlim (f_) F (uniformly_on_family Fam flim) .  
Proof.
  move => Fam f_ flim F FF.
  split. 
  {
    move => all P [l+]. 
    move: l P.
    elim.
    - move => ? H. 
      apply: filter_imp; last by apply filter_true.
      move => *.
      apply H.
      apply Forall_nil.
    - move => a l IH P H.
      have {}H: forall g : U -> V,
            ((`a).2 g) /\ (List.Forall (fun z => (` z).2 g) l) ->
            P g by
         move => *; apply H; apply Forall_cons; tauto.
      apply (filter_imp _ P H).
      apply filter_and.
      + clear H. move: a => [[??][??]].
        apply: all; eauto.
      + apply IH; auto.
  }
  {
    move => H E FamE.
    apply: filterlim_filter_le_2; last by apply H.
    apply family_le_on_one.
    auto.
  }
Qed.

Definition fam_union (Fam :(U -> Prop ) -> Prop) (P: U -> Prop): Prop := 
  exists l, List.Forall Fam l /\ 
  (forall u, P u <-> List.Exists (fun E => E u) l).
  
Lemma fam_union_aux: forall (Fam :(U -> Prop ) -> Prop) f r E Q ,
  (exists E , Fam E) ->
  uniformly_on E f Q ->
  List.Forall Fam r /\ (forall u : U, E u <-> Exists (@^~ u) r) ->
  uniformly_on_family Fam f Q.
Proof.
  move => Fam  f +++ [E0 FamE0].
  have?:Filter (uniformly_on_family (Fam) f). {
    apply uniformly_on_family_filter.
    exists E0.
    auto.
  }
  elim. {
    move => E  Q unifQ [_  H'].
    case: unifQ => [? R].
    apply: (filter_imp _ _ R).
    apply: (filter_imp (fun=> True)_ ); last by apply filter_true.
    move => x _ y .
    rewrite H' Exists_nil; tauto.
  }
  move => E l IH E' Q [del H] [fams Eunion].
  have Hunion:forall g : U -> V, 
    ((forall x : U, E x -> ball (f x) del (g x)) /\
     (forall x : U, (Exists (@^~x) l) -> ball (f x) del (g x))) ->
     Q g. {
       move => g [HE HE'].
       apply H => x.
       rewrite Eunion.
       rewrite Exists_cons.
       case => ?; auto.
  }
  apply: (filter_imp _ _ Hunion).
  inversion fams.
  subst.
  apply: filter_and.
  - apply: family_le_on_one.
    apply H2.
    exists del => *; auto.
  - apply (IH (fun u => Exists (@^~ u) l)).
    + exists del => *; auto.
    + repeat split; auto.
Qed.
Lemma fam_union_singleton: forall (Fam :(U -> Prop ) -> Prop) E, 
  Fam E -> fam_union Fam E.
Proof.
  move => Fam E FamE.
  exists [E].
  split; auto.
  move => *; split; auto.
  rewrite Exists_cons Exists_nil.
  move => [|]; tauto.
Qed.

Lemma fam_union_equiv:
  forall (Fam: (U -> Prop) -> Prop) (f: U -> V) P,
  (exists E , Fam E) ->
  uniformly_on_family Fam f P <-> 
  uniformly_on_family (fam_union Fam) f P .
Proof.
  move => Fam  f P [E0 FamE0].
  have?:Filter (uniformly_on_family (fam_union Fam) f). {
    apply uniformly_on_family_filter.
    exists E0.
    by apply fam_union_singleton.
  }
  have?:Filter (uniformly_on_family (Fam) f). {
    apply uniformly_on_family_filter.
    exists E0.
    auto.
  }
  split. {
    case => l +.
    move:P.
    elim: l; first 
      by (move => *; exists []; auto).
    move => a l IH P H.
    have {}H: forall g : U -> V,
          ((`a).2 g) /\ (List.Forall (fun z => (` z).2 g) l) ->
          P g by
       move => *; apply H; apply Forall_cons; tauto.
    apply: (filter_imp _ _ H).
    apply: filter_and; last by apply IH.
    move: a H => [[E Q][FamE unifQ]] H.
    simpl in *.
    have Hf: fam_union Fam E /\ uniformly_on E f Q by
      split; [apply fam_union_singleton| ].


    exists [exist _ ( E , Q ) Hf].
    move => g /Forall_forall.
    move => /(_ (exist _ (E,Q) Hf)).
    apply.
    constructor.
    auto.
  }
  {
    move => [l +].
    move: P.
    elim:l; first by 
      move => *; exists []; auto.
    move => a l IH P H.
    have {}H: forall g : U -> V,
          ((`a).2 g) /\ (List.Forall (fun z => (` z).2 g) l) ->
          P g by
       move => *; apply H; apply Forall_cons; tauto.
    apply: (filter_imp _ _ H).
    apply: filter_and; last by apply IH.
    move: a H => [[E Q][[r Famr] unifQ]] H.
    simpl in *.
    apply: fam_union_aux.
    exists E0; auto.
    apply unifQ.
    apply Famr.
  }

Qed.

Lemma filterlim_compose_aux {T: UniformSpace} {T': UniformSpace}: 
  forall (Fam: (U -> Prop) -> Prop) (f_: T -> U -> V) flim F {FF: Filter F} (g: T' -> U),
  filterlim (f_) F (uniformly_on_family Fam flim) ->
  (exists E, Fam E /\ (forall t':T', E (g t'))) ->
  filterlim (fun t u => f_ t (g u)) F (@locally (fct_UniformSpace T' V) (fun u => flim (g u))) .
Proof.
  move => Fam f_ flim F FF g + [E [Efam gcover]] P loc.
  move => /(_ (fun h => P(fun t => h (g t) ))).
  apply.
  set P' := fun h => P (fun t => h (g t)).
  have Ef: uniformly_on E flim P'. {
    move: loc => [del H]. 
    exists del.
    move => h hball.
    apply H.
    rewrite /ball /= /fct_ball in hball .
    rewrite /ball /= /fct_ball => t.
    apply hball.
    apply gcover.
  }
  apply: family_le_on_one; eauto.
Qed.

Lemma filterlim_compose_fam {T: UniformSpace} {T': UniformSpace}: 
  forall (Fam: (U -> Prop) -> Prop) (f_: T -> U -> V) flim F {FF: Filter F} (g: T' -> U),
  (exists E , Fam E) ->
  filterlim (f_) F (uniformly_on_family Fam flim) ->
  (exists E, fam_union Fam E /\ (forall t':T', E (g t'))) ->
  filterlim (fun t u => f_ t (g u)) F (@locally (fct_UniformSpace T' V) (fun u => flim (g u))) .
Proof.
  move => Fam *.
  apply (@filterlim_compose_aux _ _ (fam_union Fam)); auto.
  apply: filterlim_filter_le_2; last by eauto.
  move => P.
  apply fam_union_equiv.
  auto.
Qed.

End UniformOn.

Definition square_in (D: C -> Prop) (P:C -> Prop) : Prop := 
  (forall z, P z -> D z) /\
  (exists a b c d, 
    (forall z, P z <-> a <= z.1 <= b /\ c <= z.2 <= d)).

Definition compactly D (f: C -> C) := uniformly_on_family (square_in D) f.

Lemma compactly_non_trivial: forall D, open D -> 
  (exists z0, D z0) ->
  exists P, square_in D P.
Proof.
  move => D openD [z0 Dz0].
  have := openD z0 Dz0.
  move => [del H].
  have?:= cond_pos del.
  pose P := fun z => z0.1 - del/2 <= z.1 <= z0.1 + del/2 /\
                     z0.2 - del/2 <= z.2 <= z0.2 + del/2.
  exists P.
  split.
  2: do 4 eexists; rewrite /P => z; apply reflexivity.
  move => z [/Rabs_le_between' P1 /Rabs_le_between' P2]. 
  apply H.
  split; (apply (@Rle_lt_trans _ (del/2)); last by lra);
  [apply P1 | apply P2].
Qed.
     
Instance compactly_filter: forall (D: C -> Prop) f,
  open D ->
  (exists z0, D z0) ->
  ProperFilter (compactly D f).
Proof.
  move => D f op ex.
  apply uniformly_on_family_filter.
  apply compactly_non_trivial;
  auto.
Qed.

Lemma not_not_impl : forall (P Q:Prop), (P -> Q) -> (~ ~ P -> ~ ~ Q).
move => P Q.
tauto.
Qed.

Open Scope program_scope.
Lemma path_in_circles: forall (g: R -> C) D a b, 
  open D -> 
  a < b ->
  (forall z, D z \/ ~D z) ->
  (forall t, a <= t <= b -> D (g t)) ->
  (forall t, a <= t <= b -> continuous g t) ->
  (~ ~ exists l, 
   (List.Forall (square_in D) l ) /\
   (forall t, a <= t <= b -> List.Exists (fun E => E (g t)) l)).
Proof.
  move => g D a b openD aleb decD inD cts.

  have inlocD: forall t, ~t < a -> ~ b < t -> locally (g t) D by
    ( move => *; apply openD; apply inD; lra).

  have eps: forall t, 
     {d: posreal | a <= t <= b -> forall y, ball (g t) d y -> D y }. {
      move => t.
      have := locally_ex_dec (g t) D decD. 
      destruct (Rlt_dec t a); first by
        move => _; exists pos_half; lra.
      destruct (Rlt_dec b t); first by
        move => _; exists pos_half; lra.
      case;first by (apply openD; apply inD; lra). 
      move => del H.
      exists del.
      move => *. 
      by apply H.
  }

  have: {delta: R -> posreal | forall t, a <= t <= b ->
      (forall t', a <= t' <= b -> ball t (delta t) t' -> 
         ball_norm (g t) (pos_div_2 (` (eps t))) (g t')) /\ 
      (forall z, ball (g t) (` (eps t)) z -> D z)
  }. {

    pose delta := (unifcont_normed_1d g a b cts (pos_div_2 (` (eps _)))).
  
    exists (fun t => (proj1_sig (delta t))).
    move => t tbd.
    split.
    - move => t' t'bd H.
      apply (proj2_sig (delta t)); auto.
    - move => z zball.
      apply (proj2_sig (eps t)); auto.
  }
  case => delta H.
  have := compactness_list 1 (a, tt) (b, tt) (fun t => delta (fst t)).
  apply not_not_impl.
  case.
  move => l H'.

  pose del_sqr := fun t z => 
    let eps' := pos_div_2 (proj1_sig (eps t)) in
    (g t).1 - eps' <= z.1 <= (g t).1 + eps' /\
    (g t).2 - eps' <= z.2 <= (g t).2 + eps'.
  exists (map (compose del_sqr fst) 
         (filter (fun l => Rle_dec a l.1 && Rle_dec l.1 b)l)).
  split. {
    apply/Forall_forall => P.
    move => /in_map_iff [t0 [<- /filter_In [int0
      /andP [/RleP ? /RleP ?]]]].
    rewrite/compose //=.
    split.
    - move => z [/Rabs_le_between' P1 /Rabs_le_between' P2]. 
      move: H => /(_ t0.1 (ltac:(lra))) H.
      apply H.
      split.
      + apply: Rle_lt_trans; first by apply P1.
        simpl.
        rewrite Rlt_div_l; try lra.
        rewrite -[x in x < _]Rmult_1_r.
        apply Rmult_lt_compat_l; try lra.
        apply cond_pos.
      + apply: Rle_lt_trans; first by apply P2.
        simpl.
        rewrite Rlt_div_l; try lra.
        rewrite -[x in x < _]Rmult_1_r.
        apply Rmult_lt_compat_l; try lra.
        apply cond_pos.
    - do 4 eexists. 
      move => z.
      rewrite /del_sqr.
      reflexivity.
  }

  move => x xbd.
  apply/ Exists_exists.
  move: H' => /(_ (x,tt)).
  case; first by simpl.
  move => t0 [t0In [t0bd t0close]]. 
   destruct t0. simpl in *.
  exists (del_sqr r).
  split.
  - apply/ in_map_iff.
    exists (r,t).
    split; first by simpl.
    apply/ filter_In.
    split; first by tauto.
    apply /andP. split; apply/RleP; simpl; apply t0bd.
  - rewrite /del_sqr -?Rabs_le_between'.
    have: (Rmax (Rabs (g x - g r).1) (Rabs (g x - g r).2) <= ` (eps r) /2).
    2: { 
      move => Hmax.
      split.
      + apply: Rle_trans; last apply Hmax.
        apply Rmax_l.
      + apply: Rle_trans; last apply Hmax.
        apply Rmax_r.
    }
    apply: Rle_trans; first by apply Rmax_Cmod.
  move: H => /(_ r (ltac:(lra))) [/(_ x xbd) H _].
  left.
  apply H.
  apply t0close.
Qed.

Lemma filterlim_compose_path forall D
  (f_: T -> C -> C) flim F {FF: Filter F} (g: R -> C),
  open D,
  (exists z0, D z0) ->
  filterlim (f_) F (compactly flim) ->
  (exists E, fam_union Fam E /\ (forall t':T', E (g t'))) ->
  filterlim (fun t u => f_ t (g u)) F (@locally (fct_UniformSpace T' V) (fun u => flim (g u))) .