
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


Require Import domains cauchy_riemann path_independence cauchy_integral.

Lemma filterlim_CInt: forall f gamma
  F (fun r => cts_on_contour gamma f r) -> 
  filterlim (f r) = 
  filterlim (fun r => CInt (g:= gamma) (f r) ) F 
