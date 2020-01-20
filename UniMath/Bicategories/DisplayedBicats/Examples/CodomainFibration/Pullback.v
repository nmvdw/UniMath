(** Pullback of types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Local Open Scope cat.

(**
Definition of when something is a pullback square.
It needs to satisfy a universal property for the 1-cells (existence of maps).
There needs to be a universal property for the 2-cells (uniqueness of maps).
There also needs to be a universal property saying that such 2-cells are unique.
 *)
Section IsPullback.
  Context {X Y Z : one_type}
          (f : X → Z) (g : Y → Z)
          (P : one_type)
          (pb_pr1 : P → X)
          (pb_pr2 : P → Y)
          (pb_commute : ∏ (z : P), f(pb_pr1 z) = g(pb_pr2 z)).

  Definition has_ump
    : UU
    := ∏ (Q : one_type)
         (p : Q → X) (q : Q → Y)
         (e : ∏ (z : Q), f(p z) = g(q z)),
       ∑ (u : Q → P),
       ∑ (upr1 : ∏ (z : Q), pb_pr1(u z) = p z),
       ∑ (upr2 : ∏ (z : Q), pb_pr2(u z) = q z),
       ∏ (z : Q),
       pb_commute (u z)
       @ maponpaths g (upr2 z)
       =
       maponpaths f (upr1 z)
       @ e z.

  Definition has_ump_path
    : UU
    := ∏ (Q : one_type)
         (p : Q → X) (q : Q → Y)
         (e : ∏ (z : Q), f(p z) = g(q z))
         (u₁ u₂ : Q → P)
         (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
         (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
         (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
         (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
         (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                           @ maponpaths g (qu₁ z)
                           =
                           maponpaths f (pu₁ z)
                           @ e z)
         (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                           @ maponpaths g (qu₂ z)
                           =
                           maponpaths f (pu₂ z)
                           @ e z),
       ∑ (eu : u₁ ~ u₂),
       (∏ (z : Q),
        maponpaths
          pb_pr1
          (eu z)
        =
        pu₁ z @ !(pu₂ z))
        ×
        (∏ (z : Q),
         maponpaths
           pb_pr2
           (eu z)
         =
         qu₁ z @ !(qu₂ z)).

  Definition has_ump_homot
    : UU
    := ∏ (Q : UU)
         (p : Q → X) (q : Q → Y)
         (e : ∏ (z : Q), f(p z) = g(q z))
         (u₁ u₂ : Q → P)
         (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
         (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
         (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
         (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
         (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                           @ maponpaths g (qu₁ z)
                           =
                           maponpaths f (pu₁ z)
                           @ e z)
         (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                           @ maponpaths g (qu₂ z)
                           =
                           maponpaths f (pu₂ z)
                           @ e z)
         (e₁ e₂ : u₁ ~ u₂)
         (pr1_e₁ : ∏ (z : Q),
                   maponpaths
                     pb_pr1
                     (e₁ z)
                   =
                   pu₁ z @ !(pu₂ z))
         (pr1_e₂ : ∏ (z : Q),
                   maponpaths
                     pb_pr1
                     (e₂ z)
                   =
                   pu₁ z @ !(pu₂ z))
         (pr2_e₁ : ∏ (z : Q),
                   maponpaths
                     pb_pr2
                     (e₁ z)
                   =
                   qu₁ z @ !(qu₂ z))
         (pr2_e₂ : ∏ (z : Q),
                   maponpaths
                     pb_pr2
                     (e₂ z)
                   =
                   qu₁ z @ !(qu₂ z)),
       e₁ ~ e₂.

  Definition is_pb
    : UU
    := has_ump
       × has_ump_path
       × has_ump_homot.
End IsPullback.

(** Projections for being a pullback *)
Section ProjectionsIsPullback.
  Context {X Y Z : one_type}
          {f : X → Z} {g : Y → Z}
          {P : one_type}
          {pb_pr1 : P → X}
          {pb_pr2 : P → Y}
          {pb_commute : ∏ (z : P), f(pb_pr1 z) = g(pb_pr2 z)}
          (Hp : is_pb f g P pb_pr1 pb_pr2 pb_commute).

  Definition is_pb_ump
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             (e : ∏ (z : Q), f(p z) = g(q z))
    : Q → P
    := pr1 (pr1 Hp Q p q e).

  Definition pr1_is_pb_ump
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             (e : ∏ (z : Q), f(p z) = g(q z))
    : ∏ (z : Q), pb_pr1(is_pb_ump e z) = p z
    := pr12 (pr1 Hp Q p q e).

  Definition pr2_is_pb_ump
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             (e : ∏ (z : Q), f(p z) = g(q z))
    : ∏ (z : Q), pb_pr2(is_pb_ump e z) = q z
    := pr122 (pr1 Hp Q p q e).

  Definition commute_is_pb_ump
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             (e : ∏ (z : Q), f(p z) = g(q z))
    : ∏ (z : Q),
      pb_commute (is_pb_ump e z)
      @ maponpaths g (pr2_is_pb_ump e z)
      =
      maponpaths f (pr1_is_pb_ump e z)
      @ e z
    := pr222 (pr1 Hp Q p q e).

  Definition is_pb_ump_path
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             (e : ∏ (z : Q), f(p z) = g(q z))
             (u₁ u₂ : Q → P)
             (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
             (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
             (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
             (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
             (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                               @ maponpaths g (qu₁ z)
                               =
                               maponpaths f (pu₁ z)
                               @ e z)
             (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                               @ maponpaths g (qu₂ z)
                               =
                               maponpaths f (pu₂ z)
                                          @ e z)
    : u₁ ~ u₂
    := pr1 (pr12 Hp Q p q e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂).

  Definition pr1_is_pb_ump_path
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             (e : ∏ (z : Q), f(p z) = g(q z))
             (u₁ u₂ : Q → P)
             (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
             (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
             (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
             (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
             (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                                         @ maponpaths g (qu₁ z)
                               =
                               maponpaths f (pu₁ z)
                                          @ e z)
             (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                                         @ maponpaths g (qu₂ z)
                               =
                               maponpaths f (pu₂ z)
                                          @ e z)
    : ∏ (z : Q),
      maponpaths
        pb_pr1
        (is_pb_ump_path e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂ z)
      =
      pu₁ z @ !(pu₂ z)
    := pr12 (pr12 Hp Q p q e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂).

  Definition pr2_is_pb_ump_path
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             {e : ∏ (z : Q), f(p z) = g(q z)}
             {u₁ u₂ : Q → P}
             (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
             (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
             (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
             (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
             (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                                         @ maponpaths g (qu₁ z)
                               =
                               maponpaths f (pu₁ z)
                                          @ e z)
             (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                                         @ maponpaths g (qu₂ z)
                               =
                               maponpaths f (pu₂ z)
                                          @ e z)
    : ∏ (z : Q),
      maponpaths
        pb_pr2
        (is_pb_ump_path e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂ z)
      =
      qu₁ z @ !(qu₂ z)
    := pr22 (pr12 Hp _ _ _ _ _ _ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂).

  Definition is_pb_homot
             {Q : one_type}
             {p : Q → X} {q : Q → Y}
             {e : ∏ (z : Q), f(p z) = g(q z)}
             {u₁ u₂ : Q → P}
             {pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z}
             {pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z}
             {qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z}
             {qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z}
             (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                               @ maponpaths g (qu₁ z)
                               =
                               maponpaths f (pu₁ z)
                               @ e z)
             (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                               @ maponpaths g (qu₂ z)
                               =
                               maponpaths f (pu₂ z)
                               @ e z)
             {e₁ e₂ : u₁ ~ u₂}
             (pr1_e₁ : ∏ (z : Q),
                       maponpaths
                         pb_pr1
                         (e₁ z)
                       =
                       pu₁ z @ !(pu₂ z))
             (pr1_e₂ : ∏ (z : Q),
                       maponpaths
                         pb_pr1
                         (e₂ z)
                       =
                       pu₁ z @ !(pu₂ z))
             (pr2_e₁ : ∏ (z : Q),
                       maponpaths
                         pb_pr2
                         (e₁ z)
                       =
                       qu₁ z @ !(qu₂ z))
             (pr2_e₂ : ∏ (z : Q),
                       maponpaths
                         pb_pr2
                         (e₂ z)
                       =
                       qu₁ z @ !(qu₂ z))
    : e₁ ~ e₂.
  Proof.
    exact (pr22 Hp _ _ _ _ _ _ _ _ _ _ cu₁ cu₂ _ _ pr1_e₁ pr1_e₂ pr2_e₁ pr2_e₂).
  Defined.
End ProjectionsIsPullback.

(** Pullbacks *)
Definition pb
           {X Y Z : UU}
           (f : X → Z) (g : Y → Z)
  : UU
  := ∑ (x : X) (y : Y), f x = g y.

(** `hlevel` of pullbacks *)
Definition pb_isofhlevel
           {X Y Z : UU}
           (f : X → Z) (g : Y → Z)
           {n : nat}
           (hX : isofhlevel n X)
           (hY : isofhlevel n Y)
           (hZ : isofhlevel n Z)
  : isofhlevel n (pb f g).
Proof.
  use isofhleveltotal2.
  - exact hX.
  - intro x.
    use isofhleveltotal2.
    * exact hY.
    * intro y.
      apply hlevelntosn.
      exact hZ.
Defined.

(** Definition of the pullback *)
Definition pb_one_types
           {X Y Z : one_type}
           (f : X → Z) (g : Y → Z)
  : one_type.
Proof.
  use make_one_type.
  - exact (pb f g).
  - abstract (use pb_isofhlevel ; apply one_type_isofhlevel).
Defined.

(** Projections *)
Section Projections.
  Context {X Y Z : UU}
          {f : X → Z} {g : Y → Z}.

  Definition pb_pr1
    : pb f g → X
    := λ z, pr1 z.

  Definition pb_pr2
    : pb f g → Y
    := λ z, pr12 z.

  Definition pb_commute
    : ∏ (z : pb f g), f(pb_pr1 z) = g(pb_pr2 z)
    := λ z, pr22 z.
End Projections.

(** Builder for elements *)
Definition pb_pair
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           (x : X) (y : Y)
           (p : f x = g y)
  : pb f g
  := (x ,, y ,, p).

(** Builder for paths *)
Definition path_pb
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           {x x' : X} {y y' : Y}
           {p : f x = g y}
           {p' : f x' = g y'}
           (h₁ : x = x') (h₂ : y = y')
           (h₃ : p @ maponpaths g h₂ = maponpaths f h₁ @ p')
  : pb_pair x y p
    =
    pb_pair x' y' p'.
Proof.
  induction h₁ ; induction h₂.
  exact (maponpaths (λ z, x ,, y ,, z) (!(pathscomp0rid _) @ h₃)).
Defined.

(** Builder for homotopies *)
Definition homot_pb
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           {x x' : X} {y y' : Y}
           {p : f x = g y}
           {p' : f x' = g y'}
           {h₁ h₁' : x = x'} (e₁ : h₁ = h₁')
           {h₂ h₂' : y = y'} (e₂ : h₂ = h₂')
           (h₃ : p @ maponpaths g h₂ = maponpaths f h₁ @ p')
  : path_pb h₁ h₂ h₃
    =
    path_pb
      h₁' h₂'
      (maponpaths
         (λ z, p @ maponpaths g z)
         (!e₂)
       @ h₃
       @ maponpaths
           (λ z, maponpaths f z @ p')
           e₁).
Proof.
  induction e₁ ; induction e₂.
  simpl.
  apply maponpaths.
  exact (!(pathscomp0rid _)).
Qed.

(** Eta for points of pullbacks *)
Definition pb_eta
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           (x : pb f g)
  : x = pb_pair (pb_pr1 x) (pb_pr2 x) (pb_commute x)
  := idpath x.

(** Eta for paths of pullbacks *)
Definition path_pb_eta_commute
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           {x y : pb f g}
           (p : x = y)
  : pr22 x @ maponpaths g (maponpaths pb_pr2 p)
    =
    maponpaths f (maponpaths pb_pr1 p) @ pr22 y.
Proof.
  induction p.
  apply pathscomp0rid.
Defined.

Definition path_pb_eta
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           {x y : pb f g}
           (p : x = y)
  : p
    =
    path_pb
      (maponpaths pb_pr1 p)
      (maponpaths pb_pr2 p)
      (path_pb_eta_commute p).
Proof.
  induction p.
  cbn.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Defined.

(** Builder for homotopies of pullbacks *)
Definition homot_pb_one_types
           {X Y Z : one_type}
           {f : X → Z} {g : Y → Z}
           {x y : pb_one_types f g}
           {p q : x = y}
           (h₁ : maponpaths pb_pr1 p
                 =
                 maponpaths pb_pr1 q)
           (h₂ : maponpaths pb_pr2 p
                 =
                 maponpaths pb_pr2 q)
  : p = q.
Proof.
  refine (path_pb_eta p @ _ @ !(path_pb_eta q)).
  etrans.
  {
    exact (homot_pb h₁ h₂ _).
  }
  apply maponpaths.
  apply (proofirrelevance _ (one_type_isofhlevel _ _ _ _ _)).
Qed.

(** Properties of paths on pullbacks *)
Definition maponpaths_pr1_path_pb
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           (x x' : X) (y y' : Y)
           (p : f x = g y)
           (p' : f x' = g y')
           (h₁ : x = x') (h₂ : y = y')
           (h₃ : p @ maponpaths g h₂ = maponpaths f h₁ @ p')
  : maponpaths
      pb_pr1
      (path_pb h₁ h₂ h₃)
    =
    h₁.
Proof.
  induction h₁ ; induction h₂ ; cbn in *.
  etrans.
  {
    exact (maponpathscomp
             (λ z, x,, y,, z)
             pb_pr1
             (! pathscomp0rid p @ h₃)).
  }
  unfold funcomp ; cbn.
  apply maponpaths_for_constant_function.
Qed.

Definition maponpaths_pr2_path_pb
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           (x x' : X) (y y' : Y)
           (p : f x = g y)
           (p' : f x' = g y')
           (h₁ : x = x') (h₂ : y = y')
           (h₃ : p @ maponpaths g h₂ = maponpaths f h₁ @ p')
  : maponpaths
      pb_pr2
      (path_pb h₁ h₂ h₃)
    =
    h₂.
Proof.
  induction h₁ ; induction h₂ ; cbn in *.
  etrans.
  {
    exact (maponpathscomp
             (λ z, x,, y,, z)
             pb_pr2
             (! pathscomp0rid p @ h₃)).
  }
  unfold funcomp ; cbn.
  apply maponpaths_for_constant_function.
Qed.

(**
Universal property of pullback.
We have multiple universal properties.
The first one gives a constructor for 1-cells.
This expresses the usual universal property of pullbacks.
 *)
Section PullBackUMPOneCells.
  Context {X Y Z : UU}
          (f : X → Z) (g : Y → Z)
          {Q : UU}
          {p : Q → X} {q : Q → Y}
          (e : ∏ (z : Q), f(p z) = g(q z)).

  Definition pb_ump
    : Q → pb f g
    := λ z, pb_pair (p z) (q z) (e z).

  Definition pb_ump_pr1
             (z : Q)
    : pb_pr1(pb_ump z) = p z
    := idpath _.

  Definition pb_ump_pr2
             (z : Q)
    : pb_pr2(pb_ump z) = q z
    := idpath _.

  Definition pb_ump_commute
             (z : Q)
    : pb_commute (pb_ump z) = e z
    := idpath _.
End PullBackUMPOneCells.

(**
This is the second universal property of pullbacks.
It expresses the uniqueness
 *)
Section PullBackUMPTwoCells.
  Context {X Y Z : UU}
          (f : X → Z) (g : Y → Z)
          {Q : UU}
          {p : Q → X} {q : Q → Y}
          (e : ∏ (z : Q), f(p z) = g(q z))
          (u₁ u₂ : Q → pb f g)
          (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
          (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
          (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
          (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
          (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                            @ maponpaths g (qu₁ z)
                            =
                            maponpaths f (pu₁ z)
                            @ e z)
          (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                            @ maponpaths g (qu₂ z)
                            =
                            maponpaths f (pu₂ z)
                            @ e z).

  Definition pb_ump_path
    : u₁ ~ u₂.
  Proof.
    intros z.
    use path_pb.
    - exact (pu₁ z @ !(pu₂ z)).
    - exact (qu₁ z @ !(qu₂ z)).
    - etrans.
      {
        apply maponpaths.
        apply maponpathscomp0.
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (cu₁ z).
      }
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp0.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      use hornRotation.
      refine (!_).
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          refine (!_).
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply pathsinv0inv0.
      }
      etrans.
      {
        apply maponpaths.
        exact (cu₂ z).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply pathsinv0l.
      }
      apply idpath.
  Defined.

  Definition maponpaths_pr1_pb_path
             (z : Q)
    : maponpaths
        pb_pr1
        (pb_ump_path z)
      =
      pu₁ z @ !(pu₂ z).
  Proof.
    apply maponpaths_pr1_path_pb.
  Qed.

  Definition maponpaths_pr2_pb_path
             (z : Q)
    : maponpaths
        pb_pr2
        (pb_ump_path z)
      =
      qu₁ z @ !(qu₂ z).
  Proof.
    apply maponpaths_pr2_path_pb.
  Qed.
End PullBackUMPTwoCells.

(**
Universal property of the pullback.
Lastly, we have a universal property for the homotopies.
It says the path from the universal property for paths is unique.
 *)
Section PullBackUMPHomots.
  Context {X Y Z : one_type}
          (f : X → Z) (g : Y → Z)
          {Q : UU}
          {p : Q → X} {q : Q → Y}
          (e : ∏ (z : Q), f(p z) = g(q z))
          (u₁ u₂ : Q → pb f g)
          (pu₁ : ∏ (z : Q), pb_pr1(u₁ z) = p z)
          (pu₂ : ∏ (z : Q), pb_pr1(u₂ z) = p z)
          (qu₁ : ∏ (z : Q), pb_pr2(u₁ z) = q z)
          (qu₂ : ∏ (z : Q), pb_pr2(u₂ z) = q z)
          (cu₁ : ∏ (z : Q), pb_commute(u₁ z)
                            @ maponpaths g (qu₁ z)
                            =
                            maponpaths f (pu₁ z)
                            @ e z)
          (cu₂ : ∏ (z : Q), pb_commute(u₂ z)
                            @ maponpaths g (qu₂ z)
                            =
                            maponpaths f (pu₂ z)
                            @ e z)
          (e₁ e₂ : u₁ ~ u₂)
          (pr1_e₁ : ∏ (z : Q),
                    maponpaths
                      pb_pr1
                      (e₁ z)
                    =
                    pu₁ z @ !(pu₂ z))
          (pr1_e₂ : ∏ (z : Q),
                    maponpaths
                      pb_pr1
                      (e₂ z)
                    =
                    pu₁ z @ !(pu₂ z))
          (pr2_e₁ : ∏ (z : Q),
                    maponpaths
                      pb_pr2
                      (e₁ z)
                    =
                    qu₁ z @ !(qu₂ z))
          (pr2_e₂ : ∏ (z : Q),
                    maponpaths
                      pb_pr2
                      (e₂ z)
                    =
                    qu₁ z @ !(qu₂ z)).

  Definition pb_ump_homot
    : e₁ ~ e₂.
  Proof.
    intro z.
    use homot_pb_one_types.
    - exact (pr1_e₁ z @ !(pr1_e₂ z)).
    - exact (pr2_e₁ z @ !(pr2_e₂ z)).
  Qed.
End PullBackUMPHomots.

Definition pb_is_pb
           {X Y Z : one_type}
           (f : X → Z) (g : Y → Z)
  : is_pb f g (pb_one_types f g) pb_pr1 pb_pr2 pb_commute.
Proof.
  refine (_ ,, _ ,, _).
  - intros Q p q e.
    simple refine (_ ,, _ ,, _ ,, _).
    + exact (pb_ump f g e).
    + apply pb_ump_pr1.
    + apply pb_ump_pr2.
    + intro z.
      etrans.
      {
        apply pathscomp0rid.
      }
      exact (pb_ump_commute f g e z).
  - intros Q p q e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂.
    simple refine (_ ,, _ ,, _).
    + exact (pb_ump_path f g e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂).
    + apply maponpaths_pr1_pb_path.
    + simpl ; apply maponpaths_pr2_pb_path.
  - intros Q p q e u₁ u₂ pu₁ pu₂ qu₁ qu₂ cu₁ cu₂ e₁ e₂ pr1e₁ pr1e₂ pr2e₁ pr2e₂.
    exact (pb_ump_homot f g u₁ u₂ pu₁ pu₂ qu₁ qu₂ e₁ e₂ pr1e₁ pr1e₂ pr2e₁ pr2e₂).
Defined.
