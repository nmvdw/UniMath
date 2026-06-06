(**

 Operations in a topos

 This file introduces notation for various structure in an elementary topos. Specifically,
 we give notations for products, power sets, and exponentials. The purposes of this notation
 is solely to have a more compact way to write certain morphisms, and most of the notation
 is for definitions already introduced elsewhere.

 Contents
 1. Notation for products
 2. Notation for exponentials
 3. Notation for power objects
 4. Some useful isomorphisms

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.

Declare Scope topos.
Local Open Scope topos.
Delimit Scope topos with topos.

(** * 1. Notation for products *)
Definition topos_prod
           {E : Topos}
           (BP := Topos_BinProducts E)
           (x y : E)
  : E
  := BP x y.

Notation "x × y" := (topos_prod x y) : topos.

Definition topos_pr1
           {E : Topos}
           (BP := Topos_BinProducts E)
           (x y : E)
  : (x × y) --> x
  := BinProductPr1 _ (BP x y).

Definition topos_pr2
           {E : Topos}
           (BP := Topos_BinProducts E)
           (x y : E)
  : (x × y) --> y
  := BinProductPr2 _ (BP x y).

Notation "'π₁'" := (topos_pr1 _ _) : topos.
Notation "'π₂'" := (topos_pr2 _ _) : topos.

Definition topos_pair
           {E : Topos}
           (BP := Topos_BinProducts E)
           {w x y : E}
           (f : w --> x)
           (g : w --> y)
  : w --> (x × y)
  := BinProductArrow E (BP x y) f g.

Definition topos_prod_ar
           {E : Topos}
           {x₁ x₂ y₁ y₂ : E}
           (f : x₁ --> x₂)
           (g : y₁ --> y₂)
  : (x₁ × y₁) --> (x₂ × y₂)
  := BinProductOfArrows _ _ _ f g.

Definition topos_diagonal
           {E : Topos}
           (BP := Topos_BinProducts E)
           (x : E)
  : x --> (x × x)
  := diagonalMap' BP x.

Notation "⟨ f , g ⟩" := (topos_pair f g) : topos.
Notation "f '#×' g" := (topos_prod_ar f g) (at level 75, right associativity) : topos.
Notation "Δ_{ x }" := (topos_diagonal x) : topos.

Proposition topos_pair_pr1
            {E : Topos}
            (BP := Topos_BinProducts E)
            {w x y : E}
            (f : w --> x)
            (g : w --> y)
  : ⟨ f , g ⟩ · π₁ = f.
Proof.
  apply BinProductPr1Commutes.
Qed.

Proposition topos_pair_pr2
            {E : Topos}
            (BP := Topos_BinProducts E)
            {w x y : E}
            (f : w --> x)
            (g : w --> y)
  : ⟨ f , g ⟩ · π₂ = g.
Proof.
  apply BinProductPr2Commutes.
Qed.

Proposition topos_prod_ar_pr1
            {E : Topos}
            {x₁ x₂ y₁ y₂ : E}
            (f : x₁ --> x₂)
            (g : y₁ --> y₂)
  : (f #× g) · π₁ = π₁ · f.
Proof.
  apply BinProductOfArrowsPr1.
Qed.

Proposition topos_prod_ar_pr2
            {E : Topos}
            {x₁ x₂ y₁ y₂ : E}
            (f : x₁ --> x₂)
            (g : y₁ --> y₂)
  : (f #× g) · π₂ = π₂ · g.
Proof.
  apply BinProductOfArrowsPr2.
Qed.

Proposition topos_diagonal_pr1
            {E : Topos}
            (x : E)
  : Δ_{x} · π₁ = identity _.
Proof.
  apply BinProductPr1Commutes.
Qed.

Proposition topos_diagonal_pr2
            {E : Topos}
            (x : E)
  : Δ_{x} · π₂ = identity _.
Proof.
  apply BinProductPr2Commutes.
Qed.

Notation "𝟙" := (Topos_Terminal _) : topos.
Notation "'Ω'" := (Topos_SubobjectClassifier _) : topos.

Proposition topos_pair_eq
            {E : Topos}
            (BP := Topos_BinProducts E)
            {w x y : E}
            {f g : w --> (x × y)}
            (p : f · π₁ = g · π₁)
            (q : f · π₂ = g · π₂)
  : f = g.
Proof.
  use BinProductArrowsEq.
  - exact p.
  - exact q.
Qed.

Proposition topos_pair_comp
            {E : Topos}
            {w₁ w₂ x y : E}
            (s : w₁ --> w₂)
            (f : w₂ --> x)
            (g : w₂ --> y)
  : s · ⟨ f , g ⟩ = ⟨ s · f , s · g ⟩.
Proof.
  use topos_pair_eq.
  - rewrite !assoc'.
    rewrite !topos_pair_pr1.
    apply idpath.
  - rewrite !assoc'.
    rewrite !topos_pair_pr2.
    apply idpath.
Qed.

Proposition topos_pair_id_id
            {E : Topos}
            {x y : E}
  : ⟨ π₁ , π₂ ⟩ = identity (x × y).
Proof.
  use topos_pair_eq.
  - rewrite topos_pair_pr1.
    rewrite id_left.
    apply idpath.
  - rewrite topos_pair_pr2.
    rewrite id_left.
    apply idpath.
Qed.

Proposition topos_prod_ar_comp
            {E : Topos}
            {x₁ x₂ x₃ y₁ y₂ y₃ : E}
            (f₁ : x₁ --> x₂)
            (f₂ : x₂ --> x₃)
            (g₁ : y₁ --> y₂)
            (g₂ : y₂ --> y₃)
  : ((f₁ · f₂) #× (g₁ · g₂)) = (f₁ #× g₁) · (f₂ #× g₂).
Proof.
  refine (!_).
  apply BinProductOfArrows_comp.
Qed.

Proposition topos_prod_ar_comp_r_id_l
            {E : Topos}
            {x₁ x₂ y₁ y₂ y₃ : E}
            (f : x₁ --> x₂)
            (g₁ : y₁ --> y₂)
            (g₂ : y₂ --> y₃)
  : (f #× (g₁ · g₂)) = (f #× g₁) · (identity _ #× g₂).
Proof.
  use topos_pair_eq ; rewrite !assoc'.
  - rewrite !topos_prod_ar_pr1.
    rewrite id_right.
    rewrite topos_prod_ar_pr1.
    apply idpath.
  - rewrite !topos_prod_ar_pr2.
    rewrite !assoc.
    rewrite topos_prod_ar_pr2.
    apply idpath.
Qed.

Proposition topos_prod_ar_comp_r_id_r
            {E : Topos}
            {x₁ x₂ y₁ y₂ y₃ : E}
            (f : x₁ --> x₂)
            (g₁ : y₁ --> y₂)
            (g₂ : y₂ --> y₃)
  : (f #× (g₁ · g₂)) = (identity _ #× g₁) · (f #× g₂).
Proof.
  use topos_pair_eq ; rewrite !assoc'.
  - rewrite !topos_prod_ar_pr1.
    rewrite !assoc.
    rewrite topos_prod_ar_pr1.
    rewrite id_right.
    apply idpath.
  - rewrite !topos_prod_ar_pr2.
    rewrite !assoc.
    rewrite topos_prod_ar_pr2.
    apply idpath.
Qed.

Proposition topos_prod_ar_comp_l_id_l
            {E : Topos}
            {x₁ x₂ x₃ y₁ y₂ : E}
            (f₁ : x₁ --> x₂)
            (f₂ : x₂ --> x₃)
            (g : y₁ --> y₂)
  : ((f₁ · f₂) #× g) = (f₁ #× g) · (f₂ #× identity _).
Proof.
  use topos_pair_eq ; rewrite !assoc'.
  - rewrite !topos_prod_ar_pr1.
    rewrite !assoc.
    rewrite topos_prod_ar_pr1.
    apply idpath.
  - rewrite !topos_prod_ar_pr2.
    rewrite !assoc.
    rewrite topos_prod_ar_pr2.
    rewrite id_right.
    apply idpath.
Qed.

Proposition topos_prod_ar_comp_l_id_r
            {E : Topos}
            {x₁ x₂ x₃ y₁ y₂ : E}
            (f₁ : x₁ --> x₂)
            (f₂ : x₂ --> x₃)
            (g : y₁ --> y₂)
  : ((f₁ · f₂) #× g) = (f₁ #× identity _) · (f₂ #× g).
Proof.
  use topos_pair_eq ; rewrite !assoc'.
  - rewrite !topos_prod_ar_pr1.
    rewrite !assoc.
    rewrite topos_prod_ar_pr1.
    apply idpath.
  - rewrite !topos_prod_ar_pr2.
    rewrite !assoc.
    rewrite topos_prod_ar_pr2.
    rewrite id_right.
    apply idpath.
Qed.

Proposition topos_comp_diagonal
            {E : Topos}
            {x y : E}
            (f : x --> y)
  : f · Δ_{y} = ⟨ f , f ⟩.
Proof.
  use topos_pair_eq ; rewrite !assoc'.
  - rewrite topos_pair_pr1, topos_diagonal_pr1.
    rewrite id_right.
    apply idpath.
  - rewrite topos_pair_pr2, topos_diagonal_pr2.
    rewrite id_right.
    apply idpath.
Qed.

(** * 2. Notation for exponentials *)
Definition topos_exp
           {E : Topos}
           (x y : E)
  : E
  := exp (Exponentials_from_Topos y) x.

Notation "x ^ y" := (topos_exp x y) : topos.

Definition topos_eval
           {E : Topos}
           (x y : E)
  : ((y ^ x) × x) --> y
  := exp_eval_alt (Exponentials_from_Topos x) y.

Notation "'ε'" := (topos_eval _ _) : topos.

Definition topos_lam
           {E : Topos}
           {x y z : E}
           (f : (z × x) --> y)
  : z --> y ^ x
  := exp_lam_alt _ f.

Notation "'Λ'" := topos_lam : topos.

Proposition topos_lam_beta
            {E : Topos}
            {x y z : E}
            (f : (z × x) --> y)
  : (Λ f #× identity _) · ε = f.
Proof.
  apply exp_beta_alt.
Qed.

Proposition topos_lam_eta
            {E : Topos}
            {x y z : E}
            (f : z --> y ^ x)
  : Λ ((f #× identity x) · ε) = f.
Proof.
  exact (exp_lam_app_alt _ _).
Qed.

Proposition topos_lam_funext
            {E : Topos}
            {x y z : E}
            {f g : z --> y ^ x}
            (p : (f #× identity _) · ε = (g #× identity _) · ε)
  : f = g.
Proof.
  use exp_funext_alt.
  intros a h.
  rewrite <- (id_right h).
  rewrite <- (id_left f).
  rewrite <- (id_left g).
  rewrite <- !BinProductOfArrows_comp.
  rewrite !assoc'.
  apply maponpaths.
  clear a h.
  exact p.
Qed.

Proposition topos_lam_subst
            {E : Topos}
            {x y z₁ z₂ : E}
            (f : (z₂ × x) --> y)
            (s : z₁ --> z₂)
  : s · Λ f = Λ (⟨ π₁ · s , π₂ ⟩ · f).
Proof.
  use topos_lam_funext.
  rewrite !topos_prod_ar_comp_l_id_l.
  rewrite !assoc'.
  rewrite !topos_lam_beta.
  apply maponpaths_2.
  use topos_pair_eq.
  - rewrite topos_pair_pr1, topos_prod_ar_pr1.
    apply idpath.
  - rewrite topos_pair_pr2, topos_prod_ar_pr2.
    rewrite id_right.
    apply idpath.
Qed.

(** * 3. Notation for power objects *)
Definition topos_power_obj
           {E : Topos}
           (x : E)
  : E
  := Ω ^ x.

Notation "'ℙ'" := topos_power_obj : topos.

Definition topos_compr
           {E : Topos}
           {x z : E}
           (φ : (z × x) --> Ω)
  : z --> ℙ x
  := Λ φ.

Notation "{{ φ }}" := (topos_compr φ) : topos.

Proposition topos_compr_subst
            {E : Topos}
            {x z₁ z₂ : E}
            (φ : (z₂ × x) --> Ω)
            (s : z₁ --> z₂)
  : s · {{ φ }} = {{ ⟨ π₁ · s , π₂ ⟩ · φ }}.
Proof.
  apply topos_lam_subst.
Qed.

Definition topos_in
           {E : Topos}
           {x z : E}
           (t : z --> x)
           (φ : z --> ℙ x)
  : z --> Ω
  := ⟨ φ , t ⟩ · ε.

Notation "t ∈ φ" := (topos_in t φ) : topos.

Proposition topos_in_compr
            {E : Topos}
            {x z : E}
            (φ : (z × x) --> Ω)
            (t : z --> x)
  : t ∈ {{ φ }} = ⟨ identity _ , t ⟩ · φ.
Proof.
  unfold topos_in, topos_compr.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    exact (topos_lam_beta φ).
  }
  rewrite !assoc.
  apply maponpaths_2.
  use topos_pair_eq.
  - rewrite !assoc'.
    rewrite topos_prod_ar_pr1.
    rewrite !assoc.
    rewrite !topos_pair_pr1.
    apply id_left.
  - rewrite !assoc'.
    rewrite topos_prod_ar_pr2.
    rewrite !assoc.
    rewrite !topos_pair_pr2.
    apply id_right.
Qed.

Proposition topos_comp_eta
            {E : Topos}
            {x y : E}
            (f : x --> ℙ y)
  : f = {{ π₂ ∈ (π₁ · f) }}.
Proof.
  refine (!(topos_lam_eta _) @ _).
  unfold topos_compr.
  apply maponpaths.
  unfold topos_in.
  apply maponpaths_2.
  use topos_pair_eq.
  - rewrite topos_pair_pr1, topos_prod_ar_pr1.
    apply idpath.
  - rewrite topos_pair_pr2, topos_prod_ar_pr2.
    rewrite id_right.
    apply idpath.
Qed.

(** * 4. Some useful isomorphisms *)
Definition topos_prod_pb_isomorphism
           {E : Topos}
           {Γ₁ Γ₂ A₁ A₂ : E}
           {s₁ : Γ₁ --> Γ₂}
           {s₂ : (Γ₁ × A₁) --> (Γ₂ × A₂)}
           (p : s₂ · (identity _ · π₁) = (identity _ · π₁) · s₁)
           (Hp : isPullback p)
  : z_iso (Γ₁ × A₂) (Γ₁ × A₁).
Proof.
  pose (PB := make_Pullback _ Hp).
  use make_z_iso.
  - use (PullbackArrow PB).
    + exact ⟨ π₁ · s₁ , π₂ ⟩.
    + exact π₁.
    + abstract
        (rewrite id_left ;
         rewrite topos_pair_pr1 ;
         apply idpath).
  - exact ⟨ π₁ , s₂ · π₂ ⟩.
  - split.
    + abstract
        (use topos_pair_eq ;
         rewrite !assoc' ;
         rewrite ?topos_pair_pr1, ?topos_pair_pr2, id_left ;
         [ refine (maponpaths (λ z, _ · z) (!(id_left π₁)) @ _) ;
           apply (PullbackArrow_PullbackPr2 PB)
         | ] ;
         rewrite !assoc ;
         etrans ;
         [ apply maponpaths_2 ;
           apply (PullbackArrow_PullbackPr1 PB)
         | ] ;
         rewrite topos_pair_pr2 ;
         apply idpath).
    + abstract
        (use (MorphismsIntoPullbackEqual (isPullback_Pullback PB)) ;
         rewrite !assoc' ;
         rewrite ?(PullbackArrow_PullbackPr1 PB), ?(PullbackArrow_PullbackPr2 PB) ;
         cbn ;
         [
         | rewrite !id_left, topos_pair_pr1 ;
           apply idpath ] ;
         rewrite topos_pair_comp ;
         rewrite assoc ;
         rewrite topos_pair_pr1, topos_pair_pr2, id_left ;
         clear Hp PB ;
         rewrite !id_left in p ;
         rewrite <- p ;
         rewrite <- topos_pair_comp ;
         rewrite topos_pair_id_id ;
         apply id_right).
Defined.

Proposition topos_prod_pb_isomorphism_pr1
            {E : Topos}
            {Γ₁ Γ₂ A₁ A₂ : E}
            {s₁ : Γ₁ --> Γ₂}
            {s₂ : (Γ₁ × A₁) --> (Γ₂ × A₂)}
            (p : s₂ · (identity _ · π₁) = (identity _ · π₁) · s₁)
            (Hp : isPullback p)
  : topos_prod_pb_isomorphism p Hp · π₁ = π₁.
Proof.
  pose (PB := make_Pullback _ Hp).
  etrans.
  {
    rewrite <- (id_left π₁).
    apply (PullbackArrow_PullbackPr2 PB).
  }
  apply idpath.
Qed.

Proposition topos_prod_pb_isomorphism_pr2
            {E : Topos}
            {Γ₁ Γ₂ A₁ A₂ : E}
            {s₁ : Γ₁ --> Γ₂}
            {s₂ : (Γ₁ × A₁) --> (Γ₂ × A₂)}
            (p : s₂ · (identity _ · π₁) = (identity _ · π₁) · s₁)
            (Hp : isPullback p)
  : topos_prod_pb_isomorphism p Hp · s₂ = ⟨ π₁ · s₁ , π₂ ⟩.
Proof.
  pose (PB := make_Pullback _ Hp).
  apply (PullbackArrow_PullbackPr1 PB).
Qed.
