Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.

Local Open Scope cat.

(**
 1. Horizontal identities
 *)
Definition hor_id_data
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (Im : ∏ (x : C), D x x),
     ∏ (x y : C)
       (f : x --> y),
     Im x -->[ f ][ f ] Im y.

Definition double_id
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id_data D)
           (x : C)
  : D x x
  := pr1 I x.

Definition double_id_mor
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id_data D)
           {x y : C}
           (f : x --> y)
  : double_id I x -->[ f ][ f ] double_id I y
  := pr2 I x y f.

Definition hor_id_laws
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id_data D)
  : UU
  := (∏ (x : C), double_id_mor I (identity x) = id_two_disp _)
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z),
      double_id_mor I (f · g)
      =
      double_id_mor I f ;;2 double_id_mor I g).

Definition hor_id
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (I : hor_id_data D), hor_id_laws I.

Coercion hor_id_to_data
         {C : category}
         {D : twosided_disp_cat C C}
         (I : hor_id D)
  : hor_id_data D
  := pr1 I.

Proposition double_id_mor_id
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (x : C)
  : double_id_mor I (identity x) = id_two_disp _.
Proof.
  exact (pr12 I x).
Qed.

Definition double_id_mor_id_comp
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           {x y z : C}
           (f : x --> y)
           (g : y --> z)
  : double_id_mor I (f · g) = double_id_mor I f ;;2 double_id_mor I g.
Proof.
  exact (pr22 I x y z f g).
Qed.

(**
 2. Horizontal composition
 *)
Definition hor_comp_data
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (Cm : ∏ (x y z : C), D x y → D y z → D x z),
     ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (v₃ : z₁ --> z₂)
       (h₁ : D x₁ y₁)
       (h₂ : D y₁ z₁)
       (k₁ : D x₂ y₂)
       (k₂ : D y₂ z₂)
       (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
       (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂),
     Cm _ _ _ h₁ h₂ -->[ v₁ ][ v₃ ] Cm _ _ _ k₁ k₂.

Definition double_hor_comp
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
           {x y z : C}
           (h₁ : D x y)
           (h₂ : D y z)
  : D x z
  := pr1 Cm x y z h₁ h₂.

Definition double_hor_comp_mor
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ --> x₂}
           {v₂ : y₁ --> y₂}
           {v₃ : z₁ --> z₂}
           {h₁ : D x₁ y₁}
           {h₂ : D y₁ z₁}
           {k₁ : D x₂ y₂}
           {k₂ : D y₂ z₂}
           (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
           (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp Cm h₁ h₂ -->[ v₁ ][ v₃ ] double_hor_comp Cm k₁ k₂
  := pr2 Cm x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂.

Definition hor_comp_laws
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
  : UU
  := (∏ (x y z : C)
        (h₁ : D x y)
        (h₂ : D y z),
      double_hor_comp_mor Cm (id_two_disp h₁) (id_two_disp h₂)
      =
      id_two_disp (double_hor_comp Cm h₁ h₂))
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C)
        (v₁ : x₁ --> x₂) (v₁' : x₂ --> x₃)
        (v₂ : y₁ --> y₂) (v₂' : y₂ --> y₃)
        (v₃ : z₁ --> z₂) (v₃' : z₂ --> z₃)
        (h₁ : D x₁ y₁)
        (h₂ : D y₁ z₁)
        (k₁ : D x₂ y₂)
        (k₂ : D y₂ z₂)
        (l₁ : D x₃ y₃)
        (l₂ : D y₃ z₃)
        (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
        (s₁' : k₁ -->[ v₁' ][ v₂' ] l₁)
        (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
        (s₂' : k₂ -->[ v₂' ][ v₃' ] l₂),
      double_hor_comp_mor Cm (s₁ ;;2 s₁') (s₂ ;;2 s₂')
      =
      double_hor_comp_mor Cm s₁ s₂ ;;2 double_hor_comp_mor Cm s₁' s₂').

Definition hor_comp
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (Cm : hor_comp_data D), hor_comp_laws Cm.

Coercion hor_comp_to_data
         {C : category}
         {D : twosided_disp_cat C C}
         (Cm : hor_comp D)
  : hor_comp_data D
  := pr1 Cm.

Proposition double_hor_comp_mor_id
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x y z : C}
            (h₁ : D x y)
            (h₂ : D y z)
  : double_hor_comp_mor Cm (id_two_disp h₁) (id_two_disp h₂)
    =
    id_two_disp (double_hor_comp Cm h₁ h₂).
Proof.
  exact (pr12 Cm x y z h₁ h₂).
Qed.

Proposition double_hor_comp_mor_comp
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
            {v₁ : x₁ --> x₂} {v₁' : x₂ --> x₃}
            {v₂ : y₁ --> y₂} {v₂' : y₂ --> y₃}
            {v₃ : z₁ --> z₂} {v₃' : z₂ --> z₃}
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            {l₁ : D x₃ y₃}
            {l₂ : D y₃ z₃}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₁' : k₁ -->[ v₁' ][ v₂' ] l₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
            (s₂' : k₂ -->[ v₂' ][ v₃' ] l₂)
  : double_hor_comp_mor Cm (s₁ ;;2 s₁') (s₂ ;;2 s₂')
    =
    double_hor_comp_mor Cm s₁ s₂ ;;2 double_hor_comp_mor Cm s₁' s₂'.
Proof.
  exact ((pr22 Cm)
           x₁ x₂ x₃
           y₁ y₂ y₃
           z₁ z₂ z₃
           v₁ v₁'
           v₂ v₂'
           v₃ v₃'
           h₁ h₂
           k₁ k₂
           l₁ l₂
           s₁ s₁' s₂ s₂').
Qed.

Proposition double_hor_comp_mor_transportf_disp_mor2_left
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ --> x₂}
            (p : v₁ = v₁')
            {v₂ v₂' : y₁ --> y₂}
            (q : v₂ = v₂')
            {v₃ v₃' : z₁ --> z₂}
            (r : v₃ = v₃')
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₂ : h₂ -->[ v₂' ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      (transportf_disp_mor2 p q s₁)
      s₂
    =
    transportf_disp_mor2
      p
      (!r)
      (double_hor_comp_mor
         Cm
         s₁
         (transportf_disp_mor2 (!q) r s₂)).
Proof.
  induction p, q, r ; cbn.
  apply idpath.
Qed.

Proposition double_hor_comp_mor_transportf_disp_mor2_right
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ --> x₂}
            (p : v₁' = v₁)
            {v₂ v₂' : y₁ --> y₂}
            (q : v₂ = v₂')
            {v₃ v₃' : z₁ --> z₂}
            (r : v₃ = v₃')
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁' ][ v₂' ] k₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      s₁
      (transportf_disp_mor2 q r s₂)
    =
    transportf_disp_mor2
      (!p)
      r
      (double_hor_comp_mor
         Cm
         (transportf_disp_mor2 p (!q) s₁)
         s₂).
Proof.
  induction p, q, r ; cbn.
  apply idpath.
Qed.

(**
 3. Left unitor
 *)
Definition double_lunitor_data
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∏ (x y : C)
       (h : D x y),
    iso_twosided_disp
      (identity_z_iso x)
      (identity_z_iso y)
      (double_hor_comp Cm (double_id I x) h)
      h.

Proposition isaset_double_lunitor_data
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_lunitor_data I Cm).
Proof.
  use impred_isaset ; intro x.
  use impred_isaset ; intro y.
  use impred_isaset ; intro h.
  apply isaset_iso_twosided_disp.
Qed.

Definition double_lunitor_laws
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_lunitor_data I Cm)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ : C)
       (h₁ : D x₁ y₁)
       (h₂ : D x₂ y₂)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (τ : h₁ -->[ v₁ ][ v₂ ] h₂),
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (l _ _ h₁ ;;2 τ)
     =
     double_hor_comp_mor Cm (double_id_mor I _) τ ;;2 l _ _ h₂.

Proposition isaprop_double_lunitor_laws
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (l : double_lunitor_data I Cm)
  : isaprop (double_lunitor_laws l).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_cat_lunitor
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∑ (l : double_lunitor_data I Cm), double_lunitor_laws l.

Proposition isaset_double_cat_lunitor
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_cat_lunitor I Cm).
Proof.
  use isaset_total2.
  - apply isaset_double_lunitor_data.
  - intro.
    apply isasetaprop.
    apply isaprop_double_lunitor_laws.
Qed.

Definition make_double_lunitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_lunitor_data I Cm)
           (Hl : double_lunitor_laws l)
  : double_cat_lunitor I Cm
  := l ,, Hl.

Definition double_lunitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_cat_lunitor I Cm)
           {x y : C}
           (h : D x y)
  : double_hor_comp Cm (double_id I x) h
    -->[ identity x ][ identity y ]
    h
  := pr1 l x y h.

Proposition double_lunitor_nat
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (l : double_cat_lunitor I Cm)
            {x₁ x₂ y₁ y₂ : C}
            {h₁ : D x₁ y₁}
            {h₂ : D x₂ y₂}
            {v₁ : x₁ --> x₂}
            {v₂ : y₁ --> y₂}
            (τ : h₁ -->[ v₁ ][ v₂ ] h₂)
  : transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_lunitor l h₁ ;;2 τ)
    =
    double_hor_comp_mor Cm (double_id_mor I _) τ ;;2 double_lunitor l h₂.
Proof.
  exact (pr2 l x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
Qed.

(**
 4. Right unitor
 *)
Definition double_runitor_data
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∏ (x y : C)
       (h : D x y),
    iso_twosided_disp
      (identity_z_iso x)
      (identity_z_iso y)
      (double_hor_comp Cm h (double_id I y))
      h.

Proposition isaset_double_runitor_data
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_runitor_data I Cm).
Proof.
  use impred_isaset ; intro x.
  use impred_isaset ; intro y.
  use impred_isaset ; intro h.
  apply isaset_iso_twosided_disp.
Qed.

Definition double_runitor_laws
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (r : double_runitor_data I Cm)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ : C)
       (h₁ : D x₁ y₁)
       (h₂ : D x₂ y₂)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (τ : h₁ -->[ v₁ ][ v₂ ] h₂),
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (r _ _ h₁ ;;2 τ)
     =
     double_hor_comp_mor Cm τ (double_id_mor I _) ;;2 r _ _ h₂.

Proposition isaprop_double_runitor_laws
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (r : double_runitor_data I Cm)
  : isaprop (double_runitor_laws r).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_cat_runitor
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∑ (r : double_runitor_data I Cm), double_runitor_laws r.

Proposition isaset_double_cat_runitor
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_cat_runitor I Cm).
Proof.
  use isaset_total2.
  - apply isaset_double_runitor_data.
  - intro.
    apply isasetaprop.
    apply isaprop_double_runitor_laws.
Qed.

Definition make_double_runitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_runitor_data I Cm)
           (Hl : double_runitor_laws l)
  : double_cat_runitor I Cm
  := l ,, Hl.

Definition double_runitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (r : double_cat_runitor I Cm)
           {x y : C}
           (h : D x y)
  : double_hor_comp Cm h (double_id I y)
    -->[ identity x ][ identity y ]
    h
  := pr1 r x y h.

Proposition double_runitor_nat
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (r : double_cat_runitor I Cm)
            {x₁ x₂ y₁ y₂ : C}
            {h₁ : D x₁ y₁}
            {h₂ : D x₂ y₂}
            {v₁ : x₁ --> x₂}
            {v₂ : y₁ --> y₂}
            (τ : h₁ -->[ v₁ ][ v₂ ] h₂)
  : transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_runitor r h₁ ;;2 τ)
    =
    double_hor_comp_mor Cm τ (double_id_mor I _) ;;2 double_runitor r h₂.
Proof.
  exact (pr2 r x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
Qed.

(**
 5. Associator
 *)
Definition double_associator_data
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp D)
  : UU
  := ∏ (w x y z : C)
       (h₁ : D w x)
       (h₂ : D x y)
       (h₃ : D y z),
    iso_twosided_disp
      (identity_z_iso w)
      (identity_z_iso z)
      (double_hor_comp
         Cm
         h₁
         (double_hor_comp
            Cm
            h₂
            h₃))
      (double_hor_comp
         Cm
         (double_hor_comp
            Cm
            h₁
            h₂)
         h₃).

Proposition isaset_double_associator_data
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : isaset (double_associator_data Cm).
Proof.
  repeat (use impred_isaset ; intro).
  apply isaset_iso_twosided_disp.
Qed.

Definition double_associator_laws
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_associator_data Cm)
  : UU
  := ∏ (w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C)
       (h₁ : D w₁ x₁)
       (h₂ : D w₂ x₂)
       (j₁ : D x₁ y₁)
       (j₂ : D x₂ y₂)
       (k₁ : D y₁ z₁)
       (k₂ : D y₂ z₂)
       (vw : w₁ --> w₂)
       (vx : x₁ --> x₂)
       (vy : y₁ --> y₂)
       (vz : z₁ --> z₂)
       (τ₁ : h₁ -->[ vw ][ vx ] h₂)
       (τ₂ : j₁ -->[ vx ][ vy ] j₂)
       (τ₃ : k₁ -->[ vy ][ vz ] k₂),
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (a _ _ _ _ h₁ j₁ k₁ ;;2 double_hor_comp_mor Cm (double_hor_comp_mor Cm τ₁ τ₂) τ₃)
     =
     double_hor_comp_mor Cm τ₁ (double_hor_comp_mor Cm τ₂ τ₃) ;;2 a _ _ _ _ h₂ j₂ k₂.

Proposition isaprop_double_associator_laws
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            (a : double_associator_data Cm)
  : isaprop (double_associator_laws a).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_cat_associator
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp D)
  : UU
  := ∑ (a : double_associator_data Cm), double_associator_laws a.

Proposition isaset_double_cat_associator
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : isaset (double_cat_associator Cm).
Proof.
  use isaset_total2.
  - apply isaset_double_associator_data.
  - intro.
    apply isasetaprop.
    apply isaprop_double_associator_laws.
Qed.

Definition make_double_associator
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_associator_data Cm)
           (Ha : double_associator_laws a)
  : double_cat_associator Cm
  := a ,, Ha.

Definition double_associator
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_cat_associator Cm)
           {w x y z : C}
           (h₁ : D w x)
           (h₂ : D x y)
           (h₃ : D y z)
  : double_hor_comp
      Cm
      h₁
      (double_hor_comp
         Cm
         h₂
         h₃)
    -->[ identity w ][ identity z ]
    double_hor_comp
      Cm
      (double_hor_comp
         Cm
         h₁
         h₂)
      h₃
  := pr1 a w x y z h₁ h₂ h₃.

Proposition double_associator_nat
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            (a : double_cat_associator Cm)
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {h₁ : D w₁ x₁}
            {h₂ : D w₂ x₂}
            {j₁ : D x₁ y₁}
            {j₂ : D x₂ y₂}
            {k₁ : D y₁ z₁}
            {k₂ : D y₂ z₂}
            {vw : w₁ --> w₂}
            {vx : x₁ --> x₂}
            {vy : y₁ --> y₂}
            {vz : z₁ --> z₂}
            (τ₁ : h₁ -->[ vw ][ vx ] h₂)
            (τ₂ : j₁ -->[ vx ][ vy ] j₂)
            (τ₃ : k₁ -->[ vy ][ vz ] k₂)
  : transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_associator a h₁ j₁ k₁
       ;;2
       double_hor_comp_mor Cm (double_hor_comp_mor Cm τ₁ τ₂) τ₃)
    =
    double_hor_comp_mor Cm τ₁ (double_hor_comp_mor Cm τ₂ τ₃)
    ;;2
    double_associator a h₂ j₂ k₂.
Proof.
  apply (pr2 a).
Qed.

(**
 6. Triangle and pentagon laws
 *)

(**
 7. Bundled version of double categories
 *)
