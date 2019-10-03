(* ******************************************************************************* *)
(** * 2-categories
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Definition two_cat_data
  : UU
  := ∑ (C : category)
       (cells_C : ∏ (x y : C), x --> y → x --> y → UU),
     (∏ (x y : C) (f : x --> y), cells_C _ _ f f)
     × (∏ (x y : C) (f g h : x --> y),
        cells_C _ _ f g → cells_C _ _ g h → cells_C _ _ f h)
     × (∏ (x y z : C)
          (f : x --> y)
          (g1 g2 : y --> z),
        cells_C _ _ g1 g2 → cells_C _ _ (f · g1) (f · g2))
     × (∏ (x y z : C)
          (f1 f2 : x --> y)
          (g : y --> z),
        cells_C _ _ f1 f2 → cells_C _ _ (f1 · g) (f2 · g)).

Coercion category_from_two_cat_data (C : two_cat_data)
  : category
  := pr1 C.

Definition two_cat_cells
           (C : two_cat_data)
           {a b : C}
           (f g : C⟦a, b⟧)
  : UU
  := pr12 C a b f g.

Local Notation "f '==>' g" := (two_cat_cells _ f g) (at level 60).
Local Notation "f '<==' g" := (two_cat_cells _ g f) (at level 60, only parsing).

(* ----------------------------------------------------------------------------------- *)
(** Data projections.                                                                  *)
(* ----------------------------------------------------------------------------------- *)

Definition id2 {C : two_cat_data} {a b : C} (f : C⟦a, b⟧) : f ==> f
  := pr122 C a b f.

Definition vcomp2 {C : two_cat_data} {a b : C} {f g h : C⟦a, b⟧}
  : f ==> g → g ==> h → f ==> h
  := λ x y, pr1 (pr222 C) _ _ _ _ _ x y.

Definition lwhisker {C : two_cat_data} {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
  : g1 ==> g2 → f · g1 ==> f · g2
  := λ x, pr12 (pr222 C) _ _ _ _ _ _ x.

Definition rwhisker {C : two_cat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
  : f1 ==> f2 → f1 · g ==> f2 · g
  := λ x, pr22 (pr222 C) _ _ _ _ _ _ x.

Local Notation "x • y" := (vcomp2 x y) (at level 60).
Local Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Local Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

Definition hcomp {C : two_cat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2
  := λ x y, (x ▹ g1) • (f2 ◃ y).

Definition hcomp' {C : two_cat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2
  := λ x y, (f1 ◃ y) • (x ▹ g2).

Local Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).

(* ----------------------------------------------------------------------------------- *)
(** ** Laws                                                                            *)
(* ----------------------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------------------- *)
(** The numbers in the following laws refer to the list of axioms given in ncatlab
    (Section "Definition / Details")
    https://ncatlab.org/nlab/show/bicategory#detailedDefn
    version of October 7, 2015 10:35:36                                                *)
(* ----------------------------------------------------------------------------------- *)

Definition two_cat_laws (C : two_cat_data)
  : UU
  :=   (** 1a id2_left *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), id2 f • x = x)
     × (** 1b id2_right *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), x • id2 g = x)
     × (** 2 vassocr *)
       (∏ (a b : C) (f g h k : C⟦a, b⟧) (x : f ==> g) (y : g ==> h) (z : h ==> k),
        x • (y • z) = (x • y) • z)
     × (** 3a lwhisker_id2 *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), f ◃ id2 g = id2 _)
     × (** 3b id2_rwhisker *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), id2 f ▹ g = id2 _)
     × (** 4 lwhisker_vcomp *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g h i : C⟦b, c⟧) (x : g ==> h) (y : h ==> i),
        (f ◃ x) • (f ◃ y) = f ◃ (x • y))
     × (** 5 rwhisker_vcomp *)
       (∏ (a b c : C) (f g h : C⟦a, b⟧) (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h),
        (x ▹ i) • (y ▹ i) = (x • y) ▹ i)
     × (** 6 vcomp_whisker *)
       (∏ (a b c : C) (f g : C⟦a, b⟧) (h i : C⟦b, c⟧) (x : f ==> g) (y : h ==> i),
        (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i)).

Definition two_precat : UU := ∑ C : two_cat_data, two_cat_laws C.

Coercion two_cat_data_from_two_cat (C : two_precat) : two_cat_data := pr1 C.
Coercion two_cat_laws_from_two_cat (C : two_precat) : two_cat_laws C := pr2 C.

(* ----------------------------------------------------------------------------------- *)
(** Laws projections.                                                                  *)
(* ----------------------------------------------------------------------------------- *)

Section two_cat_law_projections.

Context {C : two_precat}.

(** 1a id2_left *)
Definition id2_left {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : id2 f • x = x
  := pr1 (pr2 C) _ _ _ _ x.

(** 1b id2_right *)
Definition id2_right {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : x • id2 g = x
  := pr1 (pr2 (pr2 C)) _ _ _ _ x.

(** 2 vassocr *)
Definition vassocr {a b : C} {f g h k : C⟦a, b⟧}
           (x : f ==> g) (y : g ==> h) (z : h ==> k)
  : x • (y • z) = (x • y) • z
  := pr1 (pr2 (pr2 (pr2 C))) _ _ _ _ _ _ x y z.

(** 3a lwhisker_id2 *)
Definition lwhisker_id2 {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : f ◃ id2 g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) _ _ _ f g.

(** 3b id2_rwhisker *)
Definition id2_rwhisker {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : id2 f ▹ g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) _ _ _ f g.

(** 4 lwhisker_vcomp *)
Definition lwhisker_vcomp {a b c : C} (f : C⟦a, b⟧) {g h i : C⟦b, c⟧}
           (x : g ==> h) (y : h ==> i)
  : (f ◃ x) • (f ◃ y) = f ◃ (x • y)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) _ _ _ f _ _ _ x y.

(** 5 rwhisker_vcomp *)
Definition rwhisker_vcomp {a b c : C} {f g h : C⟦a, b⟧}
           (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h)
  : (x ▹ i) • (y ▹ i) = (x • y) ▹ i
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) _ _ _ _ _ _ i x y.


(** 6 vcomp_whisker *)
Definition vcomp_whisker {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧}
           (x : f ==> g) (y : h ==> i)
  : (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i)
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) _ _ _ _ _ _ i x y.
End two_cat_law_projections.

(* ----------------------------------------------------------------------------------- *)
(** ** Bicategories                                                                    *)
(* ----------------------------------------------------------------------------------- *)

Definition isaset_cells (C : two_precat) : UU
  := ∏ (a b : C) (f g : a --> b), isaset (f ==> g).

Definition two_cat : UU
  := ∑ C : two_precat, isaset_cells C.

(**
Identities to isomorphisms
 *)
Definition two_cat_idtoiso
           {C : two_precat}
           {a b : C}
           {f g : a --> b}
           (p : f = g)
  : f ==> g.
Proof.
  induction p.
  apply id2.
Defined.

Definition two_cat_idtoiso_comp
           {C : two_precat}
           {a b : C}
           {f g h : a --> b}
           (p : f = g) (q : g = h)
  : two_cat_idtoiso p • two_cat_idtoiso q = two_cat_idtoiso (p @ q).
Proof.
  induction p.
  induction q.
  apply id2_left.
Defined.

Definition two_cat_idtoiso_lwhisker
           {C : two_precat}
           {a b c : C}
           (h : a --> b)
           {f g : b --> c}
           (p : f = g)
  : h ◃ two_cat_idtoiso p
    =
    two_cat_idtoiso (maponpaths (λ z, h · z) p).
Proof.
  induction p.
  apply lwhisker_id2.
Defined.

Definition two_cat_idtoiso_rwhisker
           {C : two_precat}
           {a b c : C}
           {f g : a --> b}
           (h : b --> c)
           (p : f = g)
  : two_cat_idtoiso p ▹ h
    =
    two_cat_idtoiso (maponpaths (λ z, z · h) p).
Proof.
  induction p.
  apply id2_rwhisker.
Defined.

(**
Unitors and associators
 *)
Definition two_cat_lunitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : identity a · f ==> f.
Proof.
  apply two_cat_idtoiso.
  apply id_left.
Defined.

Definition two_cat_linvunitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : f ==> identity a · f.
Proof.
  apply two_cat_idtoiso.
  exact (!(id_left f)).
Defined.

Definition two_cat_runitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : f · identity b ==> f.
Proof.
  apply two_cat_idtoiso.
  apply id_right.
Defined.

Definition two_cat_rinvunitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : f ==> f · identity b.
Proof.
  apply two_cat_idtoiso.
  exact (!(id_right f)).
Defined.

Definition two_cat_lassociator
           {C : two_precat}
           {a b c d : C}
           (f : a --> b) (g : b --> c) (h : c --> d)
  : f · (g · h) ==> (f · g) · h.
Proof.
  apply two_cat_idtoiso.
  exact (assoc f g h).
Defined.

Definition two_cat_rassociator
           {C : two_precat}
           {a b c d : C}
           (f : a --> b) (g : b --> c) (h : c --> d)
  : (f · g) · h ==> f · (g · h).
Proof.
  apply two_cat_idtoiso.
  exact (!(assoc f g h)).
Defined.

(** Laws of unitors and associators *)

(** Naturality laws *)
Definition two_cat_vcomp_lunitor
           {C : two_precat}
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : (identity a ◃ x) • two_cat_lunitor g = two_cat_lunitor f • x.
Proof.
  apply test.
  unfold two_cat_lunitor.
  simpl. cbn in *.
  induction (id_left g).
Admitted.

Definition two_cat_vcomp_runitor
           {C : two_precat}
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : (x ▹ identity b) • two_cat_runitor g = two_cat_runitor f • x.
Proof.
Admitted.

Definition two_cat_lwhisker_lwhisker
           {C : two_precat}
           {a b c d : C}
           (f : a --> b) (g : b --> c)
           {h i : c --> d}
           (x : h ==> i)
  : f ◃ (g ◃ x) • two_cat_lassociator _ _ _
    =
    two_cat_lassociator _ _ _ • (f · g ◃ x).
Proof.
Admitted.

Definition two_cat_rwhisker_lwhisker
           {C : two_precat}
           {a b c d : C}
           (f : a --> b)
           {g h : b --> c}
           (i : c --> d)
           (x : g ==> h)
  : (f ◃ (x ▹ i)) • two_cat_lassociator _ _ _
    =
    two_cat_lassociator _ _ _ • ((f ◃ x) ▹ i).
Proof.
Admitted.

Definition two_cat_rwhisker_rwhisker
           {C : two_precat}
           {a b c d : C}
           {f g : a --> b}
           (h : b --> c)
           (i : c --> d)
           (x : f ==> g)
  : two_cat_lassociator _ _ _ • ((x ▹ h) ▹ i)
    =
    (x ▹ h · i) • two_cat_lassociator _ _ _.
Proof.
Admitted.

(** Inverse laws *)
Definition two_cat_lunitor_linvunitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : two_cat_lunitor f • two_cat_linvunitor f = id2 _.
Proof.
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0r.
  }
  apply idpath.
Qed.

Definition two_cat_linvunitor_lunitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : two_cat_linvunitor f • two_cat_lunitor f = id2 _.
Proof.
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Qed.

Definition two_cat_runitor_rinvunitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : two_cat_runitor f • two_cat_rinvunitor f = id2 _.
Proof.
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0r.
  }
  apply idpath.
Qed.

Definition two_cat_rinvunitor_runitor
           {C : two_precat}
           {a b : C}
           (f : a --> b)
  : two_cat_rinvunitor f • two_cat_runitor f = id2 _.
Proof.
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Qed.

Definition two_cat_lassociator_rassociator
           {C : two_precat}
           {a b c d : C}
           (f : a --> b) (g : b --> c) (h : c --> d)
  : two_cat_lassociator f g h • two_cat_rassociator f g h
    =
    id2 _.
Proof.
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0r.
  }
  apply idpath.
Qed.

Definition two_cat_rassociator_lassociator
           {C : two_precat}
           {a b c d : C}
           (f : a --> b) (g : b --> c) (h : c --> d)
  : two_cat_rassociator f g h • two_cat_lassociator f g h
    =
    id2 _.
Proof.
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Qed.

(** Coherencies *)
Definition two_cat_runitor_rwhisker
           {C : two_precat}
           {a b c : C}
           (f : a --> b) (g : b --> c)
  : two_cat_lassociator _ _ _ • ((two_cat_runitor f) ▹ g)
    =
    f ◃ two_cat_lunitor g.
Proof.
  etrans.
  {
    apply maponpaths.
    apply two_cat_idtoiso_rwhisker.
  }
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  refine (!_).
  etrans.
  {
    apply two_cat_idtoiso_lwhisker.
  }
  apply maponpaths.
  apply (pr11 C).
Qed.

Definition two_cat_lassociator_lassociator
           {C : two_precat}
           {a b c d e : C}
           (f : a --> b) (g : b --> c)
           (h : c --> d) (i : d --> e)
  : (f ◃ two_cat_lassociator g h i)
      • two_cat_lassociator _ _ _
      • (two_cat_lassociator _ _ _ ▹ i)
    =
    two_cat_lassociator f g _  • two_cat_lassociator _ _ _.
Proof.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply two_cat_idtoiso_lwhisker.
    }
    apply two_cat_idtoiso_comp.
  }
  etrans.
  {
    etrans.
    {
      apply maponpaths.
      apply two_cat_idtoiso_rwhisker.
    }
    apply two_cat_idtoiso_comp.
  }
  refine (!_).
  etrans.
  {
    apply two_cat_idtoiso_comp.
  }
  apply maponpaths.
  apply (pr11 C).
Qed.

Module Notations.

Notation "f '==>' g" := (two_cat_cells _ f g) (at level 60).
Notation "f '<==' g" := (two_cat_cells _ g f) (at level 60, only parsing).
Notation "x • y" := (vcomp2 x y) (at level 60).
Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)
Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).
Notation "'id₁'" := identity.
Notation "'id₂'" := id2.

End Notations.
