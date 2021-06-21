Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

(** Preservation of terminal objects *)
Definition map_preserves_terminal
           {C D : precategory}
           (F : C ⟶ D)
           (tC : Terminal C)
           (tD : Terminal D)
  : F tC --> tD
  := TerminalArrow tD (F tC).

Definition preserves_terminal
           {C D : precategory}
           (F : C ⟶ D)
           (tC : Terminal C)
           (tD : Terminal D)
  : UU
  := is_iso (map_preserves_terminal F tC tD).

Definition isaprop_preserves_terminal
           {C D : precategory}
           (F : C ⟶ D)
           (tC : Terminal C)
           (tD : Terminal D)
  : isaprop (preserves_terminal F tC tD).
Proof.
  apply isaprop_is_iso.
Qed.

Definition identity_preserves_terminal
           (C : precategory)
           (tC : Terminal C)
  : preserves_terminal (functor_identity C) tC tC.
Proof.
  unfold preserves_terminal, map_preserves_terminal ; cbn.
  use is_iso_qinv.
  - apply identity.
  - abstract (split ; apply TerminalArrowEq).
Defined.

Definition composition_preserves_terminal
           {C₁ C₂ C₃ : precategory}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {tC₁ : Terminal C₁}
           {tC₂ : Terminal C₂}
           {tC₃ : Terminal C₃}
           (tF : preserves_terminal F tC₁ tC₂)
           (tG : preserves_terminal G tC₂ tC₃)
  : preserves_terminal (F ∙ G) tC₁ tC₃.
Proof.
  unfold preserves_terminal, map_preserves_terminal in * ; cbn.
  use is_iso_qinv.
  - exact (inv_from_iso (make_iso _ tG) · # G (inv_from_iso (make_iso _ tF))).
  - assert (TerminalArrow tC₃ (G (F tC₁))
            =
            # G (TerminalArrow tC₂ (F tC₁)) · TerminalArrow tC₃ (G tC₂))
      as H.
    {
      apply TerminalArrowEq.
    }
    split.
    + rewrite H.
      rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        exact (iso_inv_after_iso (make_iso _ tG)).
      }
      rewrite id_left.
      rewrite <- functor_comp.
      refine (_ @ functor_id _ _).
      apply maponpaths.
      exact (iso_inv_after_iso (make_iso _ tF)).
    + rewrite H.
      rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        rewrite <- functor_comp.
        apply maponpaths.
        exact (iso_after_iso_inv (make_iso _ tF)).
      }
      rewrite functor_id.
      rewrite id_left.
      exact (iso_after_iso_inv (make_iso _ tG)).
Defined.

(** *)
Definition disp_cat_ob_mor_terminal_obj
  : disp_cat_ob_mor bicat_of_cats.
Proof.
  use tpair.
  - exact (λ C, Terminal (C : univalent_category)).
  - exact (λ C D tC tD F, preserves_terminal F tC tD).
Defined.

Definition disp_cat_id_comp_terminal_obj
  : disp_cat_id_comp bicat_of_cats disp_cat_ob_mor_terminal_obj.
Proof.
  use tpair ; simpl.
  - exact identity_preserves_terminal.
  - exact (λ _ _ _ _ _ tC₁ tC₂ tC₃ tF tG, composition_preserves_terminal tF tG).
Defined.

Definition disp_cat_data_terminal_obj
  : disp_cat_data bicat_of_cats.
Proof.
  use tpair.
  - exact disp_cat_ob_mor_terminal_obj.
  - exact disp_cat_id_comp_terminal_obj.
Defined.

Definition disp_bicat_terminal_obj : disp_bicat bicat_of_cats.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_terminal_obj.
Defined.

Definition disp_bicat_terminal_obj_univalent_2_1
  : disp_univalent_2_1 disp_bicat_terminal_obj.
Proof.
  use disp_cell_unit_bicat_univalent_2_1.
  intros ; simpl.
  apply isaprop_preserves_terminal.
Defined.

Definition disp_bicat_terminal_obj_univalent_2_0
  : disp_univalent_2_0 disp_bicat_terminal_obj.
Proof.
  use disp_cell_unit_bicat_univalent_2_0.
  - apply univalent_cat_is_univalent_2_1.
  - intros ; simpl.
    apply isaprop_preserves_terminal.
  - simpl.
    intro C.
    apply isasetaprop.
    apply isaprop_Terminal.
    apply C.
  - intros C ? ? ?.
    apply isaprop_Terminal.
    apply C.
Defined.

(** Preservation of pullbacks *)
Definition map_preserves_pullbacks
           {C D : precategory}
           (F : C ⟶ D)
           (pC : Pullbacks C)
           (pD : Pullbacks D)
           {a b c : C}
           (f : b --> a)
           (g : c --> a)
  : F (pC _ _ _ f g) --> pD _ _ _ (#F f) (#F g).
Proof.
  use PullbackArrow.
  - exact (#F (PullbackPr1 _)).
  - exact (#F (PullbackPr2 _)).
  - abstract
      (rewrite <- !functor_comp ;
       apply maponpaths ;
       apply PullbackSqrCommutes).
Defined.

Definition preserves_pullbacks
           {C D : precategory}
           (F : C ⟶ D)
           (pC : Pullbacks C)
           (pD : Pullbacks D)
  : UU
  := ∏ (a b c : C) (f : b --> a) (g : c --> a),
     is_iso (map_preserves_pullbacks F pC pD f g).

Definition isaprop_preserves_pullbacks
           {C D : precategory}
           (F : C ⟶ D)
           (pC : Pullbacks C)
           (pD : Pullbacks D)
  : isaprop (preserves_pullbacks F pC pD).
Proof.
  do 5 (use impred ; intro).
  apply isaprop_is_iso.
Qed.

Definition identity_preserves_pullbacks
           (C : precategory)
           (pC : Pullbacks C)
  : preserves_pullbacks (functor_identity C) pC pC.
Proof.
  unfold preserves_pullbacks, map_preserves_pullbacks ; cbn.
  intros a b c f g.
  use is_iso_qinv.
  - apply identity.
  - split.
    + abstract
        (rewrite id_right ;
         refine (!_) ;
         apply PullbackArrowUnique' ;
         apply id_left).
    + abstract
        (rewrite id_left ;
         refine (!_) ;
         apply PullbackArrowUnique' ;
         apply id_left).
Defined.

Definition composition_preserves_pullbacks
           {C₁ C₂ C₃ : precategory}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {pC₁ : Pullbacks C₁}
           {pC₂ : Pullbacks C₂}
           {pC₃ : Pullbacks C₃}
           (pF : preserves_pullbacks F pC₁ pC₂)
           (pG : preserves_pullbacks G pC₂ pC₃)
  : preserves_pullbacks (F ∙ G) pC₁ pC₃.
Proof.
  unfold preserves_pullbacks, map_preserves_pullbacks in * ; cbn.
  intros a b c f g.
  use is_iso_qinv.
  - exact (inv_from_iso (make_iso _ (pG _ _ _ _ _))
           · # G (inv_from_iso (make_iso _ (pF _ _ _ _ _)))).
  - split.
    + rewrite functor_on_inv_from_iso.
      rewrite assoc.
      do 2 (refine (!_) ; use iso_inv_on_left) ; simpl.
      rewrite id_left.
      refine (!_).
      use PullbackArrowUnique'.
      * rewrite assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite <- functor_comp.
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      * rewrite assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite <- functor_comp.
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
    + rewrite functor_on_inv_from_iso.
      rewrite assoc'.
      do 2 use iso_inv_on_right.
      refine (!_).
      rewrite id_right.
      use PullbackArrowUnique' ; simpl.
      * rewrite assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite <- functor_comp.
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      * rewrite assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite <- functor_comp.
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
Defined.

Definition disp_cat_ob_mor_pullbacks
  : disp_cat_ob_mor bicat_of_cats.
Proof.
  use tpair.
  - exact (λ C, Pullbacks (C : univalent_category)).
  - exact (λ C D pC pD F, preserves_pullbacks F pC pD).
Defined.

Definition disp_cat_id_comp_pullbacks
  : disp_cat_id_comp bicat_of_cats disp_cat_ob_mor_pullbacks.
Proof.
  use tpair ; simpl.
  - exact identity_preserves_pullbacks.
  - exact (λ _ _ _ _ _ pC₁ pC₂ pC₃ pF pG, composition_preserves_pullbacks pF pG).
Defined.

Definition disp_cat_data_pullbacks
  : disp_cat_data bicat_of_cats.
Proof.
  use tpair.
  - exact disp_cat_ob_mor_pullbacks.
  - exact disp_cat_id_comp_pullbacks.
Defined.

Definition disp_bicat_pullbacks : disp_bicat bicat_of_cats.
Proof.
  use disp_cell_unit_bicat.
  exact disp_cat_data_pullbacks.
Defined.

Definition disp_bicat_pullbacks_univalent_2_1
  : disp_univalent_2_1 disp_bicat_pullbacks.
Proof.
  use disp_cell_unit_bicat_univalent_2_1.
  intros ; simpl.
  apply isaprop_preserves_pullbacks.
Defined.

Definition disp_bicat_pullbacks_univalent_2_0
  : disp_univalent_2_0 disp_bicat_pullbacks.
Proof.
  use disp_cell_unit_bicat_univalent_2_0.
  - apply univalent_cat_is_univalent_2_1.
  - intros ; simpl.
    apply isaprop_preserves_pullbacks.
  - simpl.
    intro C.
    apply isasetaprop.
    apply isaprop_Pullbacks ; apply C.
  - intros C ? ? ?.
    apply isaprop_Pullbacks ; apply C.
Defined.
