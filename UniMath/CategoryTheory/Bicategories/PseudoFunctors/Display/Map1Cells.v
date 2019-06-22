(** This is the first layer of the construction of the bicategory of pseudofunctors.
    To a function of objects, we add an action of 1-cells.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section Map1Cells.
  Variable (C D : bicat).

  Definition map1cells_disp_cat : disp_cat_ob_mor (ps_base C D).
  Proof.
    use tpair.
    - exact (λ F₀, ∏ (X Y : C), X --> Y → F₀ X --> F₀ Y).
    - exact (λ F₀ G₀ F₁ G₁ η, ∏ (X Y : C) (f : X --> Y),
             invertible_2cell (η X · G₁ X Y f) (F₁ X Y f · η Y)).
  Defined.

  Definition map1cells_disp_cat_id_comp : disp_cat_id_comp (ps_base C D) map1cells_disp_cat.
  Proof.
    use tpair.
    - cbn.
      refine (λ F₀ F₁ X Y f, (lunitor (F₁ X Y f) • rinvunitor (F₁ X Y f) ,, _)).
      is_iso.
    - cbn.
      refine (λ F₀ G₀ H₀ η₁ ε₁ F₁ G₁ H₁ η₂ ε₂ X Y f,
              (rassociator (η₁ X) (ε₁ X) (H₁ X Y f))
                • (η₁ X ◃ ε₂ X Y f)
                • lassociator (η₁ X) (G₁ X Y f) (ε₁ Y)
                • (η₂ X Y f ▹ ε₁ Y)
                • rassociator (F₁ X Y f) (η₁ Y) (ε₁ Y) ,, _).
      is_iso.
      + apply ε₂.
      + apply η₂.
  Defined.

  Definition map1cells_disp_cat_2cell : disp_2cell_struct map1cells_disp_cat
    := λ F₀ G₀ η₁ ε₁ m F₁ G₁ η₂ ε₂,
       ∏ (X Y : C) (f : X --> Y),
       η₂ X Y f • (F₁ X Y f ◃ m Y)
       =
       (m X ▹ G₁ X Y f) • ε₂ X Y f.

  Definition map1cells_prebicat_1 : disp_prebicat_1_id_comp_cells (ps_base C D).
  Proof.
    use tpair.
    - use tpair.
      + exact map1cells_disp_cat.
      + exact map1cells_disp_cat_id_comp.
    - exact (λ F₀ G₀ η₁ ε₁ m F₁ G₁ η₂ ε₂,
             ∏ (X Y : C) (f : X --> Y),
             η₂ X Y f • (F₁ X Y f ◃ m Y)
             =
             (m X ▹ G₁ X Y f) • ε₂ X Y f).
  Defined.

  Definition map1cells_ops : disp_prebicat_ops map1cells_prebicat_1.
  Proof.
    repeat split.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite lwhisker_id2, id2_right.
      rewrite id2_rwhisker, id2_left.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocl.
      rewrite (lwhisker_hcomp _ (lunitor _)).
      rewrite triangle_l.
      rewrite <- !rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor, id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      rewrite <- lunitor_assoc.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocl.
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      refine (_ @ vassocl _ _ _).
      rewrite !runitor_triangle.
      rewrite (rwhisker_hcomp _ (runitor _)).
      rewrite <- triangle_r.
      rewrite vcomp_runitor.
      rewrite <- lwhisker_vcomp, <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_runitor, id2_left.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      refine (vassocl _ _ _ @ _).
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv, <- rwhisker_hcomp.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite lunitor_triangle.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      refine (vassocl _ _ _ @ _).
      rewrite rinvunitor_triangle.
      rewrite (rwhisker_hcomp _ (rinvunitor _)).
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
    - intros F₀ G₀ H₀ K₀ α₁ η₁ ε₁ F₁ G₁ H₁ K₁ α₂ η₂ ε₂ X Y f ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      refine (!(_ @ _)).
      {
        rewrite !vassocr.
        do 7 apply maponpaths_2.
        symmetry.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite vassocl.
        apply inverse_pentagon.
      }
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 5 apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite vassocl, <- inverse_pentagon_6.
        rewrite <- rwhisker_hcomp.
        reflexivity.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        rewrite !vassocl.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        apply inverse_pentagon.
      }
      rewrite (lwhisker_hcomp _ (rassociator _ _ _)), (rwhisker_hcomp _ (rassociator _ _ _)).
      rewrite <- inverse_pentagon.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_rwhisker_alt.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rassociator_lassociator, id2_right.
      reflexivity.
    - intros F₀ G₀ H₀ K₀ α₁ η₁ ε₁ F₁ G₁ H₁ K₁ α₂ η₂ ε₂ X Y f ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 8 apply maponpaths_2.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        rewrite !vassocl.
        apply inverse_pentagon.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite inverse_pentagon.
        rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2, id2_left.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 4 apply maponpaths_2.
        rewrite vassocl, lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        apply inverse_pentagon.
      }
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rassociator_lassociator, id2_left.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      symmetry.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      apply inverse_pentagon_6.
    - intros F₀ G₀ α₁ η₁ ε₁ m₂ n₂ F₁ G₁ α₂ η₂ ε₂ m₃ n₃ X Y f ; cbn in *.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      rewrite m₃.
      rewrite !vassocl.
      rewrite n₃.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      reflexivity.
    - intros F₀ G₀ H₀ α₁ η₁ ε₁ m₂ F₁ G₁ H₁ α₂ η₂ ε₂ m₃ X Y f ; cbn in *.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      rewrite <- m₃.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      reflexivity.
    - intros F₀ G₀ H₀ α₁ η₁ ε₁ m₂ F₁ G₁ H₁ α₂ η₂ ε₂ m₃ X Y f ; cbn in *.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite m₃.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      reflexivity.
  Qed.

  Definition map1cells_ops_laws : disp_prebicat_laws (_ ,, map1cells_ops).
  Proof.
    repeat split ; intro ; intros ; do 3 (apply funextsec ; intro) ; apply D.
  Qed.

  Definition map1cells_disp_prebicat : disp_prebicat (ps_base C D)
    := (_ ,, map1cells_ops_laws).

  Definition map1cells_disp_bicat : disp_bicat (ps_base C D).
  Proof.
    refine (map1cells_disp_prebicat ,, _).
    intros X Y f g α hX hY hf hg hα hβ.
    apply isasetaprop.
    do 3 (apply impred ; intro).
    apply D.
  Defined.

  Definition map1cells_disp_univalent_2_1
    : disp_univalent_2_1 map1cells_disp_bicat.
  Proof.
    apply fiberwise_local_univalent_is_univalent_2_1.
    intros F G η F₁ G₁ η₁ η₁'.
    use isweqimplimpl.
    - intro m ; cbn in * ; unfold idfun.
      apply funextsec ; intro X.
      apply funextsec ; intro Y.
      apply funextsec ; intro f.
      pose (pr1 m X Y f) as n.
      cbn in n.
      rewrite id2_rwhisker, lwhisker_id2 in n.
      rewrite id2_left, id2_right in n.
      apply subtypeEquality.
      + intro.
        apply isaprop_is_invertible_2cell.
      + apply n.
    - repeat (apply impred_isaset ; intro).
      use isaset_total2.
      + apply D.
      + intro.
        apply isasetaprop.
        apply isaprop_is_invertible_2cell.
    - apply isaproptotal2.
      + intro.
        apply (@isaprop_is_disp_invertible_2cell (ps_base C D)).
      + intros.
        repeat (apply funextsec ; intro).
        apply D.
  Defined.

  Definition all_invertible_map1cells_inv
             {F G : ps_base C D}
             {η ε : F --> G}
             (m : invertible_2cell η ε)
             {F₁ : map1cells_disp_bicat F}
             {G₁ : map1cells_disp_bicat G}
             {η₁ : F₁ -->[ η ] G₁}
             {ε₁ : F₁ -->[ ε ] G₁}
             (m₁ : η₁ ==>[ m ] ε₁)
    : ε₁ ==>[ m^-1 ] η₁.
  Proof.
    intros X Y f.
    use vcomp_move_R_Mp.
    {
      is_iso.
      apply is_invertible_2cell_to_all_is_invertible.
      is_iso.
    }
    rewrite !vassocl.
    use vcomp_move_L_pM.
    {
      is_iso.
      apply is_invertible_2cell_to_all_is_invertible.
      is_iso.
    }
    exact (!(m₁ X Y f)).
  Qed.

  Definition all_invertible_map1cells
             {F G : ps_base C D}
             {η ε : F --> G}
             (m : invertible_2cell η ε)
             {F₁ : map1cells_disp_bicat F}
             {G₁ : map1cells_disp_bicat G}
             {η₁ : F₁ -->[ η ] G₁}
             {ε₁ : F₁ -->[ ε ] G₁}
             (m₁ : η₁ ==>[ m ] ε₁)
    : is_disp_invertible_2cell m m₁.
  Proof.
    use tpair.
    - exact (all_invertible_map1cells_inv m m₁).
    - split ; repeat (apply funextsec ; intro) ; apply D.
  Qed.

  Section AllInvertible2CellToDispAdjEquiv.
    Variable (F₀ F₀' : ps_base C D)
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀')
             (αequiv : adjoint_equivalence F₀ F₀').

    Local Notation "'α'" := (pr1 αequiv).
    Local Notation "'β'" := (left_adjoint_right_adjoint αequiv).
    Local Notation "'η'" := (left_adjoint_unit αequiv).
    Local Notation "'ε'" := (left_adjoint_counit αequiv).

    Variable (αnat : ∏ (X Y : C) (f : X --> Y),
                  invertible_2cell
                    (α X · F₁' X Y f)
                    (F₁ X Y f · α Y)).

    Local Definition all_invertible_left_adj
      : F₁ -->[ α ] F₁'.
    Proof.
      intros X Y f ; cbn.
      use tpair.
      - exact (αnat X Y f).
      - apply αnat.
    Defined.

    Local Definition τ₁
          {X Y : C}
          (f : C ⟦ X, Y ⟧)
      := (rinvunitor (F₁ X Y f))
           • (F₁ X Y f ◃ η Y)
           • lassociator (F₁ X Y f) (α Y) (β Y)
           • (((αnat X Y f)^-1) ▹ (β Y)).

    Local Definition τ₂
          {X Y : C}
          (f : C ⟦ X, Y ⟧)
      := (ε X ▹ F₁' X Y f)
           • lunitor (F₁' X Y f).

    Local Definition all_invertible_right_adj_help
               {X Y : C}
               (f : C ⟦ X, Y ⟧)
      : (β X · F₁ X Y f) ==> F₁' X Y f · β Y
      := β X ◃ (τ₁ f)
           • lassociator (β X) (α X · F₁' X Y f) (β Y)
           • ((lassociator (β X) (α X) (F₁' X Y f) • τ₂ f)
                ▹ β Y).

    Local Definition all_invertible_right_adj
      : F₁' -->[ β ] F₁.
    Proof.
      intros X Y f.
      use tpair.
      - exact (all_invertible_right_adj_help f).
      - cbn ; unfold all_invertible_right_adj_help, τ₁, τ₂.
        is_iso.
        + exact (is_invertible_2cell_to_all_is_invertible
                   _ _ _
                   (left_equivalence_unit_iso αequiv) Y).
        + exact (is_invertible_2cell_to_all_is_invertible
                   _ _ _
                   (left_equivalence_counit_iso αequiv) X).
    Defined.

    Local Definition all_invertible_unit
      : id_disp F₁ ==>[ η ] all_invertible_left_adj;;all_invertible_right_adj.
    Proof.
      intros X Y f ; simpl.
      unfold all_invertible_right_adj_help.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        do 3 apply maponpaths_2.
        apply maponpaths.
        rewrite !vassocl.
        refine (!_).
        apply lwhisker_vcomp.
      }
      etrans.
      {
        apply maponpaths.
        do 3 apply maponpaths_2.
        rewrite vassocr.
        apply maponpaths_2.
        apply lwhisker_lwhisker_rassociator.
      }
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        rewrite vassocl.
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply lwhisker_vcomp.
        }
        rewrite vassocl.
        apply maponpaths.
        apply rwhisker_lwhisker.
      }
      rewrite !vassocr.
      etrans.
      {
        do 6 apply maponpaths_2.
        apply vcomp_whisker.
      }
      pose (linvunitor_natural (τ₁ f)) as p.
      rewrite <- lwhisker_hcomp in p.
      refine (_ @ vassocr _ _ _).
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      rewrite !vassocr.
      etrans.
      {
        do 7 apply maponpaths_2.
        exact (!p).
      }
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      unfold τ₁.
      rewrite !vassocl.
      do 2 apply maponpaths.
      refine (_ @ id2_right _).
      apply maponpaths.
      use vcomp_move_R_pM.
      { is_iso. }
      simpl.
      refine (_ @ !(id2_right _)).
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      pose (inverse_pentagon_4 (β Y) (α X · F₁' X Y f) (β X) (α X)) as q.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp in q.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          exact q.
        }
        rewrite !vassocl.
        rewrite rassociator_lassociator.
        rewrite id2_right.
        reflexivity.
      }
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite rwhisker_vcomp.
        reflexivity.
      }
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- rwhisker_rwhisker.
        rewrite !vassocr.
        rewrite linvunitor_assoc.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          apply id2_left.
        }
        rewrite rwhisker_vcomp.
        reflexivity.
      }
      rewrite rwhisker_vcomp.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      etrans.
      {
        rewrite linvunitor_assoc.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          do 2 apply maponpaths_2.
          rewrite <- rwhisker_rwhisker_alt.
          reflexivity.
        }
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite <- lwhisker_vcomp.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite inverse_pentagon.
          rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite lwhisker_vcomp.
            rewrite rassociator_lassociator.
            apply lwhisker_id2.
          }
          apply id2_right.
        }
        unfold τ₂.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite <- lwhisker_vcomp.
          rewrite vassocr.
          etrans.
          {
            apply maponpaths_2.
            apply rwhisker_lwhisker_rassociator.
          }
          rewrite !vassocl.
          apply maponpaths.
          rewrite lwhisker_hcomp.
          apply triangle_l.
        }
        rewrite <- rwhisker_hcomp.
        rewrite !rwhisker_vcomp.
        reflexivity.
      }
      pose (pr1 (pr122 αequiv)) as r.
      rewrite !vassocl in r.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      exact (eqtohomot r X).
    Qed.

    Local Definition all_invertible_counit
      : (all_invertible_right_adj;; all_invertible_left_adj) ==>[ ε ] id_disp F₁'.
    Proof.
      (*
      intros X Y f ; simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply rinvunitor_natural.
        }
        rewrite <- rwhisker_hcomp.
        reflexivity.
      }
      unfold all_invertible_right_adj_help.
      refine (!_).
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        do 3 apply maponpaths.
        etrans.
        {
          rewrite vassocr.
          apply maponpaths_2.
          apply rwhisker_rwhisker_alt.
        }
        rewrite vassocl.
        apply maponpaths.
        rewrite vcomp_whisker.
        unfold τ₂.
        apply maponpaths.
        refine (!_).
        apply rwhisker_vcomp.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          do 5 apply maponpaths_2.
          refine (!_).
          apply rwhisker_lwhisker.
        }
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        etrans.
        {
          rewrite !vassocl.
          do 2 apply maponpaths.
          apply rwhisker_rwhisker_alt.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        refine (!_).
        rewrite rwhisker_hcomp.
        rewrite !vassocl.
        apply inverse_pentagon_5.
      }
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite <- vcomp_whisker.
          reflexivity.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        apply rwhisker_vcomp.
      }
      use vcomp_move_L_Mp.
      { is_iso. }
      simpl.
      rewrite !vassocl.
      etrans.
      {
        do 6 apply maponpaths.
        rewrite <- runitor_triangle.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        reflexivity.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          rewrite <- rwhisker_vcomp.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite rwhisker_rwhisker_alt.
          reflexivity.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_hcomp.
        refine (!_).
        apply inverse_pentagon_5.
      }
      rewrite <- lwhisker_hcomp.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite vcomp_whisker.
        reflexivity.
      }
      rewrite !vassocr.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      refine (_ @ id2_rwhisker _ _).
      refine (_ @ maponpaths _ (id2_rwhisker _ _)).
      pose (eqtohomot (pr2 (pr122 αequiv)) X) as p.
      cbn in p.
      rewrite !vassocl.
      unfold τ₁.
      rewrite !vassocl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          do 4 apply maponpaths_2.
          rewrite lwhisker_vcomp.
          reflexivity.
        }
        rewrite !lwhisker_vcomp.
        rewrite !vassocl.




      use vcomp_move_R_pM.
      { is_iso. }
      simpl.
      rewrite id2_right.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      {
        is_iso.
      }
      simpl.
      rewrite !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply lwhisker_lwhisker.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        rewrite !vassocl.
        rewrite lwhisker_lwhisker_rassociator.
        reflexivity.
      }
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        refine (!_).
        apply lwhisker_vcomp.
      }
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      refine (!_).
      etrans.
      {
        rewrite left_unit_inv_assoc.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          etrans.
          {
            apply maponpaths_2.
            apply inverse_pentagon.
          }
          rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
          rewrite !vassocl.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite lwhisker_vcomp.
            rewrite rassociator_lassociator.
            apply lwhisker_id2.
          }
          rewrite id2_right.
          reflexivity.
        }
        reflexivity.
      }
      unfold τ₁.
      pose (pr1 (pr122 αequiv)).

      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite rinvunitor_triangle.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
      rewrite <- (vcomp_lunitor (F₁ X Y f)).
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite lwhisker_vcomp.
      rewrite vcomp_lid, lwhisker_id2, id2_left.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      rewrite runitor_triangle.
      rewrite rinvunitor_runitor, id2_right.
      rewrite !vassocr.
      do 2 (apply maponpaths_2).
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite triangle_r.
      rewrite lunitor_runitor_identity.
      reflexivity.
       *)
    Admitted.

    Definition all_invertible_2cell_to_disp_adjoint_equivalence
      : disp_adjoint_equivalence αequiv F₁ F₁'.
    Proof.
      use tpair.
      - exact all_invertible_left_adj.
      - use tpair.
        + use tpair.
          * exact all_invertible_right_adj.
          * split.
            ** exact all_invertible_unit.
            ** exact all_invertible_counit.
        + split ; split.
          * repeat (apply funextsec ; intro).
            apply D.
          * repeat (apply funextsec ; intro).
            apply D.
          * apply all_invertible_map1cells.
          * apply all_invertible_map1cells.
    Defined.
  End AllInvertible2CellToDispAdjEquiv.

  Definition disp_adjoint_equivalence_to_all_invertible_2cell
             (F₀ F₀' : ps_base C D)
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀')
             (αequiv : adjoint_equivalence F₀ F₀')
    : disp_adjoint_equivalence αequiv F₁ F₁'
      →
      (∏ (X Y : C) (f : X --> Y),
       invertible_2cell
         (pr1 αequiv X · F₁' X Y f)
         (F₁ X Y f · pr1 αequiv Y)).
  Proof.
    intros m X Y f.
    use tpair.
    - exact (pr1 m X Y f).
    - apply (pr1 m X Y f).
  Defined.

  Definition all_invertible_2cell_is_disp_adjoint_equivalence
             (HD_2_1 : is_univalent_2_1 D)
             (F₀ F₀' : ps_base C D)
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀')
             (αequiv : adjoint_equivalence F₀ F₀')
    : (∏ (X Y : C) (f : X --> Y),
       invertible_2cell
         (pr1 αequiv X · F₁' X Y f)
         (F₁ X Y f · pr1 αequiv Y))
        ≃
        disp_adjoint_equivalence αequiv F₁ F₁'.
  Proof.
    refine (make_weq (all_invertible_2cell_to_disp_adjoint_equivalence
                        F₀ F₀' F₁ F₁' αequiv) _).
    use isweq_iso.
    - exact (disp_adjoint_equivalence_to_all_invertible_2cell F₀ F₀' F₁ F₁' αequiv).
    - intro m.
      apply funextsec ; intro X.
      apply funextsec ; intro Y.
      apply funextsec ; intro f.
      apply subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      apply idpath.
    - intro m.
      use subtypeEquality.
      {
        intro.
        apply isaprop_disp_left_adjoint_equivalence.
        + exact (ps_base_is_univalent_2_1 _ _ HD_2_1).
        + apply map1cells_disp_univalent_2_1.
      }
      apply funextsec ; intro X.
      apply funextsec ; intro Y.
      apply funextsec ; intro f.
      apply subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      reflexivity.
  Defined.

  Definition invertible_2cell_weq_map
             {F₀ : ps_base C D}
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀)
             {X Y : C}
             (f : X --> Y)
    : (invertible_2cell (F₁ X Y f) (F₁' X Y f))
        ->
        invertible_2cell (id₁ (F₀ X) · F₁' X Y f) (F₁ X Y f · id₁ (F₀ Y)).
  Proof.
    intros α.
    use make_invertible_2cell.
    - exact (lunitor _ • α^-1 • rinvunitor _).
    - is_iso.
  Defined.

  Definition invertible_2cell_inv_map
             {F₀ : ps_base C D}
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀)
             {X Y : C}
             (f : X --> Y)
    : invertible_2cell (id₁ (F₀ X) · F₁' X Y f) (F₁ X Y f · id₁ (F₀ Y))
      ->
      invertible_2cell (F₁ X Y f) (F₁' X Y f).
  Proof.
    intros α.
    use make_invertible_2cell.
    - exact (rinvunitor _ • α^-1 • lunitor _).
    - is_iso.
  Defined.

  Definition invertible_2cell_weq
             {F₀ : ps_base C D}
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀)
             {X Y : C}
             (f : X --> Y)
    : (invertible_2cell (F₁ X Y f) (F₁' X Y f))
      ≃
      invertible_2cell (id₁ (F₀ X) · F₁' X Y f) (F₁ X Y f · id₁ (F₀ Y)).
  Proof.
    use make_weq.
    - exact (invertible_2cell_weq_map F₁ F₁' f).
    - use gradth.
      + exact (invertible_2cell_inv_map F₁ F₁' f).
      + intros α.
        use subtypeEquality.
        { intro ; apply isaprop_is_invertible_2cell. }
        cbn.
        abstract (rewrite !vassocr ;
                  rewrite rinvunitor_runitor ;
                  rewrite id2_left ;
                  rewrite !vassocl ;
                  rewrite linvunitor_lunitor ;
                  apply id2_right).
      + intros α.
        use subtypeEquality.
        { intro ; apply isaprop_is_invertible_2cell. }
        cbn.
        abstract (rewrite !vassocr ;
                  rewrite lunitor_linvunitor ;
                  rewrite id2_left ;
                  rewrite !vassocl ;
                  rewrite runitor_rinvunitor ;
                  apply id2_right).
  Defined.

  Definition map1cells_idtoiso__2_0_alt
             (HD_2_1 : is_univalent_2_1 D)
             {F₀ : ps_base C D}
             (F₁ : map1cells_disp_bicat F₀)
             (F₁' : map1cells_disp_bicat F₀)
    : F₁ = F₁'
      ≃
      disp_adjoint_equivalence (idtoiso_2_0 F₀ F₀ (idpath F₀)) F₁ F₁'.
  Proof.
    refine (all_invertible_2cell_is_disp_adjoint_equivalence
                   HD_2_1 F₀ F₀ F₁ F₁'
                   _ ∘ _)%weq.
    simple refine (_ ∘ make_weq _ (isweqtoforallpaths _ _ _))%weq.
    use weqonsecfibers.
    intro X.
    simple refine (_ ∘ make_weq _ (isweqtoforallpaths _ _ _))%weq.
    use weqonsecfibers.
    intros Y.
    simple refine (_ ∘ make_weq _ (isweqtoforallpaths _ _ _))%weq.
    use weqonsecfibers.
    intros f.
    cbn.
    refine (_ ∘ make_weq (idtoiso_2_1 (F₁ X Y f) (F₁' X Y f)) (HD_2_1 _ _ _ _))%weq.
    exact (invertible_2cell_weq F₁ F₁' f).
  Defined.

  Definition map1cells_disp_univalent_2_0
             (HD_2_1 : is_univalent_2_1 D)
    : disp_univalent_2_0 map1cells_disp_bicat.
  Proof.
    apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros F₀ F₁ F₁'.
    use weqhomot.
    - exact (map1cells_idtoiso__2_0_alt HD_2_1 F₁ F₁').
    - intro p.
      induction p.
      apply subtypeEquality.
      {
        intro.
        apply isaprop_disp_left_adjoint_equivalence.
        + exact (ps_base_is_univalent_2_1 _ _ HD_2_1).
        + apply map1cells_disp_univalent_2_1.
      }
      apply funextsec ; intro X.
      apply funextsec ; intro Y.
      apply funextsec ; intro f.
      apply subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      cbn ; unfold idfun.
      rewrite id2_right.
      reflexivity.
  Defined.

  Definition map1cells := total_bicat map1cells_disp_bicat.

  Definition map1cells_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 map1cells.
  Proof.
    apply total_is_univalent_2_1.
    - apply ps_base_is_univalent_2_1.
      exact HD_2_1.
    - exact map1cells_disp_univalent_2_1.
  Defined.

  Definition map1cells_is_univalent_2_0
             (HD : is_univalent_2 D)
    : is_univalent_2_0 map1cells.
  Proof.
    apply total_is_univalent_2_0.
    - apply ps_base_is_univalent_2. exact HD.
    - exact (map1cells_disp_univalent_2_0 (pr2 HD)).
  Defined.

  Definition map1cells_is_univalent_2
             (HD : is_univalent_2 D)
    : is_univalent_2 map1cells.
  Proof.
    split.
    - apply map1cells_is_univalent_2_0; assumption.
    - apply map1cells_is_univalent_2_1.
      exact (pr2 HD).
  Defined.

End Map1Cells.

Definition Fobj
           {C D : bicat}
           (F : map1cells C D)
  : C → D
  := pr1 F.

Definition Fmor
           {C D : bicat}
           (F : map1cells C D)
  : ∏ {X Y : C}, X --> Y → Fobj F X --> Fobj F Y
  := pr2 F.

Definition ηobj
           {C D : bicat}
           {F G : map1cells C D}
           (η : F --> G)
  : ∏ (X : C), Fobj F X --> Fobj G X
  := pr1 η.

Definition ηmor
           {C D : bicat}
           {F G : map1cells C D}
           (η : F --> G)
  : ∏ {X Y : C} (f : X --> Y), ηobj η X · Fmor G f ==> Fmor F f · ηobj η Y
  := pr2 η.
