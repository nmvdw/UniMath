Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section CodomainArrow.
  Variable (B : bicat).

  Definition cod_prod_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells (prod_bicat B B).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ X, pr2 X --> pr1 X).
        * exact (λ X Y fX fY f, fX · pr1 f ==> pr2 f · fY).
      + use tpair.
        * exact (λ X fX, runitor _ • linvunitor _).
        * exact (λ X Y Z f g fX fY fZ ff fg,
                 lassociator _ _ _
                 • (ff ▹ _)
                 • rassociator _ _ _
                 • (_ ◃ fg)
                 • lassociator _ _ _).
    - exact (λ X Y f g α fX fY ff fg,
             ff • (pr2 α ▹ _)
             =
             (_ ◃ pr1 α) • fg).
  Defined.

  Definition cod_prod_disp_prebicat_ops
    : disp_prebicat_ops cod_prod_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite id2_rwhisker, id2_right.
      rewrite lwhisker_id2, id2_left.
      apply idpath.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      rewrite lunitor_triangle.
      rewrite linvunitor_lunitor.
      apply id2_right.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite !vassocl.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite linvunitor_lunitor, id2_right.
      rewrite runitor_triangle.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite left_unit_assoc.
      apply idpath.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite !vassocr.
      rewrite rinvunitor_runitor, id2_left.
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      rewrite !vassocl.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite rassociator_lassociator, id2_right.
      apply idpath.
    - intros X Y f fX fY pf.
      simpl ; cbn.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite !rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- left_unit_inv_assoc.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite rinvunitor_runitor, id2_left.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      apply idpath.
    - intros X₁ X₂ X₃ X₄ f g h fX₁ fX₂ fX₃ fX₄ pf pg ph.
      simpl ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        etrans.
        {
          do 8 apply maponpaths_2.
          apply lassociator_lassociator.
        }
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        apply lassociator_lassociator.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_L_Mp.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocl.
        do 4 apply maponpaths.
        exact (!(lassociator_lassociator _ _ _ _)).
      }
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator, lwhisker_id2.
        apply id2_left.
      }
      rewrite rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_R_pM.
      { is_iso. }
      simpl.
      rewrite !vassocr.
      use vcomp_move_L_Mp.
      { is_iso. }
      simpl.
      rewrite lassociator_lassociator.
      apply idpath.
    - intros X₁ X₂ X₃ X₄ f g h fX₁ fX₂ fX₃ fX₄ pf pg ph.
      simpl ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 7 apply maponpaths_2.
        rewrite lassociator_lassociator.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator, id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lassociator_lassociator.
      rewrite vassocr.
      apply idpath.
    - intros X Y f g h p q fX fY pf pg ph pp pq.
      simpl ; cbn in *.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite pp.
      rewrite !vassocl.
      rewrite pq.
      rewrite !vassocr.
      apply maponpaths_2.
      apply lwhisker_vcomp.
    - intros X Y Z f g₁ g₂ p fX fY fZ pf pg₁ pg₂ pp.
      simpl ; cbn in *.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      exact pp.
    - intros X Y Z f₁ f₂ g p fX fY fZ pf₁ pf₂ pg pp.
      simpl ; cbn in *.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      rewrite <- pp.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      apply idpath.
  Qed.

  Definition cod_prod_disp_prebicat_data
    : disp_prebicat_data (prod_bicat B B).
  Proof.
    use tpair.
    - exact cod_prod_disp_prebicat_1_id_comp_cells.
    - exact cod_prod_disp_prebicat_ops.
  Defined.

  Definition cod_prod_disp_prebicat_laws
    : disp_prebicat_laws cod_prod_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply B.
  Qed.

  Definition cod_prod_disp_prebicat
    : disp_prebicat (prod_bicat B B).
  Proof.
    use tpair.
    - exact cod_prod_disp_prebicat_data.
    - exact cod_prod_disp_prebicat_laws.
  Defined.

  Definition cod_prod_has_disp_cellset
    : has_disp_cellset cod_prod_disp_prebicat.
  Proof.
    intros X Y f g p fX fY pf pg.
    apply isasetaprop.
    apply B.
  Qed.

  Definition cod_prod_disp_bicat_help
    : disp_bicat (prod_bicat B B).
  Proof.
    use tpair.
    - exact cod_prod_disp_prebicat.
    - exact cod_prod_has_disp_cellset.
  Defined.

  Definition cod_prod_disp_bicat
    : disp_bicat B
    := sigma_bicat _ _ cod_prod_disp_bicat_help.
End CodomainArrow.

(** Some projections and builders *)
Definition dom
           {B : bicat}
           {X : B}
           (f : cod_prod_disp_bicat B X)
  : B
  := pr1 f.

Definition ar
           {B : bicat}
           {X : B}
           (f : cod_prod_disp_bicat B X)
  : dom f --> X
  := pr2 f.

Definition make_ar
           {B : bicat}
           {X Y : B}
           (f : X --> Y)
  : cod_prod_disp_bicat B Y
  := (X ,, f).

Definition make_disp_1cell_cod
           {B : bicat}
           {X Y : B}
           {f : X --> Y}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           (h : dom dX --> dom dY)
           (p : pr2 dX · f ==> h · pr2 dY)
  : dX -->[ f ] dY
  := h ,, p.

Definition coherent_homot
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           (α : f ==> g)
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {df : dX -->[ f ] dY}
           {dg : dX -->[ g ] dY}
           (h : pr1 df ==> pr1 dg)
  : UU
  := pr2 df • (h ▹ pr2 dY) = (pr2 dX ◃ α) • pr2 dg.

Definition make_disp_2cell_cod
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           {α : f ==> g}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {df : dX -->[ f ] dY}
           {dg : dX -->[ g ] dY}
           (h : pr1 df ==> pr1 dg)
           (hh : coherent_homot α h)
  : df ==>[ α ] dg
  := h ,, hh.

Definition is_disp_invertible_2cell_cod
           {B : bicat}
           {X Y : B}
           {f g : X --> Y}
           {α : invertible_2cell f g}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {ff : dX -->[ f ] dY}
           {gg : dX -->[ g ] dY}
           (αα : ff ==>[ α ] gg)
           (Hαα : is_invertible_2cell (pr1 αα))
  : is_disp_invertible_2cell α αα.
Proof.
  use tpair.
  - use tpair.
    + exact (Hαα^-1).
    + abstract
        (simpl ;
         use vcomp_move_R_Mp ; is_iso ;
         simpl ;
         rewrite !vassocl ;
         use vcomp_move_L_pM ; is_iso ;
         simpl ;
         refine (!_) ;
         apply αα).
  - split.
    + abstract
        (use subtypePath ; [ intro ; apply B | ] ;
         simpl ;
         unfold transportb ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         unfold idfun ; cbn ;
         apply vcomp_rinv).
    + abstract
        (use subtypePath ; [ intro ; apply B | ] ;
         simpl ;
         unfold transportb ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         unfold idfun ; cbn ;
         apply vcomp_linv).
Defined.

Definition disp_locally_groupoid_cod
           (B : bicat)
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
  : disp_locally_groupoid (cod_prod_disp_bicat B).
Proof.
  use make_disp_locally_groupoid_univalent_2_1.
  - intros X Y f dX dY pf₁ pf₂ px.
    use tpair.
    + use tpair.
      * exact (pr1 (inv_B _ _ _ _ (pr1 px))).
      * abstract
          (simpl ; cbn ;
           pose (pr2 px) as m ;
           cbn in m ;
           use vcomp_move_L_pM ; try is_iso ;
           simpl ;
           rewrite vassocr ;
           rewrite <- m ;
           rewrite vassocl ;
           rewrite rwhisker_vcomp ;
           refine (_ @ id2_right _) ;
           apply maponpaths ;
           refine (_ @ id2_rwhisker _ _) ;
           apply maponpaths ;
           apply inv_B).
    + split.
      * abstract
          (simpl ; cbn ;
           use subtypePath ; [intro ; apply B | ] ;
           simpl ;
           unfold transportb ; rewrite pr1_transportf ; rewrite transportf_const ;
           unfold idfun ; cbn ;
           apply inv_B).
      * abstract
          (simpl ; cbn ;
           use subtypePath ; [intro ; apply B | ] ;
           simpl ;
           unfold transportb ; rewrite pr1_transportf ; rewrite transportf_const ;
           unfold idfun ; cbn ;
           apply inv_B).
  - exact HB.
Defined.

Definition disp_locally_groupoid_cod_one_types
  : disp_locally_groupoid (cod_prod_disp_bicat one_types).
Proof.
  use disp_locally_groupoid_cod.
  - exact one_types_is_univalent_2_1.
  - exact @one_type_2cell_iso.
Defined.
