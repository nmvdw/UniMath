Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FiniteLimits.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Comprehension.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Local Open Scope cat.

Definition is_iso_disp_codomain
           {C : category}
           {x : C}
           {xx yy : disp_codomain C x}
           (f : xx -->[ identity x ] yy)
           (g : yy -->[ identity x ] xx)
           (fg : pr1 f · pr1 g = identity _)
           (gf : pr1 g · pr1 f = identity _)
  : is_iso_disp (identity_iso x) f.
Proof.
  use tpair.
  - exact g.
  - split.
    + abstract
        (use subtypePath ; [ intro ; apply C | ] ;
         cbn ;
         refine (!_) ;
         refine (maponpaths pr1 (transportf_codomain _ _ _ _ _) @ _) ;
         exact (!gf)).
    + abstract
        (use subtypePath ; [ intro ; apply C | ] ;
         cbn ;
         refine (!_) ;
         refine (maponpaths pr1 (transportf_codomain _ _ _ _ _) @ _) ;
         exact (!fg)).
Defined.

Definition make_iso_disp_codomain
           {C : category}
           {x : C}
           {xx yy : disp_codomain C x}
           (f : xx -->[ identity x ] yy)
           (g : yy -->[ identity x ] xx)
           (fg : pr1 f · pr1 g = identity _)
           (gf : pr1 g · pr1 f = identity _)
  : iso_disp (identity_iso x) xx yy.
Proof.
  use make_iso_disp.
  - exact f.
  - use is_iso_disp_codomain.
    + exact g.
    + exact fg.
    + exact gf.
Defined.

Definition iso_disp_weq_codomain_map_help
           {C : category}
           {x : C}
           {xx yy : disp_codomain C x}
           (f : iso (pr1 xx) (pr1 yy))
           (h : f · pr2 yy = pr2 xx)
  : iso_disp (identity_iso x) xx yy.
Proof.
  use make_iso_disp_codomain.
  - simple refine (_ ,, _).
    + exact (pr1 f).
    + simpl.
      rewrite id_right.
      exact h.
  - simple refine (_ ,, _).
    + exact (inv_from_iso f).
    + simpl.
      rewrite id_right.
      use iso_inv_on_right.
      rewrite h.
      apply idpath.
  - apply iso_inv_after_iso.
  - apply iso_after_iso_inv.
Defined.

Definition iso_disp_weq_codomain_map
           {C : category}
           {x : C}
           {xx yy : disp_codomain C x}
           (ff : ∑ (f : iso (pr1 xx) (pr1 yy)), f · pr2 yy = pr2 xx)
  : iso_disp (identity_iso x) xx yy.
Proof.
  use iso_disp_weq_codomain_map_help.
  - exact (pr1 ff).
  - exact (pr2 ff).
Defined.

Definition iso_disp_weq_codomain_inv
           {C : category}
           {x : C}
           {xx yy : disp_codomain C x}
           (ff : iso_disp (identity_iso x) xx yy)
  : ∑ (f : iso (pr1 xx) (pr1 yy)), f · pr2 yy = pr2 xx.
Proof.
  simple refine (_ ,, _).
  - use make_iso.
    + exact (pr11 ff).
    + use is_iso_qinv.
      * exact (pr1 (inv_mor_disp_from_iso ff)).
      * split.
        ** exact (maponpaths
                    pr1
                    (inv_mor_after_iso_disp ff
                     @ transportf_codomain _ _ _ _ _)).
        ** exact (maponpaths
                    pr1
                    (iso_disp_after_inv_mor ff
                     @ transportf_codomain _ _ _ _ _)).
  - abstract
      (refine (pr21 ff @ _) ;
       apply id_right).
Defined.

Definition iso_disp_weq_pr2
           {C : category}
           {x : C}
           {xx yy : disp_codomain C x}
           (p : pr1 xx = pr1 yy)
  : transportf _ p (pr2 xx) = pr2 yy ≃ idtoiso p · pr2 yy = pr2 xx.
Proof.
  induction xx as [xx fx].
  induction yy as [yy fy].
  simpl in *.
  induction p ; cbn.
  use weqiff.
  - split.
    + intro p.
      rewrite id_left, p.
      apply idpath.
    + intro p.
      rewrite id_left in p.
      exact (!p).
  - apply C.
  - apply C.
Qed.

Definition iso_disp_weq_codomain
           {C : category}
           {x : C}
           (xx yy : disp_codomain C x)
  : (∑ (f : iso (pr1 xx) (pr1 yy)), f · pr2 yy = pr2 xx)
    ≃
    iso_disp (identity_iso x) xx yy.
Proof.
  use make_weq.
  - exact iso_disp_weq_codomain_map.
  - use gradth.
    + exact iso_disp_weq_codomain_inv.
    + intro ff.
      use subtypePath.
      {
        intro ; apply C.
      }
      use subtypePath.
      {
        intro ; apply isaprop_is_iso.
      }
      apply idpath.
    + intro ff.
      use subtypePath.
      {
        intro ; apply isaprop_is_iso_disp.
      }
      use subtypePath.
      {
        intro ; apply C.
      }
      apply idpath.
Defined.

Definition idtoiso_disp_codomain
           {C : category}
           (HC : is_univalent C)
           {x : C}
           (xx yy : disp_codomain C x)
  : xx = yy ≃ iso_disp (identity_iso x) xx yy
  := (iso_disp_weq_codomain xx yy
      ∘ weqtotal2 (make_weq idtoiso (pr1 HC _ _)) iso_disp_weq_pr2
      ∘ total2_paths_equiv _ xx yy)%weq.

Definition is_univalent_disp_codomain
           (C : category)
           (HC : is_univalent C)
  : is_univalent_disp (disp_codomain C).
Proof.
  use is_univalent_disp_from_fibers.
  intros x xx yy.
  use weqhomot.
  - exact (idtoiso_disp_codomain HC xx yy).
  - intro p.
    induction p.
    use subtypePath.
    {
      intro ; apply isaprop_is_iso_disp.
    }
    use subtypePath.
    {
      intro ; apply C.
    }
    apply idpath.
Defined.

Definition cleaving_codomain
           (C : category)
           (PB : Pullbacks C)
  : cleaving (disp_codomain C).
Proof.
  intros c₁ c₂ f g.
  pose (pb := PB _ _ _ (pr2 g) f).
  simple refine ((_ ,, _) ,, (_ ,, _) ,, _) ; simpl.
  - exact (pr11 pb).
  - apply PullbackPr2.
  - apply PullbackPr1.
  - apply PullbackSqrCommutes.
  - apply isPullback_cartesian_in_cod_disp.
    apply pb.
Defined.

Definition fin_lim_to_comp_cat
           (C : bicat_of_cats)
           (LC : disp_bicat_fin_lim C)
  : disp_bicat_comprehension_category C.
Proof.
  use make_comprehension_category_on.
  - exact (disp_codomain _).
  - apply is_univalent_disp_codomain.
    apply C.
  - apply cleaving_codomain.
    apply LC.
  - apply LC.
  - apply disp_functor_identity.
  - intros ? ? ? ? ? ? H.
    exact H.
Defined.

Definition fin_lim_functor_to_comp_cat_functor
           {C D : bicat_of_cats}
           {F : C --> D}
           {LC : disp_bicat_fin_lim C}
           {LD : disp_bicat_fin_lim D}
           (LF : LC -->[ F ] LD)
  : fin_lim_to_comp_cat C LC
    -->[ F ]
    fin_lim_to_comp_cat D LD.
Proof.
  use (@make_comprehension_cat_mor_on
         (C ,, fin_lim_to_comp_cat C LC)
         (D ,, fin_lim_to_comp_cat D LD)).
  - apply LF.
  - exact (disp_codomain_functor F).
  - use tpair.
    + intros x xx.
      simple refine (identity _ ,, _) ; cbn.
      (*
      rewrite !id_left, !id_right.
      apply idpath.
       *)
      apply TODO.
    + (*
      simpl.
      intros x y f xx yy ff.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      simpl.
      unfold transportb.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_codomain _ _ _ _ _).
      }
      simpl.
      rewrite id_left, id_right.
      apply idpath.
       *)
      apply TODO.
Defined.

Definition fin_lim_trans_to_comp_cat_trans
           {C D : bicat_of_cats}
           {F G : C --> D}
           {τ : F ==> G}
           {LC : disp_bicat_fin_lim C}
           {LD : disp_bicat_fin_lim D}
           {LF : LC -->[ F ] LD}
           {LG : LC -->[ G ] LD}
           (Lτ : LF ==>[ τ ] LG)
  : fin_lim_functor_to_comp_cat_functor LF
    ==>[ τ ]
    fin_lim_functor_to_comp_cat_functor LG.
Proof.
  use (@make_comprehension_cat_2cell_on
           (C ,, _)
           (D ,, _)
           (F ,, fin_lim_functor_to_comp_cat_functor LF)
           (G ,, fin_lim_functor_to_comp_cat_functor LG)).
  - exact (disp_codomain_nat_trans τ).
  - abstract
      (intros x xx ;
       cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition finite_limits_to_comprehension_identity
           {C : bicat_of_cats}
           (LC : disp_bicat_fin_lim C)
  : disp_invertible_2cell
      (psfunctor_id (id_psfunctor bicat_of_cats) C)
      (id_disp (fin_lim_to_comp_cat C LC))
      (fin_lim_functor_to_comp_cat_functor (id_disp LC)).
Proof.
  use tpair.
  - use (@make_comprehension_cat_2cell_on
           (C ,, _)
           (C ,, _)
           (_ ,, id_disp (fin_lim_to_comp_cat C LC))
           (_ ,, fin_lim_functor_to_comp_cat_functor (id_disp LC))).
    + use tpair.
      * intros x xx.
        refine (identity _ ,, _).
        (*
        simpl.
        rewrite id_left, id_right.
        apply idpath.
         *)
        apply TODO.
      * (*
        simpl.
        intros x y f xx yy ff.
        simpl.
        use subtypePath.
        {
          intro.
          apply C.
        }
        simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (transportf_codomain _ _ _ _ _).
        }
        simpl.
        rewrite id_left, id_right.
        apply idpath.
         *)
        apply TODO.
    + simpl.
      intros.
      apply idpath.
  - (* principle for invertible 2-cells is needed *)

    (*use tpair.
    + use (@make_comprehension_cat_2cell_on
             (C ,, _)
             (C ,, _)
             (_ ,, fin_lim_functor_to_comp_cat_functor (id_disp LC))
             (_ ,, id_disp (fin_lim_to_comp_cat C LC))).
      * use tpair.
        ** intros x xx.
           refine (identity _ ,, _).
           (*
           simpl.
           rewrite id_left, id_right.
           apply idpath.
            *)
           apply TODO.
        ** apply TODO.
      * apply TODO.
    + apply TODO.
     *)
    apply TODO.
Defined.

Definition finite_limits_to_comprehension_disp_psfunctor_data
  : disp_psfunctor_data
      disp_bicat_fin_lim
      disp_bicat_comprehension_category
      (id_psfunctor _).
Proof.
  use make_disp_psfunctor_data.
  - exact fin_lim_to_comp_cat.
  - exact @fin_lim_functor_to_comp_cat_functor.
  - exact @fin_lim_trans_to_comp_cat_trans.
  - exact @finite_limits_to_comprehension_identity.
  - apply TODO.
Defined.

Definition finite_limits_to_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      _ _ _
      finite_limits_to_comprehension_disp_psfunctor_data.
Proof.
  repeat split.
  - intros C D F LC LD LF.
    (* equality principles for 2-cells are required *)
    simpl.
    apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
Qed.

Definition finite_limits_to_comprehension_disp_psfunctor
  : disp_psfunctor
      disp_bicat_fin_lim
      disp_bicat_comprehension_category
      (id_psfunctor _).
Proof.
  simple refine (_ ,, _).
  - exact finite_limits_to_comprehension_disp_psfunctor_data.
  - exact finite_limits_to_comprehension_is_disp_psfunctor.
Defined.
