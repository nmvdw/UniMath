Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Core.Univalence.

Open Scope cat.
Open Scope mor_disp.

(** Move somewhere else? *)
(** Needed operations *)
Definition transportf_reindex_single
           {C' C : category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {x : C'}
           {xx xx' : (reindex_disp_cat F D) x}
           {f g : x --> x}
           (p : f = g)
           (z : xx' -->[ f] xx')
  : transportf
      (@mor_disp C' (reindex_disp_cat F D) x x xx' xx')
      p
      z
    =
    transportf
      (@mor_disp C D (F x) (F x) xx' xx')
      (maponpaths (λ q, (# F)%Cat q) p)
      z.
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_reindex
           {C' C : category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : category}
           {D'' : disp_cat C''}
           {F' : C'' ⟶ C'}
           (GG : disp_functor (F' ∙ F) D'' D)
           {x y : C'}
           {xx : D(F x)} {yy : D(F y)}
           {f g : x --> y}
           (p : f = g)
           (ff : xx -->[ (# F)%Cat f] yy)
  : transportf
      (@mor_disp
         C'
         (reindex_disp_cat F D)
         _ _
         xx yy)
      p
      ff
    =
    transportf
      (@mor_disp
         C
         D
         _ _
         xx yy)
      (maponpaths (#F)%Cat p)
      ff.
Proof.
  induction p ; apply idpath.
Qed.

(** Univalence of reindexing *)
Definition iso_to_iso_reindex
           {C' C : category}
           (D : disp_cat C)
           (F : C' ⟶ C)
           {x : C'}
           (xx xx' : (reindex_disp_cat F D) x)
  : @iso_disp C D (F x) (F x) (identity_iso (F x)) xx xx'
    →
    @iso_disp C' (reindex_disp_cat F D) x x (identity_iso x) xx xx'.
Proof.
  intros f.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (transportb _ (functor_id F x) (pr1 f)).
  - exact (transportb _ (functor_id F x) (inv_mor_disp_from_iso f)).
  - abstract
      (cbn ; unfold transportb ;
       refine (_ @ !(@transportf_reindex_single C' C D F x xx xx' _ _ _ _)) ;
       rewrite mor_disp_transportf_postwhisker ;
       rewrite mor_disp_transportf_prewhisker ;
       rewrite !transport_f_f ;
       refine (maponpaths _ (iso_disp_after_inv_mor f) @ _) ;
       unfold transportb ;
       rewrite !transport_f_f ;
       refine (!_) ;
       cbn ;
       apply transportf_paths ;
       apply C).
  - abstract
      (cbn ; unfold transportb ;
       refine (_ @ !(@transportf_reindex_single C' C D F x xx' xx _ _ _ _)) ;
       rewrite mor_disp_transportf_postwhisker ;
       rewrite mor_disp_transportf_prewhisker ;
       rewrite !transport_f_f ;
       refine (maponpaths _ (inv_mor_after_iso_disp f) @ _) ;
       unfold transportb ;
       rewrite !transport_f_f ;
       refine (!_) ;
       cbn ;
       apply transportf_paths ;
       apply C).
Defined.

Definition iso_reindex_to_iso
           {C' C : category}
           (D : disp_cat C)
           (F : C' ⟶ C)
           {x : C'}
           (xx xx' : (reindex_disp_cat F D) x)
  : @iso_disp C' (reindex_disp_cat F D) x x (identity_iso x) xx xx'
    →
    @iso_disp C D (F x) (F x) (identity_iso (F x)) xx xx'.
Proof.
  intros f.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (transportf _ (functor_id F x) (pr1 f)).
  - exact (transportf _ (functor_id F x) (inv_mor_disp_from_iso f)).
  - abstract
      (unfold transportb ;
       cbn ;
       rewrite mor_disp_transportf_postwhisker ;
       rewrite mor_disp_transportf_prewhisker ;
       rewrite transport_f_f ;
       pose (iso_disp_after_inv_mor f) as p ;
       cbn in p ;
       refine (maponpaths _ (transportf_transpose_right p) @ _) ;
       unfold transportb ;
       rewrite !transport_f_f ;
       refine (maponpaths _ (@transportf_reindex_single C' C D F x xx xx' _ _ _ _)
               @ _) ;
       rewrite !transport_f_f ;
       apply transportf_paths ;
       apply C).
  - abstract
      (unfold transportb ;
       cbn ;
       rewrite mor_disp_transportf_postwhisker ;
       rewrite mor_disp_transportf_prewhisker ;
       rewrite transport_f_f ;
       pose (inv_mor_after_iso_disp f) as p ;
       cbn in p ;
       refine (maponpaths _ (transportf_transpose_right p) @ _) ;
       unfold transportb ;
       rewrite !transport_f_f ;
       refine (maponpaths _ (@transportf_reindex_single C' C D F x xx' xx _ _ _ _)
                          @ _) ;
       rewrite !transport_f_f ;
       apply transportf_paths ;
       apply C).
Defined.

Definition iso_to_iso_reindex_weq
           {C' C : category}
           (D : disp_cat C)
           (F : C' ⟶ C)
           {x : C'}
           (xx xx' : (reindex_disp_cat F D) x)
  : (@iso_disp C D (F x) (F x) (identity_iso (F x)) xx xx')
    ≃
    (@iso_disp C' (reindex_disp_cat F D) x x (identity_iso x) xx xx').
Proof.
  use make_weq.
  - exact (iso_to_iso_reindex D F xx xx').
  - use gradth.
    + exact (iso_reindex_to_iso D F xx xx').
    + abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
         cbn ;
         apply transportfbinv).
    + abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
         cbn ;
         apply transportbfinv).
Defined.

Definition reindex_is_univalent_disp
           {C' C : category}
           (D : disp_cat C)
           (HD : is_univalent_disp D)
           (F : C' ⟶ C)
  : is_univalent_disp (reindex_disp_cat F D).
Proof.
  use is_univalent_disp_from_fibers.
  intros x xx xx'.
  unfold idtoiso_fiber_disp.
  use weqhomot.
  - exact (iso_to_iso_reindex_weq D F xx xx'
            ∘ make_weq
                (@idtoiso_disp C D (F x) (F x) (idpath _) xx xx')
                (HD _ _ _ _ _))%weq.
  - abstract
      (intros p ;
       induction p ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
       apply idpath).
Defined.

Definition reindex_cleaving
           {C C' : category}
           (D' : disp_cat C')
           (F : functor C C')
           (CD' : cleaving D')
  : cleaving (reindex_disp_cat F D').
Proof.
  intros c c' f d.
  cbn in d.
  pose (CD' (F c) (F c') (#F f)%Cat d) as m.
  use tpair.
  - exact (object_of_cartesian_lift _ _ m).
  - use tpair.
    + exact (mor_disp_of_cartesian_lift _ _ m).
    + intros c'' g d'' h''.
      apply iscontraprop1.
      * abstract
          (apply invproofirrelevance ;
           intros x y ;
           use subtypePath ; [ intro ; apply D' | ] ;
           use (cartesian_factorisation_unique m) ;
           pose (p := pr2 x) ; pose (q := pr2 y) ;
           cbn in p, q ;
           exact (transportf_transpose_right p @ !(transportf_transpose_right q))).
      * use tpair.
        ** simpl in *.
           exact (cartesian_factorisation
                    m (#F g)%Cat
                    (transportf
                       (λ z, d'' -->[ z ] d)
                       (functor_comp F g f)
                       h'')).
        ** abstract
             (simpl in * ; cbn ;
              refine (maponpaths
                        (transportb (mor_disp d'' d) (functor_comp F g f))
                        (cartesian_factorisation_commutes
                           m (#F g)%Cat
                           (transportf
                              (λ z, d'' -->[ z ] d)
                              (functor_comp F g f)
                              h''))
                        @ _) ;
              apply transportbfinv).
Defined.

Definition from_reindexing
           {C C' : category}
           (D' : disp_cat C')
           (F : functor C C')
  : disp_functor F (reindex_disp_cat F D') D'.
Proof.
  use tpair.
  - use tpair.
    + exact (λ x xx, xx).
    + exact (λ a b c d e f, f).
  - abstract (split ; intro ; intros; apply idpath).
Defined.

Definition into_reindexing_data
           {C' C : category}
           {D : disp_cat C}
           {F : functor C' C}
           {C'' : category}
           {D'' : disp_cat C''}
           {F' : functor C'' C'}
           (GG : disp_functor (F' ∙ F)%Cat D'' D)
  : disp_functor_data F' D'' (reindex_disp_cat F D).
Proof.
  use tpair.
  - exact (λ x xx, GG x xx).
  - exact (λ x y xx yy f ff, #GG ff).
Defined.

Definition into_reindexing_laws
           {C' C : category}
           {D : disp_cat C}
           {F : functor C' C}
           {C'' : category}
           {D'' : disp_cat C''}
           {F' : functor C'' C'}
           (GG : disp_functor (F' ∙ F)%Cat D'' D)
  : disp_functor_axioms (into_reindexing_data GG).
Proof.
  split.
  - intros x xx.
    etrans.
    {
      apply (disp_functor_id GG).
    }
    refine (!_).
    etrans.
    {
      apply (transportf_reindex GG).
    }
    etrans.
    {
      cbn.
      unfold transportb.
      apply transport_f_f.
    }
    cbn.
    apply transportf_paths.
    apply C.
  - intros x y z xx yy zz f g ff gg.
    cbn.
    etrans.
    {
      apply (disp_functor_comp GG).
    }
    refine (!_).
    etrans.
    {
      apply (transportf_reindex GG).
    }
    etrans.
    {
      cbn.
      unfold transportb.
      apply transport_f_f.
    }
    cbn.
    apply transportf_paths.
    apply C.
Qed.

Definition into_reindexing
           {C' C : category}
           {D : disp_cat C}
           {F : functor C' C}
           {C'' : category}
           {D'' : disp_cat C''}
           {F' : functor C'' C'}
           (GG : disp_functor (F' ∙ F)%Cat D'' D)
  : disp_functor F' D'' (reindex_disp_cat F D).
Proof.
  use tpair.
  - exact (into_reindexing_data GG).
  - exact (into_reindexing_laws GG).
Defined.

Definition into_reindexing_from_reindexing_data
           {C' C : category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : univalent_category}
           {D'' : disp_cat C''}
           {F' : C'' ⟶ C'}
           (GG : disp_functor (F' ∙ F) D'' D)
  : disp_nat_trans_data
      (nat_trans_id (F' ∙ F))
      (disp_functor_composite_data
         (into_reindexing GG)
         (from_reindexing D F))
      GG
  := λ x xx, id_disp (GG x xx).

Definition into_reindexing_from_reindexing_laws
           {C' C : category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : univalent_category}
           {D'' : disp_cat C''}
           {F' : C'' ⟶ C'}
           (GG : disp_functor (F' ∙ F) D'' D)
  : disp_nat_trans_axioms (into_reindexing_from_reindexing_data GG).
Proof.
  simpl.
  intros x xx y yy f ff.
  simpl ; cbn.
  etrans.
  {
    apply id_right_disp.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply id_left_disp.
  }
  etrans.
  {
    apply transport_f_f.
  }
  apply transportf_paths.
  apply C.
Qed.

Definition into_reindexing_from_reindexing
           {C' C : category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : univalent_category}
           {D'' : disp_cat C''}
           {F' : C'' ⟶ C'}
           (GG : disp_functor (F' ∙ F) D'' D)
  : disp_nat_trans
      (nat_trans_id (F' ∙ F))
      (disp_functor_composite_data
         (into_reindexing GG)
         (from_reindexing D F))
      GG.
Proof.
  use tpair.
  - exact (into_reindexing_from_reindexing_data GG).
  - exact (into_reindexing_from_reindexing_laws GG).
Defined.

Definition whisker_into_reindexing_data
           {C' C : univalent_category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : univalent_category}
           {D'' : disp_cat C''}
           {H₁ H₂ : C'' ⟶ C'}
           {GG : disp_functor (H₁ ∙ F) D'' D}
           {GG' : disp_functor (H₂ ∙ F) D'' D}
           {δ : H₁ ⟹ H₂}
           (σσ : disp_nat_trans (post_whisker δ F) GG GG')
  : disp_nat_trans_data δ (into_reindexing_data GG) (into_reindexing_data GG')
  := λ z zz, σσ z zz.

Definition whisker_into_reindexing_laws
           {C' C : univalent_category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : univalent_category}
           {D'' : disp_cat C''}
           {H₁ H₂ : C'' ⟶ C'}
           {GG : disp_functor (H₁ ∙ F) D'' D}
           {GG' : disp_functor (H₂ ∙ F) D'' D}
           {δ : H₁ ⟹ H₂}
           (σσ : disp_nat_trans (post_whisker δ F) GG GG')
  : disp_nat_trans_axioms (whisker_into_reindexing_data σσ).
Proof.
  intros x xx y yy f ff ; cbn.
  etrans.
  {
    apply maponpaths.
    exact (pr2 σσ x xx y yy f ff).
  }
  etrans.
  {
    apply transport_f_f.
  }
  refine (!_).
  unfold transportb.
  etrans.
  {
    apply (transportf_reindex GG).
  }
  etrans.
  {
    apply transport_f_f.
  }
  apply transportf_paths.
  apply C.
Qed.

Definition whisker_into_reindexing
           {C' C : univalent_category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {C'' : univalent_category}
           {D'' : disp_cat C''}
           {H₁ H₂ : C'' ⟶ C'}
           {GG : disp_functor (H₁ ∙ F) D'' D}
           {GG' : disp_functor (H₂ ∙ F) D'' D}
           {δ : H₁ ⟹ H₂}
           (σσ : disp_nat_trans (post_whisker δ F) GG GG')
  : disp_nat_trans δ (into_reindexing_data GG) (into_reindexing_data GG').
Proof.
  use tpair.
  - exact (whisker_into_reindexing_data σσ).
  - exact (whisker_into_reindexing_laws σσ).
Defined.

Definition reindex_nat_trans_src_data
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           (CD' : cleaving D')
           {F₁ F₂ : C ⟶ C'}
           (FF₂ : disp_functor F₂ D D')
           (n : F₁ ⟹ F₂)
  : disp_functor_data F₁ D D'.
Proof.
  use tpair.
  - exact (λ x xx,
           object_of_cartesian_lift
             _ _
             (CD' _ _ (n x) (FF₂ x xx))).
  - exact (λ x y xx yy f ff,
           cartesian_factorisation
             (CD' _ _ (n y) (FF₂ y yy))
             (#F₁ f)%Cat
             (transportb
                (λ z, _ -->[ z ] _)
                (nat_trans_ax n x y f)
                (mor_disp_of_cartesian_lift
                   _ _
                   (CD' _ _ (n x) (FF₂ x xx)) ;; #FF₂ ff))
          ).
Defined.

Definition reindex_nat_trans_src_laws
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           (CD' : cleaving D')
           {F₁ F₂ : C ⟶ C'}
           (FF₂ : disp_functor F₂ D D')
           (n : F₁ ⟹ F₂)
  : disp_functor_axioms (reindex_nat_trans_src_data CD' FF₂ n).
Proof.
  split.
  - intros x xx.
    simpl ; cbn ; unfold cartesian_factorisation.
    pose (λ t, maponpaths
                 pr1
                 (pr2 ((pr22 (CD' (F₂ x) (F₁ x) (n x) (FF₂ x xx)) _)
                         ((# F₁)%Cat (id₁ x))
                         _
                         (transportb
                            (λ z, pr1 (CD' (F₂ x) (F₁ x) (n x) (FF₂ x xx))
                                  -->[ z]
                                  FF₂ x xx)
                            (pr2 n x x (id₁ x))
                            (CD' (F₂ x) (F₁ x) (n x) (FF₂ x xx)
                             ;; # FF₂ (id_disp xx)))) t))
      as p.
    simpl in p.
    refine (!p (_ ,, _)).
    clear p.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (disp_functor_id FF₂ xx).
      }
      etrans.
      {
        apply mor_disp_transportf_prewhisker.
      }
      apply maponpaths.
      apply id_right_disp.
    }
    etrans.
    {
      apply maponpaths.
      apply transport_f_f.
    }
    etrans.
    {
      apply transport_f_f.
    }
    refine (!_).
    etrans.
    {
      apply mor_disp_transportf_postwhisker.
    }
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    etrans.
    {
      apply transport_f_f.
    }
    apply transportf_paths.
    apply C'.
  - intros x y z xx yy zz f g ff gg.
    simpl ; cbn.
    pose (λ t, maponpaths
                 pr1
                 (pr2 ((pr22 (CD' (F₂ z) (F₁ z) (n z) (FF₂ z zz)) _)
                         ((# F₁)%Cat (f · g))
                         _
                         (transportb
                            (λ q, pr1 (CD' (F₂ x) (F₁ x) (n x) (FF₂ x xx))
                                  -->[ q ]
                                  FF₂ z zz)
                            (nat_trans_ax n x z (f · g))
                            (CD' (F₂ x) (F₁ x) (n x) (FF₂ x xx)
                             ;; # FF₂ (ff;;gg)))) t))
      as p.
    simpl in p.
    refine (!p (_ ,, _)).
    clear p.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (disp_functor_comp FF₂ ff gg).
      }
      apply mor_disp_transportf_prewhisker.
    }
    etrans.
    {
      apply transport_f_f.
    }
    refine (!_).
    etrans.
    {
      apply mor_disp_transportf_postwhisker.
    }
    etrans.
    {
      apply maponpaths.
      apply assoc_disp_var.
    }
    etrans.
    {
      apply transport_f_f.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply (cartesian_factorisation_commutes
               (CD' (F₂ z) (F₁ z) (n z) (FF₂ z zz))
               ((# F₁)%Cat g)).
    }
    etrans.
    {
      apply maponpaths.
      apply mor_disp_transportf_prewhisker.
    }
    etrans.
    {
      apply transport_f_f.
    }
    etrans.
    {
      apply maponpaths.
      apply assoc_disp.
    }
    etrans.
    {
      apply transport_f_f.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (cartesian_factorisation_commutes
               (CD' (F₂ y) (F₁ y) (n y) (FF₂ y yy))
               ((# F₁)%Cat f)).
    }
    etrans.
    {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    etrans.
    {
      apply transport_f_f.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply assoc_disp.
    }
    etrans.
    {
      apply transport_f_f.
    }
    apply transportf_paths.
    apply C'.
Qed.

Definition reindex_nat_trans_src
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           {F₁ F₂ : C ⟶ C'}
           (CD' : cleaving D')
           (FF₂ : disp_functor F₂ D D')
           (n : F₁ ⟹ F₂)
  : disp_functor F₁ D D'.
Proof.
  use tpair.
  - exact (reindex_nat_trans_src_data CD' FF₂ n).
  - exact (reindex_nat_trans_src_laws CD' FF₂ n).
Defined.

Definition reindex_nat_trans
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           {F₁ F₂ : C ⟶ C'}
           (CD' : cleaving D')
           (FF₂ : disp_functor F₂ D D')
           (n : F₁ ⟹ F₂)
  : disp_nat_trans n (reindex_nat_trans_src CD' FF₂ n) FF₂.
Proof.
  use tpair.
  - exact (λ x xx,
           mor_disp_of_cartesian_lift
             _ _
             (CD' _ _ (n x) (FF₂ x xx))).
  - abstract
      (intros x y f xx yy ff ;
       exact (cartesian_factorisation_commutes
                (CD' _ _ (n y) (FF₂ y yy))
                (#F₁ f)%Cat
                (transportb
                   (λ z, _ -->[ z ] _)
                   (pr2 n x y f)
                   (mor_disp_of_cartesian_lift
                      _ _
                      (CD' _ _ (n x) (FF₂ x xx)) ;; #FF₂ ff)))).
Defined.

(** Proof that it is a fibration *)
Section GloballyFibred.
  Context {C' C : bicat_of_cats}
          (D : DispBicatOfFibs C)
          (F : C' --> C).

  Definition reindex_DispBicatOfFibs
    : DispBicatOfFibs C'.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (reindex_disp_cat F (pr1 D)).
    - apply reindex_is_univalent_disp.
      exact (pr12 D).
    - exact (reindex_cleaving (pr1 D) F (pr22 D)).
  Defined.

  Definition from_reindexing_DispBicatOfFibs
    : reindex_DispBicatOfFibs -->[ F] D
    := from_reindexing (pr1 D) F ,, tt.

  Definition lift_1cell_DispBicatOfFibs
             {C'' : bicat_of_cats}
             {D'' : DispBicatOfFibs C''}
             {F' : C'' --> C'}
             (GG : D'' -->[ F' · F] D)
    : lift_1cell DispBicatOfFibs from_reindexing_DispBicatOfFibs GG.
  Proof.
    use tpair.
    - exact (into_reindexing (pr1 GG) ,, tt).
    - simpl.
      use tpair.
      + exact (into_reindexing_from_reindexing (pr1 GG) ,, tt).
      + use DispBicatOfFibs_is_disp_invertible_2cell.
        intros x xx.
        exact (id_is_iso_disp (pr1 (pr1 GG) x xx)).
  Defined.

  Definition lift_2cell_DispBicatOfFibs_uniqueness
             {C'' : bicat_of_cats}
             {D'' : DispBicatOfFibs C''}
             {H₁ H₂ : C'' --> C'}
             {GG : D'' -->[ H₁ · F] D}
             {GG' : D'' -->[ H₂ · F] D}
             {δ : H₁ ==> H₂}
             (σσ : GG ==>[ δ ▹ F] GG')
    : isaprop
        (lift_2cell_type
           DispBicatOfFibs from_reindexing_DispBicatOfFibs σσ
           (lift_1cell_DispBicatOfFibs GG)
           (lift_1cell_DispBicatOfFibs GG')).
  Proof.
    simpl in C'', C', C.
    apply invproofirrelevance.
    intros x y.
    use subtypePath.
    { intro ; apply DispBicatOfFibs. }
    use subtypePath.
    { intro ; apply isapropunit. }
    use subtypePath.
    { intro ; apply (@isaprop_disp_nat_trans_axioms C'' C'). }
    use funextsec ; intro z.
    use funextsec ; intro zz.
    pose (eqtohomot (eqtohomot (maponpaths pr1 (maponpaths pr1 (pr2 x))) z) zz) as p.
    simpl in p ; cbn in p.
    rewrite pr1_transportf in p.
    cbn in p.
    rewrite (disp_nat_trans_transportf
               C'' C (pr1 D'') (pr1 D)
               (functor_composite H₁ F)
               (functor_composite H₂ F)
               _ _ _
               (disp_functor_composite
                  (into_reindexing (pr1 GG))
                  (from_reindexing (pr1 D) F)) (pr1 GG'))
      in p.
    cbn in p ; unfold into_reindexing_from_reindexing_data in p ; cbn in p.
    rewrite id_right_disp in p.
    rewrite id_left_disp in p.
    unfold transportb in p.
    rewrite transport_f_f in p.
    unfold idfun in p.
    etrans.
    {
      exact (transportb_transpose_right p).
    }
    clear p.
    refine (!_).
    pose (eqtohomot (eqtohomot (maponpaths pr1 (maponpaths pr1 (pr2 y))) z) zz) as p.
    simpl in p ; cbn in p.
    rewrite pr1_transportf in p.
    cbn in p.
    rewrite (disp_nat_trans_transportf
               C'' C (pr1 D'') (pr1 D)
               (functor_composite H₁ F)
               (functor_composite H₂ F)
               _ _ _
               (disp_functor_composite
                  (into_reindexing (pr1 GG))
                  (from_reindexing (pr1 D) F)) (pr1 GG'))
      in p.
    cbn in p ; unfold into_reindexing_from_reindexing_data in p ; cbn in p.
    rewrite id_right_disp in p.
    rewrite id_left_disp in p.
    unfold transportb in p.
    rewrite transport_f_f in p.
    unfold idfun in p.
    exact (transportb_transpose_right p).
  Qed.

  Definition lift_2cell_DispBicatOfFibs
             {C'' : bicat_of_cats}
             {D'' : DispBicatOfFibs C''}
             {H₁ H₂ : C'' --> C'}
             {GG : D'' -->[ H₁ · F] D}
             {GG' : D'' -->[ H₂ · F] D}
             {δ : H₁ ==> H₂}
             (σσ : GG ==>[ δ ▹ F] GG')
    : lift_2cell
        DispBicatOfFibs
        from_reindexing_DispBicatOfFibs
        σσ
        (lift_1cell_DispBicatOfFibs GG)
        (lift_1cell_DispBicatOfFibs GG').
  Proof.
    use iscontraprop1.
    - exact (lift_2cell_DispBicatOfFibs_uniqueness σσ).
    - use tpair.
      + exact (whisker_into_reindexing (pr1 σσ) ,, tt).
      + abstract
          (simpl in C'', C ;
           use subtypePath ; [intro ; apply isapropunit | ] ;
           use subtypePath ; [intro ; apply (@isaprop_disp_nat_trans_axioms C'' C) | ] ;
           use funextsec ;
           intro z ;
           use funextsec ;
           intro zz ;
           cbn ; unfold into_reindexing_from_reindexing_data ;
           rewrite pr1_transportf ;
           cbn ;
           rewrite (disp_nat_trans_transportf
                      (C'' : univalent_category) (C : univalent_category)
                      (pr1 D'') (pr1 D)
                      (H₁ ∙ F) (H₂ ∙ F)
                      _ _ _
                      (disp_functor_composite
                         (into_reindexing (pr1 GG))
                         (from_reindexing (pr1 D) F))
                      (pr1 GG')
                   ) ;
           refine (!_) ;
           refine (id_left_disp @ _) ;
           cbn ;
           unfold into_reindexing_from_reindexing_data, whisker_into_reindexing_data ;
           refine (!_) ;
           refine (maponpaths _ id_right_disp @ _) ;
           refine (transport_f_f _ _ _ _ @ _) ;
           apply transportf_paths ;
           apply C).
  Defined.

  Definition cartesian_1cell_DispBicatOfFibs
    : cartesian_1cell
        DispBicatOfFibs
        from_reindexing_DispBicatOfFibs.
  Proof.
    use tpair.
    - exact @lift_1cell_DispBicatOfFibs.
    - exact @lift_2cell_DispBicatOfFibs.
  Defined.
End GloballyFibred.

Definition globally_fibered_DispBicatOfFibs : global_cleaving DispBicatOfFibs.
Proof.
  intros C' C D F.
  use tpair.
  - exact (reindex_DispBicatOfFibs D F).
  - use tpair.
    + exact (from_reindexing_DispBicatOfFibs D F).
    + exact (cartesian_1cell_DispBicatOfFibs D F).
Defined.

(** Locally fibred *)
Definition to_reindex_nat_trans_src_data
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           (HD' : cleaving D')
           {F₁ F₂ F₃ : C ⟶ C'}
           {FF₂ : disp_functor F₂ D D'}
           {n : F₁ ⟹ F₂}
           {FF₃ : disp_functor F₃ D D'}
           {γ : F₃ ⟹ F₁}
           (ββ : disp_nat_trans (nat_trans_comp _ _ _ γ n) FF₃ FF₂)
  : disp_nat_trans_data γ FF₃ (reindex_nat_trans_src HD' FF₂ n)
  := λ x xx,
     cartesian_factorisation
       (HD' (F₂ x) (F₁ x) (n x) (pr1 FF₂ x xx))
       (γ x) (pr1 ββ x xx).

Definition to_reindex_nat_trans_src_laws
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           (HD' : cleaving D')
           {F₁ F₂ F₃ : C ⟶ C'}
           {FF₂ : disp_functor F₂ D D'}
           {n : F₁ ⟹ F₂}
           {FF₃ : disp_functor F₃ D D'}
           {γ : F₃ ⟹ F₁}
           (ββ : disp_nat_trans (nat_trans_comp _ _ _ γ n) FF₃ FF₂)
  : disp_nat_trans_axioms (to_reindex_nat_trans_src_data HD' ββ).
Proof.
  intros x y f xx yy ff ; simpl in *.
  pose (disp_nat_trans_ax ββ ff) as p.
  cbn in p.
  use (cartesian_factorisation_unique (HD' (F₂ y) (F₁ y) (n y) (FF₂ y yy))).
  etrans.
  {
    rewrite assoc_disp_var.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    apply p.
  }
  refine (!_).
  etrans.
  {
    apply mor_disp_transportf_postwhisker.
  }
  etrans.
  {
    apply maponpaths.
    rewrite assoc_disp_var.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    etrans.
    {
      apply mor_disp_transportf_prewhisker.
    }
    apply maponpaths.
    rewrite assoc_disp.
    apply maponpaths.
    apply maponpaths_2.
    apply cartesian_factorisation_commutes.
  }
  unfold transportb.
  rewrite !transport_f_f.
  apply transportf_paths.
  apply C'.
Qed.

Definition to_reindex_nat_trans_src
           {C C' : univalent_category}
           {D : disp_cat C}
           {D' : disp_cat C'}
           (HD' : cleaving D')
           {F₁ F₂ F₃ : C ⟶ C'}
           {FF₂ : disp_functor F₂ D D'}
           {n : F₁ ⟹ F₂}
           {FF₃ : disp_functor F₃ D D'}
           {γ : F₃ ⟹ F₁}
           (ββ : disp_nat_trans (nat_trans_comp _ _ _ γ n) FF₃ FF₂)
  : disp_nat_trans γ FF₃ (reindex_nat_trans_src HD' FF₂ n).
Proof.
  use tpair.
  - exact (to_reindex_nat_trans_src_data HD' ββ).
  - exact (to_reindex_nat_trans_src_laws HD' ββ).
Defined.

Definition local_cleaving_DispBicatOfFibs
  : local_cleaving DispBicatOfFibs.
Proof.
  intros C C' D D' F₁ F₂ FF₂ n.
  use tpair.
  - exact (reindex_nat_trans_src (pr22 D') (pr1 FF₂) n ,, tt).
  - simpl.
    use tpair.
    + exact (reindex_nat_trans _ (pr1 FF₂) n ,, tt).
    + intros F₃ FF₃ γ ββ.
      simpl in *.
      apply iscontraprop1.
      * abstract
          (apply invproofirrelevance ;
           intros nn mm ;
           use subtypePath ; [ intro ; apply DispBicatOfFibs | ] ;
           use subtypePath ; [ intro ; exact isapropunit | ] ;
           use (@disp_nat_trans_eq C C') ;
           intros x xx ;
           pose (eqtohomot
                   (eqtohomot
                      (maponpaths
                         pr1
                         (maponpaths pr1 (pr2 nn)))
                      x)
                   xx)
             as p ;
           cbn in p ;
           pose (eqtohomot
                   (eqtohomot
                      (maponpaths
                         pr1
                         (maponpaths pr1 (pr2 mm)))
                      x)
                   xx)
             as q ;
           cbn in p, q ;
           use (cartesian_factorisation_unique
                  (pr22 D' (F₂ x) (F₁ x) (n x) (pr1 FF₂ x xx))) ;
           exact (p @ !q)).
      * use tpair.
        ** exact (to_reindex_nat_trans_src (pr22 D') (pr1 ββ) ,, tt).
        ** abstract
             (simpl ;
              use subtypePath ; [ intro ; exact isapropunit | ] ;
              use (@disp_nat_trans_eq C C') ;
              intros x xx ;
              exact (pr21 (pr22 (pr22 D' (F₂ x) (F₁ x) (n x) (pr1 FF₂ x xx))
                                (F₃ x) (γ x) (pr1 FF₃ x xx) (pr1 ββ x xx)))).
Defined.

Definition TODO {A : UU} : A.
Admitted.
(*
Definition test
           {C C' : bicat_of_cats}
           {D : DispBicatOfFibs C}
           {D' : DispBicatOfFibs C'}
           {F₁ F₂ : C --> C'}
           {FF₁ : D -->[ F₁ ] D'}
           {FF₂ : D -->[ F₂ ] D'}
           {n : F₁ ==> F₂}
           (nn : FF₁ ==>[ n ] FF₂)
  : is_cartesian_2cell DispBicatOfFibs nn.
Proof.
  intros G GG γ ββ.
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros x y.
    use subtypePath ; [ intro ; apply DispBicatOfFibs | ].
    use subtypePath ; [ intro ; exact isapropunit | ].
    simpl in C, C'.
    use (@disp_nat_trans_eq C C').
    intros z zz.
    pose (maponpaths
            (λ (n : disp_nat_trans _ _ _), n z zz)
            (maponpaths pr1 (pr2 x))) as p1.
    pose (maponpaths
            (λ (n : disp_nat_trans _ _ _), n z zz)
            (maponpaths pr1 (pr2 y))) as p2.
    pose (p1 @ !p2) as r.
    cbn in r.
    apply TODO.
  - use tpair.
    + refine (_ ,, tt).
      * simpl.
        cbn in *.
        use tpair.
        ** intros x xx.
           pose (pr11 ββ x xx).
           simpl in *.
*)

Definition lwhisker_cartesian_DispBicatOfFibs
  : lwhisker_cartesian DispBicatOfFibs.
Proof.
  intros C C' C'' D D' D'' F G₁ G₂ FF GG₁ GG₂ n nn hnn.
  intros H HH γ ββ.
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros x y.
    use subtypePath ; [ intro ; apply DispBicatOfFibs | ].
    use subtypePath ; [ intro ; exact isapropunit | ].
    simpl in C, C', C''.
    use (@disp_nat_trans_eq C C'').
    intros z zz.
    pose (maponpaths
            (λ (n : disp_nat_trans _ _ _), n z zz)
            (maponpaths pr1 (pr2 x))) as p1.
    pose (maponpaths
            (λ (n : disp_nat_trans _ _ _), n z zz)
            (maponpaths pr1 (pr2 y))) as p2.
    pose (p1 @ !p2) as r.
    cbn in r.
    unfold is_cartesian_2cell in hnn.
    apply TODO.
  - use tpair.
    + refine (_ ,, tt).
      cbn in *.
      cbn.
      use tpair.
      * intros x xx.
        pose (m := pr1 ββ x xx).
        cbn in m.
        pose (m' := pr1 nn (F x) (pr1 FF x xx)).
        cbn in m'.
        cbn.
        apply TODO.
      * apply TODO.
    + use subtypePath ; [ intro ; exact isapropunit | ].
      simpl in C, C', C''.
      use (@disp_nat_trans_eq C C'').
      intros x xx.
      simpl.
      apply TODO.
Defined.

Definition Fibration_DispBicatOfFibs
  : fibration_of_bicats DispBicatOfFibs.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - exact local_cleaving_DispBicatOfFibs.
  - exact globally_fibered_DispBicatOfFibs.
  - exact lwhisker_cartesian_DispBicatOfFibs.
  - apply TODO.
Defined.
