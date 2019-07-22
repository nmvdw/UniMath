(* ******************************************************************************* *)
(** Export file for fibrations
 ********************************************************************************* *)

Require Export UniMath.CategoryTheory.Bicategories.DisplayedBicats.Fibration.Fibration1.
Require Export UniMath.CategoryTheory.Bicategories.DisplayedBicats.Fibration.Fibration2.

(** Displayed univalence from univalence of fiber *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Definition discrete_fiber_bicat
           {B : bicat}
           (D : disp_bicat B)
           (h : local_iso_cleaving D)
           (x : B)
  : bicat.
Proof.
  use tpair.
  - exact (discrete_fiber D h x).
  - intros xx yy ff gg.
    apply D.
Defined.

Section DisplayedUnivalenceFromFiberUnivalence.
  Context {B : bicat}.
  Variable (D : disp_bicat B)
           (h : local_iso_cleaving D).

  Local Notation "'F' x" := (discrete_fiber_bicat D h x) (at level 40).

  Section DispGlobalUnivalenceViaFiber.
    Context {x : B}
            (xx yy : D x)
            (HF : is_univalent_2_0 (F x)).

    Section FiberAdjEquivToDispAdjequiv.
      Variable (f : @adjoint_equivalence (F x) xx yy).

      Local Definition fiber_adjequiv_to_disp_adjequiv_data
        : disp_left_adjoint_data (internal_adjunction_data_identity x) (pr1 f).
      Proof.
        use tpair.
        - exact (left_adjoint_right_adjoint f).
        - split ; cbn.
          + refine (transportf
                      (λ p, _ ==>[ p ] _)
                      (id2_left _)
                      (left_adjoint_unit f •• _)).
            apply (disp_local_iso_cleaving_invertible_2cell
                     h (pr1 f;; pr112 f) (idempunitor x)).
          + refine (transportf
                      (λ p, _ ==>[ p ] _)
                      (id2_right _)
                      (_ •• left_adjoint_counit f)).
            apply (disp_local_iso_cleaving_invertible_2cell
                     h (pr112 f;; pr1 f) (idempunitor x)).
      Defined.

      Definition fiber_adjequiv_to_disp_adjequiv
        : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy.
      Proof.
        use tpair.
        - apply f.
        - Print disp_left_adjoint_equivalence.
          cbn.
          use tpair.
          + exact fiber_adjequiv_to_disp_adjequiv_data.
          + split.
            * split.
              ** cbn.
                 apply TODO.
              ** apply TODO.
            * split.
              ** cbn.
                 apply TODO.
              ** apply TODO.
      Defined.
    End FiberAdjEquivToDispAdjequiv.

    Definition disp_adjequiv_to_fiber_adjequiv
      : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy
        →
        (@adjoint_equivalence (F x) xx yy).
    Proof.
      cbn.
      intro f.
      use build_adjoint_equivalence ; cbn.
      - exact (pr1 f).
      - exact (pr112 f).
      - (*refine (transportf
                  (λ p, _ ==>[ p ] _)
                  _
                  (pr1 (pr212 f) •• _)).
        cbn.
          as m.
          cbn in m.
          Check (local_iso_cleaving_1cell h (pr1 f;; pr112 f) (idempunitor x)).
          pose (disp_local_iso_cleaving_invertible_2cell h (pr1 f;; pr112 f) (idempunitor x))
            as mm.
          apply TODO.
         *)
        apply TODO.
      - apply TODO.
      - apply TODO.
      - apply TODO.
      - apply TODO.
      - apply TODO.
    Defined.

    Definition fiber_adjequiv_to_disp_adjequiv_is_weq
      : isweq fiber_adjequiv_to_disp_adjequiv.
    Proof.
      use gradth.
      - exact disp_adjequiv_to_fiber_adjequiv.
      - intros f.
        use total2_paths_f.
        + apply idpath.
        + use subtypePath.
          { intro.
            repeat apply isapropdirprod
            ; try apply D
            ; apply isaprop_is_invertible_2cell.
          }
          use total2_paths_f.
          * apply idpath.
          * cbn.
            use pathsdirprod.
            ** apply TODO.
            ** apply TODO.
      - intros f.
        use total2_paths_f.
        + apply idpath.
        + use subtypePath.
          { intro.
            repeat apply isapropdirprod
            ; try apply D
            ; apply isaprop_is_disp_invertible_2cell.
          }
          use total2_paths_f.
          * apply idpath.
          * cbn.
            use pathsdirprod.
            ** apply TODO.
            ** apply TODO.
    Defined.

    Definition fiber_adjequiv_to_disp_adjequiv_weq
      : (@adjoint_equivalence (F x) xx yy)
          ≃
          disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy.
    Proof.
      use make_weq.
      - exact fiber_adjequiv_to_disp_adjequiv.
      - apply fiber_adjequiv_to_disp_adjequiv_is_weq.
    Defined.

    Definition disp_idtoiso_2_0_alt
      : (xx = yy)
          ≃
          disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy
      := (fiber_adjequiv_to_disp_adjequiv_weq
            ∘ make_weq (@idtoiso_2_0 (F x) xx yy) (HF xx yy))%weq.
  End DispGlobalUnivalenceViaFiber.

  Local Arguments transportf {_} {_} {_} {_} {_} _.
  Local Arguments transportb {_} {_} {_} {_} {_} _.


  Definition disp_idtoiso_2_0_alt_weq_disp_idtoiso_2_0
             (HF : ∏ (x : B), is_univalent_2_0 (F x))
             {x : B}
             {xx yy : D x}
             (p : xx = yy)
    : (disp_idtoiso_2_0_alt xx yy (HF x)) p = disp_idtoiso_2_0 D (idpath x) xx yy p.
  Proof.
    induction p ; cbn.
    use total2_paths_f.
    - apply idpath.
    - use subtypePath.
      { intro.
        repeat apply isapropdirprod
        ; try apply D
        ; apply isaprop_is_disp_invertible_2cell.
      }
      use total2_paths_f.
      + apply idpath.
      + cbn.
        use pathsdirprod.
        ** rewrite disp_mor_transportf_postwhisker.
           rewrite transport_f_f.
           rewrite disp_vassocl.
           unfold transportb.
           rewrite transport_f_f.
           etrans.
           {
             do 2 apply maponpaths.
             exact (disp_vcomp_linv
                      (disp_local_iso_cleaving_invertible_2cell
                         h (id_disp xx;; id_disp xx) (idempunitor x))).
           }
           unfold transportb.
           rewrite disp_mor_transportf_prewhisker.
           rewrite transport_f_f.
           rewrite disp_id2_right.
           unfold transportb.
           rewrite transport_f_f.
           rewrite transportf_set.
           { apply idpath. }
           apply B.
        ** rewrite disp_mor_transportf_prewhisker.
           rewrite transport_f_f.
           rewrite disp_vassocr.
           unfold transportb.
           rewrite transport_f_f.
           etrans.
           {
             apply maponpaths.
             apply maponpaths_2.
             exact (disp_vcomp_linv
                      (disp_local_iso_cleaving_invertible_2cell
                         h (id_disp xx;; id_disp xx) (idempunitor x))).
           }
           unfold transportb.
           rewrite disp_mor_transportf_postwhisker.
           rewrite transport_f_f.
           rewrite disp_id2_left.
           unfold transportb.
           rewrite transport_f_f.
           rewrite transportf_set.
           { apply idpath. }
           apply B.
  Qed.

  Definition fiber_univalence_2_0_to_displayed_univalence_2_0
             (HF : ∏ (x : B), is_univalent_2_0 (F x))
    : disp_univalent_2_0 D.
  Proof.
    apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x xx yy.
    use weqhomot.
    - cbn ; unfold idfun.
      exact (disp_idtoiso_2_0_alt xx yy (HF x)).
    - intro p ; cbn in p ; unfold idfun in p.
      apply disp_idtoiso_2_0_alt_weq_disp_idtoiso_2_0.
  Defined.


  disp_mor_transportf_prewhisker
    disp_mor_transportf_postwhisker
