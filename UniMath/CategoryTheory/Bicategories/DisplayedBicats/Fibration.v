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
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
(*
Definition disp_equivalence
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           (f : adjoint_equivalence x y)
           (xx : D x) (yy : D y)
  : UU
  := ∑ (ff : xx -->[ f ] yy)
       (Hf : disp_left_adjoint_data f ff),
     disp_left_equivalence_axioms f Hf.

Section DispEquivToDispAdjequiv.
  Context {B : bicat}
          {D : disp_bicat B}
          {x y : B}
          {xx : D x} {yy : D y}
          (f : adjoint_equivalence x y)
          (Hf : disp_equivalence f xx yy).

  Local Definition Ef_help
    : @left_adjoint_equivalence (total_bicat D) (x ,, xx) (y ,, yy) (pr1 f,, pr1 Hf).
  Proof.
    apply equiv_to_isadjequiv.
    use tpair.
    - use tpair.
      + exact (left_adjoint_right_adjoint f ,, pr112 Hf).
      + split.
        * exact (left_adjoint_unit f ,, pr121 (pr2 Hf)).
        * exact (left_adjoint_counit f ,, pr221 (pr2 Hf)).
    - simpl.
      apply left_equivalence_axioms_disp_to_total.
      use tpair.
      + exact (pr222 f).
      + exact (pr22 Hf).
  Qed.

  Local Definition Ef : @adjoint_equivalence (total_bicat D) (x ,, xx) (y ,, yy)
    := (pr1 f ,, pr1 Hf) ,, Ef_help.

  Definition disp_equiv_to_disp_adjequiv
    : disp_adjoint_equivalence f xx yy.
  Proof.
    exact (pr2 (adjoint_equivalence_total_disp_weq _ _ Ef)).
    use tpair.

    - exact (pr1 Hf).
    - simpl.
      apply left_adjoint_equivalence_total_disp_weq.
      apply Ef_help.
      pose (pr2 (adjoint_equivalence_total_disp_weq _ _ Ef)) as d.
      pose (pr2 d) as e.

      exact e.
      cbn in e.


Print disp_adjoint_equivalence.
Definition disp_equiv_to_disp_adjequiv
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {xx : D x} {yy : D y}
           (f : adjoint_equivalence x y)
           (ff : xx -->[ f ] yy)
  : disp_left_adjoint_equivalence f ff.
Proof.
  Check (pr2 (@adjoint_equivalence_total_disp_weq B D x y xx yy _)).
  Check (pr2 (adjoint_equivalence_total_disp_weq (x ,, xx) (y ,, yy) _)).
  apply (pr2


Definition disp_equiv_to_disp_adjequiv
*)
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
(*
  Definition help_test₂
             {x : B}
             {xx : D x} {yy : D x}
             (f : @adjoint_equivalence (F x) xx yy)
    : @adjoint_equivalence (total_bicat D) (x ,, xx) (x ,, yy).
  Proof.
    use tpair.
    - exact (id₁ x ,, pr1 f).
    - apply equiv_to_isadjequiv.
      use tpair.
      + use tpair.
        * exact (id₁ x ,, left_adjoint_right_adjoint f).
        * split.
          ** simple refine (linvunitor _ ,, _) ; simpl.
             refine (transportf
                       (λ p, _ ==>[ p ] _)
                       (id2_left _)
                       (left_adjoint_unit f •• _)).
             apply (disp_local_iso_cleaving_invertible_2cell
                      h (pr1 f;; pr112 f) (idempunitor x)).
          ** simple refine (lunitor _ ,, _) ; simpl.
             refine (transportf
                      (λ p, _ ==>[ p ] _)
                      (id2_right _)
                      (_ •• left_adjoint_counit f)).
             apply (disp_local_iso_cleaving_invertible_2cell
                      h (pr112 f;; pr1 f) (idempunitor x)).
      + split ; cbn.
        * use (@disp_iso_to_invetible_2cell_weq B D _ _ _ _ (linvunitor (id₁ x) ,, _)).
          ** cbn.
             is_iso.
          ** apply TODO.
        * use (@disp_iso_to_invetible_2cell_weq B D _ _ _ _ (lunitor (id₁ x) ,, _)).
          ** cbn.
             is_iso.
          ** apply TODO.
  Defined.

  Definition help_test
             {x y : B}
             {xx : D x} {yy : D y}
             (p : x = y)
             (f : @adjoint_equivalence (F x) xx (transportb D p yy))
    : @adjoint_equivalence (total_bicat D) (x ,, xx) (y ,, yy).
  Proof.
    induction p.
    cbn in *.
    apply help_test₂.
    exact f.
  Defined.
 *)

  Definition help_test
             {x y : B}
             {xx : D x} {yy : D y}
    : (∑ p : x = y, @adjoint_equivalence (F x) xx (transportb D p yy))
        →
        @adjoint_equivalence (total_bicat D) (x ,, xx) (y,, yy).
  Proof.
    intros p.
    induction p as [p f].
    induction p ; cbn in * ; unfold idfun in *.
    use equiv_to_adjequiv.
    - exact (id₁ x ,, pr1 f).
    - use tpair.
      + use tpair.
        * exact (id₁ x ,, left_adjoint_right_adjoint f).
        * split.
          ** simple refine (linvunitor _ ,, _) ; cbn.
             refine (transportf
                       (λ p, _ ==>[ p ] _)
                       (id2_left _)
                       (left_adjoint_unit f •• _)).
             apply (disp_local_iso_cleaving_invertible_2cell
                      h (pr1 f;; pr112 f) (idempunitor x)).
          ** simple refine (lunitor _ ,, _) ; cbn.
             refine (transportf
                  (λ p, _ ==>[ p ] _)
                  (id2_right _)
                  (_ •• left_adjoint_counit f)).
             apply (disp_local_iso_cleaving_invertible_2cell
                      h (pr112 f;; pr1 f) (idempunitor x)).
      + split ; cbn.
        * apply TODO.
        * apply TODO.
  Defined.

  Definition help_test_weq
             {x y : B}
             {xx : D x} {yy : D y}
    : (∑ p : x = y, @adjoint_equivalence (F x) xx (transportb D p yy))
      ≃
      @adjoint_equivalence (total_bicat D) (x ,, xx) (y,, yy).
  Proof.
    use make_weq.
    - exact help_test.
    - use gradth.
      + apply TODO.
      + apply TODO.
      + apply TODO.
  Defined.

  Definition factor_test
             (HB : is_univalent_2_0 B)
             (HF : ∏ (x : B), is_univalent_2_0 (F x))
             (Ex Ey : total_bicat D)
    : Ex = Ey ≃ adjoint_equivalence Ex Ey.
  Proof.
    induction Ex as [x xx].
    induction Ey as [y yy].
    refine (_ ∘ total2_paths_equiv _ _ _)%weq.
    unfold PathPair.
    cbn.
    refine (help_test_weq ∘ _)%weq.
    apply weqfibtototal.
    intros p.
    induction p ; cbn ; unfold idfun.
    exact (make_weq (@idtoiso_2_0 (F x) xx yy) (HF x xx yy)).
  Defined.

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

      Local Arguments transportf {_} {_} {_} {_} {_} _.
      Local Arguments transportb {_} {_} {_} {_} {_} _.

      Definition fiber_adjequiv_to_disp_adjequiv_adjoint_axioms
        : disp_left_adjoint_axioms
            (internal_adjoint_equivalence_identity x)
            fiber_adjequiv_to_disp_adjequiv_data.
       Proof.
        split.
        - cbn.
          refine (!(_ @ _)).
          {
            apply maponpaths.
            exact (!(pr112 (pr2 f))).
          }
          unfold transportb.
          refine (!_).
          rewrite disp_rwhisker_transport_right.
          rewrite disp_mor_transportf_prewhisker.
          rewrite disp_mor_transportf_postwhisker.
          rewrite disp_rwhisker_transport_left_new.
          rewrite disp_mor_transportf_prewhisker.
          do 3 rewrite disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          refine (!_).
          etrans.
          {
            cbn.
            rewrite !transport_f_f.
            rewrite !disp_mor_transportf_prewhisker.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !transport_f_f.
            apply idpath.
          }
          cbn.
          apply idpath.
          rewrite disp_mor_transportf_prewhisker.

          apply TODO.
        - apply TODO.
      Qed.

      disp_mor_transportf_prewhisker
        disp_mor_transportf_postwhisker
        disp_rwhisker_transport_left_new

      Definition fiber_adjequiv_to_disp_adjequiv
        : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy.
      Proof.
        use tpair.
        - apply f.
        - cbn.
          use tpair.
          + exact fiber_adjequiv_to_disp_adjequiv_data.
          + split.
            * exact fiber_adjequiv_to_disp_adjequiv_adjoint_axioms.
            * split.
              ** cbn.
                 pose (pr122 (pr2 f)).
                 cbn in i.
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
