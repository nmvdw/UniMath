(**

 The internal higher-order logic of a topos

 We show that every topos gives rise to a model of higher-order logic. More precisely,
 every topos gives rise to a tripos.

 Let `E` be a topos. We define a formula in context `Γ` to be a morphism from `Γ` to `Ω`
 where `Ω` is the subobject classifier of `E`. Note that such morphisms are the same as
 monomorphisms into `Γ` due to the universal mapping property of subobject classifiers.
 We already showed that this gives rise to a fibration over `E` for which each fiber is
 a preorder. Now we show that we have the desired connectives.

 To construct these connectives, we use an idea from "Introduction to higher order
 categorical logic" by Lambek and Scott. Specifically, all connectives can be reduced
 to equality if we work in a higher-order setting. For falsity, disjunction, and the
 existential quantification we use Church encodings. The falsity formula is defined to
 be `∀ (ω : Ω), ω`, and for disjunction and existential quantification we use similar idea.
 For universal quantification, we use comprehension. If we have a predicate `φ` in context
 `Γ × A`, then we can prove `∀ (x : A), φ(x)` if and only if we can prove `{{ φ }}` is equal
 to `{{ ⊤ }}`. Here `{{ φ }}` denotes the comprehension of `φ`, which is the term of the
 power object associated to `φ`. For conjunction and implication, we can use similar ideas,
 and that allows us to reduce all necessary connectives to equality. Note that in the
 formalization, we do not do this reduction for `⊤`, because that formula is easy to define
 anyway.

 The main work thus lies in establishing all necessary laws for equality. However, we can
 establish these laws directly using the universal property of equalizers and subobject
 classifiers.

 References
 - "Introduction to higher order categorical logic" by Lambek and Scott

 Contents
 1. Fiberwise terminal object
 2. Additional operations for comprehension
 3. Equality formula
 4. Fiberwise binary products
 5. Additional rules related to conjunction
 6. Fiberwise exponentials
 7. Universal quantification
 8. Fiberwise initial object
 9. Fiberwise binary coproducts
 10. Existential quantification
 11. The hyperdoctrine associated to a topos

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Properties.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.PullbackConstructions.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.ElementaryTopos.ToposOperations.
Require Import UniMath.CategoryTheory.ElementaryTopos.PredicateDispCat.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.
Local Open Scope topos.

Section ToposLogic.
  Context (E : Topos).

  Let PB : Pullbacks E := Topos_Pullbacks E.
  Let EQ : Equalizers E := Topos_Equalizers E.

  Notation "'form'" := (ob_disp (topos_logic_disp_cat E)).
  Notation "P₁ ⊢ P₂" := (mor_disp
                           (D := topos_logic_disp_cat E)
                           P₁ P₂
                           (identity _))
                          (at level 100).
  Arguments topos_logic_subst /.
  Notation "φ '[[' s ']]'" := (topos_logic_subst _ s φ).

  (** * 1. Fiberwise terminal object *)
  Definition topos_logic_truth_form
             (Γ : E)
    : form Γ
    := const_true Γ Ω.

  Arguments topos_logic_truth_form /.

  Notation "⊤" := (topos_logic_truth_form _).

  Definition topos_logic_truth_form_z_iso_mono
             (Γ : E)
    : is_z_isomorphism
        (topos_logic_compr_mono E (topos_logic_truth_form Γ)).
  Proof.
    use make_is_z_isomorphism.
    - use PullbackArrow.
      + apply identity.
      + apply TerminalArrow.
      + abstract
          (cbn ;
           unfold const_true ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
    - abstract
        (split ;
         [
         | cbn ;
           apply PullbackArrow_PullbackPr1 ] ;
         use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
         [ | apply TerminalArrowEq ] ;
         cbn ;
         rewrite !assoc' ;
         rewrite PullbackArrow_PullbackPr1 ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition topos_logic_compr_truth_z_iso
             (Γ : E)
    : z_iso (topos_logic_compr E ⊤) Γ
    := _ ,, topos_logic_truth_form_z_iso_mono Γ.

  Proposition topos_logic_truth_subst
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
    : ⊤ [[ s ]] = ⊤.
  Proof.
    cbn.
    unfold const_true.
    rewrite !assoc.
    apply maponpaths_2.
    apply TerminalArrowEq.
  Qed.

  Proposition topos_logic_truth_subst'
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
    : s · ⊤ = ⊤.
  Proof.
    apply topos_logic_truth_subst.
  Qed.

  Proposition topos_logic_truth_intro
              {Γ : E}
              (Δ : form Γ)
    : Δ ⊢ ⊤.
  Proof.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr2 _).
      + abstract
          (unfold topos_logic_truth_form, const_true ; cbn ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr1 ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition topos_logic_fiberwise_terminal
    : fiberwise_terminal (topos_logic_cleaving E).
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - apply locally_propositional_topos_logic_disp_cat.
    - intro Γ.
      exact ⊤.
    - intros Γ Δ.
      apply topos_logic_truth_intro.
    - abstract
        (intros Γ₁ Γ₂ s ;
         cbn -[topos_logic_disp_cat topos_logic_truth_form] ;
         rewrite topos_logic_truth_subst' ;
         apply topos_logic_hyp).
  Defined.

  (** * 2. Additional operations for comprehension *)
  Lemma topos_logic_to_comprehension_tm_eq
        {Γ A : E}
        (P : form A)
        (t : Γ --> A)
        (p : ⊤ ⊢ P [[ t ]])
    : t · P = TerminalArrow 𝟙 Γ · Ω.
  Proof.
    cbn in p.
    rewrite id_right in p.
    assert (identity Γ · const_true Γ Ω = TerminalArrow 𝟙 Γ · true' Ω) as q.
    {
      unfold const_true.
      rewrite !assoc.
      apply maponpaths_2.
      apply TerminalArrowEq.
    }
    pose (PullbackArrow
            (PB _ _ _ (const_true Γ Ω) (true' Ω))
            _
            (identity _)
            (TerminalArrow _ _)
            q)
      as φ.
    pose (maponpaths
            (λ z, φ · pr1 p · z)
            (PullbackSqrCommutes (PB _ _ _ (t · P) (true' Ω))))
      as r.
    cbn in r.
    refine (_ @ r @ _) ; clear r.
    - refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        exact (pr2 p).
      }
      unfold φ.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_left.
      apply idpath.
    - rewrite !assoc.
      apply maponpaths_2.
      apply TerminalArrowEq.
  Qed.

  Definition topos_logic_comprehension_tm
             {Γ A : E}
             {φ : form A}
             (t : Γ --> A)
             (p : ⊤ ⊢ φ [[ t ]])
    : Γ --> topos_logic_compr E φ.
  Proof.
    use PullbackArrow.
    - exact t.
    - apply TerminalArrow.
    - apply topos_logic_to_comprehension_tm_eq.
      exact p.
  Defined.

  Definition topos_logic_comprehension_pr
             {Γ A : E}
             {φ : form A}
             (t : Γ --> topos_logic_compr E φ)
    : Γ --> A
    := t · PullbackPr1 _.

  Proposition topos_logic_comprehension_proof
              {Γ A : E}
              {φ : form A}
              (t : Γ --> topos_logic_compr E φ)
    : ⊤ ⊢ φ [[ topos_logic_comprehension_pr t ]].
  Proof.
    unfold topos_logic_comprehension_pr, topos_logic_subst.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + apply PullbackPr1.
      + apply PullbackPr2.
      + rewrite !assoc'.
        cbn.
        rewrite PullbackSqrCommutes.
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
    - cbn.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_right.
      apply idpath.
  Qed.

  Proposition topos_logic_comprehension_beta
              {Γ A : E}
              {φ : form A}
              (t : Γ --> A)
              (p : ⊤ ⊢ φ [[ t ]])
    : topos_logic_comprehension_pr (topos_logic_comprehension_tm t p)
      =
      t.
  Proof.
    unfold topos_logic_comprehension_pr, topos_logic_comprehension_tm ; cbn.
    apply PullbackArrow_PullbackPr1.
  Qed.

  Proposition topos_logic_comprehension_eta
              {Γ A : E}
              {φ : form A}
              (t : Γ --> topos_logic_compr E φ)
    : topos_logic_comprehension_tm
        (topos_logic_comprehension_pr t)
        (topos_logic_comprehension_proof t)
      =
      t.
  Proof.
    unfold topos_logic_comprehension_pr, topos_logic_comprehension_tm.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
      [ | apply TerminalArrowEq ].
    apply topos_logic_comprehension_beta.
  Qed.

  Definition topos_logic_comprehension_tm_weq
             {Γ A : E}
             (φ : form A)
    : (∑ (t : Γ --> A), ⊤ ⊢ φ [[ t ]])
      ≃
      Γ --> topos_logic_compr E φ.
  Proof.
    use weq_iso.
    - intros t.
      exact (topos_logic_comprehension_tm (pr1 t) (pr2 t)).
    - exact (λ f, f · PullbackPr1 _ ,, topos_logic_comprehension_proof f).
    - abstract
        (intro f ;
         use subtypePath ;
         [ intro ;
           use invproofirrelevance ;
           intros ? ? ;
           apply topos_logic_disp_mor_eq
         | ] ;
         apply topos_logic_comprehension_beta).
    - abstract
        (intro f ; cbn ;
         apply topos_logic_comprehension_eta).
  Defined.

  (** * 3. Equality formula *)
  Definition topos_logic_eq
             {Γ A : E}
             (t₁ t₂ : Γ --> A)
    : form Γ
    := characteristic_morphism Ω (EqualizerArrowMonic (EQ _ _ t₁ t₂)).

  Notation "t₁ ≡ t₂" := (topos_logic_eq t₁ t₂).

  Section EqPullback.
    Context {Γ A : E}
            (t₁ t₂ : Γ --> A).

    Definition topos_logic_eq_to_pb
      : EQ _ _ t₁ t₂ --> PB _ _ _ (t₁ ≡ t₂) Ω.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1
                 (subobject_classifier_pullback
                    Ω
                    (EqualizerArrowMonic (EQ _ _ t₁ t₂)))).
      - apply TerminalArrow.
      - exact (subobject_classifier_square_commutes Ω (EqualizerArrowMonic (EQ Γ A t₁ t₂))).
    Defined.

    Definition topos_logic_pb_to_eq
      : PB _ _ _ (t₁ ≡ t₂) Ω --> EQ _ _ t₁ t₂.
    Proof.
      use (PullbackArrow
             (subobject_classifier_pullback
                Ω
                (EqualizerArrowMonic (EQ Γ A t₁ t₂)))).
      - exact (PullbackPr1 _).
      - exact (PullbackPr2 _).
      - apply PullbackSqrCommutes.
    Defined.

    Proposition topos_logic_eq_pullback_invs
      : is_inverse_in_precat topos_logic_pb_to_eq topos_logic_eq_to_pb.
    Proof.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
          [ | apply TerminalArrowEq ].
        cbn.
        unfold topos_logic_eq_to_pb, topos_logic_pb_to_eq.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        etrans.
        {
          apply (PullbackArrow_PullbackPr1
                   (subobject_classifier_pullback
                      Ω
                      (EqualizerArrowMonic (EQ Γ A t₁ t₂)))).
        }
        rewrite id_left.
        apply idpath.
      - unfold topos_logic_eq_to_pb, topos_logic_pb_to_eq.
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (subobject_classifier_pullback
                     Ω
                     (EqualizerArrowMonic (EQ Γ A t₁ t₂))))) ;
          [ | apply TerminalArrowEq ].
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1
                   (subobject_classifier_pullback
                      Ω
                      (EqualizerArrowMonic (EQ Γ A t₁ t₂)))).
        }
        rewrite PullbackArrow_PullbackPr1.
        rewrite id_left.
        apply idpath.
    Qed.

    Definition topos_logic_eq_pullback
      : z_iso (PB _ _ _ (t₁ ≡ t₂) Ω) (EQ _ _ t₁ t₂).
    Proof.
      use make_z_iso.
      - exact topos_logic_pb_to_eq.
      - exact topos_logic_eq_to_pb.
      - exact topos_logic_eq_pullback_invs.
    Defined.
  End EqPullback.

  Proposition topos_logic_refl
              {Γ A : E}
              (t : Γ --> A)
              (Δ : form Γ)
    : Δ ⊢ t ≡ t.
  Proof.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (TerminalArrow _ _).
      + abstract
          (cbn ;
           unfold topos_logic_eq ;
           pose (_ ,, z_iso_Equalizer_of_same_map (EQ _ _ t t) (idpath _) : z_iso _ _) as i ;
           pose proof (maponpaths
                         (λ z, inv_from_z_iso i · z)
                         (subobject_classifier_square_commutes
                            Ω
                            (EqualizerArrowMonic (EQ Γ A t t))))
             as p ;
           simpl in p ;
           unfold i in p ;
           rewrite !assoc in p ;
           rewrite z_iso_after_z_iso_inv in p ;
           rewrite id_left in p ;
           rewrite p ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
    - abstract
        (cbn ;
         rewrite id_right ;
         apply PullbackArrow_PullbackPr1).
  Defined.

  Proposition topos_logic_refl_from_eq
              {Γ A : E}
              {t₁ t₂ : Γ --> A}
              (Δ : form Γ)
              (p : topos_logic_compr_mono E Δ · t₁
                   =
                   topos_logic_compr_mono E Δ · t₂)
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    cbn in p.
    simple refine (_ ,, _).
    - refine (_ · topos_logic_eq_to_pb _ _).
      use EqualizerIn.
      + exact (PullbackPr1 _).
      + exact p.
    -  cbn.
       unfold topos_logic_eq_to_pb.
       rewrite !assoc'.
       rewrite PullbackArrow_PullbackPr1 ; cbn.
       rewrite EqualizerCommutes.
       rewrite id_right.
       apply idpath.
  Qed.

  Proposition topos_logic_refl_to_eq_ctx
              {Γ A : E}
              {t₁ t₂ : Γ --> A}
              {Δ : form Γ}
              (p : Δ ⊢ t₁ ≡ t₂)
    : topos_logic_compr_mono E Δ · t₁
      =
      topos_logic_compr_mono E Δ · t₂.
  Proof.
    unfold topos_logic_compr_mono ; cbn.
    induction p as [ f p ].
    rewrite id_right in p.
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    rewrite !assoc'.
    apply maponpaths.
    use (cancel_z_iso' (z_iso_inv (topos_logic_eq_pullback t₁ t₂))).
    cbn.
    unfold topos_logic_eq_to_pb.
    rewrite !assoc.
    rewrite !PullbackArrow_PullbackPr1.
    cbn.
    refine (!_).
    apply EqualizerEqAr.
  Qed.

  Proposition topos_logic_extensional
              {Γ A : E}
              {t₁ t₂ : Γ --> A}
              (p : ⊤ ⊢ t₁ ≡ t₂)
    : t₁ = t₂.
  Proof.
    pose proof (maponpaths
                  (λ z, inv_from_z_iso (topos_logic_compr_truth_z_iso Γ) · z)
                  (topos_logic_refl_to_eq_ctx p))
      as q.
    cbn in q.
    rewrite !assoc in q.
    refine (_ @ q @ _).
    - rewrite !PullbackArrow_PullbackPr1.
      rewrite id_left.
      apply idpath.
    - rewrite !PullbackArrow_PullbackPr1.
      rewrite id_left.
      apply idpath.
  Qed.

  Proposition topos_logic_pair_eq
              {Γ A B : E}
              {Δ : form Γ}
              {t₁ t₂ : Γ --> (A × B)}
              (p : Δ ⊢ (t₁ · π₁) ≡ (t₂ · π₁))
              (q : Δ ⊢ (t₁ · π₂) ≡ (t₂ · π₂))
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    use topos_logic_refl_from_eq.
    apply topos_logic_refl_to_eq_ctx in p.
    apply topos_logic_refl_to_eq_ctx in q.
    cbn in *.
    use topos_pair_eq.
    - rewrite !assoc'.
      exact p.
    - rewrite !assoc'.
      exact q.
  Qed.

  Proposition topos_logic_eq_subst_mor_char_morphism_eq
              {Γ₁ Γ₂ A : E}
              {t₁ t₂ : Γ₂ --> A}
              (s : Γ₁ --> Γ₂)
    : characteristic_morphism Ω (EqualizerArrowMonic (EQ Γ₁ A (s · t₁) (s · t₂)))
      =
      s · characteristic_morphism Ω (EqualizerArrowMonic (EQ Γ₂ A t₁ t₂)).
  Proof.
    use (subobject_classifier_map_eq
           Ω
           (EqualizerArrowMonic (EQ Γ₁ A (s · t₁) (s · t₂)))).
    - apply subobject_classifier_square_commutes.
    - abstract
        (simpl ;
         pose proof (maponpaths
                       (λ z, equalizer_subst_mor EQ s · z)
                       (subobject_classifier_square_commutes
                          Ω
                          (EqualizerArrowMonic (EQ Γ₂ A t₁ t₂))))
           as p ;
         cbn in p ;
         unfold equalizer_subst_mor in p ;
         rewrite !assoc in p ;
         rewrite !EqualizerCommutes in p ;
         rewrite !assoc' in p ;
         refine (p @ _) ;
         unfold const_true ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply TerminalArrowEq).
    - apply subobject_classifier_pullback.
    - intros w h k p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ].
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (equalizer_subst_pullback EQ t₁ t₂ s))) ;
          [
          | exact (pr12 φ₁ @ !(pr12 φ₂)) ].
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (subobject_classifier_pullback
                     Ω
                     (EqualizerArrowMonic (EQ Γ₂ A t₁ t₂))))) ;
          [ | apply TerminalArrowEq ].
        cbn.
        unfold equalizer_subst_mor.
        rewrite !assoc'.
        rewrite !EqualizerCommutes.
        rewrite !assoc.
        apply maponpaths_2.
        exact (pr12 φ₁ @ !(pr12 φ₂)).
      + simple refine (_ ,, _ ,, _).
        * use (PullbackArrow (equalizer_subst_pullback EQ t₁ t₂ s)).
          ** use (PullbackArrow
                    (subobject_classifier_pullback
                       Ω
                       (EqualizerArrowMonic (EQ Γ₂ A t₁ t₂)))).
             *** exact (h · s).
             *** exact k.
             *** abstract
                 (rewrite !assoc' ;
                  exact p).
          ** exact h.
          ** abstract
              (apply (PullbackArrow_PullbackPr1
                        (subobject_classifier_pullback
                           Ω
                           (EqualizerArrowMonic (EQ Γ₂ A t₁ t₂))))).
        * abstract
            (apply (PullbackArrow_PullbackPr2
                      (equalizer_subst_pullback EQ t₁ t₂ s))).
        * abstract
            (apply TerminalArrowEq).
  Qed.

  Proposition topos_logic_eq_subst_mor
              {Γ₁ Γ₂ A : E}
              {t₁ t₂ : Γ₂ --> A}
              (s : Γ₁ --> Γ₂)
    : (t₁ ≡ t₂) [[ s ]] ⊢ s · t₁ ≡ s · t₂.
  Proof.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + apply TerminalArrow.
      + cbn.
        unfold topos_logic_eq.
        rewrite topos_logic_eq_subst_mor_char_morphism_eq.
        rewrite PullbackSqrCommutes.
        apply maponpaths_2.
        apply TerminalArrowEq.
    - cbn.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_right.
      apply idpath.
  Qed.

  Proposition topos_logic_eq_subst_inv
              {Γ₁ Γ₂ A : E}
              {t₁ t₂ : Γ₂ --> A}
              (s : Γ₁ --> Γ₂)
    : s · t₁ ≡ s · t₂ ⊢ (t₁ ≡ t₂) [[ s ]].
  Proof.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + apply TerminalArrow.
      + cbn.
        unfold topos_logic_eq.
        rewrite <- topos_logic_eq_subst_mor_char_morphism_eq.
        rewrite PullbackSqrCommutes.
        apply maponpaths_2.
        apply TerminalArrowEq.
    - cbn.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_right.
      apply idpath.
  Qed.

  Proposition topos_logic_eq_subst_eq
              {Γ₁ Γ₂ A : E}
              {t₁ t₂ : Γ₂ --> A}
              (s : Γ₁ --> Γ₂)
    : (t₁ ≡ t₂) [[ s ]] = (s · t₁ ≡ s · t₂).
  Proof.
    use topos_logic_prop_ext.
    - apply topos_logic_eq_subst_mor.
    - apply topos_logic_eq_subst_inv.
  Qed.

  Proposition topos_logic_eq_ap
              {Γ A B : E}
              {Δ : form Γ}
              {t₁ t₂ : Γ --> A}
              (f : A --> B)
              (p : Δ ⊢ t₁ ≡ t₂)
    : Δ ⊢ t₁ · f ≡ t₂ · f.
  Proof.
    use topos_logic_refl_from_eq.
    rewrite !assoc.
    apply maponpaths_2.
    use topos_logic_refl_to_eq_ctx.
    exact p.
  Qed.

  Proposition topos_logic_to_eq_truth
              {Γ : E}
              {Δ φ : form Γ}
              (p : Δ ⊢ φ)
    : Δ ⊢ φ ≡ ⊤.
  Proof.
    induction p as [ f p ].
    use topos_logic_refl_from_eq.
    cbn ; cbn in p.
    rewrite id_right in p.
    rewrite <- p.
    rewrite !assoc'.
    rewrite PullbackSqrCommutes.
    unfold const_true.
    rewrite !assoc.
    apply maponpaths_2.
    apply TerminalArrowEq.
  Qed.

  Proposition topos_logic_from_eq_truth
              {Γ : E}
              {Δ φ : form Γ}
              (p : Δ ⊢ φ ≡ ⊤)
    : Δ ⊢ φ.
  Proof.
    apply topos_logic_refl_to_eq_ctx in p.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr2 _).
      + abstract
          (refine (p @ _) ;
           cbn ; unfold const_true ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr1 ;
         rewrite id_right ;
         apply idpath).
  Qed.

  Proposition topos_logic_eq_elim
              {Γ A : E}
              {Δ : form Γ}
              (φ : form (Γ × A))
              {t₁ t₂ : Γ --> A}
              (p : Δ ⊢ φ [[ ⟨ identity _ , t₁ ⟩ ]])
              (q : Δ ⊢ t₁ ≡ t₂)
    : Δ ⊢ φ [[ ⟨ identity _ , t₂ ⟩ ]].
  Proof.
    assert (Δ ⊢ ⟨ identity _ , t₁ ⟩ ≡ ⟨ identity _ , t₂ ⟩)
      as r.
    {
      use topos_logic_refl_from_eq.
      use topos_pair_eq ; rewrite !assoc', ?topos_pair_pr1, ?topos_pair_pr2.
      {
        apply idpath.
      }
      apply topos_logic_refl_to_eq_ctx.
      exact q.
    }
    apply topos_logic_refl_to_eq_ctx in r.
    cbn ; cbn in r.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + refine (pr1 p · _).
        exact (PullbackPr1 _).
      + exact (PullbackPr2 _).
      + rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (pr2 p).
        }
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          exact (!r).
        }
        refine (_ @ PullbackSqrCommutes _).
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (_ @ !(pr2 p)).
          rewrite id_right.
          apply idpath.
        }
        rewrite !assoc'.
        rewrite PullbackSqrCommutes.
        refine (_ @ !(PullbackSqrCommutes _)).
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
    - cbn.
      etrans.
      {
        apply PullbackArrow_PullbackPr1.
      }
      apply (pr2 p).
  Qed.

  Proposition topos_logic_eq_elim'
              {Γ A : E}
              {Δ : form Γ}
              (φ : form A)
              {t₁ t₂ : Γ --> A}
              (p : Δ ⊢ φ [[ t₁ ]])
              (q : Δ ⊢ t₁ ≡ t₂)
    : Δ ⊢ φ [[ t₂ ]].
  Proof.
    assert (Δ ⊢ (φ [[ π₂ ]]) [[ ⟨ identity _ , t₁ ⟩ ]]) as p'.
    {
      rewrite topos_logic_subst_comp.
      rewrite topos_pair_pr2.
      exact p.
    }
    refine (topos_logic_cut
              _
              (topos_logic_eq_elim (φ [[ π₂ ]]) p' q)
              _).
    rewrite topos_logic_subst_comp.
    rewrite topos_pair_pr2.
    apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_eq_sym
              {Γ A : E}
              {Δ : form Γ}
              {t₁ t₂ : Γ --> A}
              (p : Δ ⊢ t₁ ≡ t₂)
    : Δ ⊢ t₂ ≡ t₁.
  Proof.
    use topos_logic_refl_from_eq.
    refine (!_).
    use topos_logic_refl_to_eq_ctx.
    exact p.
  Qed.

  Proposition topos_logic_eq_trans
              {Γ A : E}
              {Δ : form Γ}
              {t₁ t₂ t₃ : Γ --> A}
              (p : Δ ⊢ t₁ ≡ t₂)
              (q : Δ ⊢ t₂ ≡ t₃)
    : Δ ⊢ t₁ ≡ t₃.
  Proof.
    use topos_logic_refl_from_eq.
    apply topos_logic_refl_to_eq_ctx in p, q.
    exact (p @ q).
  Qed.

  (** * 4. Fiberwise binary products *)
  Definition topos_logic_conj
             {Γ : E}
             (φ ψ : form Γ)
    : form Γ
    := ⟨ φ , ψ ⟩ ≡ ⟨ ⊤ , ⊤ ⟩.

  Notation "φ ∧ ψ" := (topos_logic_conj φ ψ).

  Proposition topos_logic_conj_subst
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
              (φ ψ : form Γ₂)
    : (φ ∧ ψ) [[ s ]] = ((φ [[ s ]]) ∧ (ψ [[ s ]])).
  Proof.
    unfold topos_logic_conj.
    rewrite topos_logic_eq_subst_eq.
    rewrite !topos_pair_comp.
    rewrite !topos_logic_truth_subst'.
    apply idpath.
  Qed.

  Proposition topos_logic_conj_intro
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ φ)
              (q : Δ ⊢ ψ)
    : Δ ⊢ φ ∧ ψ.
  Proof.
    unfold topos_logic_conj.
    use topos_logic_pair_eq.
    - rewrite !topos_pair_pr1.
      apply topos_logic_to_eq_truth.
      exact p.
    - rewrite !topos_pair_pr2.
      apply topos_logic_to_eq_truth.
      exact q.
  Qed.

  Proposition topos_logic_conj_elim_left
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ φ ∧ ψ)
    : Δ ⊢ φ.
  Proof.
    pose (topos_logic_eq_ap π₁ p) as r.
    rewrite !topos_pair_pr1 in r.
    apply topos_logic_from_eq_truth in r.
    exact r.
  Qed.

  Proposition topos_logic_conj_elim_right
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ φ ∧ ψ)
    : Δ ⊢ ψ.
  Proof.
    pose (topos_logic_eq_ap π₂ p) as r.
    rewrite !topos_pair_pr2 in r.
    apply topos_logic_from_eq_truth in r.
    exact r.
  Qed.

  Definition topos_logic_fiberwise_binproducts
    : fiberwise_binproducts (topos_logic_cleaving E).
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - apply locally_propositional_topos_logic_disp_cat.
    - intros Γ φ ψ.
      exact (φ ∧ ψ).
    - abstract
        (intros Γ φ ψ ;
         refine (topos_logic_conj_elim_left _) ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ φ ψ ;
         refine (topos_logic_conj_elim_right _) ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ φ ψ Δ p q ;
         exact (topos_logic_conj_intro p q)).
    - abstract
        (intros Γ₁ Γ₂ s φ ψ;
         cbn -[topos_logic_disp_cat topos_logic_conj] ;
         apply (idtoiso_disp (idpath _)) ;
         refine (!_) ;
         apply topos_logic_conj_subst).
  Defined.

  (** * 5. Additional rules related to conjunction *)
  Proposition topos_logic_weaken_left
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ ψ)
    : φ ∧ Δ ⊢ ψ.
  Proof.
    refine (topos_logic_cut _ _ p).
    use topos_logic_conj_elim_right.
    - exact φ.
    - apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_weaken_right
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ ψ)
    : Δ ∧ φ ⊢ ψ.
  Proof.
    refine (topos_logic_cut _ _ p).
    use topos_logic_conj_elim_left.
    - exact φ.
    - apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_swap
              {Γ : E}
              (φ ψ : form Γ)
    : φ ∧ ψ ⊢ ψ ∧ φ.
  Proof.
    use topos_logic_conj_intro.
    - use topos_logic_weaken_left.
      apply topos_logic_hyp.
    - use topos_logic_weaken_right.
      apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_gcut
              {Γ : E}
              {Δ₁ Δ₂ Δ₃ : form Γ}
              (p : Δ₁ ⊢ Δ₂)
              (q : Δ₁ ∧ Δ₂ ⊢ Δ₃)
    : Δ₁ ⊢ Δ₃.
  Proof.
    refine (topos_logic_cut _ _ q).
    use topos_logic_conj_intro.
    - apply topos_logic_hyp.
    - exact p.
  Qed.

  Proposition topos_logic_comp_subset
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ∧ φ ⊢ ψ)
    : φ [[ topos_logic_compr_mono E Δ ]] ⊢ ψ [[ topos_logic_compr_mono E Δ ]].
  Proof.
    refine (topos_logic_cut _ _ (topos_logic_subst_proof _ _ p)).
    clear p ψ.
    rewrite topos_logic_conj_subst.
    use topos_logic_conj_intro.
    - simple refine (_ ,, _).
      + use PullbackArrow.
        * use PullbackArrow.
          ** exact (PullbackPr1 _ · topos_logic_compr_mono _ _).
          ** exact (PullbackPr2 _).
          ** abstract
              (cbn ;
               rewrite !assoc' ;
               rewrite PullbackSqrCommutes ;
               rewrite !assoc ;
               apply maponpaths_2 ;
               apply TerminalArrowEq).
        * exact (PullbackPr2 _).
        * abstract
            (cbn ;
             rewrite !assoc ;
             rewrite PullbackArrow_PullbackPr1 ;
             rewrite !assoc' ;
             rewrite PullbackSqrCommutes ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply TerminalArrowEq).
      + simpl.
        rewrite PullbackArrow_PullbackPr1.
        rewrite id_right.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ; [ | apply TerminalArrowEq ].
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
    - apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_prop_ext'
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ∧ φ ⊢ ψ)
              (q : Δ ∧ ψ ⊢ φ)
    : Δ ⊢ φ ≡ ψ.
  Proof.
    assert (φ [[ topos_logic_compr_mono _ Δ ]] ⊢ ψ [[ topos_logic_compr_mono _ Δ ]])
      as r₁.
    {
      use topos_logic_comp_subset.
      exact p.
    }
    assert (ψ [[ topos_logic_compr_mono _ Δ ]] ⊢ φ [[ topos_logic_compr_mono _ Δ ]])
      as r₂.
    {
      use topos_logic_comp_subset.
      exact q.
    }
    use topos_logic_refl_from_eq.
    exact (topos_logic_prop_ext _ r₁ r₂).
  Qed.

  (** * 6. Fiberwise exponentials *)
  Definition topos_logic_impl
             {Γ : E}
             (φ ψ : form Γ)
    : form Γ
    := (φ ∧ ψ) ≡ φ.

  Notation "φ ⇒ ψ" := (topos_logic_impl φ ψ).

  Proposition topos_logic_impl_subst
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
              (φ ψ : form Γ₂)
    : (φ ⇒ ψ) [[ s ]] = ((φ [[ s ]]) ⇒ (ψ [[ s ]])).
  Proof.
    unfold topos_logic_impl.
    rewrite topos_logic_eq_subst_eq.
    apply maponpaths_2.
    apply topos_logic_conj_subst.
  Qed.

  Proposition topos_logic_impl_intro
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ∧ φ ⊢ ψ)
    : Δ ⊢ φ ⇒ ψ.
  Proof.
    use topos_logic_prop_ext'.
    - use (topos_logic_conj_elim_left (ψ := ψ)).
      use (topos_logic_conj_elim_right (φ := Δ)).
      apply id_disp.
    - use topos_logic_conj_intro.
      + use (topos_logic_conj_elim_right (φ := Δ)).
        apply id_disp.
      + exact p.
  Qed.

  Proposition topos_logic_impl_elim
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ φ ⇒ ψ)
              (q : Δ ⊢ φ)
    : Δ ⊢ ψ.
  Proof.
    unfold topos_logic_impl in p.
    use (topos_logic_conj_elim_right (φ := φ)).
    use topos_logic_from_eq_truth.
    apply topos_logic_to_eq_truth in q.
    exact (topos_logic_eq_trans p q).
  Qed.

  Definition topos_logic_fiberwise_exponentials
    : fiberwise_exponentials topos_logic_fiberwise_binproducts.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - apply locally_propositional_topos_logic_disp_cat.
    - intros Γ φ ψ.
      exact (φ ⇒ ψ).
    - abstract
        (intros Γ φ ψ ;
         refine (topos_logic_impl_elim _ _) ;
         [ use topos_logic_weaken_left ; apply topos_logic_hyp
         | use topos_logic_weaken_right ; apply topos_logic_hyp ]).
    - abstract
        (intros Γ φ ψ Δ p ;
         use topos_logic_impl_intro ;
         cbn -[topos_logic_disp_cat] in p ;
         refine (topos_logic_cut _ _ p) ;
         apply topos_logic_swap).
    - abstract
        (intros Γ₁ Γ₂ s φ ψ;
         cbn -[topos_logic_disp_cat topos_logic_impl] ;
         apply (idtoiso_disp (idpath _)) ;
         refine (!_) ;
         apply topos_logic_impl_subst).
  Defined.

  (** * 7. Universal quantification *)
  Definition topos_logic_forall
             {Γ A : E}
             (φ : form (Γ × A))
    : form Γ
    := {{ φ }} ≡ {{ ⊤ }}.

  Notation "'∀t'" := topos_logic_forall.

  Proposition topos_logic_forall_subst
              {Γ₁ Γ₂ A : E}
              (φ : form (Γ₂ × A))
              (s : Γ₁ --> Γ₂)
    : (∀t φ) [[ s ]]
      =
      (∀t (φ [[ ⟨ π₁ · s , π₂ ⟩ ]])).
  Proof.
    unfold topos_logic_forall.
    rewrite topos_logic_eq_subst_eq.
    rewrite !topos_compr_subst.
    do 2 apply maponpaths.
    apply topos_logic_truth_subst.
  Qed.

  Proposition topos_logic_forall_intro
              {Γ A : E}
              {Δ : form Γ}
              {φ : form (Γ × A)}
              (p : Δ [[ π₁ ]] ⊢ φ)
    : Δ ⊢ (∀t φ).
  Proof.
    unfold topos_logic_forall.
    apply topos_logic_to_eq_truth in p.
    apply topos_logic_refl_to_eq_ctx in p.
    apply topos_logic_refl_from_eq.
    rewrite !topos_compr_subst.
    apply maponpaths.
    cbn in p.
    transparent assert (f : ((topos_logic_compr E Δ × A) --> PB Ω (Γ × A) 𝟙 (π₁ · Δ) (true' Ω))).
    {
      use PullbackArrow.
      - exact (PullbackPr1 _ #× identity _).
      - apply TerminalArrow.
      - abstract
          (rewrite !assoc ;
           rewrite topos_prod_ar_pr1 ;
           rewrite !assoc' ;
           etrans ;
           [ apply maponpaths ;
             apply (PullbackSqrCommutes (PB Ω Γ 𝟙 Δ Ω))
           | ] ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
    }
    pose proof (maponpaths (λ z, f · z) p) as q.
    cbn in q.
    rewrite !assoc in q.
    unfold f in q.
    rewrite !PullbackArrow_PullbackPr1 in q.
    refine (_ @ q @ _).
    - cbn.
      apply maponpaths_2.
      use topos_pair_eq.
      + rewrite topos_pair_pr1, topos_prod_ar_pr1.
        apply idpath.
      + rewrite topos_pair_pr2, topos_prod_ar_pr2.
        rewrite id_right.
        apply idpath.
    - cbn.
      unfold const_true.
      rewrite !assoc.
      apply maponpaths_2.
      apply TerminalArrowEq.
  Qed.

  Proposition topos_logic_forall_elim
              {Γ A : E}
              {Δ : form Γ}
              {φ : form (Γ × A)}
              (p : Δ ⊢ ∀t φ)
              (t : Γ --> A)
    : Δ ⊢ φ [[ ⟨ identity _ , t ⟩ ]].
  Proof.
    unfold topos_logic_forall in p.
    refine (topos_logic_cut
              _
              (topos_logic_eq_elim ((π₁ · t) ∈ π₂) _ (topos_logic_eq_sym p))
              _).
    - rewrite topos_in_subst.
      rewrite topos_pair_pr2.
      rewrite topos_in_compr.
      rewrite assoc.
      rewrite topos_pair_pr1.
      rewrite topos_logic_truth_subst'.
      apply topos_logic_truth_intro.
    - rewrite topos_in_subst.
      rewrite topos_pair_pr2.
      rewrite topos_in_compr.
      rewrite assoc.
      rewrite topos_pair_pr1.
      rewrite id_left.
      apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_forall_type_iso
              {Γ A B : E}
              (f : z_iso (Γ × A) (Γ × B))
              (φ : form (Γ × B))
              (p : f · π₁ = π₁)
    : (∀t φ ⊢ ∀t (φ [[ f ]])).
  Proof.
    use topos_logic_forall_intro.
    rewrite topos_logic_forall_subst.
    use (topos_logic_cut
           _
           (topos_logic_forall_elim (topos_logic_hyp _ _) (f · π₂))
           _).
    rewrite topos_logic_subst_comp.
    rewrite topos_pair_comp.
    rewrite !assoc.
    rewrite topos_pair_pr1, topos_pair_pr2.
    rewrite id_left.
    use (idtoiso_disp (idpath _)).
    cbn.
    apply maponpaths_2.
    use topos_pair_eq.
    - rewrite topos_pair_pr1.
      exact (!p).
    - rewrite topos_pair_pr2.
      apply idpath.
  Qed.

  (** * 8. Fiberwise initial object *)
  Definition topos_logic_false
             (Γ : E)
    : form Γ
    := (∀t π₂).

  Notation "⊥" := (topos_logic_false _).

  Proposition topos_logic_false_subst
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
    : (topos_logic_false Γ₂) [[ s ]] = topos_logic_false Γ₁.
  Proof.
    unfold topos_logic_false.
    rewrite topos_logic_forall_subst.
    apply maponpaths.
    cbn.
    rewrite topos_pair_pr2.
    apply idpath.
  Qed.

  Proposition topos_logic_false_elim
              (Γ : E)
              {Δ φ : form Γ}
              (p : Δ ⊢ ⊥)
    : Δ ⊢ φ.
  Proof.
    refine (topos_logic_cut _ (topos_logic_forall_elim p φ) _).
    unfold topos_logic_subst.
    rewrite topos_pair_pr2.
    apply topos_logic_hyp.
  Qed.

  Definition topos_logic_fiberwise_initial
    : fiberwise_initial (topos_logic_cleaving E).
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - apply locally_propositional_topos_logic_disp_cat.
    - intro Γ.
      exact ⊥.
    - abstract
        (intros Γ φ ;
         use topos_logic_false_elim ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ₁ Γ₂ s ;
         cbn -[topos_logic_disp_cat topos_logic_false] ;
         apply (idtoiso_disp (idpath _)) ;
         apply topos_logic_false_subst).
  Defined.

  (** * 9. Fiberwise binary coproducts *)
  Definition topos_logic_disj
             {Γ : E}
             (φ ψ : form Γ)
    : form Γ
    := (∀t ((φ [[ π₁ ]] ⇒ π₂) ⇒ (ψ [[ π₁ ]] ⇒ π₂) ⇒ π₂)).

  Notation "φ ∨ ψ" := (topos_logic_disj φ ψ).

  Proposition topos_logic_disj_subst
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
              (φ ψ : form Γ₂)
    : (φ ∨ ψ) [[ s ]] = (φ [[ s ]] ∨ ψ [[ s ]]).
  Proof.
    unfold topos_logic_disj.
    rewrite topos_logic_forall_subst.
    rewrite !topos_logic_impl_subst.
    apply maponpaths.
    rewrite !topos_logic_subst_comp.
    simpl.
    rewrite !topos_pair_pr1, !topos_pair_pr2.
    apply idpath.
  Qed.

  Proposition topos_logic_disj_intro_l
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ φ)
    : Δ ⊢ φ ∨ ψ.
  Proof.
    use topos_logic_forall_intro.
    do 2 use topos_logic_impl_intro.
    use topos_logic_impl_elim.
    - exact (φ [[π₁]]).
    - use topos_logic_weaken_right.
      use topos_logic_weaken_left.
      apply topos_logic_hyp.
    - do 2 use topos_logic_weaken_right.
      use topos_logic_subst_proof.
      exact p.
  Qed.

  Proposition topos_logic_disj_intro_r
              {Γ : E}
              {Δ φ ψ : form Γ}
              (p : Δ ⊢ ψ)
    : Δ ⊢ φ ∨ ψ.
  Proof.
    use topos_logic_forall_intro.
    use topos_logic_impl_intro.
    use topos_logic_impl_intro.
    use topos_logic_impl_elim.
    - exact (ψ [[π₁]]).
    - use topos_logic_weaken_left.
      apply topos_logic_hyp.
    - do 2 use topos_logic_weaken_right.
      use topos_logic_subst_proof.
      exact p.
  Qed.

  Proposition topos_logic_disj_elim
              {Γ : E}
              {Δ φ ψ χ : form Γ}
              (p : Δ ⊢ φ ∨ ψ)
              (q : φ ⊢ χ)
              (r : ψ ⊢ χ)
    : Δ ⊢ χ.
  Proof.
    refine (topos_logic_cut _ (topos_logic_forall_elim p χ) _).
    rewrite !topos_logic_impl_subst.
    rewrite !topos_logic_subst_comp.
    rewrite !topos_pair_pr1.
    rewrite !topos_logic_subst_id.
    cbn -[topos_logic_disp_cat].
    rewrite !topos_pair_pr2.
    use topos_logic_impl_elim.
    - exact (ψ ⇒ χ).
    - use topos_logic_impl_elim.
      + exact (φ ⇒ χ).
      + apply topos_logic_hyp.
      + use topos_logic_impl_intro.
        use topos_logic_weaken_left.
        exact q.
    - use topos_logic_impl_intro.
      use topos_logic_weaken_left.
      exact r.
  Qed.

  Definition topos_logic_fiberwise_bincoproducts
    : fiberwise_bincoproducts (topos_logic_cleaving E).
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - apply locally_propositional_topos_logic_disp_cat.
    - intros Γ φ ψ.
      exact (φ ∨ ψ).
    - abstract
        (intros Γ φ ψ ;
         refine (topos_logic_disj_intro_l _) ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ φ ψ ;
         refine (topos_logic_disj_intro_r _) ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ φ ψ Δ p q ;
         exact (topos_logic_disj_elim (topos_logic_hyp _ _) p q)).
    - abstract
        (intros Γ₁ Γ₂ s φ ψ;
         cbn -[topos_logic_disp_cat topos_logic_disj] ;
         apply (idtoiso_disp (idpath _)) ;
         apply topos_logic_disj_subst).
  Defined.

  (** * 10. Existential quantification *)
  Definition topos_logic_exists
             {Γ A : E}
             (φ : form (Γ × A))
    : form Γ
    := ∀t ((∀t (φ [[ ⟨ π₁ · π₁ , π₂ ⟩ ]] ⇒ (π₁ · π₂))) ⇒ π₂).

  Notation "'∃t'" := topos_logic_exists.

  Proposition topos_logic_exists_subst
              {Γ₁ Γ₂ A : E}
              (φ : form (Γ₂ × A))
              (s : Γ₁ --> Γ₂)
    : (∃t φ) [[ s ]]
      =
      (∃t (φ [[ ⟨ π₁ · s , π₂ ⟩ ]])).
  Proof.
    unfold topos_logic_exists.
    rewrite topos_logic_forall_subst.
    apply maponpaths.
    rewrite topos_logic_impl_subst.
    rewrite topos_logic_forall_subst.
    rewrite !topos_logic_impl_subst.
    rewrite !topos_logic_subst_comp.
    simpl.
    rewrite topos_pair_pr2.
    apply maponpaths_2.
    apply maponpaths.
    rewrite !topos_pair_comp.
    rewrite !assoc.
    rewrite !topos_pair_pr1.
    rewrite !topos_pair_pr2.
    apply idpath.
  Qed.

  Proposition topos_logic_exists_intro
              {Γ A : E}
              {Δ : form Γ}
              {φ : form (Γ × A)}
              {t : Γ --> A}
              (p : Δ ⊢ φ [[ ⟨ identity _ , t ⟩ ]])
    : (Δ ⊢ ∃t φ).
  Proof.
    use topos_logic_forall_intro.
    use topos_logic_impl_intro.
    refine (topos_logic_gcut
              (topos_logic_forall_elim
                 (topos_logic_weaken_left (topos_logic_hyp _ _))
                 (π₁ · t))
              _).
    rewrite topos_logic_impl_subst.
    rewrite topos_logic_subst_comp.
    cbn -[topos_logic_disp_cat].
    rewrite !topos_pair_comp.
    rewrite !assoc.
    rewrite !topos_pair_pr1.
    rewrite !topos_pair_pr2.
    rewrite !id_left.
    refine (topos_logic_impl_elim _ _).
    {
      use topos_logic_weaken_left.
      apply topos_logic_hyp.
    }
    do 2 use topos_logic_weaken_right.
    refine (topos_logic_cut _ (topos_logic_subst_proof _ π₁ p) _).
    rewrite topos_logic_subst_comp.
    cbn -[topos_logic_disp_cat].
    rewrite !topos_pair_comp.
    rewrite id_right.
    apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_exists_elim
              {Γ A : E}
              {Δ ψ : form Γ}
              {φ : form (Γ × A)}
              (p : Δ ⊢ ∃t φ)
              (q : φ ⊢ ψ [[ π₁ ]])
    : Δ ⊢ ψ.
  Proof.
    refine (topos_logic_cut _ p _) ; clear p.
    simple refine (topos_logic_cut _ (topos_logic_forall_elim (topos_logic_hyp _ _) _) _).
    {
      exact ψ.
    }
    rewrite topos_logic_impl_subst.
    rewrite topos_logic_forall_subst.
    rewrite topos_logic_impl_subst.
    cbn -[topos_logic_disp_cat].
    rewrite !topos_pair_comp.
    rewrite !topos_pair_pr2.
    rewrite !id_right.
    rewrite !assoc.
    rewrite topos_pair_comp.
    rewrite !topos_pair_pr1, !topos_pair_pr2.
    rewrite !assoc.
    rewrite !topos_pair_pr1.
    use (topos_logic_impl_elim (topos_logic_hyp _ _)).
    use topos_logic_forall_intro.
    use topos_logic_impl_intro.
    use topos_logic_weaken_left.
    rewrite topos_pair_id_id.
    rewrite id_left.
    exact q.
  Qed.

  Proposition topos_logic_exists_type_iso
              {Γ A B : E}
              (f : z_iso (Γ × A) (Γ × B))
              (φ : form (Γ × B))
              (p : f · π₁ = π₁)
    : (∃t (φ [[ f ]]) ⊢ ∃t φ).
  Proof.
    refine (topos_logic_exists_elim (topos_logic_hyp _ _) _).
    rewrite topos_logic_exists_subst.
    use topos_logic_exists_intro.
    - exact (f · π₂).
    - rewrite topos_logic_subst_comp.
      rewrite topos_pair_comp.
      rewrite !assoc.
      rewrite topos_pair_pr1, topos_pair_pr2.
      rewrite id_left.
      use (idtoiso_disp (idpath _)).
      cbn.
      apply maponpaths_2.
      rewrite <- p.
      rewrite <- topos_pair_comp.
      rewrite topos_pair_id_id.
      rewrite id_right.
      apply idpath.
  Qed.

  (** * 11. The hyperdoctrine associated to a topos *)
  Definition topos_hyperdoctrine
    : hyperdoctrine.
  Proof.
    use make_hyperdoctrine.
    - exact E.
    - exact (topos_logic_disp_cat E).
    - exact (Topos_Terminal E).
    - exact (Topos_BinProducts E).
    - exact (topos_logic_cleaving E).
    - exact (locally_propositional_topos_logic_disp_cat E).
    - exact (is_univalent_disp_topos_logic_disp_cat E).
  Defined.

  Definition is_univalent_topos_univalent_hyperdoctrine
             (HE : is_univalent E)
    : univalent_hyperdoctrine.
  Proof.
    use make_univalent_hyperdoctrine.
    - exact E.
    - exact (topos_logic_disp_cat E).
    - exact (Topos_Terminal E).
    - exact (Topos_BinProducts E).
    - exact (topos_logic_cleaving E).
    - exact (locally_propositional_topos_logic_disp_cat E).
    - exact (is_univalent_disp_topos_logic_disp_cat E).
    - exact HE.
  Defined.

  Definition topos_logic_universal_quantifiers
    : universal_quantifiers topos_hyperdoctrine.
  Proof.
    use make_universal_quantifiers.
    - exact (λ Γ A φ, ∀t φ).
    - abstract
        (intros Γ A φ ; simpl ;
         refine (topos_logic_cut _ _ _) ;
         [ use (idtoiso_disp (idpath _)) ;
           apply topos_logic_forall_subst
         | ] ;
         refine (topos_logic_cut
                   _
                   (topos_logic_forall_elim (topos_logic_hyp _ _) π₂)
                   _) ;
         rewrite topos_logic_subst_comp ;
         unfold hyperdoctrine_pr1, tm_var ;
         cbn -[topos_logic_disp_cat] ;
         fold (topos_pr1 Γ A) ;
         rewrite id_left ;
         rewrite topos_pair_comp ;
         rewrite !assoc ;
         rewrite topos_pair_pr1 ;
         rewrite topos_pair_pr2 ;
         rewrite id_left ;
         rewrite topos_pair_id_id;
         rewrite id_left ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ A ψ φ p ; simpl ;
         use topos_logic_forall_intro ;
         refine (topos_logic_cut _ _ p) ;
         unfold tm_var, hyperdoctrine_pr1 ;
         cbn -[topos_logic_disp_cat] ;
         rewrite id_left ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ ;
         cbn -[topos_logic_disp_cat] ;
         refine (topos_logic_cut
                   _
                   (topos_logic_forall_type_iso
                      (topos_prod_pb_isomorphism p Hp)
                      (φ [[ s₂ ]])
                      (topos_prod_pb_isomorphism_pr1 p Hp))
                   _) ;
         apply (idtoiso_disp (idpath _)) ;
         refine (_ @ !(topos_logic_forall_subst _ _)) ;
         cbn -[topos_logic_disp_cat] ;
         apply maponpaths ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact (topos_prod_pb_isomorphism_pr2 _ _)).
  Defined.

  Definition topos_logic_existential_quantifiers
    : existential_quantifiers topos_hyperdoctrine.
  Proof.
    use make_existential_quantifiers.
    - exact (λ Γ A φ, ∃t φ).
    - abstract
        (intros Γ A φ ; simpl ;
         refine (topos_logic_cut _ _ _) ;
         [
         | use (idtoiso_disp (idpath _)) ;
           refine (!_) ;
           apply topos_logic_exists_subst ] ;
         use (topos_logic_exists_intro (t := π₂)) ;
         rewrite topos_logic_subst_comp ;
         unfold hyperdoctrine_pr1, tm_var ;
         cbn -[topos_logic_disp_cat] ;
         fold (topos_pr1 Γ A) ;
         rewrite id_left ;
         rewrite topos_pair_comp ;
         rewrite !assoc ;
         rewrite topos_pair_pr1 ;
         rewrite topos_pair_pr2 ;
         rewrite id_left ;
         rewrite topos_pair_id_id;
         rewrite id_left ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ A φ Δ p ; simpl ;
         refine (topos_logic_exists_elim (topos_logic_hyp _ _) _) ;
         refine (topos_logic_cut _ p _) ;
         unfold tm_var, hyperdoctrine_pr1 ;
         cbn -[topos_logic_disp_cat] ;
         rewrite id_left ;
         apply topos_logic_hyp).
    - abstract
        (intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ ;
         cbn -[topos_logic_disp_cat] ;
         refine (topos_logic_cut
                   _
                   _
                   (topos_logic_exists_type_iso
                      (topos_prod_pb_isomorphism p Hp)
                      (φ [[ s₂ ]])
                      (topos_prod_pb_isomorphism_pr1 p Hp))
                   ) ;
         apply (idtoiso_disp (idpath _)) ;
         refine (topos_logic_exists_subst _ _ @ _) ;
         cbn -[topos_logic_disp_cat] ;
         apply maponpaths ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact (!(topos_prod_pb_isomorphism_pr2 _ _))).
  Defined.

  Proposition topos_logic_equality_formulas_intro
              {A : E}
              (φ : form A)
    : φ ⊢ ((π₁ ≡ π₂) ∧ φ [[ π₁ ]]) [[ Δ_{A} ]].
  Proof.
    rewrite topos_logic_conj_subst.
    rewrite topos_logic_eq_subst_eq.
    rewrite topos_logic_subst_comp.
    rewrite !topos_diagonal_pr1, topos_diagonal_pr2.
    rewrite topos_logic_subst_id.
    use topos_logic_conj_intro.
    - use topos_logic_refl.
    - apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_equality_formulas_elim
              {A : E}
              {Δ : form A}
              {φ : form (A × A)}
              (p : Δ ⊢ φ [[ Δ_{A} ]])
    : (π₁ ≡ π₂) ∧ Δ [[ π₁ ]] ⊢ φ.
  Proof.
    rewrite <- (topos_logic_subst_id _ φ).
    refine (topos_logic_gcut _ _).
    {
      use topos_logic_weaken_left.
      exact (topos_logic_subst_proof E π₁ p).
    }
    refine (topos_logic_cut _ _ _).
    {
      refine (topos_logic_conj_intro _ _).
      {
        do 2 use topos_logic_weaken_right.
        apply topos_logic_hyp.
      }
      use topos_logic_weaken_left.
      apply topos_logic_hyp.
    }
    clear Δ p.
    rewrite topos_logic_subst_comp.
    rewrite topos_comp_diagonal.
    rewrite <- (maponpaths (λ z, φ [[ z ]]) topos_pair_id_id).
    use topos_logic_eq_elim'.
    - exact ⟨ π₁ , π₁ ⟩.
    - use topos_logic_weaken_left.
      apply topos_logic_hyp.
    - use topos_logic_weaken_right.
      use topos_logic_pair_eq.
      + rewrite !topos_pair_pr1.
        apply topos_logic_refl.
      + rewrite !topos_pair_pr2.
        apply topos_logic_hyp.
  Qed.

  Definition topos_logic_equality_formulas
    : equality_formulas topos_hyperdoctrine.
  Proof.
    use make_equality_formulas.
    - exact (λ A φ, (π₁ ≡ π₂) ∧ φ [[ π₁ ]]).
    - intros A φ.
      apply topos_logic_equality_formulas_intro.
    - intros A Δ φ p.
      apply topos_logic_equality_formulas_elim.
      exact p.
  Defined.

  Definition topos_logic
    : first_order_hyperdoctrine.
  Proof.
    use make_first_order_hyperdoctrine.
    - exact topos_hyperdoctrine.
    - exact topos_logic_fiberwise_terminal.
    - exact topos_logic_fiberwise_initial.
    - exact topos_logic_fiberwise_binproducts.
    - exact topos_logic_fiberwise_bincoproducts.
    - exact topos_logic_fiberwise_exponentials.
    - exact topos_logic_universal_quantifiers.
    - exact topos_logic_existential_quantifiers.
    - exact topos_logic_equality_formulas.
  Defined.

  Definition is_univalent_topos_logic
             (HE : is_univalent E)
    : univalent_first_order_hyperdoctrine.
  Proof.
    use make_univalent_first_order_hyperdoctrine.
    - use is_univalent_topos_univalent_hyperdoctrine.
      exact HE.
    - exact topos_logic_fiberwise_terminal.
    - exact topos_logic_fiberwise_initial.
    - exact topos_logic_fiberwise_binproducts.
    - exact topos_logic_fiberwise_bincoproducts.
    - exact topos_logic_fiberwise_exponentials.
    - exact topos_logic_universal_quantifiers.
    - exact topos_logic_existential_quantifiers.
    - exact topos_logic_equality_formulas.
  Defined.

  Proposition is_tripos_topos_logic_eq
              {Γ A : E}
              (R : form (A × Γ))
    : R
      =
      (π₁ ∈ π₂) [[ ⟨ π₁ , {{ R [[ ⟨ π₂ , π₁ · π₂ ⟩ ]] }} ⟩ ]].
  Proof.
    rewrite topos_in_subst.
    rewrite topos_pair_pr1, topos_pair_pr2.
    rewrite topos_in_compr.
    cbn.
    rewrite assoc.
    rewrite topos_pair_comp.
    rewrite !assoc.
    rewrite topos_pair_pr1, topos_pair_pr2.
    rewrite !id_left.
    rewrite topos_pair_id_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition is_tripos_topos_logic
    : is_tripos topos_hyperdoctrine.
  Proof.
    simple refine (λ (A : E), _ ,, _ ,, _).
    - exact (ℙ A).
    - exact (π₁ ∈ π₂).
    - intros Γ R.
      simple refine (_ ,, _).
      + exact {{ ⟨ π₂ , π₁ ⟩ · R }}.
      + abstract
          (refine (is_tripos_topos_logic_eq R @ _) ;
           unfold hyperdoctrine_pr1, hyperdoctrine_pr2, tm_var ; cbn ;
           apply maponpaths_2 ;
           rewrite id_left ;
           apply maponpaths ;
           rewrite id_left ;
           refine (_ @ !(topos_compr_subst _ _)) ;
           apply maponpaths ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           rewrite topos_pair_comp ;
           rewrite topos_pair_pr1, topos_pair_pr2 ;
           apply idpath).
  Defined.

  Definition topos_logic_tripos
    : tripos.
  Proof.
    use make_tripos.
    - exact topos_logic.
    - exact is_tripos_topos_logic.
  Defined.

  Definition topos_logic_extensionality_eq
             {A B : E}
             {f g : A --> B}
             (p : ⊤ ⊢ ∀t ((π₂ : (𝟙 × A) --> A) · f ≡ π₂ · g))
    : f = g.
  Proof.
    use topos_logic_extensional.
    pose (topos_logic_subst_proof _ (TerminalArrow _ A) p) as q.
    rewrite topos_logic_truth_subst in q.
    refine (topos_logic_cut _ q _) ; clear q.
    rewrite topos_logic_forall_subst.
    rewrite topos_logic_eq_subst_eq.
    refine (topos_logic_cut
              _
              (topos_logic_forall_elim (topos_logic_hyp _ _) (identity _))
              _).
    rewrite topos_logic_eq_subst_eq.
    rewrite !assoc.
    rewrite !topos_pair_comp.
    rewrite !assoc.
    rewrite !topos_pair_pr1, !topos_pair_pr2.
    rewrite !id_left.
    apply topos_logic_hyp.
  Qed.

  Proposition topos_logic_hyperdoctrine_eq
              {A B : (ty topos_logic)%hd}
              {f g : (tm A B)%hd}
    : (f ≡ g)%hd = (f ≡ g).
  Proof.
    cbn -[first_order_hyperdoctrine_truth].
    etrans.
    {
      apply topos_logic_conj_subst.
    }
    rewrite topos_logic_truth_subst'.
    rewrite topos_logic_truth_subst.
    rewrite topos_logic_eq_subst_eq.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply BinProductPr1Commutes.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply BinProductPr2Commutes.
    }
    use topos_logic_prop_ext.
    - use topos_logic_weaken_right.
      apply topos_logic_hyp.
    - apply topos_logic_conj_intro.
      + apply topos_logic_hyp.
      + apply topos_logic_truth_intro.
  Qed.

  Definition topos_logic_extensionality
    : extensional_first_order_hyperdoctrine topos_logic.
  Proof.
    intros A B f g p.
    use topos_logic_extensionality_eq.
    refine (topos_logic_cut _ p _).
    rewrite topos_logic_hyperdoctrine_eq.
    unfold hyperdoctrine_pr2, tm_var.
    rewrite !id_left.
    apply topos_logic_hyp.
  Qed.

  Definition topos_logic_comprehension_hd
    : first_order_hyperdoctrine_comprehension topos_logic.
  Proof.
    use make_first_order_hyperdoctrine_comprehension.
    - exact (topos_logic_comprehension E).
    - abstract
        (intros A φ ;
         refine (topos_logic_cut
                   _
                   (topos_logic_comprehension_proof (identity _))
                   _) ;
         unfold topos_logic_comprehension_pr ;
         rewrite id_left ;
         apply topos_logic_hyp).
    - intros Γ A φ t p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros ζ₁ ζ₂ ;
           use subtypePath ;
           [ intro ; apply homset_property | ] ;
           use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
           [ | apply TerminalArrowEq ] ;
           exact (pr2 ζ₁ @ !(pr2 ζ₂))).
      + simple refine (_ ,, _).
        * exact (topos_logic_comprehension_tm t p).
        * abstract
            (unfold tm_subst, topos_logic_comprehension_tm ;
             cbn ;
             apply PullbackArrow_PullbackPr1).
  Defined.

  Let EE : tripos := topos_logic_tripos.

  Local Open Scope hd.

  Proposition topos_tripos_prop_ext
              {Γ : ty EE}
              {Δ φ ψ : form Γ}
              (p : Δ ∧ φ ⊢ ψ)
              (q : Δ ∧ ψ ⊢ φ)
    : Δ ⊢ φ ≡ ψ.
  Proof.
    enough (Δ ⊢ topos_logic_eq φ ψ) as r.
    {
      rewrite <- (topos_logic_hyperdoctrine_eq (f := φ) (g := ψ)) in r.
      exact r.
    }
    use topos_logic_prop_ext'.
    - exact p.
    - exact q.
  Qed.

  Local Definition topos_tripos_compr_eq_pointwise_mor
                   (Γ A : ty EE)
                   (Δ : form Γ)
    : (Topos_Pullbacks E Ω Γ 𝟙 Δ (true' Ω) × A)%topos
      -->
      Topos_Pullbacks
        E Ω%topos (A ×h Γ)
        𝟙%topos (topos_logic_subst E (π₂ (tm_var (A ×h Γ))) Δ)
        (true' Ω%topos).
  Proof.
    use PullbackArrow.
    - refine ⟨ _ , _ ⟩%topos.
      + exact π₂%topos.
      + exact (π₁%topos · PullbackPr1 _).
    - apply TerminalArrow.
    - abstract
        (unfold topos_logic_subst ;
         unfold hyperdoctrine_pr2, tm_var ;
         rewrite id_left ;
         rewrite !assoc ;
         etrans ;
         [ apply maponpaths_2 ;
           apply BinProductPr2Commutes
         | ] ;
         rewrite !assoc' ;
         rewrite PullbackSqrCommutes ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply TerminalArrowEq).
  Defined.

  Proposition topos_tripos_compr
              {Γ A : ty EE}
              (φ : form (A ×h Γ))
    : {{ φ }} = {{ φ [ (⟨ π₂ (tm_var _) , π₁ (tm_var _) ⟩)%hd ] }}%topos.
  Proof.
    unfold hyperdoctrine_pr1, hyperdoctrine_pr2, tm_var.
    rewrite !id_left.
    apply idpath.
  Qed.

  Proposition topos_tripos_in
              {Γ A : ty EE}
              (t₁ : tm Γ A)
              (t₂ : tm Γ (ℙ A))
    : (t₁ ∈ t₂)%topos = (tripos_in A) [ ⟨ t₁ , t₂ ⟩ ].
  Proof.
    cbn.
    unfold topos_logic_subst, topos_in.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    rewrite topos_pair_comp.
    etrans.
    {
      apply maponpaths.
      apply BinProductPr1Commutes.
    }
    apply maponpaths_2.
    apply BinProductPr2Commutes.
  Qed.

  Proposition topos_tripos_compr_eq_pointwise
              {Γ A : ty EE}
              {Δ : form Γ}
              {x₁ x₂ : form (A ×h Γ)}
              (p : Δ [ π₂ (tm_var _) ] ⊢ x₁ ≡ x₂)
    : Δ ⊢ {{ x₁ }} ≡ {{ x₂ }}.
  Proof.
    rewrite topos_logic_hyperdoctrine_eq in p.
    rewrite topos_logic_hyperdoctrine_eq.
    use topos_logic_refl_from_eq.
    apply topos_logic_refl_to_eq_ctx in p.
    cbn in p ; cbn.
    use topos_lam_funext.
    rewrite !topos_prod_ar_comp_l_id_r.
    rewrite !assoc'.
    unfold topos_compr.
    rewrite !topos_lam_beta.
    rewrite !assoc.
    rewrite topos_pair_comp.
    rewrite topos_prod_ar_pr1, topos_prod_ar_pr2.
    rewrite !id_right.
    refine (_ @ maponpaths (λ z, topos_tripos_compr_eq_pointwise_mor _ _ _ · z) p @ _).
    - unfold topos_tripos_compr_eq_pointwise_mor.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    - unfold topos_tripos_compr_eq_pointwise_mor.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
  Qed.

  Proposition topos_tripos_compr_eq
              {Γ A : ty EE}
              {Δ : form Γ}
              {x₁ x₂ : tm Γ (ℙ A)}
              (p : Δ ⊢ ∀h ((π₂ (tm_var _) ∈ x₁ [ π₁ (tm_var _) ]tm)
                           ⇔
                           (π₂ (tm_var _) ∈ x₂ [ π₁ (tm_var _) ]tm)))
    : Δ ⊢ x₁ ≡ x₂.
  Proof.
    rewrite (topos_comp_eta x₁), (topos_comp_eta x₂).
    refine (hyperdoctrine_cut
              (topos_tripos_compr_eq_pointwise
                 (Δ := Δ)
                 (x₁ := π₁ (tm_var _) ∈ x₁ [ π₂ (tm_var _) ]tm)
                 (x₂ := π₁ (tm_var _) ∈ x₂ [ π₂ (tm_var _) ]tm)
                 _)
              _).
    - refine (hyperdoctrine_cut
                (hyperdoctrine_proof_subst _ p)
                _).
      simplify.
      refine (hyperdoctrine_cut
                (forall_elim (hyperdoctrine_hyp _) (π₁ (tm_var _)))
                _).
      simplify.
      use topos_tripos_prop_ext.
      + refine (impl_elim _ _).
        {
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + refine (impl_elim _ _).
        {
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
    - rewrite !topos_tripos_compr.
      rewrite !tripos_in_subst.
      simplify.
      rewrite !topos_tripos_in.
      unfold hyperdoctrine_pr1, hyperdoctrine_pr2, tm_var.
      rewrite !id_left.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition topos_tripos_compr_in
              {Γ A : ty EE}
              (φ : form (A ×h Γ))
              (t : tm Γ A)
    : t ∈ {{ φ }} = φ [ ⟨ t , tm_var _ ⟩ ].
  Proof.
    cbn.
    etrans.
    {
      apply topos_in_subst.
    }
    etrans.
    {
      apply maponpaths.
      apply BinProductPr2Commutes.
    }
    rewrite topos_in_compr.
    rewrite !assoc.
    rewrite topos_pair_comp.
    rewrite !topos_pair_pr1, !topos_pair_pr2.
    unfold topos_logic_subst.
    do 2 apply maponpaths_2.
    apply BinProductPr1Commutes.
  Qed.

  Proposition topos_tripos_compr_subst
              {Γ₁ Γ₂ A : ty EE}
              (φ : form (A ×h Γ₂))
              (s : tm Γ₁ Γ₂)
              (a := π₁ (tm_var (A ×h Γ₁)))
              (γ := s [ π₂ (tm_var (A ×h Γ₁)) ]tm)
    : {{ φ }} [ s ]tm = {{ φ [ ⟨ a , γ ⟩ ] }}.
  Proof.
    unfold tm_subst.
    refine (topos_compr_subst _ _ @ _).
    cbn ; unfold topos_logic_subst.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    use topos_pair_eq.
    - rewrite !assoc'.
      rewrite topos_pair_pr1.
      rewrite topos_pair_pr2.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply BinProductPr1Commutes.
      }
      unfold a, hyperdoctrine_pr1, tm_var.
      rewrite id_left.
      apply BinProductPr1Commutes.
    - rewrite !assoc'.
      rewrite topos_pair_pr2.
      rewrite topos_pair_pr1.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply BinProductPr2Commutes.
      }
      unfold γ, hyperdoctrine_pr2, tm_var, tm_subst.
      rewrite id_left.
      rewrite !assoc.
      apply maponpaths_2.
      apply BinProductPr2Commutes.
  Qed.

  Proposition eq_comprehension_term_topos
              {Γ A : ty EE}
              {φ : form A}
              {t₁ t₂ : tm Γ (formula_comprehension topos_logic_comprehension_hd φ)}
              {Δ : form Γ}
              (p : Δ ⊢ (formula_inclusion topos_logic_comprehension_hd φ) [ t₁ ]tm
                       ≡
                       (formula_inclusion topos_logic_comprehension_hd φ) [ t₂ ]tm)
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    refine (hyperdoctrine_cut p _) ; clear p.
    rewrite !topos_logic_hyperdoctrine_eq.
    use topos_logic_refl_from_eq.
    use (eq_comprehension_term topos_logic_comprehension_hd).
    use (cancel_z_iso' (z_iso_inv (topos_logic_eq_pullback _ _))).
    unfold tm_subst ; cbn.
    rewrite !assoc.
    unfold topos_logic_eq_to_pb.
    rewrite !PullbackArrow_PullbackPr1 ; cbn.
    rewrite !assoc'.
    apply EqualizerEqAr.
  Qed.
End ToposLogic.
