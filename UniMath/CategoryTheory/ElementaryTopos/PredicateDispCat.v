(**

 Predicates in an elementary topos

 To interpret higher-order logic in an elementary topos, we first define a displayed category
 of predicates. If `Γ` is an object in a topos `E`, then a predicate in context `Γ` is the
 same as a morphism `φ : Γ --> Ω` where `Ω` is the subobject classifier in `E`. To define
 morphisms between predicates (i.e., the entailment relation), we use pullbacks in toposes.
 Specifically, every predicate `φ : Γ --> Ω` gives rise to a monomorphism into `Γ` by taking
 the pullback of `φ` and `true : T --> Ω` where `T` is the terminal object. If we have
 predicates `φ₁ : Γ₁ --> Ω` and `φ₂ : Γ₂ --> Ω` and a morphism `s : Γ₁ --> Γ₂`, then a morphism
 over `s` from `φ₁` to `φ₂` is a morphism between the associated pullbacks.

 We show that this displayed category is univalent and we equip it with a cleaving. In addition,
 we construct a comprehension functor. Specifically, we show that every predicate `φ : Γ --> Ω`
 gives rise to a monomorphism into `Γ`, and we show that this operation gives rise to a fully
 faithful functor.

 Contents
 1. The displayed category of predicates
 2. Notation of identity and composition
 3. This displayed category is univalent
 4. A cleaving for the displayed category
 5. The comprehension operation

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.ElementaryTopos.ToposOperations.

Local Open Scope cat.
Local Open Scope topos.

Section ToposLogic.
  Context (E : Topos).

  Let PB : Pullbacks E := Topos_Pullbacks E.

  (** * 1. The displayed category of predicates *)
  Definition topos_logic_disp_cat_ob_mor
    : disp_cat_ob_mor E.
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ, Γ --> Ω).
    - exact (λ Γ₁ Γ₂ φ₁ φ₂ s,
             ∑ (f : PB _ _ _ φ₁ (true Ω) --> PB _ _ _ φ₂ (true Ω)),
             f · PullbackPr1 _ = PullbackPr1 _ · s).
  Defined.

  Proposition topos_logic_disp_cat_id_comp
    : disp_cat_id_comp E topos_logic_disp_cat_ob_mor.
  Proof.
    split ; cbn.
    - intros Γ φ.
      simple refine (_ ,, _).
      + apply identity.
      + abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ φ₁ φ₂ φ₃ p₁ p₂.
      induction p₁ as [ f₁ p₁ ].
      induction p₂ as [ f₂ p₂ ].
      simple refine (_ ,, _).
      + exact (f₁ · f₂).
      + abstract
          (cbn ;
           rewrite !assoc' ;
           rewrite p₂ ;
           rewrite !assoc ;
           rewrite p₁ ;
           apply idpath).
  Defined.

  Definition topos_logic_disp_cat_data
    : disp_cat_data E.
  Proof.
    simple refine (_ ,, _).
    - exact topos_logic_disp_cat_ob_mor.
    - exact topos_logic_disp_cat_id_comp.
  Defined.

  Proposition topos_logic_disp_mor_eq
              {x y : E}
              {f : x --> y}
              {xx : topos_logic_disp_cat_data x}
              {yy : topos_logic_disp_cat_data y}
              (ff gg : xx -->[ f ] yy)
    : ff = gg.
  Proof.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ; [ | apply TerminalArrowEq ].
    exact (pr2 ff @ !(pr2 gg)).
  Qed.

  Proposition topos_logic_transportb
              {x y : E}
              {f g : x --> y}
              {xx : topos_logic_disp_cat_data x}
              {yy : topos_logic_disp_cat_data y}
              (ff : xx -->[ f ] yy)
              (p : g = f)
    : pr1 (transportb (λ z, _ -->[ z ] _) p ff) = pr1 ff.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition topos_logic_transportf
              {x y : E}
              {f g : x --> y}
              {xx : topos_logic_disp_cat_data x}
              {yy : topos_logic_disp_cat_data y}
              (ff : xx -->[ f ] yy)
              (p : f = g)
    : pr1 (transportf (λ z, _ -->[ z ] _) p ff) = pr1 ff.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition topos_logic_disp_cat_axioms
    : disp_cat_axioms E topos_logic_disp_cat_data.
  Proof.
    repeat split ; intros ; try apply topos_logic_disp_mor_eq.
    apply isaset_total2.
    - apply homset_property.
    - intro.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition topos_logic_disp_cat
    : disp_cat E.
  Proof.
    simple refine (_ ,, _).
    - exact topos_logic_disp_cat_data.
    - exact topos_logic_disp_cat_axioms.
  Defined.

  Proposition locally_propositional_topos_logic_disp_cat
    : locally_propositional topos_logic_disp_cat.
  Proof.
    intro ; intros.
    use invproofirrelevance.
    intros ? ?.
    apply topos_logic_disp_mor_eq.
  Qed.

  (** * 2. Notation of identity and composition *)

  (**
     From a logical point of view, morphisms from `φ` to `ψ` over the identity represent
     proofs that `ψ` holds under the assumption `φ`. The identity morphism represents the
     hypothesis rule, which says that `φ` assuming `φ`. Composition represents the cut rule.
   *)

  Notation "φ₁ ⊢ φ₂" := (mor_disp (D := topos_logic_disp_cat) φ₁ φ₂ (identity _)) (at level 100).

  Proposition topos_logic_hyp
              {Γ : E}
              (Δ : topos_logic_disp_cat Γ)
    : Δ ⊢ Δ.
  Proof.
    apply id_disp.
  Qed.

  Proposition topos_logic_cut
              {Γ : E}
              {Δ₁ Δ₂ Δ₃ : topos_logic_disp_cat Γ}
              (p : Δ₁ ⊢ Δ₂)
              (q : Δ₂ ⊢ Δ₃)
    : Δ₁ ⊢ Δ₃.
  Proof.
    exact (compose (C := fiber_category topos_logic_disp_cat Γ) p q).
  Qed.

  (** * 3. This displayed category is univalent *)
  Section Isos.
    Context {Γ : E}
            (φ₁ φ₂ : topos_logic_disp_cat Γ).

    Definition z_iso_disp_to_z_iso_topos_logic
               (f : z_iso_disp (identity_z_iso Γ) φ₁ φ₂)
      : ∑ (g : z_iso (PB _ _ _ φ₁ (true' Ω)) (PB Ω _ _ _ (true' Ω))),
        g · PullbackPr1 (PB _ _ _ φ₂ (true' Ω))
        =
        PullbackPr1 (PB _ _ _ φ₁ (true' Ω)) · identity Γ.
    Proof.
      simple refine (_ ,, _).
      - use make_z_iso.
        + exact (pr11 f).
        + exact (pr1 (inv_mor_disp_from_z_iso f)).
        + split.
          * abstract
              (refine (maponpaths pr1 (inv_mor_after_z_iso_disp f) @ _) ;
               exact (topos_logic_transportb _ _)).
          * abstract
              (refine (maponpaths pr1 (z_iso_disp_after_inv_mor f) @ _) ;
               exact (topos_logic_transportb _ _)).
      - apply (pr21 f).
    Defined.

    Definition z_iso_z_iso_disp_topos_logic
               (g : z_iso (PB _ _ _ φ₁ (true' Ω)) (PB _ _ _ φ₂ (true' Ω)))
               (p : g · PullbackPr1 (PB _ _ _ φ₂ (true' Ω))
                    =
                    PullbackPr1 (PB _ _ _ φ₁ (true' Ω)) · identity Γ)
      : z_iso_disp (identity_z_iso Γ) φ₁ φ₂.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact (pr1 g ,, p).
      - refine (inv_from_z_iso g ,, _).
        abstract
          (use z_iso_inv_on_left ;
           rewrite !assoc' ;
           refine (!_) ;
           use z_iso_inv_on_right ;
           exact (!p)).
      - apply topos_logic_disp_mor_eq.
      - apply topos_logic_disp_mor_eq.
    Defined.

    Definition topos_logic_z_iso_disp_weq
      : z_iso_disp (identity_z_iso Γ) φ₁ φ₂
        ≃
        ∑ (g : z_iso (PB _ _ _ φ₁ (true' Ω)) (PB _ _ _ φ₂ (true' Ω))),
        g · PullbackPr1 (PB _ _ _ φ₂ (true' Ω))
        =
        PullbackPr1 (PB _ _ _ φ₁ (true' Ω)) · identity Γ.
    Proof.
      use weq_iso.
      - exact z_iso_disp_to_z_iso_topos_logic.
      - exact (λ gp, z_iso_z_iso_disp_topos_logic (pr1 gp) (pr2 gp)).
      - abstract
          (intro f ;
           use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
           apply idpath).
      - abstract
          (intro f ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           use z_iso_eq ;
           apply idpath).
    Defined.
  End Isos.

  Proposition is_univalent_disp_topos_logic_disp_cat
    : is_univalent_disp topos_logic_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros Γ φ₁ φ₂.
    use isweqimplimpl.
    - intros f.
      use subobject_classifier_map_eq.
      + exact (PB _ _ _ φ₁ (true' Ω)).
      + use make_Monic.
        * apply PullbackPr1.
        * abstract
            (apply (MonicPullbackisMonic' _ _ (true _))).
      + abstract
          (cbn ;
           refine (PullbackSqrCommutes (PB _ _ _ φ₁ (true' Ω)) @ _) ;
           unfold const_true ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
      + abstract
          (cbn ;
           pose (pr21 f) as p ; cbn in p ;
           rewrite id_right in p ;
           rewrite <- p ;
           rewrite !assoc' ;
           rewrite PullbackSqrCommutes ;
           unfold const_true ; cbn ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
      + intros w h k p.
        use iscontraprop1.
        * abstract
            (use invproofirrelevance ;
             intros ψ₁ ψ₂ ;
             use subtypePath ;
             [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use (MorphismsIntoPullbackEqual (isPullback_Pullback _))
             ; [ | apply TerminalArrowEq ] ;
             exact (pr12 ψ₁ @ !(pr12 ψ₂))).
        * simple refine (_ ,, _ ,, _).
          ** exact (PullbackArrow _ _ h k p).
          ** abstract
              (cbn ;
               apply PullbackArrow_PullbackPr1).
          ** abstract
              (cbn ;
               apply TerminalArrowEq).
      + intros w h k p.
        use iscontraprop1.
        * abstract
            (use invproofirrelevance ;
             intros ψ₁ ψ₂ ;
             use subtypePath ;
             [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use (MorphismsIntoPullbackEqual (isPullback_Pullback _))
             ; [ | apply TerminalArrowEq ] ;
             exact (pr12 ψ₁ @ !(pr12 ψ₂))).
        * simple refine (_ ,, _ ,, _).
          ** exact (PullbackArrow _ _ h k p · pr112 f).
          ** abstract
              (cbn ;
               rewrite !assoc' ;
               refine (maponpaths (λ z, _ · z) (pr212 f) @ _) ;
               cbn ;
               rewrite id_right ;
               apply PullbackArrow_PullbackPr1).
          ** abstract
              (cbn ;
               apply TerminalArrowEq).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply topos_logic_disp_mor_eq.
  Qed.

  Proposition topos_logic_prop_ext
              {Γ : E}
              {φ ψ : topos_logic_disp_cat Γ}
              (p : φ ⊢ ψ)
              (q : ψ ⊢ φ)
    : φ = ψ.
  Proof.
    use (isotoid _ (is_univalent_fiber _ _ (is_univalent_disp_topos_logic_disp_cat))).
    use make_z_iso.
    - apply p.
    - apply q.
    - split ; apply topos_logic_disp_mor_eq.
  Defined.

  (** * 4. A cleaving for the displayed category *)
  Section Cleaving.
    Context {Γ₁ Γ₂ : E}
            (s : Γ₁ --> Γ₂)
            (φ : topos_logic_disp_cat Γ₂).

    Definition topos_logic_subst
      : topos_logic_disp_cat Γ₁
      := s · φ.

    Definition topos_logic_subst_mor
      : topos_logic_subst -->[ s ] φ.
    Proof.
      simple refine (_ ,, _).
      - use PullbackArrow.
        + exact (PullbackPr1 _ · s).
        + apply PullbackPr2.
        + abstract
            (rewrite !assoc' ;
             apply PullbackSqrCommutes).
      - abstract
          (apply PullbackArrow_PullbackPr1).
    Defined.

    Proposition is_cartesian_topos_logic_subst_mor
      : is_cartesian topos_logic_subst_mor.
    Proof.
      intros w f Q q.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
           [ | apply TerminalArrowEq ] ;
           exact (pr21 φ₁ @ !(pr21 φ₂))).
      - simple refine ((_ ,, _) ,, _) ; cbn.
        + use PullbackArrow.
          * exact (PullbackPr1 _ · f).
          * exact (PullbackPr2 _).
          * abstract
              (unfold topos_logic_subst ;
               rewrite !assoc ;
               rewrite !(maponpaths (λ z, z · _) (assoc' _ _ _)) ;
               pose proof (pr2 q) as p ; cbn in p ;
               rewrite <- p ;
               rewrite !assoc' ;
               rewrite !PullbackSqrCommutes ;
               rewrite !assoc ;
               apply maponpaths_2 ;
               apply TerminalArrowEq).
        + abstract
            (apply PullbackArrow_PullbackPr1).
        + abstract
            (apply topos_logic_disp_mor_eq).
    Defined.
  End Cleaving.

  Arguments topos_logic_subst /.
  Notation "φ '[[' s ']]'" := (topos_logic_subst s φ).

  Definition topos_logic_cleaving
    : cleaving topos_logic_disp_cat.
  Proof.
    intros x y s P.
    simple refine (_ ,, _).
    - exact (P [[ s ]]).
    - simple refine (_ ,, _).
      + exact (topos_logic_subst_mor s P).
      + exact (is_cartesian_topos_logic_subst_mor s P).
  Defined.

  Proposition topos_in_subst
              {x z₁ z₂ : E}
              (s : z₁ --> z₂)
              (t : z₂ --> x)
              (φ : z₂ --> ℙ x)
    : (t ∈ φ) [[ s ]] = (s · t ∈ s · φ).
  Proof.
    simpl ; unfold topos_in.
    rewrite !assoc.
    rewrite topos_pair_comp.
    apply idpath.
  Qed.

  Proposition topos_logic_subst_proof
              {Γ₁ Γ₂ : E}
              (s : Γ₁ --> Γ₂)
              {Δ φ : topos_logic_disp_cat Γ₂}
              (p : Δ ⊢ φ)
    : Δ [[ s ]] ⊢ φ [[ s ]].
  Proof.
    exact (#(fiber_functor_from_cleaving _ topos_logic_cleaving s) p).
  Qed.

  Proposition topos_logic_subst_id
              {Γ : E}
              (φ : topos_logic_disp_cat Γ)
    : φ [[ identity _ ]] = φ.
  Proof.
    refine (!_).
    use (isotoid_disp is_univalent_disp_topos_logic_disp_cat (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    exact (_ ,, is_nat_z_iso_fiber_functor_from_cleaving_identity topos_logic_cleaving Γ φ).
  Qed.

  Proposition topos_logic_subst_comp
              {Γ₁ Γ₂ Γ₃ : E}
              (s₁ : Γ₁ --> Γ₂)
              (s₂ : Γ₂ --> Γ₃)
              (φ : topos_logic_disp_cat Γ₃)
    : φ [[ s₂ ]] [[ s₁ ]] = φ [[ s₁ · s₂ ]].
  Proof.
    use (isotoid_disp is_univalent_disp_topos_logic_disp_cat (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    exact (nat_z_iso_pointwise_z_iso
             (fiber_functor_from_cleaving_comp_nat_z_iso topos_logic_cleaving s₂ s₁)
             φ).
  Qed.

  (** * 5. The comprehension operation *)
  Definition topos_logic_to_mono
             {Γ : E}
             (φ : topos_logic_disp_cat Γ)
    : E /m Γ.
  Proof.
    use make_mono_cod_fib_ob.
    - exact (PB _ _ _ φ (true _)).
    - use make_Monic.
      + apply PullbackPr1.
      + abstract
          (apply (MonicPullbackisMonic' _ _ (true _))).
  Defined.

  Definition topos_logic_compr
             {Γ : E}
             (φ : topos_logic_disp_cat Γ)
    : E
    := mono_cod_dom (topos_logic_to_mono φ).

  Definition topos_logic_compr_mono
             {Γ : E}
             (φ : topos_logic_disp_cat Γ)
    : Monic _ (topos_logic_compr φ) Γ
    := mono_cod_mor (topos_logic_to_mono φ).

  Definition topos_logic_comprehension_data
    : disp_functor_data
        (functor_identity _)
        topos_logic_disp_cat
        (disp_mono_codomain E).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ φ, topos_logic_to_mono φ).
    - intros Γ₁ Γ₂ φ₁ φ₂ f q ; simpl.
      simple refine ((_ ,, _) ,, tt).
      + exact (pr1 q).
      + exact (pr2 q).
  Defined.

  Proposition topos_logic_comprehension_axioms
    : disp_functor_axioms topos_logic_comprehension_data.
  Proof.
    split ;
      intro ; intros ;
      apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Definition topos_logic_comprehension
    : disp_functor
        (functor_identity _)
        topos_logic_disp_cat
        (disp_mono_codomain E).
  Proof.
    simple refine (_ ,, _).
    - exact topos_logic_comprehension_data.
    - exact topos_logic_comprehension_axioms.
  Defined.

  Proposition topos_logic_comprehension_ff
    : disp_functor_ff topos_logic_comprehension.
  Proof.
    intros Γ₁ Γ₂ φ₁ φ₂ s.
    use isweqimplimpl.
    - exact (λ f, pr1 f).
    - apply locally_propositional_topos_logic_disp_cat.
    - apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Proposition is_cartesian_topos_logic_comprehension
    : is_cartesian_disp_functor topos_logic_comprehension.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact topos_logic_cleaving.
    }
    intros Γ₁ Γ₂ s φ.
    use isPullback_cartesian_in_mono_cod_disp.
    intros Γ₀ h k p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros ψ₁ ψ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
         [ | apply TerminalArrowEq ] ;
         exact (pr22 ψ₁ @ !(pr22 ψ₂))).
    - simple refine (_ ,, _ ,, _).
      + use PullbackArrow.
        * exact k.
        * apply TerminalArrow.
        * abstract
            (cbn ; cbn in p ;
             rewrite !assoc ;
             rewrite <- p ;
             rewrite !assoc' ;
             rewrite PullbackSqrCommutes ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply TerminalArrowEq).
      + abstract
          (use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ;
           [ | apply TerminalArrowEq ] ;
           simpl ;
           rewrite !assoc' ;
           rewrite PullbackArrow_PullbackPr1 ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr1 ;
           exact (!p)).
      + abstract
          (simpl ;
           rewrite PullbackArrow_PullbackPr1 ;
           apply idpath).
  Defined.
End ToposLogic.
