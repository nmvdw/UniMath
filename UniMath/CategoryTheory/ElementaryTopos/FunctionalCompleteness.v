(**

 Functional completeness in toposes

 Every topos gives rise to a first-order hyperdoctrine. This hyperdoctrine is well-behaved
 in many different ways, and one nice feature of it is that it is functionally complete.
 This allows us to define moprhisms in a topos using the internal logic. Specifically, if
 we givea formula and if we prove that it is a functional relation, then we can find a
 morphism whose behavior is specified by that formula. We can view functional completeness
 as some kind of axiom of unique choice.

 Our proof of fucntional completeness is based on the book "Introduction to higher order
 categorical logic" by Lambek and Scott. The main idea is that we first prove another
 statement, namely a lifting statement along monomorphisms [topos_monic_lift]. Next we
 show that map assinging to each`x` the singleton set just containing `x` is a monomorphism,
 and then we can use the aforementioned lifting statement to get the desired map.

 References
 - "Introduction to higher order categorical logic" by Lambek and Scott

 Contents
 1. Monics to formulas
 2. Lifts along monomorphisms
 3. Singleton sets
 4. Functional completeness

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Properties.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.ElementaryTopos.ToposOperations.
Require Import UniMath.CategoryTheory.ElementaryTopos.PredicateDispCat.
Require Import UniMath.CategoryTheory.ElementaryTopos.ToposLogic.

Local Open Scope cat.
Local Open Scope hd.

Section FunctionallyComplete.
  Context (E : Topos).

  Let EE : tripos := topos_logic_tripos E.

  (** * 1. Monics to formulas *)
  Definition topos_monic_form
             {A B : ty EE}
             (m : Monic _ A B)
    : form B
    := characteristic_morphism Ω%topos m.

  Proposition topos_monic_form_prf
              {A B : ty EE}
              (m : Monic _ A B)
    : (topos_monic_form m) [ pr1 m ] = ⊤.
  Proof.
    cbn ; unfold topos_logic_subst.
    apply subobject_classifier_square_commutes.
  Qed.

  Proposition topos_monic_lift_prf
              {A B C : ty EE}
              (f : A --> C)
              (g : B --> C)
              (Hg : isMonic g)
              (p : ⊤ ⊢ ∀h ∃h (f [ π₂ (π₁ (tm_var ((𝟙 ×h A) ×h B))) ]tm ≡ g [ π₂ (tm_var _) ]tm))
              (m := make_Monic _ g Hg)
    : ⊤ ⊢ (topos_monic_form m) [ f [ π₂ (tm_var (𝟙 ×h A)) ]tm ]
          ≡
          (⊤ :form (𝟙 ×h A)).
  Proof.
    rewrite (topos_logic_hyperdoctrine_eq E).
    apply topos_logic_to_eq_truth.
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_cut (hyperdoctrine_proof_subst !! p) _)).
    {
      simplify.
      apply truth_intro.
    }
    simplify.
    refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) (π₂ (tm_var _))) _).
    simplify.
    refine (exists_elim (hyperdoctrine_hyp _) _).
    simplify.
    use weaken_right.
    refine (hyperdoctrine_eq_transportf _ _ _).
    {
      use hyperdoctrine_eq_sym.
      apply hyperdoctrine_hyp.
    }
    rewrite <- hyperdoctrine_comp_subst.
    rewrite topos_monic_form_prf.
    simplify.
    apply truth_intro.
  Qed.

  (** * 2. Lifts along monomorphisms *)
  Definition topos_monic_lift
             {A B C : ty EE}
             (f : A --> C)
             (g : B --> C)
             (Hg : isMonic g)
             (p : ⊤ ⊢ ∀h ∃h (f [ π₂ (π₁ (tm_var ((𝟙 ×h A) ×h B))) ]tm ≡ g [ π₂ (tm_var _) ]tm))
    : ∑ (h : A --> B), f = h · g.
  Proof.
    pose (m := make_Monic _ g Hg).
    simple refine (_ ,, _).
    - use (PullbackArrow (subobject_classifier_pullback Ω%topos m)).
      + exact f.
      + apply TerminalArrow.
      + abstract
          (use topos_logic_extensionality ;
           use forall_intro ;
           simplify ;
           refine (hyperdoctrine_cut (topos_monic_lift_prf f g Hg p) _) ;
           unfold topos_monic_form ;
           rewrite <- hyperdoctrine_comp_subst ;
           cbn -[topos_logic_disp_cat topos_logic] ;
           unfold tm_subst ;
           refine (hyperdoctrine_eq_trans (hyperdoctrine_hyp _) _) ;
           use hyperdoctrine_refl_eq ;
           cbn ;
           unfold topos_logic_truth_form, const_true ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply TerminalArrowEq).
    - abstract
        (simpl ;
         refine (!_) ;
         apply (PullbackArrow_PullbackPr1 (subobject_classifier_pullback Ω%topos m))).
  Defined.

  (** * 3. Singleton sets *)
  Definition singleton_set
             {Γ A : ty EE}
             (a : tm Γ A)
    : tm Γ (ℙ A)
    := {{ a [ π₂ (tm_var _) ]tm ≡ π₁ (tm_var _) }}.

  Proposition isMonic_singleton_set
              (A : ty EE)
    : ⊤ ⊢ isInjective_hyperdoctrine (singleton_set (tm_var A)).
  Proof.
    unfold isInjective_hyperdoctrine.
    do 2 use forall_intro.
    use impl_intro.
    unfold singleton_set.
    rewrite !(topos_tripos_compr_subst E).
    simplify.
    pose (Γ := A ×h (𝟙 ×h A) ×h A).
    pose (x := π₂ (π₁ (π₂ (tm_var Γ)))).
    pose (y := π₂ (π₂ (tm_var Γ))).
    pose (z := π₁ (tm_var Γ)).
    unfold Γ in x, y, z.
    fold x y z.
    use weaken_right.
    refine (hyperdoctrine_cut _ _).
    {
      use (hyperdoctrine_eq_elim _ (hyperdoctrine_hyp _)).
      {
        exact (π₂ (π₁ (π₁ (tm_var _))) ∈ π₂ (tm_var _)).
      }
      simplify.
      rewrite (topos_tripos_compr_in E).
      unfold x, y, z.
      simplify.
      apply hyperdoctrine_refl.
    }
    simplify.
    rewrite (topos_tripos_compr_in E).
    unfold y, z.
    simplify.
    use hyperdoctrine_eq_sym.
    apply hyperdoctrine_hyp.
  Qed.

  (** * 4. Functional completeness *)
  Definition functional_relation_to_power
             {A B : ty EE}
             (φ : form (A ×h B))
             (p : ⊤ ⊢ functional_relation φ)
    : tm A (ℙ B)
    := {{ φ [ ⟨ π₂ (tm_var (B ×h A)) , π₁ (tm_var (B ×h A)) ⟩ ] }}.

  Proposition functional_relation_to_power_ims
              {A B : ty EE}
              (φ : form (A ×h B))
              (p : ⊤ ⊢ functional_relation φ)
    : (⊤ ⊢ ∀h ∃h ((functional_relation_to_power φ p) [ π₂ (π₁ (tm_var ((𝟙 ×h A) ×h B))) ]tm
                  ≡
                  singleton_set (π₂ (tm_var _)))).
  Proof.
    use forall_intro.
    simplify.
    refine (hyperdoctrine_cut
              (functional_relation_im φ p ⊤ (π₂ (tm_var (𝟙 ×h A))))
              _).
    refine (exists_elim (hyperdoctrine_hyp _) _).
    use weaken_right.
    simplify.
    use exists_intro.
    {
      exact (π₂ (tm_var _)).
    }
    unfold singleton_set, functional_relation_to_power.
    simplify.
    use hyperdoctrine_eq_sym.
    rewrite !(topos_tripos_compr_subst E).
    simplify.
    use topos_tripos_compr_eq.
    use forall_intro.
    simplify.
    rewrite !topos_tripos_compr_subst.
    rewrite !topos_tripos_compr_in.
    simplify.
    pose (Γ := ((𝟙 ×h A) ×h B) ×h B).
    pose (a := π₂ (π₁ (π₁ (tm_var Γ)))).
    pose (b₁ := π₂ (π₁ (tm_var Γ))).
    pose (b₂ := π₂ (tm_var Γ)).
    unfold Γ in a, b₁, b₂ ; clear Γ.
    fold a b₁ b₂.
    use conj_intro ; use impl_intro.
    - refine (hyperdoctrine_cut
                (hyperdoctrine_eq_elim
                   (φ [ ⟨ π₂ (π₁ (π₁ (π₁ (tm_var _)))) , π₂ (tm_var _) ⟩ ])
                   _
                   _)
                _).
      + use weaken_right.
        apply hyperdoctrine_hyp.
      + simplify.
        fold a.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + simplify.
        fold a b₂.
        apply hyperdoctrine_hyp.
    - use (functional_relation_unique_im φ p).
      + exact a.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition topos_logic_functional_completeness
    : first_order_hyperdoctrine_functional_completeness EE.
  Proof.
    intros A B φ p.
    assert (H₁ : isMonic (singleton_set (tm_var B))).
    {
      apply isMonic_extensional_first_order_hyperdoctrine.
      {
        apply topos_logic_extensionality.
      }
      exact (isMonic_singleton_set B).
    }
    assert (⊤ ⊢ ∀h (∃h ((functional_relation_to_power φ p)
                          [ π₂ (π₁ (tm_var ((𝟙 ×h A) ×h B))) ]tm
                        ≡
                        (singleton_set (tm_var B))
                          [ π₂ (tm_var ((𝟙 ×h A) ×h B)) ]tm)))
      as H₂.
    {
      refine (hyperdoctrine_cut (functional_relation_to_power_ims φ p) _).
      unfold singleton_set.
      rewrite !(topos_tripos_compr_subst E).
      simplify.
      apply hyperdoctrine_hyp.
    }
    pose (topos_monic_lift
            (functional_relation_to_power φ p)
            (singleton_set (tm_var B))
            H₁
            H₂)
      as tH.
    induction tH as [ t H ].
    refine (t ,, _).
    assert (⊤ ⊢ functional_relation_to_power φ p ≡ (singleton_set (tm_var B)) [ t ]tm) as r.
    {
      use hyperdoctrine_refl_eq.
      exact H.
    }
    use forall_intro.
    simplify.
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_cut (hyperdoctrine_proof_subst (π₂ (tm_var _)) r) _)).
    {
      simplify.
      apply truth_intro.
    }
    unfold singleton_set, functional_relation_to_power.
    simplify.
    rewrite !(topos_tripos_compr_subst E).
    simplify.
    refine (hyperdoctrine_cut _ _).
    {
      use (hyperdoctrine_eq_elim _ (hyperdoctrine_eq_sym (hyperdoctrine_hyp _))).
      {
        exact (t [ π₂ (π₁ (tm_var _)) ]tm ∈ π₂ (tm_var _)).
      }
      simplify.
      rewrite (topos_tripos_compr_in E).
      simplify.
      apply hyperdoctrine_refl.
    }
    simplify.
    rewrite (topos_tripos_compr_in E).
    simplify.
    apply hyperdoctrine_hyp.
  Qed.
End FunctionallyComplete.
