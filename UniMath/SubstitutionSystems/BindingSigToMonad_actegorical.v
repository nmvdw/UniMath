(** a follow-up of [BindingSigToMonad], where the semantic signatures [Signature] are replaced by functors with tensorial strength

    the concept of binding signatures is inherited, as well as the reasoning about omega-cocontinuity
    the strength notion is the one of generalized heterogeneous substitution systems (GHSS), and accordingly a GHSS
    is constructed and a monad obtained through it

author: Ralph Matthes, 2023
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.coslicecat.


Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.

Require Import UniMath.CategoryTheory.MonoidalOld.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.MonoidalOld.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.MonoidalOld.Actegories.
Require Import UniMath.CategoryTheory.MonoidalOld.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.MonoidalOld.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.MonoidalOld.ConstructionOfActegoryMorphisms.
Require Import UniMath.CategoryTheory.MonoidalOld.CoproductsInActegories.
Require Import UniMath.CategoryTheory.MonoidalOld.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.MonoidalOld.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.MonoidalOld.Examples.EndofunctorsWhiskeredMonoidalElementary.
Require Import UniMath.CategoryTheory.MonoidalOld.Examples.MonadsAsMonoidsWhiskeredElementary.

Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.ConstructionOfGHSS.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.

Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Local Open Scope cat.

Import MonoidalNotations.

Local Notation "[ C , D ]" := (functor_category C D).
Local Notation "'chain'" := (diagram nat_graph).

Section FixACategory.

  Context {C : category}.

  Local Definition endoCAT : category := [C, C].
  Local Definition Mon_endo_CAT : monoidal endoCAT := monendocat_monoidal C.
  Local Definition ptdendo_CAT : category := coslice_cat_total endoCAT I_{Mon_endo_CAT}.
  Local Definition Mon_ptdendo_CAT : monoidal ptdendo_CAT := monoidal_pointed_objects Mon_endo_CAT.


  Local Definition precomp_omegacocont_CAT  (CLC : Colims_of_shape nat_graph C) (F : endoCAT) :
    is_omega_cocont (leftwhiskering_functor Mon_endo_CAT F).
  Proof.
    apply is_omega_cocont_pre_composition_functor, CLC.
  Defined.

  Local Definition ptdtensorialstrength_CAT := pointedtensorialstrength Mon_endo_CAT.

  Local Definition coprod_distributor_CAT {I : UU} (CP : Coproducts I C) :
    actegory_coprod_distributor Mon_endo_CAT (Coproducts_functor_precat I C C CP)
      (actegory_with_canonical_self_action Mon_endo_CAT).
  Proof.
    use tpair.
    - intro F. apply precomp_coprod_distributor_data.
    - intro F. apply precomp_coprod_distributor_law.
  Defined.

  Local Definition coprod_distributor_pointed_CAT {I : UU} (CP : Coproducts I C) :
    actegory_coprod_distributor Mon_ptdendo_CAT (Coproducts_functor_precat I C C CP)
      (actegory_with_canonical_pointed_action Mon_endo_CAT).
  Proof.
    apply lifted_coprod_distributor.
    apply coprod_distributor_CAT.
  Defined.

  Local Definition bincoprod_distributor_CAT (BCP : BinCoproducts C) :
    actegory_bincoprod_distributor Mon_endo_CAT (BinCoproducts_functor_precat C C BCP)
      (actegory_with_canonical_self_action Mon_endo_CAT).
  Proof.
    use tpair.
    - intro F. apply precomp_bincoprod_distributor_data.
    - intro F. apply precomp_bincoprod_distributor_law.
  Defined.

  Local Definition bincoprod_distributor_pointed_CAT (BCP : BinCoproducts C) :
    actegory_bincoprod_distributor Mon_ptdendo_CAT (BinCoproducts_functor_precat C C BCP)
      (actegory_with_canonical_pointed_action Mon_endo_CAT).
  Proof.
    apply lifted_bincoprod_distributor.
    apply bincoprod_distributor_CAT.
  Defined.

  Local Definition ptdlifteddistributivity_CAT (G : functor C C) :=
    lifteddistributivity Mon_endo_CAT Mon_ptdendo_CAT (forget_monoidal_pointed_objects_monoidal Mon_endo_CAT) G.
  Local Definition ptdlifteddistributivity_CAT_data (G : functor C C) :=
    lifteddistributivity_data Mon_endo_CAT (F:=pr1_category (coslice_cat_disp endoCAT I_{Mon_endo_CAT})) G.

  Section ConstConst.

    Context (c : C).

    Local Definition ConstConst : functor [C, C] [C, C] := constant_functor endoCAT endoCAT (constant_functor C C c).

    Definition ConstConst_strengthCAT : ptdtensorialstrength_CAT ConstConst.
    Proof.
      use tpair.
      - intros Ze c'. cbn.
        apply nat_trans_id.
      - abstract (split4; (intro; intros; apply (nat_trans_eq C); intro c');
                  try (apply idpath);
                  cbn; repeat rewrite id_right; apply idpath).
    Defined.

  End ConstConst.

  Section genopt.

    Context (a : C) (BC : BinCoproducts C).

  Local Definition genopt : endoCAT := constcoprod_functor1 BC a.

  Definition lifteddistr_genopt_data : ptdlifteddistributivity_CAT_data genopt.
  Proof.
    apply δ_genoption.
  Defined.

(* the data part of the previous item with an interactive definition, could be put upstream:
    intros Ze. use make_nat_trans.
    - intro c.
      use BinCoproductArrow.
      + refine (BinCoproductIn1 (BC a c) · _).
        apply (pr2 Ze).
      + apply (#(pr1 Ze: functor _ _)).
        apply BinCoproductIn2.
 *)

  Lemma lifteddistr_genopt_nat : lifteddistributivity_nat Mon_endo_CAT lifteddistr_genopt_data.
  Proof.
    intro Ze; induction Ze as [Z e]; intro Z'e'; induction Z'e' as [Z' e']; intro αX; induction αX as [α X]; simpl in *.
    apply nat_trans_eq; [apply homset_property |]; intro c; simpl.
    unfold BinCoproduct_of_functors_mor, BinCoproduct_of_functors_ob, δ_genoption_mor; simpl.
    rewrite precompWithBinCoproductArrow.
    rewrite postcompWithBinCoproductArrow.
    apply maponpaths_12.
    - rewrite id_left, assoc'.
      apply maponpaths.
      apply pathsinv0.
      rewrite <- X.
      apply idpath.
    - apply pathsinv0,  nat_trans_ax.
  Qed.

  Lemma lifteddistr_genopt_tensor : lifteddistributivity_tensor Mon_endo_CAT Mon_ptdendo_CAT
                                      (forget_monoidal_pointed_objects_monoidal Mon_endo_CAT) lifteddistr_genopt_data.
  Proof.
    intros Ze Z'e'; induction Ze as [Z e]; induction Z'e' as [Z' e'].
    apply nat_trans_eq_alt; intro c; simpl.
    unfold δ_genoption_mor, BinCoproduct_of_functors_ob, BinCoproduct_of_functors_mor; simpl.
    repeat rewrite id_right. rewrite id_left.
    rewrite precompWithBinCoproductArrow.
    rewrite postcompWithBinCoproductArrow.
    apply maponpaths_12.
    - rewrite id_left.
      cbn in Z, e, Z', e'.
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply (nat_trans_ax e'). }
      simpl.
      do 2 rewrite assoc.
      rewrite BinCoproductIn1Commutes.
      apply idpath.
    - rewrite id_left.
      etrans.
      2: { apply functor_comp. }
      apply pathsinv0, maponpaths, BinCoproductIn2Commutes.
  Qed.

  Lemma lifteddistr_genopt_unit : lifteddistributivity_unit Mon_endo_CAT Mon_ptdendo_CAT
                                    (forget_monoidal_pointed_objects_monoidal Mon_endo_CAT) lifteddistr_genopt_data.
  Proof.
    apply nat_trans_eq_alt; intro c; simpl.
    unfold δ_genoption_mor, BinCoproduct_of_functors_ob, BinCoproduct_of_functors_mor, BinCoproductOfArrows; simpl.
    repeat rewrite id_left.
    repeat rewrite id_right.
    apply idpath.
  Qed.

  Definition lifteddistr_genopt : ptdlifteddistributivity_CAT genopt.
  Proof.
    exists lifteddistr_genopt_data.
    split3.
    - exact lifteddistr_genopt_nat.
    - exact lifteddistr_genopt_tensor.
    - exact lifteddistr_genopt_unit.
  Defined.

  End genopt.

    (** Define δ for G = F^n *)
  Definition lifteddistr_iter_functor1 (G : functor C C) (δ : ptdlifteddistributivity_CAT G) (n: nat) :
    ptdlifteddistributivity_CAT (iter_functor1 _ G n).
  Proof.
    induction n as [|n IHn].
    - exact δ.
    - use composedlifteddistributivity.
      + apply IHn.
      + exact δ.
  Defined.

  Definition precomp_option_iter_strengthCAT (BCC : BinCoproducts C)
    (TC : Terminal C) (n : nat) : ptdtensorialstrength_CAT (precomp_option_iter BCC TC n).
  Proof.
    destruct n; simpl.
    - apply identity_lineator.
    - use liftedstrength_from_δ.
      refine (lifteddistr_iter_functor1 (option_functor BCC TC) (lifteddistr_genopt TC BCC) n).
  Defined.


(* From here on all constructions need these hypotheses *)
  Context (BPC : BinProducts C) (BCC : BinCoproducts C).

  Let BPC2 : BinProducts [C, C] := BinProducts_functor_precat C C BPC.
  Let BCC2 : BinCoproducts [C, C] := BinCoproducts_functor_precat C C BCC.

  (** [nat] to a Signature *)
  Definition Arity_to_functor (TC : Terminal C) (xs : list nat) : functor [C, C] [C, C].
  Proof.
    exact (foldr1 (BinProduct_of_functors _ _ BPC2)
             (constant_functor [C, C] [C, C] (constant_functor C C (TerminalObject TC)))
             (map (precomp_option_iter BCC TC) xs)).
  Defined.

  (** the functor is that previously found in the semantic signature - but not w.r.t. convertibility *)
  Lemma Arity_to_functor_agrees (TC : Terminal C) (xs : list nat) :
    Arity_to_functor TC xs = Signature_Functor (Arity_to_Signature BPC BCC TC xs).
  Proof.
    induction xs as [[|n] xs].
    - induction xs. apply idpath.
    - induction n as [|n IH].
      + induction xs as [m []]. apply idpath.
      + induction xs as [m [k xs]].
        assert (IHinst := IH (k,,xs)).
        change (S (S n),, m,, k,, xs) with (cons m (cons k (n,,xs))).
        unfold Arity_to_functor.
        do 2 rewrite map_cons.
        rewrite foldr1_cons.
        change (S n,, k,, xs) with (cons k (n,,xs)) in IHinst.
        etrans.
        { apply maponpaths.
          exact IHinst. }
        apply idpath.
  Defined.

  Definition Arity_to_strengthCAT (TC : Terminal C) (xs : list nat) : ptdtensorialstrength_CAT (Arity_to_functor TC xs).
  Proof.
    induction xs as [[|n] xs].
    - induction xs. cbn.
      exact (ConstConst_strengthCAT TC).
    - induction n as [|n IH].
      + induction xs as [m []]. cbn.
        exact (precomp_option_iter_strengthCAT BCC TC m).
      + induction xs as [m [k xs]].
        refine (lax_lineator_binprod _ _ _ (precomp_option_iter_strengthCAT BCC TC _) (IH (k,,xs)) _).
  Defined.

  Definition BindingSigToFunctor (TC : Terminal C)
    (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) : functor [C, C] [C, C].
  Proof.
    exact (coproduct_of_functors (BindingSigIndex sig) _ _ (Coproducts_functor_precat (BindingSigIndex sig) C C CC)
             (fun i => Arity_to_functor TC (BindingSigMap sig i))).
  Defined.

   (** the functor is that previously found in the semantic signature - but not w.r.t. convertibility *)
  Lemma BindingSigToFunctor_agrees (TC : Terminal C)
    (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
    BindingSigToFunctor TC sig CC = Signature_Functor (BindingSigToSignature BPC BCC TC sig CC).
  Proof.
    unfold BindingSigToFunctor, BindingSigToSignature.
    assert (aux : (λ i : BindingSigIndex sig, Arity_to_functor TC (BindingSigMap sig i)) =
                  (λ i : BindingSigIndex sig, Arity_to_Signature BPC BCC TC (BindingSigMap sig i))).
    { apply funextsec.
      intro i.
      apply Arity_to_functor_agrees. }
    rewrite aux.
    apply idpath.
  Qed.

  Let Id_H : [C, C] ⟶ [C, C] → [C, C] ⟶ [C, C] := Id_H C BCC.
  Let constprod_functor1 : [C, C] → [C, C] ⟶ [C, C] := constprod_functor1 BPC2.

  Lemma is_omega_cocont_BindingSigToFunctor
    (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
    (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
    (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
    is_omega_cocont (BindingSigToFunctor TC sig CC).
  Proof.
    rewrite BindingSigToFunctor_agrees.
    apply is_omega_cocont_BindingSigToSignature; assumption.
  Defined. (* notice that it depends on an opaque proof of equality of types *)

  Definition BindingSigToStrengthCAT (TC : Terminal C)
    (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C) :
    ptdtensorialstrength_CAT (BindingSigToFunctor TC sig CC).
  Proof.
    exact (lax_lineator_coprod _ _ _ (fun i => Arity_to_strengthCAT TC (BindingSigMap sig i))
              (Coproducts_functor_precat (BindingSigIndex sig) C C CC) (coprod_distributor_pointed_CAT CC)).
  Qed.

Section PuttingAllTogether.

    Context (IC : Initial C) (TC : Terminal C) (CLC : Colims_of_shape nat_graph C)
    (HF : ∏ (F : [C,C]), is_omega_cocont (constprod_functor1 F))
    (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C).

  (** Construction of initial algebra for the omega-cocontinuous signature functor with lax lineator *)
  Definition DatatypeOfBindingSig_CAT :
    Initial (FunctorAlg (Id_H (BindingSigToFunctor TC sig CC))).
  Proof.
    use colimAlgInitial.
    - apply (Initial_functor_precat _ _ IC).
    - apply (is_omega_cocont_Id_H _ _ _ (is_omega_cocont_BindingSigToFunctor TC CLC HF sig CC)).
    - apply ColimsFunctorCategory_of_shape, CLC.
  Defined.

  (** the associated GHSS *)
  Definition GHSSOfBindingSig_CAT :
    ghss Mon_endo_CAT (BindingSigToFunctor TC sig CC) (BindingSigToStrengthCAT TC sig CC).
  Proof.
    use (initial_alg_to_ghss (BindingSigToStrengthCAT TC sig CC) BCC2 (bincoprod_distributor_pointed_CAT BCC)).
    - apply (Initial_functor_precat _ _ IC).
    - apply ColimsFunctorCategory_of_shape, CLC.
    - apply (is_omega_cocont_BindingSigToFunctor TC CLC HF sig CC).
    - intro F. apply Initial_functor_precat.
    - exact (precomp_omegacocont_CAT CLC).
  Defined.

  (** the associated Sigma-monoid *)
  Definition SigmaMonoidOfBindingSig_CAT : SigmaMonoid (BindingSigToStrengthCAT TC sig CC).
  Proof.
    apply ghhs_to_sigma_monoid.
    exact GHSSOfBindingSig_CAT.
  Defined.

  (** the associated monad *)
  Definition MonadOfBindingSig_CAT : Monad C.
  Proof.
    use monoid_to_monad_CAT.
    use SigmaMonoid_to_monoid.
    - exact (BindingSigToFunctor TC sig CC).
    - exact (BindingSigToStrengthCAT TC sig CC).
    - exact SigmaMonoidOfBindingSig_CAT.
  Defined.

End PuttingAllTogether.

End FixACategory.

Section InstanceHSET.

Definition BindingSigToMonadHSET_viaCAT : BindingSig → Monad HSET.
Proof.
intros sig; use (MonadOfBindingSig_CAT _ _ _ _ _ _ sig).
- apply BinProductsHSET.
- apply BinCoproductsHSET.
- apply InitialHSET.
- apply TerminalHSET.
- apply ColimsHSET_of_shape.
- intro F.
  apply is_omega_cocont_constprod_functor1.
  apply Exponentials_functor_HSET.
- apply CoproductsHSET.
  apply BindingSigIsaset.
Defined.

End InstanceHSET.
