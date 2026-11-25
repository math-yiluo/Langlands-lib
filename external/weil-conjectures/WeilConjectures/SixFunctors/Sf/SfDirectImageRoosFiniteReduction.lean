/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Finite reduction of a direct-image Roos limit for arbitrary input

Source: Stacks 0941, 099N; Bhatt--Scholze, Lemmas 3.5.4--3.5.7 and 6.5.11.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem imageTransition_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' : DerivedCategory (scalarReductionSource.{u, u} l E X)} (a : K ⟶ K') (n : ℕ) :
    sfDirectImageTransition l E f K n ≫
        (scalarReductionDerivedRestriction.{u, u} l E Y n).map
          ((proEtaleConstantDerivedDirectImage f
            (Padic.coefficientExtensionRing l E (n + 1))).map
            ((scalarReductionDerivedExtension.{u, u} l E X n).map a)) =
      (scalarReductionDerivedRestriction.{u, u} l E Y (n + 1)).map
          ((proEtaleConstantDerivedDirectImage f
            (Padic.coefficientExtensionRing l E (n + 2))).map
            ((scalarReductionDerivedExtension.{u, u} l E X (n + 1)).map a)) ≫
        sfDirectImageTransition l E f K' n := by
  let F := sfCompletedDerivedDirectImage l E f
  let d (k : ℕ) := sfDerivedRestrictionComparison l E f k
  have hn (k : ℕ) := (d k).hom.naturality
    ((scalarReductionDerivedExtension.{u, u} l E X k).map a)
  have hi (k : ℕ) := (d k).inv.naturality
    ((scalarReductionDerivedExtension.{u, u} l E X k).map a)
  have ht := congrArg F.map ((sfDerivedReductionTransition l E X n).naturality a)
  dsimp only [Functor.comp_map] at hn hi
  simp only [Functor.map_comp, sfDerivedReductionRestricted, Functor.comp_map] at ht
  have hn0 := hn n
  have hi0 := hi (n + 1)
  unfold sfDirectImageTransition
  simp only [Category.assoc]
  rw [← hn0, ← reassoc_of% ht, ← reassoc_of% hi0]

/-- Completing the input does not change its finite direct-image tower. Therefore
the finite projection adjunct of every chosen Roos limit is invertible, even when
the input is not complete.
Source: Stacks 0941, 099N; Bhatt--Scholze, Lemmas 3.5.4--3.5.7 and 6.5.11.
(blueprint: lem-weil-sf-direct-image-roos-finite-reduction).

Proof: complete K using the total limit of its reduction system. Normalized
reconstruction makes that limit complete and inverts the counit at the reduction
of K. The adjunction triangle then makes reduction of the completion unit an
isomorphism. Finite evaluation identifies this with each finite scalar extension
of the unit. Apply finite direct image and completed restriction to get an
isomorphism of the two finite-image towers; naturality of the specified restriction
comparisons proves the transition equations. Transport the given Roos triangle
along these isomorphisms, keeping its limit object fixed. The complete-input
direct-image theorem makes every projection adjunct of the transported triangle
invertible. Naturality of the scalar adjunction identifies it with the old
projection adjunct followed by the finite-image isomorphism. Cancel that
isomorphism. This also covers zero complexes, level zero and empty schemes. -/
theorem sfDirectImageRoos_finiteReduction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    [HasProduct (sfDirectImageTerm l E f K)]
    (L : SfIntegralDirectImage l E f K) (n : ℕ) :
    IsIso (sfDirectImageReductionComparison l E f L n) := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E X
  let K' := (coefficientSequenceLimit l E X).obj (S.reduction.obj K)
  let a : K ⟶ K' := S.adjunction.unit.app K
  have hrec := (purNormalizedReconstructionOfScheme l E X S).1
    (S.reduction.obj K) (S.reduction_normalized K)
  have hc : IsIso (S.adjunction.counit.app (S.reduction.obj K)) := hrec.2
  have ha : IsIso (S.reduction.map a) := by
    have : IsIso (S.reduction.map a ≫ S.adjunction.counit.app (S.reduction.obj K)) := by
      rw [show S.reduction.map a ≫ S.adjunction.counit.app (S.reduction.obj K) = 𝟙 _ from
        S.adjunction.left_triangle_components K]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (S.adjunction.counit.app (S.reduction.obj K))
  have hfinite (k : ℕ) : IsIso ((scalarReductionDerivedExtension.{u, u} l E X k).map a) := by
    exact (NatIso.isIso_map_iff (S.reductionEvaluation k) a).mp (by
      change IsIso ((coefficientSequenceDerivedEvaluation l E X k).map (S.reduction.map a))
      infer_instance)
  let b (k : ℕ) := (proEtaleConstantDerivedDirectImage f
    (Padic.coefficientExtensionRing l E (k + 1))).mapIso
      (asIso ((scalarReductionDerivedExtension.{u, u} l E X k).map a))
  let c (k : ℕ) := (scalarReductionDerivedRestriction.{u, u} l E Y k).mapIso (b k)
  let q (k : ℕ) := L.projection ≫ Pi.π (sfDirectImageTerm l E f K) k ≫ (c k).hom
  obtain ⟨hp, δ, hδ⟩ := roos_transport
    (sfDirectImageTransition l E f K) (sfDirectImageTransition l E f K')
    (Iso.refl L.obj) c
    (fun k ↦ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) k) q
    (fun k ↦ imageTransition_naturality l E f a k)
    (fun k ↦ by simp only [q, Iso.refl_hom, Category.id_comp, Category.assoc])
    ⟨inferInstance, L.boundary, by
      have he : Pi.lift (fun k ↦ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) k) =
          L.projection := by
        apply Pi.hom_ext
        intro k
        simp only [Pi.lift_comp_π]
      rw [he]
      exact L.roos⟩
  let := hp
  let L' : SfIntegralDirectImage l E f K' := ⟨L.obj, Pi.lift q, δ, hδ⟩
  obtain ⟨D, hl, hK'⟩ := hrec.1
  have hcomplete : IsSfDerivedComplete l E X K' :=
    (sfDerivedComplete_iff_legacy l E X D hl K').mpr hK'
  have hL' := (sfCompleteDirectImage_reduction l E f K' hcomplete L').2 n
  have heq : sfDirectImageReductionComparison l E f L' n =
      sfDirectImageReductionComparison l E f L n ≫ (b n).hom := by
    dsimp only [sfDirectImageReductionComparison, L']
    rw [Pi.lift_comp_π]
    dsimp only [q, c, b, Functor.mapIso_hom, asIso_hom]
    simpa only [b, Functor.mapIso_hom, asIso_hom, Category.assoc] using
      (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
        |>.homEquiv_naturality_right_symm
          (L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n) (b n).hom
  have : IsIso (sfDirectImageReductionComparison l E f L n ≫ (b n).hom) := by
    rw [← heq]
    exact hL'
  exact IsIso.of_isIso_comp_right _ (b n).hom

end WeilConjectures
