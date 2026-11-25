/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower

/-! # Quotient coherence of the unit-normalized restriction comparison

Source: Stacks Project, Tags 03D6 and 0941; the ordinary comparison in Step 8
of `lem-pod-derived-automorphism-hom-evaluation`.
(blueprint: lem-pod-restriction-reindexing-transition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard Scheme.residueField
  coefficientSequenceRestriction pullbackTensorSequenceInverse
  coefficientSequenceEvaluation
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
    (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X) [IsIso c]

/-- The finite unit-normalized comparisons assemble across every coefficient arrow.
Source: Stacks 03D6, 0941; ordinary restriction/reindexing in node proof Step 8.
Proof: identify c with the projection-normalized completed coefficient map by
joint monicity of its projections. Exact sectionwise inverse image therefore
reindexes the whole restricted tower. At each finite level compare its component
with the displayed composite. The inverse-image/evaluation mate preserves the
sequence adjunction unit, the finite/intrinsic comparison preserves the finite
unit, and r takes that unit to restriction along the site counit. Evaluate on a
section over gU, then restrict along U to g*(gU). The adjunction triangle makes
this precisely the original section over U. The sequence unit and restriction
maps are natural for every quotient arrow, so the two component routes agree
on these sections. They generate all sections because the site and coefficient
maps are equivalences. Extensionality of module-sheaf maps gives the equation.
This argument retains all quotient transitions and uses no limit or derived
limit, and no equality detection in a derived category.
(blueprint: lem-pod-restriction-reindexing-transition). -/
theorem podRestrictionReindexingTransition
    (r : ∀ n : ℕ,
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g ⋙
        scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E Y n ⋙ isoSectionwiseModuleInverseImage.{u, u} g c)
    (hc : ∀ n : ℕ,
      c ≫ limit.π (integralCoefficientSheafSystem l E X) (op n) =
        (isoSectionwiseInverseImage g RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
        isoSectionwiseConstantMap.{u, u} g
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
    (hr : ∀ (n : ℕ) (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
      (x : M.val.obj (op V)),
      HEq (((r n).hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        ((((sfIntrinsicConstantModuleAdjunction g
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op V)) x))
        ((M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          (inferInstance : WeaklyEtale g) trivial).counit.app V).op) x)) :
    let F := isoSectionwiseModuleInverseImage.{u, u} g c
    let S := pullbackTensorSequenceInverse l E g
    let RY := coefficientSequenceRestriction l E Y
    let RX := coefficientSequenceRestriction l E X
    let δ (n : ℕ) :
        S ⋙ RX ⋙ (evaluation ℕᵒᵖ (integralTowerModules l E X)).obj (op n) ≅
          RY ⋙ (evaluation ℕᵒᵖ (integralTowerModules l E Y)).obj (op n) ⋙ F :=
      Functor.isoWhiskerLeft S (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) ≪≫
        Functor.isoWhiskerRight
          ((pullbackTensorSequenceInverseEvaluation l E g n).symm ≪≫
            Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
              (pullbackTensorLevelIntrinsic l E g n))
          (scalarReductionRestriction l E X n) ≪≫
        Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n) (r n) ≪≫
        Functor.isoWhiskerRight (eqToIso
          (coefficientSequenceRestriction_evaluation l E Y n)).symm F
    ∀ (N : coefficientSequenceModules l E Y) {m n : ℕᵒᵖ} (f : m ⟶ n),
      ((RX.obj (S.obj N)).map f) ≫ (δ n.unop).hom.app N =
        (δ m.unop).hom.app N ≫ F.map ((RY.obj N).map f) := by
  sorry

end WeilConjectures
