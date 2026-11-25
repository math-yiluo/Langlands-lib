/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarTensorKFlatModel

/-! # Preservation of good complexes under coefficient-normalized reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-good-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The two completed coefficient maps coincide because every finite projection agrees.
Source: Stacks 03CO (blueprint: lem-pod-reindexing-good-complex). -/
theorem podCompletedCoefficientMap_eq :
    (isoReductionCompletedMap l E g).hom = inverseImageCompletedCoefficientMap l E g := by
  apply limit.hom_ext
  intro n
  have h := (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec n.unop
  change (isoReductionCompletedMap l E g).hom ≫
    limit.π (integralCoefficientSheafSystem l E X) n = _ at h
  exact h.trans (by
    simp only [inverseImageCompletedCoefficientMap, limit.lift_π,
      inverseImageCompletedCoefficientComponent, inverseImageFiniteCoefficientMap])

/-- Relabelling preserves the flat-term K-flat representatives used by reduction.
Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), and Stacks 03EL
(blueprint: lem-pod-reindexing-good-complex).

Proof: identify the two completed coefficient maps by composing with every finite
projection. They then induce the identical sectionwise module inverse image.
Specialize the existing coefficient-compatible K-flat model theorem to the identity
extension of E. Its first preservation assertion gives exactly the result, without
any bound on the complex or any completeness hypothesis. -/
theorem podReindexingGoodComplex
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    integralOperationsGoodComplex l E X ((isoReductionIntegralComplex l E g).obj P) := by
  have hx : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := fun x ↦ by
    apply isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x))
    simpa only [map_natCast] using isUnit_of_invertible (l : X.residueField x)
  have hy : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := fun y ↦ by
    apply isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y))
    simpa only [map_natCast] using isUnit_of_invertible (l : Y.residueField y)
  obtain ⟨_, _, _, _, _, _, _, hm, _⟩ :=
    AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_tensor_kflat_model
      l E E (AlgHom.id ℚ_[l] E) g hx hy
  have hg := (hm ⟨P, hP⟩).1
  change integralOperationsGoodComplex l E X
    (((isoSectionwiseModuleInverseImage g
      (isoReductionCompletedMap l E g).hom).mapHomologicalComplex (.up ℤ)).obj P)
  simpa only [podCompletedCoefficientMap_eq l E g] using hg

end WeilConjectures
