/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresentedField
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj

/-!
# The field coefficients satisfy the hypotheses of the tensor closure of `Dᵇc`

The coefficient rings `ℚ̲̄_ℓ` and `E̲`, for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, satisfy
`ProEtale.CondensedRing.TensorHypotheses`
(`ProEtale.CondensedRing.tensorHypotheses_padicAlgClRingObj`,
`ProEtale.CondensedRing.tensorHypotheses_continuousMapRingObj`): on a scheme with noetherian
underlying space, a pro-étale locally finitely presented module object is locally free
(`condensedQbar_lfp_locally_free`, `exists_finiteFree_cover_of_condensedField_lfp`; the lisse
sheaves of Bhatt–Scholze, Definition 6.8.6), and the bounded constructible complexes form a
triangulated subcategory (`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj`,
`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient ring `ℚ̲̄_ℓ` satisfies `ProEtale.CondensedRing.TensorHypotheses`. -/
theorem tensorHypotheses_padicAlgClRingObj :
    TensorHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) where
  isLocallyFree Z _ _ hM := isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace ℓ Z hM
  isTriangulated _ _ := inferInstance

/-- The coefficient ring `E̲` of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` satisfies
`ProEtale.CondensedRing.TensorHypotheses`. -/
theorem tensorHypotheses_continuousMapRingObj (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    TensorHypotheses (Profinite.continuousMapRingObj.{u} E) where
  isLocallyFree Z _ _ hM :=
    ContinuousMapRingObj.isLocallyFree_of_isLocallyFinitelyPresented ℓ E Z hM
  isTriangulated _ _ := inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
