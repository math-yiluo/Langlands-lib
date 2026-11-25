/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Constructible étale complexes as condensed constructible complexes

For a bounded constructible étale complex `N` of `𝒪_E ⧸ ℓⁿ`-modules, the condensed complex
`Φ⁻¹ (ν^* N)` is bounded constructible (`ProEtale.CondensedRing.boundedConstructibleOfEtale`, the
statement `ProEtale.CondensedRing.BoundedConstructibleOfEtale`), where
`Φ = ProEtale.finiteCoefficientModEquivalence`: `ν^*` and `Φ⁻¹` are exact, so they commute with the
cohomology sheaves, and the condensed reading of a constructible étale sheaf is constructible
(`ProEtale.isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **Constructible étale complexes are read from bounded constructible condensed ones**: for a
bounded constructible étale complex `N` of `𝒪_E ⧸ ℓⁿ`-modules on `X`, the condensed complex
`Φ⁻¹ (ν^* N)` is bounded constructible. The exact functors `ν^*` and `Φ⁻¹` preserve boundedness
and commute with the cohomology sheaves, and the condensed reading of a constructible étale sheaf
is constructible (`ProEtale.isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj`). -/
theorem boundedConstructibleOfEtale (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : BoundedConstructibleOfEtale ℓ E n X := by
  intro N hN
  refine ⟨Functor.bounded_mapDerivedCategory_obj _
    ((ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).bounded_mapDerivedCategory_obj
      hN.1), fun i ↦ ?_⟩
  have : IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ i).obj N) := hN.2 i
  exact (isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj
    (PadicAlgCl.integersModPow ℓ E n) _).of_iso
    ((finiteCoefficientModEquivalence X.left _).inverse.mapIso
      ((Functor.mapDerivedCategoryHomologyFunctorIso
        (ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])
        i).app N) ≪≫
      (((finiteCoefficientModEquivalence X.left
        (PadicAlgCl.integersModPow ℓ E n)).inverse.mapDerivedCategoryHomologyFunctorIso i).app _))

end AlgebraicGeometry.ProEtale.CondensedRing
