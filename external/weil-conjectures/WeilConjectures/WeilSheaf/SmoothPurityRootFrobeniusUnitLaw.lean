/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRootFrobeniusLaw
public import WeilConjectures.WeilSheaf.SmoothPurityScalarWeilLaw
public import WeilConjectures.WeilSheaf.SmoothPurityMapModUnit

/-! # The root Frobenius law with the mapped unit comparison -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

/-- The two factorization conventions agree before taking components. -/
lemma purityAbelianFactorIso_eq_upperStarFactorIso
    {U X : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (h : s ≫ p = p) :
    purityAbelianFactorIso p s h = upperStarFactorIso s p h := by
  simp [purityAbelianFactorIso, ProEtale.upperStarComp', upperStarFactorIso, upperStarCongr]
  rfl

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- The root trivialization, including the mapped-module unit, has scalar q. -/
lemma purity_tateModule_rootTrivialization_frobenius :
    (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
          (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso).hom.hom ≫
      (purityAbelianFrobeniusFactorIso a).hom.app
        (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) =
      (Nat.card k : ℤ) •
        ((purityAbelianFrobeniusFactorIso a).hom.app (tateModule X ℓ).X ≫
          (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
            a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
            (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso).hom.hom) := by
  simpa only [purity_mapModUnitIso_postcompose_hom, purityAbelianFrobeniusFactorIso,
    purityAbelianFactorIso_eq_upperStarFactorIso] using
    upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom_frobenius a hζ hζ'

end AlgebraicGeometry.ProEtale
