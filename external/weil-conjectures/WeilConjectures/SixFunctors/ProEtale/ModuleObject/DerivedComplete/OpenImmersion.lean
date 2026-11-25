/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!
# Derived completeness and restriction to an open subscheme

For an open immersion `j : U ⟶ X`, the derived pullback `Lj^*` preserves derived complete
`𝒪_E`-complexes (`ProEtale.derivedCompleteIntegers_leftDerivedUpperStar_obj_of_isOpenImmersion`),
without any quasi-compactness hypothesis: `Lj^*` is right adjoint to the extension by zero
`Dj_!`, which commutes with the first derived reduction
(`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- The derived pullback `Lj^*` along an open immersion preserves derived complete complexes: it
is right adjoint to the extension by zero `Dj_!`, which commutes with the first derived
reduction. -/
theorem derivedCompleteIntegers_leftDerivedUpperStar_obj_of_isOpenImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K) :
    derivedCompleteIntegers ℓ E U
      ((L((j)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) := by
  intro Z hZ g
  have hZ' : IsZero ((derivedReduction X ℓ E).obj
      (D((j)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj Z)) := by
    rw [isZero_derivedReduction_iff] at hZ ⊢
    exact ((D((j)_!open⟦Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).map_isZero
      hZ).of_iso ((derivedOpenImmersionShriekIso
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) j).app Z)
  let e := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
    (Profinite.padicIntegersRingObj ℓ E.1) j).app K
  have h := (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicIntegersRingObj ℓ E.1) j).eq_zero_of_forall_eq_zero (hK hZ')
    (g ≫ e.hom)
  calc
    g = (g ≫ e.hom) ≫ e.inv := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = 0 := (congrArg (fun f ↦ f ≫ e.inv) h).trans zero_comp

end AlgebraicGeometry.ProEtale
