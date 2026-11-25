/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived

/-!
# The coefficient comparison of the derived direct image is a mate

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `f : X ⟶ Y` a morphism of schemes
whose higher direct images vanish in large degrees. The coefficient comparison
`Res ⋙ Rf_* ≅ Rf_* ⋙ Res`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso`)
is the mate of the coefficient comparison `Res ⋙ Lf^* ≅ Lf^* ⋙ Res`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`) for the derived adjunctions
`Lf^* ⊣ Rf_*`, and the mate of the comparison `Res ⋙ D(f^*) ≅ D(f^*) ⋙ Res` for the adjunctions
`D(f^*) ⊣ Rf_*`. In other words, the comparison of `Rf_*` is compatible with the units and
counits of these adjunctions. This is used for the compatible systems of Frobenius coefficient
morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
  (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
    IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))

/-- The comparison `g^*(Res G) ≅ Res(g^* G)` is compatible with the units of `g^* ⊣ g_*`. -/
lemma restrictScalars_map_unit_app_comp_lowerStarCompRestrictScalarsIso_hom_app
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars Y.smallEtaleTopology ρ).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f).unit.app N) ≫
      (lowerStarCompRestrictScalarsIso ρ f).hom.app (((f)^*[ModuleCat.{u + 1} Λ']).obj N) =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology ρ).obj N) ≫
      ((f)_*[ModuleCat.{u + 1} Λ]).map ((upperStarRestrictScalarsIso ρ f).hom.app N) := by
  rw [restrictScalars_map_unit_app]
  exact Category.comp_id _

/-- **The coefficient comparison of `Rf_*` is the mate of that of `Lf^*`** for the derived
adjunctions `Lf^* ⊣ Rf_*` over `Λ'` and `Λ`. -/
lemma mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso :
    mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (leftDerivedUpperStarRestrictScalarsIso ρ f).hom =
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd).inv :=
  Adjunction.mateEquiv_derivedAdjunction_restrict
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f) (upperStarRestrictScalarsIso ρ f)
    (lowerStarCompRestrictScalarsIso ρ f)
    (restrictScalars_map_unit_app_comp_lowerStarCompRestrictScalarsIso_hom_app ρ f)
    (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ f d hd K)

/-- **The coefficient comparison of `Rf_*` is the mate of that of `D(f^*)`** for the
adjunctions `D(f^*) ⊣ Rf_*` over `Λ'` and `Λ`. -/
lemma mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars :
    mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ f)).hom =
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd).inv :=
  Adjunction.mateEquiv_mapDerivedCategoryRightDerivedAdjunction_restrict
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f) (upperStarRestrictScalarsIso ρ f)
    (lowerStarCompRestrictScalarsIso ρ f)
    (restrictScalars_map_unit_app_comp_lowerStarCompRestrictScalarsIso_hom_app ρ f)
    (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ f d hd K)

end AlgebraicGeometry.Etale
