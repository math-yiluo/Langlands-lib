/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Higher direct images commute with restriction of scalars

Let `φ : Λ →+* Λ'` be a morphism of commutative rings (e.g. `ℤ → ℤ/ℓⁿ`) and `f : X ⟶ Y` a
morphism of schemes. For an étale sheaf `G` of `Λ'`-modules on `X`, the higher direct images of
`G` computed for sheaves of `Λ'`-modules and for the underlying sheaves of `Λ`-modules agree:
`res (Rᵠf_* G) ≅ Rᵠf_* (res G)`. This is the degreewise form of
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`.

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerStarRestrictScalarsIso`: the classical right derived
  functors, `res ∘ Rᵠf_* ≅ Rᵠf_* ∘ res`.
- `AlgebraicGeometry.Etale.homologyRightDerivedLowerStarRestrictScalarsIso`: the cohomology
  sheaves of the total derived functor `Rf_*` applied to `G[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images commute with restriction of scalars**: for an étale sheaf `G` of
`Λ'`-modules, `res (Rᵠf_* G) ≅ Rᵠf_* (res G)`, the right hand side being computed for sheaves of
`Λ`-modules. It is the base change morphism of the classical right derived functors
(`CategoryTheory.Functor.rightDerivedBaseChange`), invertible by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`. -/
noncomputable def rightDerivedLowerStarRestrictScalarsIso (q : ℕ) :
    ((f)_*[ModuleCat.{u + 1} Λ']).rightDerived q ⋙
        Sheaf.restrictScalars Y.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q :=
  have : IsIso (Functor.rightDerivedBaseChange (lowerStarCompRestrictScalarsIso φ f).hom q) := by
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarCompRestrictScalarsIso φ f).hom) :=
      isIso_rightDerivedLowerStarRestrictScalars φ f
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    infer_instance
  asIso (Functor.rightDerivedBaseChange (lowerStarCompRestrictScalarsIso φ f).hom q)

/-- **Cohomology sheaves of `Rf_*` commute with restriction of scalars**: for an étale sheaf `G`
of `Λ'`-modules and `q : ℕ`, `res Hᵠ(Rf_* G[0]) ≅ Hᵠ(Rf_* (res G)[0])`, where `Rf_*` is the total
derived direct image on the unbounded derived categories of sheaves of `Λ'`-modules and of
`Λ`-modules respectively. -/
noncomputable def homologyRightDerivedLowerStarRestrictScalarsIso
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (q : ℕ) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).obj
        ((DerivedCategory.homologyFunctor _ q).obj (R((f)_*[ModuleCat.{u + 1} Λ']).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))) ≅
      (DerivedCategory.homologyFunctor _ q).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G))) :=
  (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ']).homologyRightDerivedFunctorObjSingleFunctorIso G q) ≪≫
    (rightDerivedLowerStarRestrictScalarsIso φ f q).app G ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm

end AlgebraicGeometry.Etale
