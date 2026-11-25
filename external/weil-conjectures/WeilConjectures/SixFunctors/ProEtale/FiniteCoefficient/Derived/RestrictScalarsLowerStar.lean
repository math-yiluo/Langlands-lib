/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.RestrictScalarsAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Restriction of scalars commutes with the derived direct image of pro-étale sheaves

Let `φ : Λ →+* Λ'` be a morphism of commutative rings (e.g. `ℤ → ℤ/ℓⁿ`) and `f : X ⟶ Y` a
morphism of schemes. Restriction of scalars along `φ` is exact and commutes with the direct image
`f_*` of pro-étale sheaves (both are computed objectwise). It also commutes with the derived
direct image: `res (Rᵠf_* G) ≅ Rᵠf_* (res G)` for a sheaf `G` of `Λ'`-modules on `X_proét`.
The input is that restriction of scalars sends injective sheaves of `Λ'`-modules to
`f_*`-acyclic sheaves of `Λ`-modules
(`CategoryTheory.Sheaf.rightAcyclic_restrictScalars_obj_of_injective`).

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar`.
It is what identifies the higher direct images of the terms `Gₙ` of an `ℓ`-adic tower, computed
for sheaves of `ℤ/ℓⁿ`-modules, with those computed for the underlying sheaves of `ℤ`-modules, on
which the Milnor sequence (`AlgebraicGeometry.ProEtale.shortExact_milnor_rightDerivedLowerStar`)
is formulated.

## Main results

- `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_restrictScalars_obj`: injective sheaves of
  `Λ'`-modules are `f_*`-acyclic as sheaves of `Λ`-modules.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarRestrictScalars`:
  `res ∘ R⁺f_* ≅ R⁺f_* ∘ res` on `D⁺`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarRestrictScalarsIso`:
  `res (Rᵠf_* G) ≅ Rᵠf_* (res G)` for the classical right derived functors.
- `AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarRestrictScalarsIso`: the same for the
  cohomology sheaves of the total derived functor `Rf_*` applied to `G[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct image of pro-étale sheaves of `Λ`-modules sends morphisms which are surjective on
sections to epimorphisms: it is computed objectwise. -/
lemma epi_lowerStar_map_of_surjective
    {A B : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (p : A ⟶ B) (hp : ∀ U, Function.Surjective (p.hom.app U)) :
    Epi ((f)_*[ModuleCat.{u + 1} Λ].map p) := by
  have : Sheaf.IsLocallySurjective ((f)_*[ModuleCat.{u + 1} Λ].map p) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun U ↦ hp _
  exact Sheaf.epi_of_isLocallySurjective _

/-- **Injective pro-étale sheaves of `Λ'`-modules are `f_*`-acyclic as sheaves of
`Λ`-modules.** -/
theorem rightAcyclic_lowerStar_restrictScalars_obj
    (J : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ')) [Injective J] :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightAcyclic
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj J) :=
  Sheaf.rightAcyclic_restrictScalars_obj_of_injective.{u + 1, u} φ _ _
    (epi_lowerStar_map_of_surjective f) J

/-- Restriction of scalars commutes with the direct image, both being computed objectwise. -/
noncomputable def lowerStarCompRestrictScalarsIso :
    (f)_*[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙ (f)_*[ModuleCat.{u + 1} Λ] :=
  Iso.refl _

/-- The comparison `res(R⁺f_* K) ⟶ R⁺f_*(res K)` between restriction of scalars along
`φ : Λ →+* Λ'` and the derived direct image of pro-étale sheaves on `D⁺`: the base change
morphism of the identification `f_* ∘ res = res ∘ f_*`. It is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarRestrictScalars`). -/
noncomputable def rightDerivedLowerStarRestrictScalars :
    ((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus ⋙
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryPlus ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryPlus ⋙
        ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarCompRestrictScalarsIso φ f).hom

/-- **Restriction of scalars commutes with the derived direct image of pro-étale sheaves**: the
comparison `res(R⁺f_* K) ⟶ R⁺f_*(res K)` is an isomorphism, since restriction of scalars sends
injective sheaves of `Λ'`-modules to `f_*`-acyclic sheaves of `Λ`-modules
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_restrictScalars_obj`). -/
instance isIso_rightDerivedLowerStarRestrictScalars :
    IsIso (rightDerivedLowerStarRestrictScalars φ f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun I _ ↦ rightAcyclic_lowerStar_restrictScalars_obj φ f I

/-- **Higher direct images commute with restriction of scalars**: for a pro-étale sheaf `G` of
`Λ'`-modules, `res (Rᵠf_* G) ≅ Rᵠf_* (res G)`, the right hand side being computed for sheaves of
`Λ`-modules. It is the base change morphism of the classical right derived functors
(`CategoryTheory.Functor.rightDerivedBaseChange`), invertible by
`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarRestrictScalars`. -/
noncomputable def rightDerivedLowerStarRestrictScalarsIso (q : ℕ) :
    ((f)_*[ModuleCat.{u + 1} Λ']).rightDerived q ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
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

/-- **Cohomology sheaves of `Rf_*` commute with restriction of scalars**: for a pro-étale sheaf
`G` of `Λ'`-modules and `q : ℕ`, `res Hᵠ(Rf_* G[0]) ≅ Hᵠ(Rf_* (res G)[0])`, where `Rf_*` is the
total derived direct image on the unbounded derived categories of sheaves of `Λ'`-modules and of
`Λ`-modules respectively. -/
noncomputable def homologyRightDerivedLowerStarRestrictScalarsIso
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ')) (q : ℕ) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).obj
        ((DerivedCategory.homologyFunctor _ q).obj (R((f)_*[ModuleCat.{u + 1} Λ']).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))) ≅
      (DerivedCategory.homologyFunctor _ q).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj G))) :=
  (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ']).homologyRightDerivedFunctorObjSingleFunctorIso G q) ≪≫
    (rightDerivedLowerStarRestrictScalarsIso φ f q).app G ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm

end AlgebraicGeometry.ProEtale
