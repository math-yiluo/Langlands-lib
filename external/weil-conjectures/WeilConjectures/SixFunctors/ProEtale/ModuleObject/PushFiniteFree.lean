/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsBiproductUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsBasis
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear

/-!
# (Push) for a finite free coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings along which extension of scalars is
exact, and `f : X ⟶ Y` a morphism of schemes. Suppose that `Λ'` is a finite free `Λ`-module with
a basis `φ(b₁), …, φ(bₙ)` of constant global sections, for a ring homomorphism `φ : K →+* Γ Λ'`.
Then the comparison **(Push)** `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'`
(`ProEtale.CondensedRing.derivedPushHom`) is an isomorphism on all unbounded objects
(`ProEtale.CondensedRing.isIso_derivedPushHom_of_isIso_biproductDesc_globalSmul`).

Indeed, on every scheme `Z` the maps `K ⟶ Res (Λ'_Z ⊗ᴸ K)`, `m ↦ bᵢ ⊗ m`, exhibit
`Res (Λ'_Z ⊗ᴸ K)` as `Kⁿ`
(`ProEtale.CondensedRing.isIso_biproductDesc_derivedUnit_coefficientMap`, by
`Mod.isIso_biproductDesc_derivedUnit_smul`), the derived pushforward `Rf_*^Λ'` is `K`-linear
(`ProEtale.CondensedRing.linear_rightDerivedLowerStar`), and the mate of (Push) along `T ⊣ Res`
is the isomorphism `Rf_*^Λ' ⋙ Res ≅ Res ⋙ Rf_*^Λ`
(`ProEtale.CondensedRing.derivedComapLowerStarIso`). We conclude by
`Adjunction.isIso_app_of_isIso_mateEquiv_of_isIso_biproductDesc`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {K : Type*} [CommRing K] (φ : K →+* Γ Λ') {n : ℕ} (b : Fin n → K)

/-- If `Λ'` is free over `Λ` with basis the constant global sections `φ(bᵢ)`, then on every
scheme `Z` and for every `K` in the derived category of `Λ_Z`-modules, the maps
`K ⟶ Res (Λ'_Z ⊗ᴸ K)`, `m ↦ bᵢ ⊗ m`, exhibit `Res (Λ'_Z ⊗ᴸ K)` as `Kⁿ`. -/
theorem isIso_biproductDesc_derivedUnit_coefficientMap
    (h : IsIso (biproduct.desc fun i ↦ a ≫ Mod.globalSmul (φ (b i)).hom (Mod.regular Λ') :
      ⨁ (fun _ : Fin n ↦ Λ) ⟶ Λ'))
    (Z : Scheme.{u})
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    letI := modLinear Λ' φ Z
    IsIso (biproduct.desc fun i : Fin n ↦
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z)).unit.app M ≫
        (Mod.comap (coefficientMap a Z)).mapDerivedCategory.map
          (b i • 𝟙 ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.obj M))) := by
  let := modLinear Λ' φ Z
  refine Mod.isIso_biproductDesc_derivedUnit_smul _ b (fun N ↦ ?_) M
  simp only [Mod.linearOfRingHom_smul_id]
  exact Mod.isIso_biproductDesc_extendUnit_smul _ (fun i ↦ (constRingHom Λ' φ Z (b i)).hom)
    (isIso_biproductDesc_coefficientMap_globalSmul a φ b h Z) N

/-- **(Push) for a finite free coefficient change**: if `Λ'` is free over `Λ` with basis the
constant global sections `φ(bᵢ)`, i.e. `Λⁿ ⟶ Λ'`, `(xᵢ) ↦ ∑ xᵢ φ(bᵢ)`, is an isomorphism, then
the comparison `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` is an isomorphism on all unbounded objects. -/
theorem isIso_derivedPushHom_of_isIso_biproductDesc_globalSmul
    (h : IsIso (biproduct.desc fun i ↦ a ≫ Mod.globalSmul (φ (b i)).hom (Mod.regular Λ') :
      ⨁ (fun _ : Fin n ↦ Λ) ⟶ Λ'))
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (derivedPushHom a f) := by
  let := modLinear Λ' φ X
  let := modLinear Λ' φ Y
  have := linear_rightDerivedLowerStar Λ' φ f
  have : IsIso (mateEquiv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
      (TwoSquare.mk _ _ _ _ (derivedPushHom a f))) := by
    change IsIso ((mateEquiv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)))
        ((mateEquiv
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))).symm
          (TwoSquare.mk _ _ _ _ (derivedComapLowerStarIso a f).inv)))
    rw [Equiv.apply_symm_apply]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have := isIso_biproductDesc_derivedUnit_coefficientMap a φ b h X M
  have := isIso_biproductDesc_derivedUnit_coefficientMap a φ b h Y (R((f)_*⟦Λ⟧).obj M)
  exact Adjunction.isIso_app_of_isIso_mateEquiv_of_isIso_biproductDesc
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (TwoSquare.mk _ _ _ _ (derivedPushHom a f)) M (fun i ↦ b i • 𝟙 _) (fun i ↦ b i • 𝟙 _)
    (fun i ↦ by
      simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp,
        Linear.comp_smul, Category.id_comp, Functor.comp_obj, Category.comp_id])

end AlgebraicGeometry.ProEtale.CondensedRing
