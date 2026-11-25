/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal

/-!
# The pullback of `ℓ`-adic sheaves preserves K-flat complexes

For an arbitrary morphism of schemes `f : Y ⟶ X`, the pullback `f^*` of sheaves of
`ℚ̄_ℓ,X`-modules (`AlgebraicGeometry.ProEtale.adicUpperStar`), applied degreewise, sends K-flat
complexes to K-flat complexes, and it sends flat objects to flat objects. Through the monoidal
equivalence `AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}` of the two models of `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), which is compatible with the pullbacks
(`AlgebraicGeometry.ProEtale.upperStarCondensedModInverseIso`), this is the corresponding statement
for module objects over the condensed ring `ℚ̲̄_ℓ`
(`AlgebraicGeometry.ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj`).

## Main statements

- `AlgebraicGeometry.ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj`: `f^*` preserves
  K-flat complexes.
- `AlgebraicGeometry.ProEtale.preservesFlat_adicUpperStar`: `f^*` preserves flat objects.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The equivalence `AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}` admits a monoidal structure. -/
theorem nonempty_monoidal_adicSheafEquivCondensedMod_functor (X : Scheme.{u}) :
    Nonempty (adicSheafEquivCondensedMod l X).functor.Monoidal := by
  obtain ⟨m⟩ := nativeScalarForgetting_monoidal l X
  let : (AdicSheaf.forgetAb l X).Monoidal := m
  exact ⟨inferInstanceAs (AdicSheaf.forgetAb l X ⋙
    Mod.comap (condensedRingObjIsoForgetAb l X).hom).Monoidal⟩

/-- The pullback of `ℓ`-adic sheaves along an arbitrary morphism of schemes preserves K-flat
complexes. -/
theorem kFlat_adicUpperStar_mapHomologicalComplex_obj {P : CochainComplex (AdicSheaf l X) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((f)^*ᵃ[l]).mapHomologicalComplex (.up ℤ) |>.obj P) := by
  let EX := adicSheafEquivCondensedMod l X
  let EY := adicSheafEquivCondensedMod l Y
  let U := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f
  obtain ⟨mX⟩ := nonempty_monoidal_adicSheafEquivCondensedMod_functor l X
  obtain ⟨mY⟩ := nonempty_monoidal_adicSheafEquivCondensedMod_functor l Y
  let : EX.functor.Monoidal := mX
  let : EY.functor.Monoidal := mY
  let : EY.inverse.Monoidal := EY.inverseMonoidal
  have : EY.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let Q := (EX.functor.mapHomologicalComplex (.up ℤ)).obj P
  have h₁ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q :=
    EX.functor.kFlat_mapHomologicalComplex_obj_of_isEquivalence hP
  have h₂ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((U.mapHomologicalComplex (.up ℤ)).obj Q) :=
    CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj (Profinite.padicAlgClRingObj l) f h₁
  have h₃ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((EY.inverse.mapHomologicalComplex (.up ℤ)).obj ((U.mapHomologicalComplex (.up ℤ)).obj Q)) :=
    EY.inverse.kFlat_mapHomologicalComplex_obj_of_isEquivalence h₂
  have : EX.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have e₁ : (EY.inverse.mapHomologicalComplex (.up ℤ)).obj
      ((U.mapHomologicalComplex (.up ℤ)).obj Q) ≅
      ((f)^*ᵃ[l].mapHomologicalComplex (.up ℤ)).obj
        ((EX.inverse.mapHomologicalComplex (.up ℤ)).obj Q) :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ EY.inverse)) (.up ℤ)).app Q ≪≫
      (NatIso.mapHomologicalComplex (upperStarCondensedModInverseIso l f) (.up ℤ)).app Q ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (EX.inverse ⋙ (f)^*ᵃ[l]))
        (.up ℤ)).symm.app Q
  have e₂ : (EX.inverse.mapHomologicalComplex (.up ℤ)).obj Q ≅ P :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (EX.functor ⋙ EX.inverse)) (.up ℤ)).app P ≪≫
      (NatIso.mapHomologicalComplex EX.unitIso (.up ℤ)).symm.app P ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P
  exact ObjectProperty.prop_of_iso _ (e₁ ≪≫ ((f)^*ᵃ[l].mapHomologicalComplex (.up ℤ)).mapIso e₂) h₃

/-- The pullback of `ℓ`-adic sheaves along an arbitrary morphism of schemes preserves flat
objects: an object is flat if and only if it is K-flat as a complex concentrated in degree
`0`. -/
instance preservesFlat_adicUpperStar : ((f)^*ᵃ[l]).PreservesFlat where
  flat_obj {M} hM := by
    rw [← CochainComplex.kFlat_single_obj_iff_flat _ 0] at hM ⊢
    exact ObjectProperty.prop_of_iso _
      ((HomologicalComplex.singleMapHomologicalComplex (f)^*ᵃ[l] (.up ℤ) 0).app M)
      (kFlat_adicUpperStar_mapHomologicalComplex_obj l f hM)

end AlgebraicGeometry.ProEtale
