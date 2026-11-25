/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Monoidal

/-!
# The reduction of the unit

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`), the composite
`K ↦ Rν_* Φ (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`. This file proves that `red_X` sends the monoidal unit `𝒪_E` to the
monoidal unit, the constant étale sheaf `𝒪_E ⧸ ℓⁿ`
(`ProEtale.CondensedRing.etaleReductionUnitIso`), one factor at a time:

* the derived reduction `- ⊗ᴸ 𝒪_E ⧸ ℓⁿ` is monoidal
  (`CategoryTheory.Functor.leftDerivedFunctorMonoidal`);
* the comparison `Φ` of the two finite-coefficient models preserves the unit
  (`ProEtale.finiteCoefficientDerivedEquivalenceUnitIso`), as the underlying equivalence of
  abelian categories does (`ProEtale.finiteCoefficientModEquivalenceUnitIso`, through
  `CategoryTheory.Sheaf.modToSheafModuleUnitIso`);
* `Rν_*` preserves the unit (`ProEtale.rightDerivedComparisonLowerStarUnitIso`): the unit is
  `ν^*` of the étale unit, and `Rν_* ν^* ≅ id` on bounded below complexes.

## Main definitions

- `ProEtale.CondensedRing.etaleReductionUnitIso`: `red_X (𝟙_) ≅ 𝟙_`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Presheaf

variable {C : Type (u + 1)} [Category.{u} C] (T : Type (u + 1)) [CommRing T]

/-- The presheaf of `T`-modules underlying the unit module object (the constant ring presheaf
`T` itself) is the unit presheaf of `T`-modules: both have the sections `T`, with `T` acting by
multiplication. -/
noncomputable def modToModuleUnitIso :
    (modToModule T).obj (𝟙_ (Mod (Cᵒᵖ ⥤ Ab.{u + 1}) (constRingObj (C := C) T))) ≅
      𝟙_ (Cᵒᵖ ⥤ ModuleCat.{u + 1} T) :=
  NatIso.ofComponents (fun _ ↦ LinearEquiv.toModuleIso
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) fun _ ↦ rfl

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (T : Type (u + 1)) [CommRing T]

/-- The equivalence `modToSheafModule` sends the unit module object over the constant ring sheaf
`T` to the unit sheaf of `T`-modules: the unit module object is the sheafification of the unit
presheaf of `T`-modules (`Functor.mapModUnitIso`, `Presheaf.modToModuleUnitIso`), and
`modToSheafModule` of a sheafification is the sheafification (`sheafifyModuleCompIso`), which is
monoidal. -/
noncomputable def modToSheafModuleUnitIso :
    (modToSheafModule J T).obj (𝟙_ _) ≅ 𝟙_ (Sheaf J (ModuleCat.{u + 1} T)) :=
  (modToSheafModule J T).mapIso
      ((presheafToSheaf J Ab.{u + 1}).mapModUnitIso (R := Presheaf.constRingObj T) ≪≫
        ((presheafToSheaf J Ab.{u + 1}).mapMod (Presheaf.constRingObj T)).mapIso
          ((Presheaf.modConstRingEquivalence C T).unitIso.app _ ≪≫
            (Presheaf.moduleToMod T).mapIso (Presheaf.modToModuleUnitIso T))) ≪≫
    (sheafifyModuleCompIso J T).app _ ≪≫
    (Functor.Monoidal.εIso (presheafToSheaf J (ModuleCat.{u + 1} T))).symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

section FiniteCoefficient

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The equivalence `finiteCoefficientModEquivalence` between module objects over the condensed
ring `T̲_X` and pro-étale sheaves of `T`-modules preserves the monoidal units: restriction of
scalars along `T_X ≅ T̲_X` does (`Mod.comapUnitIso`), and so does `Sheaf.modToSheafModule`
(`CategoryTheory.Sheaf.modToSheafModuleUnitIso`). -/
noncomputable def finiteCoefficientModEquivalenceUnitIso :
    (finiteCoefficientModEquivalence X T).functor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (Sheaf.modToSheafModule _ _).mapIso
      (Mod.comapUnitIso (constRingSheafToCondensedRingObj X T)).symm ≪≫
    Sheaf.modToSheafModuleUnitIso _ _

/-- The derived equivalence `finiteCoefficientDerivedEquivalence` preserves the monoidal units:
both units are the abelian units placed in degree `0`, and the underlying equivalence preserves
the units (`finiteCoefficientModEquivalenceUnitIso`). -/
noncomputable def finiteCoefficientDerivedEquivalenceUnitIso :
    (finiteCoefficientDerivedEquivalence X T).functor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (finiteCoefficientDerivedEquivalence X T).functor.mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (finiteCoefficientModEquivalenceUnitIso X T) ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

end FiniteCoefficient

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **The reduction of the unit is the unit**: `red_Y (𝒪_E) ≅ 𝒪_E ⧸ ℓⁿ`, the constant étale
sheaf. Each factor of `red_Y = Rν_* ∘ Φ ∘ (- ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` preserves the unit: the derived
reduction is monoidal (`Functor.leftDerivedFunctorMonoidal`), and see
`finiteCoefficientDerivedEquivalenceUnitIso` and `rightDerivedComparisonLowerStarUnitIso`. -/
noncomputable def etaleReductionUnitIso (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    (etaleReduction ℓ E n Y).obj (𝟙_ _) ≅ 𝟙_ _ :=
  letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E n)
  letI := (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctorMonoidal
  (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).mapIso
      ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).app (𝟙_ _) ≪≫
          (Functor.Monoidal.εIso _).symm) ≪≫
        finiteCoefficientDerivedEquivalenceUnitIso _ _) ≪≫
    rightDerivedComparisonLowerStarUnitIso _ _

end CondensedRing

end AlgebraicGeometry.ProEtale
