/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.WeilDual

/-!
# The dual of a strict Weil complex

Let `Λ` be a finite coefficient ring, `X` of finite type over a field `k` on which the
exponent of `Λ` is invertible, and `g` an automorphism of `X` (the geometric Frobenius `g_γ`).
For a strict Weil complex `(K, φ_K)` (`AlgebraicGeometry.Etale.WeilComplex`) this file packages
the clauses of blueprint `theorem-poincare-duality-frobenius--2` as statements about strict Weil
complexes:

* `(K^∨, φ_{K^∨})` is a strict Weil complex
  (`AlgebraicGeometry.Etale.WeilComplex.coefficientDual`): `K^∨ = RHom(K, Λ_X)` lies in
  `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.constructibleFiniteTor_coefficientDual`) and its Weil
  structure is the contragredient datum of `theorem-poincare-duality-frobenius--1`
  (`AlgebraicGeometry.Etale.WeilComplex.coefficientDual_frobenius_hom_hom`);
* the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` is a morphism of strict Weil complexes
  (`AlgebraicGeometry.Etale.WeilComplex.coefficientEvaluation`);
* for a strict Weil complex `(T, τ)` (the Tate line `(Λ_X(r), τ_r)`), the twisted dual
  `K^∨ ⊗ᴸ T` with the datum `φ_{K^∨} ⊗ τ` is a strict Weil complex
  (`AlgebraicGeometry.Etale.WeilComplex.twistedCoefficientDual`), and the twisted evaluation
  `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` is a morphism of strict Weil complexes
  (`AlgebraicGeometry.Etale.WeilComplex.twistedEvaluation`).

The unit `Λ_X` with its canonical datum is the strict Weil complex
`AlgebraicGeometry.Etale.WeilComplex.unit`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

omit [Finite Λ] in
/-- The monoidal unit `Λ_X` of `D(X_ét, Λ)` lies in `Dctf(X, Λ)`: it is the constant sheaf
placed in degree `0`, with Tor amplitude in `[0, 0]`. -/
theorem constructibleFiniteTor_unit :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  ⟨(boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0), 0, 0,
    (torAmplitudeIn _ X 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

variable {k : Type u} [Field k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasInvertibleExponent Λ X]

include aX in
/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

The coefficient dual `K^∨ = RHom(K, Λ_X)` of `K ∈ Dctf(X, Λ)` lies in `Dctf(X, Λ)`; for a
perfect `K` it is again perfect
(`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`). -/
theorem constructibleFiniteTor_coefficientDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((coefficientDual _ X).obj (op K)) :=
  constructibleFiniteTor_derivedHom Λ aX hK (constructibleFiniteTor_unit Λ)

namespace WeilComplex

section Coefficients

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [UpperStarPreservesFlat A] {Y : Scheme.{u}} (g : Y ≅ Y)

/-- The unit `Λ_Y` with its canonical datum `φ_Λ : Lg^* Λ_Y ≅ Λ_Y`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`), as a strict Weil complex, for a
coefficient category in which the unit lies in `Dctf(Y, A)`. -/
noncomputable def unitOfConstructibleFiniteTor (h : constructibleFiniteTor A Y (𝟙_ _)) :
    WeilComplex A g where
  obj := ⟨𝟙_ _, h⟩
  frobenius := ObjectProperty.isoMk _ (leftDerivedUpperStarUnitIso A g.hom)

/-- The internal-Hom Frobenius of `(K, φ_K)` and the unit is the contragredient datum `φ_{K^∨}`.
It is stated over an arbitrary coefficient category, in the form of
`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius_hom_hom`, so that its instance at
`ModuleCat Λ` is checked by the kernel without unfolding the derived internal hom. -/
lemma comp_map_unitOfConstructibleFiniteTor_frobenius_hom_hom (K : WeilComplex A g)
    (h : constructibleFiniteTor A Y (𝟙_ _)) :
    leftDerivedUpperStarDerivedHomComparison A g.hom K.obj.obj
        (unitOfConstructibleFiniteTor g h).obj.obj ≫
      (RHom(Y)[A].map K.frobenius.inv.hom.op).app _ ≫
        (RHom(Y)[A].obj (op K.obj.obj)).map (unitOfConstructibleFiniteTor g h).frobenius.hom.hom =
      contragredientWeilDatum A g.hom ((DerivedCategoryFiniteTor.ι A Y).mapIso K.frobenius) :=
  congrArg (leftDerivedUpperStarDerivedHomComparison A g.hom K.obj.obj (𝟙_ _) ≫ ·)
    ((RHom(Y)[A].map K.frobenius.inv.hom.op).naturality
      (leftDerivedUpperStarUnitIso A g.hom).hom).symm

end Coefficients

variable {Λ} (g : X ≅ X)

variable (Λ) in
/-- The unit strict Weil complex: `Λ_X` with its canonical datum `φ_Λ : Lg^* Λ_X ≅ Λ_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`).

It is an instance of `AlgebraicGeometry.Etale.WeilComplex.unitOfConstructibleFiniteTor`, made
over an arbitrary coefficient category, so that no proof nested in its body is abstracted (see
the implementation notes of `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom`). -/
noncomputable def unit : WeilComplex (ModuleCat.{u + 1} Λ) g :=
  unitOfConstructibleFiniteTor g (constructibleFiniteTor_unit Λ)

omit [Finite Λ] [HasInvertibleExponent Λ X] in
lemma unit_frobenius_hom_hom :
    (unit Λ g).frobenius.hom.hom = (leftDerivedUpperStarUnitIso _ g.hom).hom :=
  rfl

variable {g}

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

The *dual strict Weil complex* `(K^∨, φ_{K^∨})` of a strict Weil complex `(K, φ_K)`: the internal
hom `RHom(K, Λ_X)` of strict Weil complexes (`AlgebraicGeometry.Etale.WeilComplex.internalHom`)
into the unit (`AlgebraicGeometry.Etale.WeilComplex.unit`). Its Weil structure is the
contragredient datum of `theorem-poincare-duality-frobenius--1`
(`AlgebraicGeometry.Etale.WeilComplex.coefficientDual_frobenius_hom_hom`). -/
noncomputable def coefficientDual (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    WeilComplex (ModuleCat.{u + 1} Λ) g :=
  ((internalHom g aX).obj (op K)).obj (unit Λ g)

lemma coefficientDual_obj_obj (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (coefficientDual aX K).obj.obj = (DerivedCategory.coefficientDual _ X).obj (op K.obj.obj) :=
  rfl

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

The Weil structure of the dual strict Weil complex is the contragredient datum `φ_{K^∨}`
(`AlgebraicGeometry.Etale.contragredientWeilDatum`) of `theorem-poincare-duality-frobenius--1`: the
datum `φ_{K^∨}` defines a strict Weil complex `(K^∨, φ_{K^∨})`. -/
theorem coefficientDual_frobenius_hom_hom (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (coefficientDual aX K).frobenius.hom.hom =
      contragredientWeilDatum _ g.hom ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius) :=
  (internalHomFrobenius_hom_hom aX K (unit Λ g)).trans
    (comp_map_unitOfConstructibleFiniteTor_frobenius_hom_hom g K (constructibleFiniteTor_unit Λ))

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

**The evaluation is a morphism of strict Weil complexes**: the coefficient evaluation
`ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` (`AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`) is a
morphism from the tensor product (`AlgebraicGeometry.Etale.WeilComplex.tensor`) of `(K, φ_K)`
and `(K^∨, φ_{K^∨})` to the unit strict Weil complex. -/
noncomputable def coefficientEvaluation (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    ((tensor Λ g).obj K).obj (coefficientDual aX K) ⟶ unit Λ g where
  hom := ObjectProperty.homMk (DerivedCategory.coefficientEvaluation K.obj.obj)
  comm := ObjectProperty.hom_ext _ <| by
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, DerivedCategoryFiniteTor.leftDerivedUpperStar_map_hom,
      ObjectProperty.homMk_hom, tensor_obj_obj_frobenius, tensorFrobenius_hom_hom,
      coefficientDual_frobenius_hom_hom, unit_frobenius_hom_hom]
    exact (map_coefficientEvaluation_comp_leftDerivedUpperStarUnitIso_hom _ g.hom
      ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius)).symm

lemma coefficientEvaluation_hom_hom (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (coefficientEvaluation aX K).hom.hom = DerivedCategory.coefficientEvaluation K.obj.obj :=
  rfl

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

The *twisted dual strict Weil complex* `(K^∨ ⊗ᴸ T, φ_{K^∨} ⊗ τ)` of a strict Weil complex
`(K, φ_K)`, for a strict Weil complex `(T, τ)`; for the Tate line `(Λ_X(r), τ_r)` it is
`(K^∨(r), φ_{K^∨(r)})`. Its Weil structure is `φ_{K^∨} ⊗ τ`
(`AlgebraicGeometry.Etale.WeilComplex.twistedCoefficientDual_frobenius_hom_hom`). -/
noncomputable def twistedCoefficientDual (K T : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    WeilComplex (ModuleCat.{u + 1} Λ) g :=
  ((tensor Λ g).obj (coefficientDual aX K)).obj T

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

The Weil structure of the twisted dual `K^∨ ⊗ᴸ T` is the tensor product of the contragredient
datum `φ_{K^∨}` and of `τ`. -/
theorem twistedCoefficientDual_frobenius_hom_hom (K T : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (twistedCoefficientDual aX K T).frobenius.hom.hom =
      (leftDerivedUpperStarTensorIso _ g.hom _ T.obj.obj).hom ≫
        ((derivedTensor _ X).map
          (contragredientWeilDatum _ g.hom ((DerivedCategoryFiniteTor.ι _ X).mapIso
            K.frobenius))).app _ ≫
          ((derivedTensor _ X).obj _).map T.frobenius.hom.hom := by
  refine (tensorFrobenius_hom_hom (coefficientDual aX K) T).trans ?_
  rw [coefficientDual_frobenius_hom_hom]
  rfl

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

**The twisted evaluation is a morphism of strict Weil complexes**: for a strict Weil complex
`(T, τ)` (the Tate line `(Λ_X(r), τ_r)`), the twisted evaluation `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T`
(`AlgebraicGeometry.Etale.twistedEvaluation`) is a morphism from the tensor product of `(K, φ_K)`
and the twisted dual (`AlgebraicGeometry.Etale.WeilComplex.twistedCoefficientDual`) to
`(T, τ)`. -/
noncomputable def twistedEvaluation (K T : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    ((tensor Λ g).obj K).obj (twistedCoefficientDual aX K T) ⟶ T where
  hom := ObjectProperty.homMk (Etale.twistedEvaluation T.obj.obj K.obj.obj)
  comm := ObjectProperty.hom_ext _ <| by
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, DerivedCategoryFiniteTor.leftDerivedUpperStar_map_hom,
      ObjectProperty.homMk_hom, tensor_obj_obj_frobenius, tensorFrobenius_hom_hom,
      twistedCoefficientDual_frobenius_hom_hom]
    exact (map_twistedEvaluation_comp _ g.hom
      ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius) T.frobenius.hom.hom).symm

lemma twistedEvaluation_hom_hom (K T : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (twistedEvaluation aX K T).hom.hom = Etale.twistedEvaluation T.obj.obj K.obj.obj :=
  rfl

end WeilComplex

end Etale

end AlgebraicGeometry
