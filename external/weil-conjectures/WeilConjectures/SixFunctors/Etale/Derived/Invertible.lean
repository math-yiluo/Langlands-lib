/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Flat and invertible sheaves in the derived category

Let `L` be a flat `A`-valued étale sheaf on a scheme `X`, placed in degree zero in `D(X_ét)`.
Its derived tensor product with any sheaf `F` in degree zero is the underived tensor product
`L ⊗ F` in degree zero, because the complex `L[0]` is K-flat.

If `L` moreover has a tensor inverse `L'` — as a lisse sheaf of rank one does — then `L` and
`L'` are flat (`CategoryTheory.ObjectProperty.flat_of_tensorIso`), so `L[0] ⊗ᴸ L'[0]` is
`(L ⊗ L')[0] ≅ 𝟙[0]`, the unit of `D(X_ét)`, and `L[0]` is dualizable.

## Main definitions

- `AlgebraicGeometry.Etale.singleFunctorObjUnitIso`: the monoidal unit of `D(X_ét)` is the unit
  sheaf in degree zero.
- `AlgebraicGeometry.Etale.singleFunctorObjTensorIso`: `L[0] ⊗ᴸ F[0] ≅ (L ⊗ F)[0]` for a flat
  sheaf `L`.

## Main statements

- `AlgebraicGeometry.Etale.isDualizable_singleFunctor_obj_of_tensorIso`: a sheaf with a
  tensor inverse, placed in degree zero, is dualizable.

-/

@[expose] public section

open CategoryTheory Abelian Limits MonoidalCategory

universe u' u

namespace AlgebraicGeometry.Etale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

open Functor.LaxMonoidal in
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(X_ét) ⥤ D(X_ét)` is an
isomorphism when `K` is K-flat. The case of a K-flat `M` is
`AlgebraicGeometry.Etale.isIso_μNatTrans_Qh_app_app_of_kFlat`. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat_left
    (K M : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ))
    (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
    IsIso (((μNatTrans (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A))).app K).app
      M) := by
  have : (-⊗ᴸ-(X)[A]).IsLeftDerivedFunctor₂ (μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_derivedTensor A X
  exact (MorphismProperty.kFlat_prod_id_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ))
      DerivedCategory.Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(X)[A])
        (μNatTrans DerivedCategory.Qh) ⟨K, hK⟩ M

/-- A sheaf `F` placed in degree zero in `D(X_ét)` is the image under `Qh : K(X_ét) ⥤ D(X_ét)`
of the complex `F[0]`. -/
noncomputable def singleFunctorObjIsoQh (F : Sheaf X.smallEtaleTopology A) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A)
        (.up ℤ)).obj
          ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj F)) :=
  (DerivedCategory.singleFunctorIsoCompQ (Sheaf X.smallEtaleTopology A) 0).app F ≪≫
    (DerivedCategory.quotientCompQhIso (Sheaf X.smallEtaleTopology A)).symm.app _

variable (A X) in
/-- The monoidal unit of `D(X_ét)` is the unit sheaf placed in degree zero: the unit of the
derived monoidal structure is `Qh` of the unit complex `𝟙[0]`. -/
noncomputable def singleFunctorObjUnitIso :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj (𝟙_ _) ≅
      𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  have := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology A)
  singleFunctorObjIsoQh (𝟙_ _) ≪≫
    DerivedCategory.Qh.mapIso
      ((Functor.Monoidal.εIso (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A)
        (.up ℤ))).symm :
        (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
          (𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)) ≅ _) ≪≫
    (asIso (Functor.LaxMonoidal.ε DerivedCategory.Qh)).symm

open Functor.LaxMonoidal in
/-- For a flat sheaf `L` and any sheaf `F`, the derived tensor product of `L` and `F` placed in
degree zero is their tensor product placed in degree zero: `L[0]` is K-flat, so
`L[0] ⊗ᴸ F[0]` is computed by the tensor product of complexes `L[0] ⊗ F[0] = (L ⊗ F)[0]`. -/
noncomputable def singleFunctorObjTensorIso (L F : Sheaf X.smallEtaleTopology A)
    (hL : ObjectProperty.flat L) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj L ⊗
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj (L ⊗ F) :=
  have hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
        ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj L)) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hL)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat_left _
    ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
      ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj F)) hK
  tensorIso (singleFunctorObjIsoQh L) (singleFunctorObjIsoQh F) ≪≫
    asIso (((μNatTrans (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A))).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
        ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj L))).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
        ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj F))) ≪≫
    DerivedCategory.Qh.mapIso (Functor.Monoidal.μIso
      (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)) _ _) ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A)
      (.up ℤ)).mapIso (((CochainComplex.map₂HomologicalComplexObjSingleIso
        (curriedTensor _) L).app _) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app F))) ≪≫
    (singleFunctorObjIsoQh (L ⊗ F)).symm

/-- A sheaf `L` with a tensor inverse `L'`, placed in degree zero, is dualizable in `D(X_ét)`:
both are flat, so `L[0] ⊗ᴸ L'[0] ≅ (L ⊗ L')[0] ≅ 𝟙[0]`, and symmetrically using the braiding. -/
theorem isDualizable_singleFunctor_obj_of_tensorIso {L L' : Sheaf X.smallEtaleTopology A}
    (e : L ⊗ L' ≅ 𝟙_ _) :
    IsDualizable ((_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj L) :=
  isDualizable_of_tensorIso
    (singleFunctorObjTensorIso L L' (ObjectProperty.flat_of_tensorIso e) ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e ≪≫ singleFunctorObjUnitIso A X)
    (singleFunctorObjTensorIso L' L (ObjectProperty.flat_of_tensorIso (β_ L' L ≪≫ e)) ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (β_ L' L ≪≫ e) ≪≫
      singleFunctorObjUnitIso A X)

end AlgebraicGeometry.Etale
