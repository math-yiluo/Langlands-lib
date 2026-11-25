/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat

/-!
# The derived tensor product with a K-flat complex, and vanishing

- `AlgebraicGeometry.Etale.isIso_μNatTrans_Qh_app_app_of_kFlat`: `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)`
  is an isomorphism when `M` is K-flat.
- `AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_left` and
  `AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_right`: `K ⊗ᴸ M` vanishes
  when `K` or `M` does.

See `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal` for an overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
section

open _root_.DerivedCategory Functor.LaxMonoidal

variable {A} in
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(X_ét) ⥤ D(X_ét)` is an
isomorphism when `M` is K-flat. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat {X : Scheme.{u}}
    (K M : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((μNatTrans (Qh (C := Sheaf X.smallEtaleTopology A))).app K).app M) := by
  -- Instance search does not find this instance through `-⊗ᴸ-(X)[A]`.
  have : (-⊗ᴸ-(X)[A]).IsLeftDerivedFunctor₂ (μNatTrans Qh)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_derivedTensor A X
  exact (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ))
      Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(X)[A]) (μNatTrans Qh) K ⟨_, hM⟩

section

open _root_.DerivedCategory ZeroObject

variable {A} in
/-- The derived tensor product `K ⊗ᴸ M` vanishes when `K` does. -/
lemma isZero_derivedTensor_obj_obj_of_isZero_left {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsZero K)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  -- Write `M ≅ Qh M₀` with `M₀` K-flat and `K ≅ Qh 0`; then `K ⊗ᴸ M ≅ Qh (0 ⊗ M₀) = 0`.
  let R : (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A)
      (.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage M) :=
    Classical.arbitrary _
  let eM : Qh.obj R.X₁.obj ≅ M :=
    Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ)) R.w R.hw ≪≫
      Qh.objObjPreimageIso M
  let Z : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ) :=
    (HomotopyCategory.quotient _ _).obj 0
  have hZ : IsZero Z := Functor.map_isZero _ (isZero_zero _)
  have hZM : IsZero (Z ⊗ R.X₁.obj) := by
    refine IsZero.of_iso ?_
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) 0 R.X₁.obj.as).symm
    have h :
        IsZero ((0 : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) ⊗ R.X₁.obj.as) := by
      rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, (isZero_zero _).eq_of_src (𝟙 _) 0,
        MonoidalPreadditive.zero_whiskerRight]
    exact Functor.map_isZero (HomotopyCategory.quotient _ _) h
  have := isIso_μNatTrans_Qh_app_app_of_kFlat Z R.X₁.obj R.X₁.property
  refine (Functor.map_isZero Qh hZM).of_iso ?_
  exact ((-⊗ᴸ-(X)[A]).mapIso (hK.iso (Functor.map_isZero Qh hZ))).app M ≪≫
    ((-⊗ᴸ-(X)[A]).obj _).mapIso eM.symm ≪≫
    asIso (((Functor.LaxMonoidal.μNatTrans Qh).app Z).app R.X₁.obj)

variable {A} in
/-- The derived tensor product `K ⊗ᴸ M` vanishes when `M` does. -/
lemma isZero_derivedTensor_obj_obj_of_isZero_right {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hM : IsZero M) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  MonoidalCategory.isZero_tensorObj_of_isZero_right K hM

end

end

end Etale

end AlgebraicGeometry
