/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# The map `RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)` commutes with shifts in `T`

For `K, M ∈ D(X_ét)` the canonical maps
`RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)` (`AlgebraicGeometry.Etale.DerivedCategory.derivedHomTensorMap`)
form a natural transformation in `T`
(`AlgebraicGeometry.Etale.DerivedCategory.derivedHomTensorNatTrans`) between triangulated
functors, and this natural transformation commutes with the shifts
(`AlgebraicGeometry.Etale.DerivedCategory.commShift_derivedHomTensorNatTrans`). It is the composite
of the unit of `K ⊗ᴸ - ⊣ RHom(K, -)`, the inverse associator and the evaluation, each of which
commutes with the shifts.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalCategory

instance isIso_associatorNatTrans₃ (D : Type*) [Category* D] [MonoidalCategory D] (X Y : D) :
    IsIso (associatorNatTrans₃ D X Y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  rw [associatorNatTrans₃_app]
  infer_instance

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale.DerivedCategory

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

/-- The canonical maps `RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)`
(`AlgebraicGeometry.Etale.DerivedCategory.derivedHomTensorMap`), as a natural transformation in
`T`: the unit of `K ⊗ᴸ - ⊣ RHom(K, -)` followed by `RHom(K, -)` applied to the inverse
associator and the evaluation. -/
noncomputable def derivedHomTensorNatTrans
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (-⊗ᴸ-(X)[A]).obj ((RHom(X)[A].obj (op K)).obj M) ⟶
      (-⊗ᴸ-(X)[A]).obj M ⋙ RHom(X)[A].obj (op K) :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ (derivedTensorHomAdjunction A K).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (inv (associatorNatTrans₃ _ K ((RHom(X)[A].obj (op K)).obj M)) ≫
        (-⊗ᴸ-(X)[A]).map ((derivedTensorHomAdjunction A K).counit.app M : _ ⟶ M))
      (RHom(X)[A].obj (op K))

lemma derivedHomTensorNatTrans_app (K M T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedHomTensorNatTrans K M).app T = derivedHomTensorMap K M T := by
  rw [derivedHomTensorMap, MonoidalClosed.ihomTensorToIhom, MonoidalClosed.curry_eq]
  simp [derivedHomTensorNatTrans]
  rfl

attribute [local instance] Sheaf.monoidalCategory in
/-- The canonical maps `RHom(K, M) ⊗ᴸ T ⟶ RHom(K, M ⊗ᴸ T)` commute with the shifts in `T`. -/
instance commShift_derivedHomTensorNatTrans
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (derivedHomTensorNatTrans K M) ℤ := by
  have := NatTrans.CommShift.of_isIso
    (associatorNatTrans₃ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) K
      ((RHom(X)[A].obj (op K)).obj M)) ℤ
  unfold derivedHomTensorNatTrans
  infer_instance

/-- The derived hom `RHom(K, -)` is triangulated, being right adjoint to the triangulated
functor `K ⊗ᴸ -`. -/
instance isTriangulated_derivedHom_obj
    (K : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ) :
    (RHom(X)[A].obj K).IsTriangulated :=
  (derivedTensorHomAdjunction A K.unop).isTriangulated_rightAdjoint

end Etale.DerivedCategory

end AlgebraicGeometry
