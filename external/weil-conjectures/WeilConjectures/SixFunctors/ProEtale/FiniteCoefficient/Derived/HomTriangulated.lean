/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Exactness of the derived hom of pro-étale sheaves

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated`
and `WeilConjectures.SixFunctors.Etale.Derived.HomShift`. The derived hom
`RHom(-, -)` on `D(X_proét)` is exact in each variable, and turns shifts in the first variable
into opposite shifts: `RHom(K⟦a⟧, M) ≅ RHom(K, M)⟦-a⟧`.

## Main statements

- `AlgebraicGeometry.ProEtale.exists_distTriang_derivedHom_left`,
  `AlgebraicGeometry.ProEtale.exists_distTriang_derivedHom_right`: `RHom` sends distinguished
  triangles in either variable to distinguished triangles (blueprint
  `definition-verdier-dual-evaluation--3` on the pro-étale site).
- `AlgebraicGeometry.ProEtale.derivedHomShiftIso`: `RHom(K⟦a⟧, -) ≅ RHom(K, -)⟦-a⟧`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

/-- Tensoring on the left with a fixed complex, `M ↦ K ⊗ᴸ M`, commutes with shifts. -/
noncomputable instance commShiftDerivedTensorObj
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((-⊗ᴸ-(X)[A]).obj K).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).obj K).CommShift ℤ)

/-- Tensoring on the right with a fixed complex, `K ↦ K ⊗ᴸ M`, commutes with shifts. -/
noncomputable instance commShiftDerivedTensorFlipObj
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((-⊗ᴸ-(X)[A]).flip.obj M).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).flip.obj M).CommShift
      ℤ)

/-- The derived hom `RHom(K, -)` commutes with shifts, being right adjoint to `K ⊗ᴸ -`. -/
noncomputable instance commShiftDerivedHomObj
    (K : (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ) :
    ((RHom(X)[A]).obj K).CommShift ℤ :=
  (derivedTensorHomAdjunction A K.unop).rightAdjointCommShift ℤ

/-- The adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` commutes with shifts. -/
instance commShift_derivedTensorHomAdjunction
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (derivedTensorHomAdjunction A K).CommShift ℤ :=
  (derivedTensorHomAdjunction A K).commShift_of_leftAdjoint ℤ

/-- The functor `K ⊗ᴸ -` is triangulated. -/
instance isTriangulated_derivedTensorObj
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((-⊗ᴸ-(X)[A]).obj K).IsTriangulated :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).obj K).IsTriangulated)

/-- Blueprint `definition-verdier-dual-evaluation--3` on the pro-étale site, first variable: for a
distinguished triangle `K' ⟶ K ⟶ K'' ⟶ K'[1]` of `D(X_proét)` and any `M`, the maps
`RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M)` extend to a distinguished triangle. -/
theorem exists_distTriang_derivedHom_left
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (T : Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk (((RHom(X)[A]).map T.mor₂.op).app M)
      (((RHom(X)[A]).map T.mor₁.op).app M) w ∈ distTriang _ := by
  -- the graded tensor products of `DerivedCategory.exists_distinguished_ihom_pre` need countable
  -- colimits, obtained by shrinking those of the Grothendieck abelian category of sheaves
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (Scheme.ProEt.topology X) A) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X) A) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  exact DerivedCategory.exists_distinguished_ihom_pre T hT M

/-- Blueprint `definition-verdier-dual-evaluation--3` on the pro-étale site, second variable: the
functor `RHom(K, -)` is triangulated, being right adjoint to the triangulated functor `K ⊗ᴸ -`. -/
theorem exists_distTriang_derivedHom_right
    (K : (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ)
    (T : Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk (((RHom(X)[A]).obj K).map T.mor₁)
      (((RHom(X)[A]).obj K).map T.mor₂) w ∈ distTriang _ := by
  have := (derivedTensorHomAdjunction A K.unop).isTriangulated_rightAdjoint
  exact ⟨_, ((RHom(X)[A]).obj K).map_distinguished T hT⟩

/-- Tensoring with a shifted complex on the left shifts the tensor product,
`K⟦a⟧ ⊗ᴸ M ≅ (K ⊗ᴸ M)⟦a⟧`, naturally in `M`: the derived tensor product commutes with shifts
as a bifunctor (`DerivedCategory.commShift₂CurriedTensor`). -/
noncomputable def derivedTensorObjShiftIso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (a : ℤ) :
    (-⊗ᴸ-(X)[A]).obj (K⟦a⟧) ≅ (-⊗ᴸ-(X)[A]).obj K ⋙ shiftFunctor _ a :=
  NatIso.ofComponents (fun M ↦ (((-⊗ᴸ-(X)[A]).flip.obj M).commShiftIso a).app K)
    (fun f ↦
      have : NatTrans.CommShift ((-⊗ᴸ-(X)[A]).flip.map f) ℤ :=
        Functor.CommShift₂.commShift_flip_map (h := .int)
          (G := curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) f
      (NatTrans.shift_app_comm ((-⊗ᴸ-(X)[A]).flip.map f) a K).symm)

/-- The derived hom out of a shifted complex is the shifted derived hom,
`RHom(K⟦a⟧, -) ≅ RHom(K, -)⟦-a⟧`: both are right adjoint to `K⟦a⟧ ⊗ᴸ - ≅ K ⊗ᴸ (-)⟦a⟧`. -/
noncomputable def derivedHomShiftIso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (a : ℤ) :
    (RHom(X)[A]).obj (op (K⟦a⟧)) ≅ (RHom(X)[A]).obj (op K) ⋙ shiftFunctor _ (-a) :=
  (derivedTensorHomAdjunction A (K⟦a⟧)).rightAdjointUniq
    (((shiftEquiv _ a).toAdjunction.comp (derivedTensorHomAdjunction A K)).ofNatIsoLeft
      (((-⊗ᴸ-(X)[A]).obj K).commShiftIso a ≪≫ (derivedTensorObjShiftIso A K a).symm))

end AlgebraicGeometry.ProEtale
