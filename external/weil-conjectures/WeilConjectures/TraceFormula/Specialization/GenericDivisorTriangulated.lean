/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!

# The complexes with vanishing defect form a triangulated subcategory

Let `ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)` be the zero-section map and `C_{X,Z}(L)`
the defect of the specialization (`ProEtale.CondensedRing.zeroSectionMap`,
`ProEtale.CondensedRing.specializationDefect`). Since `ε_{X,Z}` is the component of the pullback
exchange, a natural transformation between triangulated functors commuting with the shifts
(`ProEtale.CondensedRing.NearbyCyclesModel.Hom.commShift_pullbackExchange`), the complexes `L`
with vanishing defect, i.e. on which `ε_{X,Z}(L)` is an isomorphism, form a triangulated
subcategory of the derived category on `X`: they are stable under the shifts and satisfy the
two-out-of-three property in distinguished triangles.

## Main results

- `ProEtale.CondensedRing.isIso_zeroSectionMap_shift_iff`,
  `ProEtale.CondensedRing.isZero_specializationDefect_shift_iff`: invariance under the shifts.
- `ProEtale.CondensedRing.isIso_zeroSectionMap_of_distTriang` (and its variants
  `isIso_zeroSectionMap_obj₁_of_distTriang`, `isIso_zeroSectionMap_obj₃_of_distTriang`), and
  `ProEtale.CondensedRing.isZero_specializationDefect_of_distTriang`: two-out-of-three in
  distinguished triangles.
- `ProEtale.CondensedRing.vanishingDefect`: the object property of vanishing defect, which is a
  triangulated subcategory (`ProEtale.CondensedRing.isTriangulated_vanishingDefect`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The zero-section map is invertible at a shift `L⟦n⟧` if and only if it is invertible at
`L`. -/
theorem isIso_zeroSectionMap_shift_iff
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) (n : ℤ) :
    IsIso (zeroSectionMap X I k' Λ (L⟦n⟧)) ↔ IsIso (zeroSectionMap X I k' Λ L) :=
  NatTrans.isIso_app_shift_iff ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ) L n

/-- The defect vanishes at a shift `L⟦n⟧` if and only if it vanishes at `L`. -/
theorem isZero_specializationDefect_shift_iff
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) (n : ℤ) :
    IsZero (specializationDefect X I k' Λ (L⟦n⟧)) ↔ IsZero (specializationDefect X I k' Λ L) := by
  rw [isZero_specializationDefect_iff, isZero_specializationDefect_iff,
    isIso_zeroSectionMap_shift_iff]

section Triangle

variable {T : Triangle (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj Λ X.left)))}

/-- Two-out-of-three for the zero-section map: if it is invertible at the first and third
objects of a distinguished triangle, it is invertible at the second. -/
theorem isIso_zeroSectionMap_of_distTriang (hT : T ∈ distTriang _)
    (h₁ : IsIso (zeroSectionMap X I k' Λ T.obj₁))
    (h₃ : IsIso (zeroSectionMap X I k' Λ T.obj₃)) : IsIso (zeroSectionMap X I k' Λ T.obj₂) :=
  NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃
    ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ) hT h₁ h₃

/-- Two-out-of-three for the zero-section map: if it is invertible at the second and third
objects of a distinguished triangle, it is invertible at the first. -/
theorem isIso_zeroSectionMap_obj₁_of_distTriang (hT : T ∈ distTriang _)
    (h₂ : IsIso (zeroSectionMap X I k' Λ T.obj₂))
    (h₃ : IsIso (zeroSectionMap X I k' Λ T.obj₃)) : IsIso (zeroSectionMap X I k' Λ T.obj₁) :=
  NatTrans.isIso_app_obj₁_of_isIso_app_obj₂₃
    ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ) hT h₂ h₃

/-- Two-out-of-three for the zero-section map: if it is invertible at the first and second
objects of a distinguished triangle, it is invertible at the third. -/
theorem isIso_zeroSectionMap_obj₃_of_distTriang (hT : T ∈ distTriang _)
    (h₁ : IsIso (zeroSectionMap X I k' Λ T.obj₁))
    (h₂ : IsIso (zeroSectionMap X I k' Λ T.obj₂)) : IsIso (zeroSectionMap X I k' Λ T.obj₃) :=
  NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂
    ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ) hT h₁ h₂

/-- The defect is closed under extensions: if it vanishes at the first and third objects of a
distinguished triangle, it vanishes at the second. -/
theorem isZero_specializationDefect_of_distTriang (hT : T ∈ distTriang _)
    (h₁ : IsZero (specializationDefect X I k' Λ T.obj₁))
    (h₃ : IsZero (specializationDefect X I k' Λ T.obj₃)) :
    IsZero (specializationDefect X I k' Λ T.obj₂) := by
  rw [isZero_specializationDefect_iff] at h₁ h₃ ⊢
  exact isIso_zeroSectionMap_of_distTriang X I k' Λ hT h₁ h₃

end Triangle

/-- The complexes `L` on `X` whose defect `C_{X,Z}(L)` vanishes. -/
def vanishingDefect :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :=
  fun L ↦ IsZero (specializationDefect X I k' Λ L)

/-- The defect vanishes exactly where the pullback exchange along `ẽ`, i.e. the zero-section
map, is invertible. -/
lemma vanishingDefect_eq_isoLocus :
    vanishingDefect X I k' Λ =
      ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ).isoLocus :=
  funext fun L ↦ propext (isZero_specializationDefect_iff X I k' Λ L)

/-- The complexes with vanishing defect form a triangulated subcategory. -/
instance isTriangulated_vanishingDefect : (vanishingDefect X I k' Λ).IsTriangulated := by
  rw [vanishingDefect_eq_isoLocus]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
