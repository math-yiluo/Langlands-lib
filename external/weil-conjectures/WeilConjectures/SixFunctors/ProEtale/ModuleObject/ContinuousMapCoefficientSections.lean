/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapSections

/-!
# Global sections of coefficient rings of continuous functions

For a Hausdorff totally disconnected topological ring `T` and a scheme `V`, the global sections of
the coefficient ring object `T_V = p_V^* T̲` are the continuous maps `V → T`
(`AlgebraicGeometry.ProEtale.continuousMapCoefficientSectionRingHom_bijective`): `T_V` is
identified with the sheaf of continuous maps `C(-, T)_V`
(`AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`), whose global sections are the
continuous maps `V → T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section Sections

variable (V : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [T2Space T] [TotallyDisconnectedSpace T]

instance : IsIso (continuousMapComparison V T) :=
  isIso_continuousMapComparison V T

/-- The global sections of `T_V = p_V^* T̲`, for a Hausdorff totally disconnected topological ring
`T`, given by continuous maps `V → T`: the global section of `C(-, T)_V` given by a continuous map,
transported along `ψ_V⁻¹ : C(-, T)_V ≅ T_V`. -/
noncomputable def continuousMapCoefficientSectionRingHom :
    C(V, T) →+* Γ (condensedRingObj (Profinite.continuousMapRingObj.{u} T) V) :=
  (Γ.map (inv (continuousMapComparison V T))).comp (continuousMapSectionRingHom V T)

/-- **The global sections of `T_V` are the continuous maps `V → T`.** -/
lemma continuousMapCoefficientSectionRingHom_bijective :
    Function.Bijective (continuousMapCoefficientSectionRingHom V T) := by
  rw [continuousMapCoefficientSectionRingHom, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ (continuousMapSectionRingHom_bijective V T)
  refine Function.bijective_iff_has_inverse.2 ⟨Γ.map (continuousMapComparison V T), fun s ↦ ?_,
    fun s ↦ ?_⟩ <;> exact Γ.ext (by simp)

lemma continuousMapCoefficientSectionRingHom_hom (f : C(V, T)) :
    (continuousMapCoefficientSectionRingHom V T f).hom =
      (continuousMapSectionRingHom V T f).hom ≫ inv (continuousMapComparison V T) :=
  Γ.map_hom _ _

end Sections

end AlgebraicGeometry.ProEtale
