/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTrace

/-!
# Split units of `Lg^* ⊣ Rg_*` from a trace of nonzero degree, for `ℚ̲̄_ℓ`-coefficients

The category of `ℚ̲̄_ℓ`-module objects on `X` is linear over the characteristic zero field `ℚ̄_ℓ`
(`ProEtale.CondensedRing.modLinear`), so multiplication by a nonzero integer is an isomorphism
on every module object (`ProEtale.CondensedRing.isIso_nsmul_id_padicAlgClRingObj`). Hence a trace
`r : g^* ⋙ g_* ⟶ 𝟭` along a finite morphism `g` of finite presentation whose composite with the
unit is multiplication by a nonzero integer `d` (classically the degree of a finite étale `g`)
splits the unit of the derived adjunction `Lg^* ⊣ Rg_*` at every complex
(`ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_nsmul`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Multiplication by a nonzero natural number is an isomorphism on every `ℚ̲̄_ℓ`-module object:
its inverse is the action of `d⁻¹ ∈ ℚ̄_ℓ`. -/
theorem isIso_nsmul_id_padicAlgClRingObj (X : Scheme.{u}) {d : ℕ} (hd : d ≠ 0)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :
    IsIso (d • 𝟙 M) := by
  let _ := modLinear _ (Profinite.PadicAlgCl.constRingHom.{u} ℓ) X
  have hd' : (d : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [← Nat.cast_smul_eq_nsmul (PadicAlgCl ℓ)]
  refine ⟨((d : PadicAlgCl ℓ)⁻¹ • 𝟙 M), ?_, ?_⟩
  · rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_inv_cancel₀ hd',
      one_smul]
  · rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, inv_mul_cancel₀ hd',
      one_smul]

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] [LocallyOfFinitePresentation g]

/-- **Split derived units from a trace of nonzero degree**, for `ℚ̲̄_ℓ`-coefficients: let `g` be
finite of finite presentation. If there is a trace `r : g^* ⋙ g_* ⟶ 𝟭` on module objects whose
composite with the unit of `g^* ⊣ g_*` is multiplication by a nonzero integer `d`, then the unit
of the derived adjunction `Lg^* ⊣ Rg_*` is a split monomorphism at every complex. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_nsmul
    (r : (g)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (g)_*⟦Profinite.padicAlgClRingObj ℓ⟧ ⟶ 𝟭 _)
    {d : ℕ} (hd : d ≠ 0)
    (hr : (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) g).unit ≫ r = d • 𝟙 _)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      g).unit.app G) := by
  have : IsIso ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) g).unit ≫ r) := by
    have (M : _) : IsIso (((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        g).unit ≫ r).app M) := by
      rw [hr, NatTrans.app_nsmul, NatTrans.id_app]
      exact isIso_nsmul_id_padicAlgClRingObj ℓ X hd M
    exact NatIso.isIso_of_isIso_app _
  exact isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_trace _ g r G

end AlgebraicGeometry.ProEtale.CondensedRing
