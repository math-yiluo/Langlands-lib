/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-!
# The endomorphisms of the unit of `Mod_{Spec Ω}` are `ℚ̄_ℓ`

Let `Ω` be a separably closed field and `Mod_{Spec Ω}` the category of `ℚ̲̄_ℓ`-modules on the
pro-étale site of `Spec Ω`, in which the stalks of `ℚ̄_ℓ`-sheaves at geometric points live and the
categorical traces of the trace formula take values. The ring `End (𝟙_ Mod_{Spec Ω})` is the
field `ℚ̄_ℓ`: the constants `ℚ̄_ℓ` map onto the endomorphisms of the regular condensed module
`ℚ̲̄_ℓ` (`Profinite.PadicAlgCl.constRingHom_surjective`), injectively since `ℚ̄_ℓ` is a field and
`𝟙 ≠ 0`, and the pullback `p^*` from condensed `ℚ̲̄_ℓ`-modules to `Mod_{Spec Ω}` is an
equivalence (`ProEtale.CondensedRing.isEquivalence_upperStarFromPointMod`) sending the regular
module to the unit.

## Main definitions

- `Profinite.PadicAlgCl.endRegularRingEquiv`: `ℚ̄_ℓ ≃+* End ℚ̲̄_ℓ`.
- `AlgebraicGeometry.ProEtale.CondensedRing.endTensorUnitRingEquiv`:
  `End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace Profinite.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The endomorphisms of the regular condensed module `ℚ̲̄_ℓ` are the multiplications by the
constants `ℚ̄_ℓ`. -/
noncomputable def endRegularRingEquiv :
    _root_.PadicAlgCl ℓ ≃+* End (Mod.regular (padicAlgClRingObj.{u} ℓ)) :=
  haveI : Nontrivial (End (Mod.regular (padicAlgClRingObj.{u} ℓ))) :=
    nontrivial_of_ne _ _ (one_ne_zero_end_regular ℓ)
  RingEquiv.ofBijective (Mod.regularEndRingHom.comp (constRingHom.{u} ℓ))
    ⟨(Mod.regularEndRingHom.comp (constRingHom.{u} ℓ)).injective,
      Mod.regularEndRingHom_surjective.comp (constRingHom_surjective ℓ)⟩

end Profinite.PadicAlgCl

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **The endomorphisms of the unit of `Mod_{Spec Ω}` form the field `ℚ̄_ℓ`**, for a separably
closed field `Ω`: the equivalence `p^*` from condensed `ℚ̲̄_ℓ`-modules sends the regular module,
whose endomorphisms are the constants `ℚ̄_ℓ`, to the unit. -/
noncomputable def endTensorUnitRingEquiv :
    End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))) ≃+*
      _root_.PadicAlgCl ℓ :=
  haveI := (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ)
    (Spec (.of Ω))).additive_of_preserves_binary_products
  let φ : End (Mod.regular (Profinite.padicAlgClRingObj ℓ)) →+*
      End ((upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))).obj
        (Mod.regular (Profinite.padicAlgClRingObj ℓ))) :=
    (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))).mapEndRingHom _
  (RingEquiv.ofBijective (R := End (Mod.regular (Profinite.padicAlgClRingObj ℓ)))
      (S := End ((upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))).obj
        (Mod.regular (Profinite.padicAlgClRingObj ℓ)))) φ
    ⟨fun _ _ h ↦ End.ext ((upperStarFromPointMod _ _).map_injective congr($(h).asHom)),
      fun t ↦ by
        obtain ⟨s, hs⟩ := (upperStarFromPointMod _ _).map_surjective t.asHom
        exact ⟨.of s, End.ext hs⟩⟩).symm.trans
    (Profinite.PadicAlgCl.endRegularRingEquiv ℓ).symm

end AlgebraicGeometry.ProEtale.CondensedRing
