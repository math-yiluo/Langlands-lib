/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris

/-!
# Extension by zero along an open immersion with closed range

For an open immersion `j : U ⟶ X` whose range is closed, the comparison `j_! ⟶ j_*` of
`ℓ`-adic sheaves is an isomorphism.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range`:
  `j_! ⟶ j_*` is an isomorphism of `ℓ`-adic sheaves for an open immersion `j` with closed range.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The comparison `j_! ⟶ j_*` of `ℓ`-adic sheaves is an isomorphism for an open immersion `j`
with closed range.** The open immersion `j` and the inclusion of the open complement `W` of its
range form a Zariski cover of `X`; the comparison restricts to an isomorphism along `j`, and
both sides vanish along `W`. -/
theorem isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range
    (hj : IsClosed (Set.range j.base)) :
    IsIso (adicOpenImmersionLowerShriekToLowerStar l j) := by
  let W : X.Opens := ⟨(Set.range j.base)ᶜ, hj.isOpen_compl⟩
  let g : ∀ i, ![U, (W : Scheme.{u})] i ⟶ X := Fin.cons j (Fin.cons W.ι fun i ↦ i.elim0)
  have : ∀ i, IsOpenImmersion (g i) :=
    Fin.cases (inferInstanceAs (IsOpenImmersion j))
      (Fin.cases (inferInstanceAs (IsOpenImmersion W.ι)) fun i ↦ i.elim0)
  have hW : Set.range W.ι.base = (Set.range j.base)ᶜ := W.range_ι
  have hsurj : ∀ x, ∃ i, x ∈ Set.range (g i).base := fun x ↦ by
    by_cases hx : x ∈ Set.range j.base
    · exact ⟨0, hx⟩
    · exact ⟨1, hW.ge hx⟩
  have hcover : Presieve.ofArrows _ g ∈ Scheme.proetalePrecoverage X :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun i ↦ this i⟩)
  have hjk : Set.range j.base ∩ Set.range W.ι.base = ∅ := by
    rw [hW, Set.inter_compl_self]
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  refine isIso_of_isIso_adicUpperStar l g hcover _ (Fin.cases ?_ (Fin.cases ?_ fun i ↦ i.elim0))
  · change IsIso ((j)^*ᵃ[l].map ((adicOpenImmersionLowerShriekToLowerStar l j).app M))
    let c := (adicOpenImmersionLowerShriekToLowerStar l j).app M
    have : IsIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M ≫ (j)^*ᵃ[l].map c) := by
      rw [adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M) _
  · change IsIso ((W.ι)^*ᵃ[l].map ((adicOpenImmersionLowerShriekToLowerStar l j).app M))
    have h₁ : IsZero ((W.ι)^*ᵃ[l].obj ((j)_!ᵃ[l].obj M)) :=
      isZero_adicUpperStar_adicOpenImmersionLowerShriek j W.ι hjk M
    have h₂ : IsZero ((W.ι)^*ᵃ[l].obj ((j)_*ᵃ[l].obj M)) :=
      AdicSheaf.isZero_of_isZero_X ((isZero_openImmersionRestriction_lowerStar _ j W.ι hjk
        M.X).of_iso ((upperStarIsoOpenImmersionRestriction _ W.ι).app _))
    exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

end ProEtale

end AlgebraicGeometry
