/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# The comparison `f_! ⟶ f_*` is an isomorphism for a proper morphism

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.Proper`.

For a proper morphism `f : X ⟶ Y` admitting a compactification, the canonical comparison
`ι_f : f_! ⟶ f_*` of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison`
is an isomorphism. It is deduced from the case of an open immersion with closed range, applied to
the open immersion of a compactification of `f`.

The only point where the argument differs from the étale one is the cover used for the
conservativity input: for the pro-étale topology, joint surjectivity is not enough, so the
two-open cover `{j, W.ι}` is fed in as a *Zariski* cover, which is a pro-étale covering
family by `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_proetalePrecoverage`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range`:
  the comparison `j_! ⟶ j_*` is an isomorphism for an open immersion `j` with closed range.
- `AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar`: for a proper `f`, the comparison
  `ι_f : f_! ⟶ f_*` is an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Closed

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The comparison `j_! ⟶ j_*` is an isomorphism for an open immersion `j` with closed
range.** The open immersion `j` and the inclusion of the open complement `W` of its range
form a Zariski cover of `X`, hence a pro-étale cover, so restriction along the two of them is
jointly conservative; the comparison restricts to an isomorphism along `j` for formal reasons
and along `W` because both sides vanish there.

```
        j             W.ι
   U ──────→ X ←────────── W        range j ⊔ range W.ι = X
```
-/
theorem ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (hj : IsClosed (Set.range j.base)) :
    IsIso (ProEtale.openImmersionLowerShriekToLowerStar A j) := by
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
  -- the two opens form a Zariski cover, hence a pro-étale cover
  have hcover : Presieve.ofArrows _ g ∈ Scheme.proetalePrecoverage X :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun i ↦ this i⟩)
  have hjk : Set.range j.base ∩ Set.range W.ι.base = ∅ := by
    rw [hW, Set.inter_compl_self]
  have happ : ∀ F, IsIso ((ProEtale.openImmersionLowerShriekToLowerStar A j).app F) := fun F ↦ by
    refine ProEtale.isIso_of_isIso_localizationRestriction A _ g hcover
      (Fin.cases ?_ (Fin.cases ?_ fun i ↦ i.elim0))
    · exact ProEtale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar A j F
    · exact ProEtale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar A j
        W.ι hjk F
  exact NatIso.isIso_of_isIso_app _

end Closed

section Proper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsProper f]

/-- **For a proper morphism `f`, the canonical comparison `ι_f : f_! ⟶ f_*` is an
isomorphism.** By `AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar_of_isIso` this
reduces to the comparison for the open immersion `i` of the chosen compactification.
Properness of `f` enters only through
`AlgebraicGeometry.Compactification.isClopen_range_openImmersion`: since the structure
morphism `g` of the compactification is separated, `i` is proper as soon as `i ≫ g` is, and a
proper open immersion has closed range.

```
       i
   X ─────→ P            f_! = g_* ∘ i_! ──→ g_* ∘ i_* ≅ f_*
    ╲       │
   f ╲      │ g
      ↘     ↓
            Y
```
-/
instance ProEtale.isIso_lowerShriekToLowerStar :
    IsIso (ProEtale.lowerShriekToLowerStar A f) :=
  ProEtale.isIso_lowerShriekToLowerStar_of_isIso A f
    (ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A
      (HasCompactification.compactification f).i
      ((HasCompactification.compactification f).isClopen_range_openImmersion
        inferInstance).isClosed)

end Proper

end AlgebraicGeometry
