/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import WeilConjectures.Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Étale algebras and square Jacobian presentations

An `R`-algebra is étale if and only if it admits a square Jacobian presentation
`R[x₁, …, xₘ] / (f₁, …, fₘ)` with invertible Jacobian determinant. A smooth algebra over a field
is reduced, being locally étale over a polynomial ring.

## Main statements

- `Algebra.Etale.iff_exists_squareJacobianPresentation`: an algebra is étale if and only if it
  admits a square Jacobian presentation.
- `Algebra.Smooth.isReduced_of_field`: a smooth algebra over a field is reduced.

## References

- Stacks Project, Tag `00U9`, <https://stacks.math.columbia.edu/tag/00U9>
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A square Jacobian presentation is standard smooth of relative dimension `0`. -/
lemma SquareJacobianPresentation.isStandardSmoothOfRelativeDimension_zero {ι : Type*} [Finite ι]
    (P : SquareJacobianPresentation R S ι) : IsStandardSmoothOfRelativeDimension 0 R S :=
  P.toSubmersivePresentation.isStandardSmoothOfRelativeDimension (by
    simp [Presentation.dimension])

/-- An algebra admitting a square Jacobian presentation is étale. -/
lemma SquareJacobianPresentation.etale {ι : Type*} [Finite ι]
    (P : SquareJacobianPresentation R S ι) : Etale R S :=
  have := P.isStandardSmoothOfRelativeDimension_zero
  inferInstance

/-- An `R`-algebra `S` is étale if and only if it admits a square Jacobian presentation
`S = R[x₁, …, xₘ] / (f₁, …, fₘ)` with `det (∂fᵢ / ∂xⱼ)` a unit in `S` (blueprint
`proposition-extension-zero-restriction-closed-subscheme`).

The forward direction starts from a submersive presentation of relative dimension `0`, given
by `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`: its injective map from the
relations to the variables is then a bijection, along which the variables are reindexed. -/
@[stacks 00U9]
theorem Etale.iff_exists_squareJacobianPresentation :
    Etale R S ↔ ∃ (ι : Type) (_ : Finite ι), Nonempty (SquareJacobianPresentation R S ι) := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, ⟨P⟩⟩ ↦ P.etale⟩
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp h).out
  have hcard : Nat.card ι ≤ Nat.card σ := by
    simpa [Presentation.dimension, Nat.sub_eq_zero_iff_le] using hP
  let e : σ ≃ ι := Equiv.ofBijective P.map (P.map_inj.bijective_of_nat_card_le hcard)
  let Q := P.toPreSubmersivePresentation.reindex e (Equiv.refl σ)
  refine ⟨σ, inferInstance, ⟨
    { toPreSubmersivePresentation := Q
      jacobian_isUnit := by
        simpa [Q, PreSubmersivePresentation.jacobian_reindex] using P.jacobian_isUnit
      map_eq_id := ?_ }⟩⟩
  ext i
  simp [Q, PreSubmersivePresentation.reindex_map, e]

/-- A smooth algebra `A` over a field `K` is reduced. Locally on `Spec A` it is standard smooth,
hence étale over a polynomial ring over `K`, and an étale algebra over a domain is reduced
(`Algebra.Etale.isReduced_of_isDomain`). An element `a` with nilpotent image therefore vanishes
in every member `A[1/x]` of a cover by standard opens, so its annihilator is the unit ideal. -/
theorem Smooth.isReduced_of_field (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Smooth K A] : IsReduced A := by
  obtain ⟨s, hs, H⟩ := Smooth.exists_span_eq_top_isStandardSmooth K A
  refine ⟨fun a ha ↦ ?_⟩
  let I : Ideal A := (Submodule.span A {a}).annihilator
  suffices I = ⊤ by
    simpa [I, Submodule.mem_annihilator_span_singleton] using (Ideal.eq_top_iff_one I).mp this
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hxs, hxm⟩ : ∃ x ∈ s, x ∉ m := by
    by_contra! h
    exact hm.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr h :))
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (H x hxs).out
  have := P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    P.dimension K (Localization.Away x)
  algebraize [g.toRingHom]
  have : IsReduced (Localization.Away x) :=
    Etale.isReduced_of_isDomain (MvPolynomial (Fin P.dimension) K) _
  have h0 : algebraMap A (Localization.Away x) a = 0 := (ha.map _).eq_zero
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x) _ a).mp h0
  have : x ^ n ∈ I := by simpa [I, Submodule.mem_annihilator_span_singleton] using hn
  exact hxm (hm.isPrime.mem_of_pow_mem n (hIm this))

end Algebra
