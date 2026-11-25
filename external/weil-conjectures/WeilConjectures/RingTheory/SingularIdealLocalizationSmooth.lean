/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SmoothOfLocalizationSpanUniverses
import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
universe u v
namespace Algebra

/-- The localization smoothness argument from a radical-span relation.

This is the finite-cover reduction: a power of `f` lies in the span of smooth
principal-localization elements, so those elements generate the unit ideal after
localizing at `f`; smoothness is then local on that cover. The final span-locality
step is isolated in `smooth_of_localization_span_universes`.
(blueprint: lem-weil-pbc-singular-ideal-localization-smooth-radical-span).
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07EU, and Algebra,
Lemma 00TC. Map the span relation into `A_f`; its left side is a unit, hence the
images of the smooth elements span the unit ideal. For each smooth element `g`,
the iterated localizations `(A_g)_f` and `(A_f)_g` are localizations of `A` at
`f * g`, so the canonical algebra equivalence identifies them. The first is
smooth by composition with a principal localization. Transport smoothness to
the second and apply the span-locality criterion. This also covers `n = 0`,
nilpotent `f`, and the zero ring without any nontriviality assumption. -/
theorem smooth_localization_span_from_radical
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (n : ℕ) (hn : f ^ n ∈ Ideal.span (smoothElements R A)) :
    Smooth R (Localization.Away f) := by
  let B := Localization.Away f
  let s : Set B := algebraMap A B '' smoothElements R A
  have hs : Ideal.span s = ⊤ := by
    have hmem : algebraMap A B (f ^ n) ∈ Ideal.span s := by
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem _ hn
    exact (Ideal.span s).eq_top_of_isUnit_mem hmem
      (by simpa only [map_pow] using
        (IsLocalization.Away.algebraMap_isUnit (S := B) f).pow n)
  apply smooth_of_localization_span_universes R B s hs
  rintro ⟨b, hb⟩
  obtain ⟨g, hg, rfl⟩ := hb
  have : Smooth R (Localization.Away g) := hg
  let C : Type v := Localization.Away (algebraMap A (Localization.Away g) f)
  let D : Type v := Localization.Away (algebraMap A B g)
  have : Smooth (Localization.Away g) C :=
    Smooth.of_isLocalization_Away (algebraMap A (Localization.Away g) f)
  have : Smooth R C := Smooth.comp R (Localization.Away g) C
  have : IsLocalization.Away (f * g) C := inferInstance
  have : IsLocalization.Away (f * g) D := inferInstance
  exact Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (f * g)) C D).restrictScalars R)

/-- If an element belongs to the singular ideal, its principal localization is smooth.
This follows by `Ideal.mem_radical_iff` and the radical-span reduction above.
(blueprint: lem-weil-pbc-singular-ideal-localization-smooth). -/
theorem smooth_localization_of_mem_singularIdeal
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (hf : f ∈ singularIdeal R A) : Smooth R (Localization.Away f) := by
  have hpow : ∃ n : ℕ, f ^ n ∈ Ideal.span (smoothElements R A) :=
    Ideal.mem_radical_iff.mp hf
  obtain ⟨n, hn⟩ := hpow
  exact smooth_localization_span_from_radical R A f n hn

end Algebra
