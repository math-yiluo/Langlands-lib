/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.BoundedFiniteFreeResolution
import WeilConjectures.RingTheory.MinimalizeBoundedFiniteFreeResolution

/-!
# Minimal finite free resolutions over a Noetherian local ring

Source: Stacks Project, Algebra, Tags 0CXF and 00MT, as used in the proof of Tag 00OA
(blueprint: lem-weil-pbc-minimal-finite-free-resolution-local).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite module over a Noetherian local ring with a projective resolution of length
at most `d` has a finite free resolution of length at most `d` whose positive-degree
maps have image in the maximal ideal times the preceding module.
Source: Stacks Project, Algebra, Tags 0CXF and 00MT, proof of Tag 00OA
(blueprint: lem-weil-pbc-minimal-finite-free-resolution-local).

Proof:
1. When `d = 0`, the given resolution makes `M` projective. Since it is finite,
   `proposition-projective-line-rational-coefficients--1` at the maximal ideal makes it
   finite free: the localizing element outside that ideal is a unit.
2. For `d ≥ 1`, choose an infinite finite free resolution using
   `lem-weil-pbc-finite-free-resolution-noetherian`. Its `d`-th syzygy is projective by
   `lem-weil-pbc-projective-resolution-kernel-projective` and the given length bound.
   It is finite by `lem-weil-pbc-noetherian-submodule-finite`.
3. Apply `proposition-projective-line-rational-coefficients--1` to that syzygy at the
   maximal ideal, where localization at a unit does nothing. Substituting it as the
   leftmost term gives a finite free resolution of length at most `d`.
4. If a differential has a unit matrix entry, use
   `lem-weil-pbc-free-complex-unit-entry-splits` to remove an identity summand
   `R → R`. The augmentation annihilates that summand (also in degrees one and zero),
   so it factors through the remaining complex, which stays exact.
5. Each removal decreases the sum of the finite ranks. Thus cancellation terminates.
   All remaining entries are nonunits, hence belong to the maximal ideal. This is
   precisely the asserted image condition. -/
theorem exists_minimal_finite_free_resolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (d : ℕ) (h : HasProjectiveResolutionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) ∧
      (∀ i : ℕ, i < d →
        LinearMap.range (P.complex.d (i + 1) i).hom ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i))) := by
  obtain ⟨P, hzero, hfree⟩ := exists_bounded_finite_free_resolution M d h
  exact minimalize_bounded_finite_free_resolution M d P hzero hfree

end ModuleCat
