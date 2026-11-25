/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.BoundedResolutionCancellationDecreasesRank
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Minimalization of bounded finite free resolutions.
(blueprint: stage3-b4-minimalize-bounded-finite-free-resolution) -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat
/-- Repeated cancellation of unit entries in a bounded finite free resolution.
Source: Stacks Project, Algebra, Tags 00MT and 00OA.
Proof:
Choose finite bases in degrees zero through `d` and induct on the sum of their ranks.
If a differential from degree `i + 1` to degree `i`, for `i < d`, has a unit matrix
coefficient, Tag 00MT splits off the identity complex `R → R` in these two degrees.
To use the integer-indexed splitting lemma, extend the complex by zero in negative
degrees; after splitting restrict back to nonnegative degrees. The two complementary
terms have ranks one smaller; all other terms keep their ranks, including the zero
terms above `d`. The identity complex is exact, so its complementary complex is exact
in positive degrees. For the augmentation, if `i = 0`, the removed degree-zero summand
is the image of the removed degree-one summand and is annihilated by the augmentation.
If `i > 0`, degree zero is unchanged. Thus the augmentation factors through the
complement, remains surjective, and its kernel is still the degree-one image. The
complementary terms are finite free, hence projective, so they give a resolution of
`M` of the same length bound. Apply the induction hypothesis, since the rank sum has
decreased by two. If no unit coefficient exists, every coefficient is in the maximal
ideal of the local ring. Expanding a vector in the finite source basis shows that its
image is a finite sum of maximal-ideal multiples of target basis vectors, which is
exactly membership in the maximal ideal times the top submodule. Take the original
resolution in this case. This also handles `d = 0`, where there are no differentials
to minimize, and zero terms, whose bases are empty.
(blueprint: stage3-b4-minimalize-bounded-finite-free-resolution) -/
theorem minimalize_bounded_finite_free_resolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R)
    (d : ℕ) (P : ProjectiveResolution M)
    (hzero : ∀ i : ℕ, d < i → IsZero (P.complex.X i))
    (hfree : ∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) :
    ∃ Q : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (Q.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (Q.complex.X i) ∧ Module.Free R (Q.complex.X i)) ∧
      (∀ i : ℕ, i < d →
        LinearMap.range (Q.complex.d (i + 1) i).hom ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Q.complex.X i))) := by
  classical
  let rankSum (P : ProjectiveResolution M) : ℕ :=
    ∑ i : Fin (d + 1), Module.finrank R (P.complex.X i.val)
  generalize hn : rankSum P = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hminimal : ∀ i : ℕ, i < d →
        LinearMap.range (P.complex.d (i + 1) i).hom ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i))
    · exact ⟨P, hzero, hfree, hminimal⟩
    · obtain ⟨P', hzero', hfree', hlt⟩ :=
        bounded_resolution_cancellation_decreases_rank M d P hzero hfree hminimal
      exact ih (rankSum P') (by simpa only [← hn] using hlt) P' hzero' hfree' rfl
end ModuleCat
