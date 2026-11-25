/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
import Mathlib.Order.KrullDimension
import WeilConjectures.RingTheory.MaximalChainLengthOfDepthPositive

/-!
# Length of maximal prime chains in a Cohen–Macaulay local ring

Source: Stacks Project, Algebra, Lemma 10.104.3 (Tag 00N9), via Lemma 10.103.9
(Tag 0AAE) for the module `S` (blueprint: lem-weil-pbc-cm-local-maximal-chain-length).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- Every maximal chain of primes in a Noetherian local ring of dimension `d` and depth
at least `d` has length `d`. Source: Stacks Project, Algebra, Tag 00N9, as the ring case
of Tag 0AAE (blueprint: lem-weil-pbc-cm-local-maximal-chain-length).

The chain is an `LTSeries` `p` of primes (as `ringKrullDim` is built), with `n = p.length`
strict inclusions among its `n + 1` entries `p 0 < ⋯ < p n`. Maximality of its range means
that no prime can be inserted before, between, or after its entries. The depth here
is the depth of `S` as a module over itself, with respect to its maximal ideal, using
`RingTheory.Sequence.IsRegular` as in `def-weil-pbc-regular-sequence`.

Proof, following the eight steps of the blueprint node:
1. Induct on `d`, for all Noetherian local rings with dimension `d` and depth at least
   `d`. The definition `def-weil-pbc-krull-dimension-ring` gives `n ≤ d`. Maximality
   implies that the first prime is minimal, the last is the maximal ideal, and there
   is no prime strictly between consecutive members.
2. If `d = 0`, the inequalities `0 ≤ n ≤ d` imply `n = d`.
3. If `d > 0`, then `n > 0`: otherwise the maximal ideal is also a minimal prime.
   Since all primes lie below the maximal ideal, it would be the only prime, making
   the dimension zero by `def-weil-pbc-krull-dimension-ring`.
4. The minimal primes are finite by `lem-weil-pbc-noetherian-finitely-many-minimal-primes`.
   The second prime is contained in none of them, since it strictly contains the
   first prime. Apply `lem-weil-pbc-prime-avoidance` to choose `x` in the second prime
   outside every minimal prime, in particular outside the first prime.
5. The first prime is associated to `S` by `lem-weil-pbc-noetherian-minimal-prime-associated`.
   The second prime is minimal over the first prime plus `(x)`: a prime in between
   would contradict the saturation of the chain. By
   `lem-weil-pbc-associated-prime-power-quotient`, some positive power `y = x^k`
   makes the second prime associated to `S/yS`.
6. The element `y` is in the maximal ideal and outside all minimal primes, so
   `lem-weil-pbc-noetherian-local-dim-drop-outside-minimal-primes` gives dimension
   `d - 1` for `S/yS`. Apply `lem-weil-pbc-cm-local-dimension-drop-regular-sequence`
   with one element to obtain that `y` is regular. By
   `lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm`, this quotient is Noetherian
   local of dimension `d - 1` and depth at least `d - 1`.
7. An element of the quotient whose annihilator over `S` is the second prime has
   annihilator over `S/yS` equal to that prime modulo `yS`. Thus this quotient prime
   is associated, and `lem-weil-pbc-cm-local-associated-prime-minimal` makes it minimal.
8. Prime correspondence for the quotient preserves and reflects inclusions. The
   images of the second through last primes form a maximal chain: the first is
   minimal by step 7, no intermediate prime can be inserted by the original
   maximality, and the last is the quotient's maximal ideal. Induction gives
   `n - 1 = d - 1`; since both `n` and `d` are positive, `n = d`. -/
theorem maximal_chain_length_eq_of_depth {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (d : ℕ)
    (hdim : ringKrullDim S = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := S) S) (p : LTSeries (PrimeSpectrum S))
    (hmax : IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p)) :
    p.length = d := by
  induction d generalizing S with
  | zero =>
    have hp : p.length ≤ 0 := by
      have hle := Order.LTSeries.length_le_krullDim p
      change (p.length : WithBot ℕ∞) ≤ ringKrullDim S at hle
      rw [hdim] at hle
      exact_mod_cast hle
    exact Nat.eq_zero_of_le_zero hp
  | succ d ih =>
    exact maximal_chain_length_eq_of_depth_pos d ih hdim hdepth p hmax

end IsLocalRing
