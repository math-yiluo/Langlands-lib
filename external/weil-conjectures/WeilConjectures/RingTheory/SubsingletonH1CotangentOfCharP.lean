/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Smooth.Field
import WeilConjectures.RingTheory.H1CotangentFiniteSubfields

/-!
# Vanishing of the first cotangent homology of a field over its positive prime field

Source: Stacks Project, Algebra, Proposition Tag 0322, characteristic `p`, (1) ⇒ (5),
with base field `𝔽_p`; More on Algebra, Proposition Tag 07E5, proof of (3) ⇔ (4)
(blueprint: lem-weil-pbc-field-char-p-h1-cotangent-vanishing).
-/

@[expose] public section

universe u

namespace Algebra

/-- For a field `K` of positive characteristic `p`, the first homology of the naive
cotangent complex of the canonical presentation `𝔽_p[K] → K` is zero. The algebra
structure is the unique one, supplied by `ZMod.algebra K p`.

Source: Stacks Project, Algebra, Proposition Tag 0322, characteristic `p`, (1) ⇒ (5),
with `k = 𝔽_p`; used in More on Algebra, Proposition Tag 07E5, proof of (3) ⇔ (4).

Proof (the three steps of the node):
1. Every finitely generated field extension `E/𝔽_p` is separable. Apply
   `lem-weil-pbc-make-separable` to obtain an overfield `E''` separable over a finite
   purely inseparable extension `k'` of its prime field `P`. For `a ∈ k'`, some
   `a^(p^m) = c ∈ P`; Fermat gives `c^(p^m) = c`, hence `(a-c)^(p^m) = 0` and `a = c`.
   Thus `k' = P`. Every finitely generated subextension of `E` embeds in `E''`;
   transport its separating transcendence basis and separable algebraic extension
   back along this embedding. This gives separability in the sense of
   `def-weil-pbc-separable-field-extension`, using the purely inseparable,
   transcendence-basis and separable-algebraic-extension definition nodes.
2. For each finitely generated subfield `E` of `K`, use
   `lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra` to write
   `E = Frac B` for a smooth `𝔽_p`-algebra `B`. Smoothness gives zero first homology
   (`def-weil-pbc-smooth-ring-map`); `lem-weil-pbc-h1-cotangent-localization` and
   `def-weil-pbc-module-localization` give the same for `Frac B`. The identification
   with `E` renames the variables of the canonical polynomial presentation
   (`def-weil-pbc-mv-polynomial-ring`), carries its kernel and its square onto those
   for `E`, and commutes with partial derivatives. It therefore identifies first homology.
3. A cycle represented by `g ∈ I = ker(𝔽_p[K] → K)` uses finitely many variables.
   Let `E` be the subfield they generate. Evaluation and partial derivatives restrict
   to `𝔽_p[E]`, so `g` represents a cycle for `E`. Step 2 gives `g ∈ I_E² ⊆ I²`.
   Every cycle is consequently zero. These are the finite-support reduction of
   Tag 07BQ and the localization argument of Tags 037X and 00S7.

(blueprint: lem-weil-pbc-field-char-p-h1-cotangent-vanishing) -/
theorem subsingleton_h1Cotangent_of_charP
    (p : ℕ) (hp : 0 < p) (K : Type u) [Field K] [CharP K p] :
    letI := ZMod.algebra K p
    Subsingleton (H1Cotangent (ZMod p) K) := by
  have : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero K (Nat.ne_of_gt hp)⟩
  let := ZMod.algebra K p
  apply subsingleton_h1Cotangent_of_finite_subfields
  intro E hE
  have : Algebra.EssFiniteType (ZMod p) E := IntermediateField.essFiniteType_iff.mpr hE
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

end Algebra
