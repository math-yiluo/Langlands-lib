/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Finiteness interface for finite p-adic coefficient extensions

Source: Weil blueprint, `def-weil-finite-field-fiber`, order 411;
Serre, Local Fields, Chapter II, §2
(auxiliary; not a blueprint node).

The coefficient constructions are imported unchanged; this supplies their finite-ring
interface at positive levels.
-/

@[expose] public section

universe u

namespace Padic

/-- The coefficient ring at a finite level is finite.

Source: Weil conjectures blueprint, node `def-weil-finite-field-fiber`,
order 411; Serre, Local Fields, Chapter II, §2
(auxiliary; not a blueprint node).

Proof: Apply `Padic.extension_integers_dvr` to the spectral absolute value to obtain
that the recorded integer ring is a DVR with finite residue field. Its recorded
uniformizer generates the recorded maximal ideal. Thus the ideal defining the level
`n` ring is the `n`th power of that maximal ideal. Each successive ideal quotient
is a finite-dimensional vector space over the finite residue field, and induction
on `n` gives the finiteness of the ring quotient. Equivalently apply
`Ideal.finite_quotient_pow` in the Noetherian integer ring after identifying ideals.
-/
theorem finite_coefficientExtensionRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n) :
    Finite (Padic.coefficientExtensionRing l E n) := by
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hfinite : Finite (coefficientExtensionIntegers l E ⧸
      coefficientExtensionMaximalIdeal l E) :=
    h.2.2.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} :
      Set (coefficientExtensionIntegers l E)) = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : Finite (coefficientExtensionIntegers l E ⧸
      Ideal.span ({coefficientExtensionUniformizer l E} :
        Set (coefficientExtensionIntegers l E))) := by
    rw [hgen]
    exact hfinite
  exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) n

end Padic
