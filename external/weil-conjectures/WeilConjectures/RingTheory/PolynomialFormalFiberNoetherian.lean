/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Polynomial.Basic
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Polynomial.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
@[expose] public section
universe u
namespace Polynomial

-- The signature also carries hypotheses used by the geometric-regularity component.
set_option linter.unusedVariables false in
/-- Noetherianity component of the formal-fibre theorem.
Source: Stacks Project, More on Algebra, Lemma 07PU.
(blueprint: lem-weil-pbc-another-helper-g-ring-noetherian-component)
Proof: localize the polynomial ring at the given maximal ideal, apply the
Noetherianity theorem for adic completions, and then apply the theorem that a
fibre of a Noetherian ring is Noetherian. -/
theorem formalFiber_isNoetherian (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing (r.Fiber C) := by
  have : IsNoetherianRing (Localization.AtPrime q) := inferInstance
  have : IsNoetherianRing
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) := AdicCompletion.isNoetherianRing _
  exact Ideal.isNoetherianRing_fiber r
end Polynomial
