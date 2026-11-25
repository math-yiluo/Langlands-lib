/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.PolynomialLocalCompletionFormallySmooth
import WeilConjectures.RingTheory.PolynomialFormalFiberNoetherian
import WeilConjectures.RingTheory.PolynomialFormalFiberGeometric

/-!
# Formal fibres of a polynomial ring over a complete local domain

Source: Stacks Project, More on Algebra, Lemma 07PU
(blueprint: lem-weil-pbc-another-helper-g-ring).
-/

@[expose] public section

universe u

namespace Polynomial

/-- The formal fibre at a nonzero prime above zero is Noetherian and geometrically regular.
Source: Stacks Project, More on Algebra, Lemma 07PU
(blueprint: lem-weil-pbc-another-helper-g-ring).

Proof plan (the seven steps of the node):
1. For any complete Noetherian local base B, its polynomial localization T at a maximal
   ideal above the maximal ideal of B is Noetherian. Its completion C is Noetherian,
   local and complete by adic-completion-noetherian, local-completion-local-ring and
   module-completion-complete. Every fibre is Noetherian by fibre-ring-noetherian.
2. A nonzero prime s of B[X] above zero becomes a nonzero maximal principal ideal (g)
   of K_B[X]. By localization-prime-residue-field-iso, its residue field is K_B[X]/(g),
   finite over K_B. By localization-base-change and tensor-cancel-base-change, the fibre
   of C is W⁻¹C/(g), where W consists of the nonzero elements of B.
3. If K_B equals the residue field, g = X - f. The map B → C is formally smooth by
   polynomial-local-completion-formally-smooth, hence regular by
   formally-smooth-complete-local-regular. Thus W⁻¹C is regular. The derivation d/dX
   extends through localization and completion by derivation-extends, kills f and sends
   X - f to 1. The quotient is regular by hypersurface-derivation-regular.
4. For a finite purely inseparable extension L of the residue field, clear denominators
   of the minimal polynomials of a K-basis. The resulting integral generators give a
   finite A-subalgebra B of L with fraction field L (finite-of-integral-generators).
   By finite-over-complete-local-product this domain B is local and complete. The kernel
   r' of evaluation B[X] → L is nonzero, lies above zero, and has residue field L.
5. By completion-finite-extension, C ⊗ B[X] is the finite product of completed local
   rings at primes q_i above q. Tensor-cancel-base-change identifies the base-changed
   fibre with the product of their fibres at r'.
6. Each q_i is maximal by finite-algebra-is-integral and contracts to the maximal ideal
   of B. If r' is not contained in q_i, the fibre is zero, hence regular. Otherwise
   step 3 applies, since the fraction field of B equals the residue field at r'.
7. Finite products of regular rings are regular: primes come from exactly one factor,
   and their localizations are the corresponding regular local rings. Thus every finite
   purely inseparable base change is regular; step 1 gives Noetherianity. The characteristic
   hypothesis is retained as in the source, although this proof does not use it.

The fibre uses Mathlib's residue-field-first tensor order, canonically isomorphic to
C ⊗ κ(r). Completion is at the maximal ideal of the localization, which is qT. -/
theorem formalFiber_isGeometricallyRegular (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsNoetherianRing (r.Fiber C) ∧ Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber C) := by
  exact ⟨formalFiber_isNoetherian A p hp q hq r hrq hr hrA,
    formalFiber_isGeometricallyRegular_component A p hp q hq r hrq hr hrA⟩

end Polynomial
