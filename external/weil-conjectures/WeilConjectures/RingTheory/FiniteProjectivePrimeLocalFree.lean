/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free

/-!
# Finite projective modules are free on a neighbourhood of each prime

Source: Stacks Project, Algebra, Tag 00NX, Lemma 10.78.2, (2) ⇒ (3) ⇒ (1) ⇒ (7),
and Tag 0GWM, Lemma 10.79.3
(blueprint: proposition-projective-line-rational-coefficients--1).
-/

@[expose] public section

universe u v

namespace Module

/-- A finite projective module becomes finite free after inverting an element outside any
specified prime. Source: Stacks Project, Algebra, Tags 00NX and 0GWM.
(blueprint: proposition-projective-line-rational-coefficients--1)

Proof:
1. A surjection from a finite free module onto `M` splits by projectivity. Its kernel is
   a direct summand of a finite free module and is finitely generated, so `M` is finitely
   presented (`lem-weil-pbc-finite-projective-finitely-presented`, Tag 00NX).
2. At the prime `p`, the localization of `M` is finite free over the local ring `A_p`
   (`lem-weil-pbc-finite-projective-rank-locally-constant`, first clause, together with
   `def-weil-pbc-module-localization` and `def-weil-pbc-localization-at-prime`). Choose its
   finite basis, of rank `r`.
3. Clear the finitely many denominators of the basis vectors by multiplying them by a
   common element outside `p`. This rescales a basis by a unit in `A_p`, giving elements
   of `M` and a map from a finite free module to `M` that is an isomorphism at `p`.
   Finite presentation spreads this isomorphism to one after inverting some `f ∉ p`
   (`lem-weil-pbc-finitely-presented-free-at-prime-spreads`, Tag 0GWM). This is exactly the
   asserted isomorphism for `LocalizedModule.Away f M`
   (`def-weil-pbc-module-localization-away`). -/
theorem exists_localizationAway_equiv_finsupp_of_finite_projective
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] (p : Ideal A) [p.IsPrime] :
    ∃ f : A, f ∉ p ∧ ∃ r : ℕ,
      Nonempty (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
        (Fin r →₀ Localization.Away f)) := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
  obtain ⟨f, hf, b', _⟩ :=
    Module.FinitePresentation.exists_basis_localizedModule_powers p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p) b
  exact ⟨f, hf, _, ⟨b'.repr⟩⟩

end Module
