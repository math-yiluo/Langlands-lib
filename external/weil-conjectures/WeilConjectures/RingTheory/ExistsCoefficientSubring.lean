/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.CharP.Defs
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CoefficientResidueSection
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import WeilConjectures.RingTheory.CoefficientSubringOfPrincipalSource

/-!
# Existence of a coefficient subring

Source: Stacks Project, Algebra, Theorem 032A(1) and Definition 0326
(blueprint: lem-weil-pbc-cohen-coefficient-ring-exists).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A complete local ring contains a coefficient subring, in the sense of Stacks Project,
Algebra, Definition 0326; existence is Theorem 032A(1).
(blueprint: lem-weil-pbc-cohen-coefficient-ring-exists)

Proof: (1) For n ≥ 2 the kernel of R/m^n → R/m^(n-1) is square-zero. In residue
characteristic zero the quotients are Q-algebras; in characteristic p > 0, R/m^n is a
Z/p^n-algebra. (2) In characteristic zero, lift the identity of the residue field successively
through these square-zero kernels using formal smoothness over Q
(lem-weil-pbc-char-zero-field-extension-formally-smooth and
theorem-finite-etale-covers-proper-henselian--2). (3) Pass to the inverse limit using
def-weil-pbc-adic-completion and def-weil-pbc-adically-complete-ring. The resulting section has
image a field with zero intersection with m, and its reduction is an isomorphism.
(4) In positive characteristic choose a Cohen ring with the prescribed residue field
(lem-weil-pbc-cohen-rings-exist). Lift its maps modulo p^n successively using
lem-weil-pbc-cohen-ring-mod-pn-formally-smooth. (5) Completeness of R gives a map from
this Cohen ring to R, whose inverse image of m is its ideal (p).
(6) By lem-weil-pbc-dvr-unit-times-uniformizer-power, its kernel is either zero or (p^N)
for N ≥ 1. (7) Its image is local with maximal ideal its intersection with m, equal to
(p), and the induced residue map is bijective. If the kernel is zero, completeness transfers
from the Cohen ring; otherwise powers of (p) eventually vanish, so the inverse system of
quotients stabilizes. This verifies all three coefficient-ring conditions. -/
theorem exists_coefficient_subring (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (p : ℕ) [CharP (ResidueField R) p] :
    ∃ (Λ : Subring R) (hΛ : IsLocalRing Λ),
      letI : IsLocalRing Λ := hΛ
      maximalIdeal Λ = (maximalIdeal R).comap Λ.subtype ∧
      IsAdicComplete ((maximalIdeal R).comap Λ.subtype) Λ ∧
      Function.Bijective
        (Ideal.quotientMap (I := (maximalIdeal R).comap Λ.subtype)
          (maximalIdeal R) Λ.subtype le_rfl) ∧
      (maximalIdeal R).comap Λ.subtype = Ideal.span {(p : Λ)} := by
  rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hp
  · obtain ⟨C, hcomm, hC, ⟨e⟩⟩ := exists_cohenRing p hp (ResidueField R)
    let _ := hcomm
    obtain ⟨f, hf⟩ := exists_cohenRing_lift R p C hC e
    obtain ⟨_, hdom, hdvr, hm, hcomplete⟩ := hC
    let _ := hdom
    let _ := hdvr
    have : IsAdicComplete (maximalIdeal C) C := hm.symm ▸ hcomplete
    have hlocal : (maximalIdeal R).comap f = maximalIdeal C := by
      ext x
      rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← RingHom.comp_apply, hf]
      simp [hm, Ideal.Quotient.eq_zero_iff_mem]
    have hsurj : Function.Surjective ((residue R).comp f) := by
      rw [hf]
      exact e.surjective.comp (Ideal.Quotient.mk_surjective)
    obtain ⟨hL, hprops⟩ := coefficient_subring_of_principal_source R C p hm f hlocal hsurj
    exact ⟨f.range, hL, hprops⟩
  · subst p
    obtain ⟨f, hf⟩ := exists_residue_section R
    have hm : maximalIdeal (ResidueField R) = Ideal.span {(0 : ResidueField R)} := by
      simp [maximalIdeal_eq_bot]
    have : IsAdicComplete (maximalIdeal (ResidueField R)) (ResidueField R) := by
      rw [maximalIdeal_eq_bot]
      exact IsAdicComplete.bot _
    have hlocal : (maximalIdeal R).comap f = maximalIdeal (ResidueField R) := by
      ext x
      rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← RingHom.comp_apply, hf]
      simp [maximalIdeal_eq_bot]
    have hsurj : Function.Surjective ((residue R).comp f) := by
      rw [hf]
      exact Function.surjective_id
    obtain ⟨hL, hprops⟩ :=
      coefficient_subring_of_principal_source R (ResidueField R) 0
        (by simpa using hm) f hlocal hsurj
    exact ⟨f.range, hL, hprops⟩

end IsLocalRing
