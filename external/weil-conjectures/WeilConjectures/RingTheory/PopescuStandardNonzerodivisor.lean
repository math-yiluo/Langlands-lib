/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import WeilConjectures.RingTheory.PopescuStandardNonzerodivisorAux
import WeilConjectures.RingTheory.ElementaryToStrict
import WeilConjectures.RingTheory.PopescuDelocalizeBase

/-! # A standard nonzerodivisor from the field case of Popescu -/

@[expose] public section

universe u v
open CategoryTheory
open scoped nonZeroDivisors

/-- The field case produces a strictly standard nonzerodivisor after a finite-presentation
factorization. Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F5,
third and fourth paragraphs, lines 2029--2043
(blueprint: lem-weil-pbc-popescu-standard-nonzerodivisor).

Proof: Localize the reduced Noetherian base at all nonzerodivisors. Its total fraction
ring is a finite product of the residue fields at the minimal primes. The corresponding
localization of Λ is the product of the fibres at those primes. Regularity supplies
Noetherian geometric regularity of each fibre; over a field flatness is automatic,
so the field hypothesis applies to each factor. ind_smooth_prod, iterated over the
finite set of minimal primes, gives ind-smoothness over the total fraction ring.
Finite presentation of A makes the localized map factor through one smooth term
of this filtered diagram. Apply exists_factorization_isElementaryStandardElement_of_localized_smooth
with the submonoid of nonzerodivisors, producing A → B → Λ and π in that submonoid
whose image in B is elementary standard. It is strictly standard: select the initial
minor in the sum over minors, set all other coefficients to zero, and use invariance
of the determinant under transposition. The finite polynomial
quotient construction of B lives in universe max u v. -/
theorem exists_popescu_standard_nonzerodivisor
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ))
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] [Nontrivial R] [IsReduced R]
    (hreg : RingHom.IsRegular (algebraMap R Λ))
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B)
      (_ : Algebra.FinitePresentation R B) (aB : A →ₐ[R] B) (β : B →ₐ[R] Λ) (π : R),
      β.comp aB = α ∧ π ∈ R⁰ ∧
        Algebra.IsStrictlyStandardElement (R := R) (algebraMap R B π) := by
  obtain ⟨B', _, _, _, β', γ', hfactor⟩ :=
    exists_localized_smooth_factorization h R Λ hreg A α
  obtain ⟨B, _, _, hBfp, aB, β, hcomp, π, hs⟩ :=
    Algebra.exists_factorization_isElementaryStandardElement_of_localized_smooth
      α R⁰ β' γ' (by
        ext x
        exact RingHom.congr_fun hfactor x)
  exact ⟨B, inferInstance, inferInstance, hBfp, aB, β, π.val, hcomp, π.property,
    elementary_standard_is_strict hs⟩
