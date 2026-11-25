/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.RingTheory.BertiniNoether

/-! # Specializing an absolutely irreducible polynomial

Source: Stacks Project, Tag 0557.
-/

@[expose] public section

universe u
namespace MvPolynomial

/-- Absolute irreducibility over a field containing a domain spreads to all
field specializations after inverting a single nonzero coefficient.

Source: Stacks Project, Tag 0557, with descent from a containing field to the
fraction field, and its coefficient-algebra proof.
Proof: Let F be the fraction field of A. The injective map iota extends to an
embedding F -> K. Embed an algebraic closure of F into an algebraic closure
of K compatibly with this embedding. A nontrivial factorization over the
algebraic closure of F would remain nontrivial over the algebraic closure of K:
injective coefficient maps preserve each factor's positive total degree.
Thus P is absolutely irreducible over F. In particular P is neither zero nor
a constant. Make a triangular change of variables by sufficiently separated
powers of the last variable, so that the leading coefficient is a nonzero
c in A. Invert c and divide by it. The resulting polynomial is monic of positive
degree d in the last variable, and the coordinate change is invertible and
commutes with every coefficient specialization. Bound degrees of possible
factors in each other variable by the corresponding degree of P. For every
pair of positive integers e1 + e2 = d construct the finite type coefficient
algebra of monic factors of these degrees with these bounds, imposing the
coefficient equations P = Q1 Q2. Absolute irreducibility over an algebraic
closure of F means that this algebra has no points there. Nullstellensatz
makes its generic localization zero. Therefore its unit is annihilated by a
nonzero element of A, and inverting that element kills the coefficient algebra.
Take a to be c times the finite product of these nonzero obstruction elements,
clearing denominators from A[1/c] if needed. It is nonzero because A is a domain.
For any map phi to a field with phi(a) nonzero the map factors through A[1/a].
All factor coefficient algebras are zero after this specialization, excluding
all nontrivial factorizations of the specialized monic polynomial. Its positive
degree excludes a unit. Undo the coordinate change and scalar division to get
irreducibility of map phi P. When d = 1 the obstruction product is empty and
is 1. When n = 0 the hypothesis is impossible, since every nonzero constant
over a field is a unit. The argument applies to arbitrary containing fields K,
not only algebraic extensions of F.
(blueprint: lem-sbc-absolute-irreducibility-specialization) -/
theorem exists_nonzero_irreducible_specializations
    {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    (n : ℕ) (P : MvPolynomial (Fin n) A) (ι : A →+* K)
    (hι : Function.Injective ι)
    (hP : Irreducible (map ((algebraMap K (AlgebraicClosure K)).comp ι) P)) :
    ∃ a : A, a ≠ 0 ∧ ∀ (L : Type u) [Field L] (φ : A →+* L),
      φ a ≠ 0 → Irreducible (map φ P) := by
  let j : A →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp ι
  have hj : Function.Injective j := (algebraMap K (AlgebraicClosure K)).injective.comp hι
  let f : FractionRing A →+* AlgebraicClosure K := IsFractionRing.lift hj
  let : Algebra (FractionRing A) (AlgebraicClosure K) := f.toAlgebra
  have hf : (algebraMap (FractionRing A) (AlgebraicClosure K)).comp
      (algebraMap A (FractionRing A)) = j := by
    ext x
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) hj x
  have hP' : Irreducible (map ((algebraMap (FractionRing A) (AlgebraicClosure K)).comp
      (algebraMap A (FractionRing A))) P) := by
    rw [hf]
    exact hP
  obtain ⟨a, ha, hs⟩ := bertini_noether P (FractionRing A) (AlgebraicClosure K) hP'
  exact ⟨a, ha, fun L _ φ hφ ↦ (hs φ hφ).1⟩

end MvPolynomial
