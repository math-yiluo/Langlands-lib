/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.RingTheory.Kaehler.Basic

import WeilConjectures.RingTheory.PthRootMonomialDimension
import WeilConjectures.FieldTheory.PthRootsExtensionDegree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The p-root quotient over a field

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), first paragraph.
-/

@[expose] public section

universe u

namespace Algebra

/-- The quotient adjoining roots of coefficients with independent differentials is
itself a finite field extension, and all its p-th powers come from the coefficient field.

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), first paragraph;
Algebra, Tag 07DZ. (blueprint: lem-weil-pbc-pth-root-field-quotient).

Proof: Choose roots alpha_i in an algebraic closure of k and form the field F they
 generate. By 07DZ its degree is p^n. The quotient Q over k is spanned by the p^n
reduced monomials: divide each exponent by p and use X_i^p = a_i. Evaluation at
alpha_i defines a homomorphism Q to F. Its image is a finite-dimensional domain
containing k, so it is a field, and since it contains every alpha_i it equals F.
The dimension bound dim Q <= p^n and dim F = p^n make evaluation injective as well
as surjective. Thus Q is a field and is finite over k. For a reduced polynomial,
Frobenius turns its p-th power into the sum of lambda_E^p times the products a^E,
which lies in k. The same computation holds in Q and proves the last assertion.
For n = 0, Q = k and the assertions follow from the identity map. -/
theorem pthRootAlgebra_isField_finite_pow
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (a : Fin n → k) :
    letI := ZMod.algebra k p
    LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) →
    let Q := pthRootAlgebra p n k a
    IsField Q ∧ Module.Finite k Q ∧
      ∀ x : Q, x ^ p ∈ (algebraMap k Q).range  := by
  classical
  intro hind
  let Q := pthRootAlgebra p n k a
  let Ω := AlgebraicClosure k
  obtain ⟨α, hα⟩ : ∃ α : Fin n → Ω, ∀ i, α i ^ p = algebraMap k Ω (a i) := by
    exact Classical.axiomOfChoice
      (fun i ↦ IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω (a i))
        (Fact.out : p.Prime).pos)
  let F := IntermediateField.adjoin k (Set.range α)
  obtain ⟨hfiniteF, hdimF⟩ :=
    IntermediateField.finiteDimensional_finrank_adjoin_pth_roots p k Ω n a hind α hα
  let := hfiniteF
  obtain ⟨hfiniteQ, hdimQ⟩ := pthRootAlgebra_finite_finrank_le k p n
    (Fact.out : p.Prime).pos a
  let := hfiniteQ
  let I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ p - MvPolynomial.C (a i)))
  let eval : MvPolynomial (Fin n) k →ₐ[k] Ω := MvPolynomial.aeval α
  have hI : I ≤ RingHom.ker eval := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change eval (MvPolynomial.X i ^ p - MvPolynomial.C (a i)) = 0
    simp [eval, hα]
  let g : Q →ₐ[k] Ω := Ideal.Quotient.liftₐ I eval (fun x hx ↦ hI hx)
  have hrange : g.range = F.toSubalgebra := by
    rw [IntermediateField.adjoin_toSubalgebra]
    rw [← MvPolynomial.aeval_range]
    apply SetLike.coe_injective
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨Ideal.Quotient.mk I f, rfl⟩
  let t : Q →ₐ[k] F :=
    (Subalgebra.equivOfEq _ _ hrange).toAlgHom.comp g.rangeRestrict
  have hsurj : Function.Surjective t :=
    (Subalgebra.equivOfEq _ _ hrange).surjective.comp g.rangeRestrict_surjective
  have hdim : Module.finrank k Q = Module.finrank k F := by
    apply le_antisymm
    · exact hdimQ.trans_eq hdimF.symm
    · exact LinearMap.finrank_le_finrank_of_surjective (f := t.toLinearMap) hsurj
  have hinj : Function.Injective t :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := t.toLinearMap) hdim).mpr hsurj
  let e : Q ≃ₐ[k] F := AlgEquiv.ofBijective t ⟨hinj, hsurj⟩
  refine ⟨e.toMulEquiv.isField (Field.toIsField F), hfiniteQ, ?_⟩
  have : Nontrivial Q := e.toEquiv.nontrivial
  have : CharP Q p := (Algebra.charP_iff k Q p).mp inferInstance
  let q : MvPolynomial (Fin n) k →+* Q := Ideal.Quotient.mk I
  have hX (i : Fin n) : q (MvPolynomial.X i) ^ p = algebraMap k Q (a i) := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.subset_span ⟨i, rfl⟩ : MvPolynomial.X i ^ p - MvPolynomial.C (a i) ∈ I)
    change q (MvPolynomial.X i ^ p - MvPolynomial.C (a i)) = 0 at hz
    rw [map_sub, map_pow, sub_eq_zero] at hz
    exact hz
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change ∃ c : k, algebraMap k Q c = q f ^ p
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨c ^ p, map_pow (algebraMap k Q) c p⟩
  | add f g hf hg =>
    obtain ⟨c, hc⟩ := hf
    obtain ⟨d, hd⟩ := hg
    refine ⟨c + d, ?_⟩
    rw [map_add, map_add, add_pow_char, hc, hd]
  | mul_X f i hf =>
    obtain ⟨c, hc⟩ := hf
    refine ⟨c * a i, ?_⟩
    rw [map_mul, map_mul, mul_pow, hc, hX]

end Algebra
