/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
import WeilConjectures.RingTheory.PBasisComplementMonomialBasisLinearIndependent
import WeilConjectures.RingTheory.PBasisComplementMonomialBasisSpanning
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The finite part of a p-basis over its complementary subfield

Source: Stacks Project, Tag 07P5, the coefficient-field finiteness in the proof,
expanded by the bounded-monomial argument of the parent node.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-basis).
-/

@[expose] public section

set_option autoImplicit false

universe u w

attribute [local instance] ZMod.algebra

namespace RingTheory

/-- Removing a finite part of a p-basis leaves exactly its bounded monomials as a basis.
Source: Stacks Project, Tag 07P5, first proof paragraph; the explicit coefficient-field
argument in lem-weil-pbc-power-series-subring-finite-basis, step 1.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-basis).

Proof: Frobenius is a field homomorphism in characteristic p. Its image is the
subfield of p-th powers and contains the prime field, so the intermediate field
in hpb equals this image. Write F for that subfield. The F-span L of the bounded monomials
on I minus J contains 1 and all the complementary generators. Multiplication preserves
L: reduce exponents modulo p and put the removed p-th powers into F. If a is nonzero
in L, then a^p lies in F and a inverse equals (a^p) inverse times a^(p-1), so L is also
closed under inverses. Thus L is kJ, by the two inclusions with its generating set.
Every exponent function splits uniquely into its restrictions to J and its complement,
and its monomial is the product of the two monomials. Expand an element in the given
F-basis and group its finitely many coordinates by the J restriction. This proves
spanning over kJ. For independence, expand the finitely many kJ coefficients in the
complementary monomial span. The resulting relation in the original F-basis has
pairwise distinct exponent functions. Every F-coordinate therefore vanishes, so every
kJ coefficient vanishes. The indicated family is consequently a basis. If J is empty,
the single empty monomial is 1 and kJ is k, so the argument includes that case. -/
theorem pBasisComplementMonomialBasis
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e ↦ t i ^ e))
    (J : Finset I) (kJ : Subfield k)
    (hkJ : kJ = Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x})) :
    ∃ b : Module.Basis (J → Fin p) kJ k,
      ∀ E, b E = ∏ i : J, t i ^ (E i : ℕ) := by
  have hli := pBasisComplementMonomialBasis_linearIndependent p k I t hpb J kJ hkJ
  have hsp := pBasisComplementMonomialBasis_spanning p k I t hpb J kJ hkJ
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  intro E
  exact Module.Basis.mk_apply hli hsp E

end RingTheory
