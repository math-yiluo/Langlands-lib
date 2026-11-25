/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Locality of the actual algebra adjoining p-th roots

Source: Stacks Project, More on Algebra, Tag 07E5, construction of A'.
-/

@[expose] public section

universe u

namespace Algebra

/-- The actual polynomial quotient adjoining the specified p-th roots. 
(blueprint: lem-weil-pbc-pth-root-algebra-local)
-/
abbrev pthRootAlgebra (p n : ℕ) (A : Type u) [CommRing A] (a : Fin n → A) :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : MvPolynomial (Fin n) A) ^ p - MvPolynomial.C (a i)))

/-- Adjoining finitely many p-th roots to a local ring in characteristic p gives
another local ring, and the coefficient map is local.

Source: Stacks Project, More on Algebra, Tag 07E5, construction of A' in the proof;
Algebra, Tag 0BR8 (powers in the coefficient image).
(blueprint: lem-weil-pbc-pth-root-algebra-local).

Proof: Map A to the algebraic closure of its residue field, and choose p-th roots
there of the images of the a_i. Evaluation at these roots kills the defining ideal
and induces a ring map g from the actual quotient to this field. This proves that
the quotient is nontrivial. Its composite with the coefficient map is the residue
map followed by the field embedding, so a coefficient whose image in the quotient
is a unit has nonzero residue and is itself a unit.

The quotient has characteristic p. Polynomial induction, using the defining
relations and the Frobenius identity for sums, shows that every b in the quotient
satisfies b^p = c for a coefficient c. In A, either c or 1-c is a unit. Mapping this
unit to the quotient shows that either b^p or (1-b)^p is a unit, hence either b or
1-b is a unit. This is the local-ring criterion. The proof works unchanged for
n = 0, for nilpotent coefficients, and for nonreduced A. -/
theorem pthRootAlgebra_local (p n : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] [IsLocalRing A]
    (a : Fin n → A) :
    ∃ hlocal : IsLocalRing (pthRootAlgebra p n A a),
      letI := hlocal
      IsLocalHom (algebraMap A (pthRootAlgebra p n A a)) := by
  classical
  let I : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : MvPolynomial (Fin n) A) ^ p - MvPolynomial.C (a i)))
  let B := pthRootAlgebra p n A a
  let q : MvPolynomial (Fin n) A →+* B := Ideal.Quotient.mk I
  let K := IsLocalRing.ResidueField A
  let Ω := AlgebraicClosure K
  let f : A →+* Ω := (algebraMap K Ω).comp (IsLocalRing.residue A)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨α, hα⟩ : ∃ α : Fin n → Ω, ∀ i, α i ^ p = f (a i) := by
    exact Classical.axiomOfChoice (fun i ↦ IsAlgClosed.exists_pow_nat_eq (f (a i)) hp)
  let e : MvPolynomial (Fin n) A →+* Ω := MvPolynomial.eval₂Hom f α
  have hI : I ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change e (MvPolynomial.X i ^ p - MvPolynomial.C (a i)) = 0
    simp [e, hα]
  let g : B →+* Ω := Ideal.Quotient.lift I e (fun x hx ↦ hI hx)
  have hgf (x : A) : g (algebraMap A B x) = f x := by
    change e (MvPolynomial.C x) = f x
    simp [e]
  have : Nontrivial B := g.domain_nontrivial
  have : CharP B p := CharP.of_ringHom_of_ne_zero
    ((algebraMap A B).comp (algebraMap (ZMod p) A)) p (ne_of_gt hp)
  have hX (i : Fin n) : q (MvPolynomial.X i) ^ p = algebraMap A B (a i) := by
    have hmem : MvPolynomial.X i ^ p - MvPolynomial.C (a i) ∈ I :=
      Ideal.subset_span ⟨i, rfl⟩
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    change q (MvPolynomial.X i ^ p - MvPolynomial.C (a i)) = 0 at hz
    rw [map_sub, map_pow, sub_eq_zero] at hz
    exact hz
  have hpow (b : B) : ∃ c : A, algebraMap A B c = b ^ p := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change ∃ c : A, algebraMap A B c = q b ^ p
    induction b using MvPolynomial.induction_on with
    | C c =>
      exact ⟨c ^ p, (map_pow (algebraMap A B) c p)⟩
    | add b c hb hc =>
      obtain ⟨r, hr⟩ := hb
      obtain ⟨s, hs⟩ := hc
      refine ⟨r + s, ?_⟩
      rw [map_add, map_add, add_pow_char, hr, hs]
    | mul_X b i hb =>
      obtain ⟨r, hr⟩ := hb
      refine ⟨r * a i, ?_⟩
      rw [map_mul, map_mul, mul_pow, hr, hX]
  have hlocal : IsLocalRing B := IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun b ↦ by
    obtain ⟨c, hc⟩ := hpow b
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
    · left
      apply (isUnit_pow_iff (ne_of_gt hp)).mp
      rw [← hc]
      exact h.map (algebraMap A B)
    · right
      apply (isUnit_pow_iff (ne_of_gt hp)).mp
      rw [sub_pow_char, one_pow, ← hc, ← map_one (algebraMap A B), ← map_sub]
      exact h.map (algebraMap A B))
  refine ⟨hlocal, ?_⟩
  refine ⟨fun x hx ↦ ?_⟩
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  intro hz
  have hne := isUnit_iff_ne_zero.mp (hx.map g)
  apply hne
  rw [hgf]
  change algebraMap K Ω (IsLocalRing.residue A x) = 0
  rw [hz, map_zero]

end Algebra
