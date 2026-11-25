/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
import WeilConjectures.RingTheory.PBasisComplementMonomialBasis
import WeilConjectures.RingTheory.PowerSeriesResidueMonomialBasis
import Mathlib.Data.Fintype.EquivFin

/-!
# A finite basis containing one for the p-basis coefficient subring

Source: Stacks Project, More on Algebra, Tag 07P5, finiteness paragraph,
with the explicit-basis argument of the parent node, steps 3(b) and 4.
-/

@[expose] public section

set_option autoImplicit false

universe u w

attribute [local instance] ZMod.algebra

namespace RingTheory

/-- The bounded p-basis and variable monomials give a finite basis containing one.
Source: Stacks Project, Tag 07P5 (lemma-power-series-ring-subfields), first proof
paragraph; parent node steps 3(b) and 4 give the explicit basis.
(blueprint: lem-weil-pbc-power-series-subring-finite-basis).

Proof: First the span over k^p of bounded monomials supported outside J equals kJ.
It is closed under products by reducing exponents modulo p. Every nonzero element
belongs to a finite-dimensional subring on finitely many p-basis generators, so
injectivity of multiplication gives an inverse there. Split the original p-basis
monomials into their J and complementary factors. Grouping their unique coordinates
shows that the bounded J-monomials are a kJ-basis of k. Divide every power-series
and polynomial exponent by p with remainder. Group coefficients using that field
basis: the resulting coefficients, at p-divisible exponents, belong to S by hS.
Only finitely many polynomial exponents occur, so each grouped coefficient defines
an element of the polynomial ring. Comparing coefficients and using independence
of the field basis proves independence and spanning of t^E x^e y^g, with E
supported on J and all exponents below p. The index set is finite and includes
the all-zero triple, whose monomial is one. Enumerate it by Fin d to obtain b and i.
This also works when J is empty or n or m is zero, using the empty monomial. -/
theorem powerSeriesSubringFiniteBasis
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ) (J : Finset I) (kJ : Subfield k)
    (hkJ : kJ = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (S : Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hS : ∀ f, f ∈ S ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ∈ kJ ∧
        (MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) S
      (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) (i : Fin d), b i = 1 := by
  classical
  obtain ⟨b, hb⟩ := pBasisComplementMonomialBasis p k I t hpb J kJ hkJ
  obtain ⟨B, hB⟩ := powerSeriesResidueMonomialBasis p (Fact.out : p.Prime).pos
    k kJ (J → Fin p) b n m S hS
  let z : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  let q : (J → Fin p) × (Fin n → Fin p) × (Fin m → Fin p) :=
    (fun _ ↦ z, fun _ ↦ z, fun _ ↦ z)
  have hb0 : b (0 : J → Fin p) = 1 := by
    rw [hb]
    simp
  have hbq : b q.1 = 1 := by
    rw [show q.1 = (0 : J → Fin p) by ext x; simp [q, z]]
    exact hb0
  have hB0 : B q = 1 := by
    rw [hB]
    rw [hbq]
    simp [q, z]
  let e := Fintype.equivFin ((J → Fin p) × (Fin n → Fin p) × (Fin m → Fin p))
  refine ⟨_, B.reindex e, e q, ?_⟩
  simpa using hB0

end RingTheory
