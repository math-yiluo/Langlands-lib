/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Differentials of a presentation adjoining p-th roots

Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (2) => (4)
(blueprint: lem-weil-pbc-pth-root-presentation-differentials).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace KaehlerDifferential

variable (p n : ℕ) (A : Type u) [CommRing A] [Algebra (ZMod p) A] (a : Fin n → A)

local notation "P" => MvPolynomial (Fin n) A
local notation "I" => Ideal.span (Set.range (fun j : Fin n =>
  (MvPolynomial.X j : P) ^ p - MvPolynomial.C (a j)))
local notation "B" => P ⧸ I

private theorem relative_relation_zero (g : P) (hg : g ∈ I) :
    (1 : B) ⊗ₜ[P] D A P g = 0 := by
  have hp : (p : P) = 0 := by
    rw [← map_natCast (algebraMap (ZMod p) P), ZMod.natCast_self, map_zero]
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    rw [map_sub, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul P, hp]
    simp
  | zero => simp
  | add g h _ _ hg hh => simp [TensorProduct.tmul_add, hg, hh]
  | smul r g hg ih =>
    have hq : algebraMap P B g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
    simp only [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add,
      TensorProduct.tmul_smul]
    rw [ih, smul_zero, zero_add, TensorProduct.smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, hq, TensorProduct.zero_tmul]

private theorem relative_basis :
    ∃ b : Module.Basis (Fin n) B Ω[B⁄A],
      ∀ j : Fin n, b j = D A B (Ideal.Quotient.mk I (MvPolynomial.X j)) := by
  have hsur : Function.Surjective (algebraMap P B) := Ideal.Quotient.mk_surjective
  have hzero : kerCotangentToTensor A P B = 0 := by
    ext x
    obtain ⟨g, rfl⟩ := Ideal.toCotangent_surjective _ x
    rw [kerCotangentToTensor_toCotangent]
    exact relative_relation_zero p n A a g.val (by
      simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using g.property)
  have hbij : Function.Bijective (mapBaseChange A P B) := by
    refine ⟨?_, mapBaseChange_surjective A P B hsur⟩
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange A P B hsur x).mp hx
    simpa only [hzero, LinearMap.zero_apply] using hy.symm
  let e := LinearEquiv.ofBijective (mapBaseChange A P B) hbij
  refine ⟨((mvPolynomialBasis A (Fin n)).baseChange B).map e, ?_⟩
  intro j
  simp [e, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    mvPolynomialBasis_apply, mapBaseChange_tmul, map_D]

private theorem coefficient_exact :
    Function.Exact
      (Finsupp.linearCombination B
        (fun j : Fin n => (1 : B) ⊗ₜ[A] D (ZMod p) A (a j)))
      (mapBaseChange (ZMod p) A B) := by
  classical
  let x : Fin n → B := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have heval : MvPolynomial.aeval x = Ideal.Quotient.mkₐ A I := by
    ext j
    simp [x]
  let Q : Algebra.Generators A B (Fin n) :=
    { val := x
      σ' := fun b => (Ideal.Quotient.mk_surjective b).choose
      aeval_val_σ' := fun b => by
        rw [heval]
        exact (Ideal.Quotient.mk_surjective b).choose_spec
      algebra := inferInstance
      algebraMap_eq := by
        rw [heval]
        rfl }
  have hker : Q.ker = I := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    change RingHom.ker (MvPolynomial.aeval x).toRingHom = I
    rw [heval]
    exact Ideal.Quotient.mkₐ_ker A I
  let δ := Algebra.Generators.H1Cotangent.δ Q (Algebra.Generators.self (ZMod p) A)
  let c := Algebra.Generators.H1Cotangent.δAux (ZMod p) Q
  let ε := Finsupp.linearCombination B
    (fun j : Fin n => (1 : B) ⊗ₜ[A] D (ZMod p) A (a j))
  have hc (j : Fin n) : c ((MvPolynomial.X j : P) ^ p - MvPolynomial.C (a j)) =
      -((1 : B) ⊗ₜ[A] D (ZMod p) A (a j)) := by
    simp [c, map_sub, MvPolynomial.X_pow_eq_monomial,
      Algebra.Generators.H1Cotangent.δAux_monomial,
      Algebra.Generators.H1Cotangent.δAux_C]
  have hcycle (g : Q.ker) :
      Q.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk g) = 0 := by
    rw [Algebra.Extension.cotangentComplex_mk]
    exact relative_relation_zero p n A a g.val (by simpa only [hker] using g.property)
  have hmem (g : P) (hg : g ∈ I) : c g ∈ LinearMap.range ε := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      rw [hc]
      apply Submodule.neg_mem
      exact ⟨Finsupp.single j 1, by simp [ε]⟩
    | zero => simp
    | add g h _ _ hg hh =>
      rw [map_add]
      exact Submodule.add_mem _ hg hh
    | smul r g hg ih =>
      have hq : algebraMap P B g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
      change c (r * g) ∈ _
      rw [Algebra.Generators.H1Cotangent.δAux_mul]
      have hgz : g • c r = 0 := by
        rw [← IsScalarTower.algebraMap_smul B, hq, zero_smul]
      rw [hgz, add_zero]
      rw [← IsScalarTower.algebraMap_smul B]
      exact Submodule.smul_mem _ _ ih
  have hrange : LinearMap.range δ = LinearMap.range ε := by
    apply le_antisymm
    · rintro y ⟨h, rfl⟩
      obtain ⟨g, hg⟩ := Algebra.Extension.Cotangent.mk_surjective h.val
      have hh : h = ⟨Algebra.Extension.Cotangent.mk g, hcycle g⟩ := Subtype.ext hg.symm
      rw [hh, Algebra.Generators.H1Cotangent.δ_eq_δAux]
      exact hmem g.val (by simpa only [hker] using g.property)
    · rw [Finsupp.range_linearCombination]
      apply Submodule.span_le.mpr
      rintro y ⟨j, rfl⟩
      have hg : ((MvPolynomial.X j : P) ^ p - MvPolynomial.C (a j)) ∈ Q.ker := by
        rw [hker]
        exact Ideal.subset_span ⟨j, rfl⟩
      let g : Q.ker := ⟨_, hg⟩
      refine ⟨-⟨Algebra.Extension.Cotangent.mk g, hcycle g⟩, ?_⟩
      rw [map_neg, Algebra.Generators.H1Cotangent.δ_eq_δAux]
      change -c _ = _
      rw [hc, neg_neg]
  intro y
  have hex := Algebra.Generators.H1Cotangent.exact_δ_map Q
    (Algebra.Generators.self (ZMod p) A) y
  change mapBaseChange (ZMod p) A B y = 0 ↔ y ∈ LinearMap.range ε
  rw [← hrange]
  exact hex

/-- Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (2) => (4).
(blueprint: lem-weil-pbc-pth-root-presentation-differentials)
The relative differentials have the indicated basis, and the absolute differential sequence
has kernel generated by the differentials of the coefficients.

Proof (Stacks 07E5, (2) => (4), using the chosen presentation directly):
1. The differential of each relation is zero over A: p = 0 in P and constants
   differentiate to zero. Ideal-span induction and Leibniz then show that
   1 tensor dg = 0 for every g in I, since each relation vanishes in B.
2. The conormal exact sequence makes mapBaseChange A P B injective; the quotient
   map is surjective, so this map is bijective. Base-change the polynomial
   differential basis and transport it through this map to obtain the stated basis.
3. Use the quotient generators Q with their actual quotient section. Mathlib's
   presentation-level connecting map is computed by its coefficient-derivative map c.
   Every conormal class is a cycle by step 1. For f_j = X_j^p - C(a_j),
   c(f_j) = -1 tensor d(a_j). Ideal-span induction using the Leibniz formula for c
   gives c(I) contained in the range of the displayed linear combination map.
   Conversely, each generator is the connecting image of the negative relation cycle.
   Thus the two ranges agree. Presentation-level Jacobi-Zariski exactness identifies
   this range with the kernel of mapBaseChange (ZMod p) A B.
4. The remaining exactness and surjectivity are Mathlib's general differential
   transitivity sequence. No comparison with the canonical presentation is needed. -/
theorem pthRootPresentation_differentials [Fact p.Prime] :
    (∃ b : Module.Basis (Fin n) B Ω[B⁄A],
      ∀ j : Fin n, b j = D A B (Ideal.Quotient.mk I (MvPolynomial.X j))) ∧
    Function.Exact
      (Finsupp.linearCombination B
        (fun j : Fin n => (1 : B) ⊗ₜ[A] D (ZMod p) A (a j)))
      (mapBaseChange (ZMod p) A B) ∧
    Function.Exact (mapBaseChange (ZMod p) A B) (map (ZMod p) A B B) ∧
    Function.Surjective (map (ZMod p) A B B) := by
  refine ⟨relative_basis p n A a, coefficient_exact p n A a, ?_, ?_⟩
  · exact exact_mapBaseChange_map (ZMod p) A B
  · exact map_surjective (ZMod p) A B

end KaehlerDifferential
