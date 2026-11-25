/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Differential decomposition of a simple transcendental field extension

Source: Stacks Project, Tags 00RS, 00RX, 00RT, 00S2, and 07FI.
(blueprint: lem-weil-pbc-simple-transcendental-differential-decomposition).
-/

@[expose] public section

set_option autoImplicit false
universe u v w

open scoped TensorProduct

namespace KaehlerDifferential

/-- The differentials of a simple rational extension split into base differentials
and the differential of the transcendental generator. Source: Stacks Project,
Tags 00RS, 00RX, 00RT, and 00S2; Tag 07FI, transcendental case.
(blueprint: lem-weil-pbc-simple-transcendental-differential-decomposition).

Proof: As m = 1, transcendence makes y algebraically independent. Evaluation
identifies P = F₀[X_j] with A = F₀[y_j]. The adjoin condition expresses every
f ∈ F as a quotient of two elements of A. Thus F is a fraction field of A and,
through evaluation, of P. The map P → F is formally étale. Scalar-extend the
polynomial basis of Ω[P/F₀] and transport it through the canonical étale
differential equivalence to obtain a relative basis b_j = D F₀ F (y_j).
The purely transcendental field extension F/F₀ is formally smooth by Mathlib.
Jacobi–Zariski and vanishing of H₁(L_{F/F₀}) make the canonical map
u : F ⊗[F₀] Ω[F₀/k] → Ω[F/k] injective. The first fundamental sequence identifies
its image with the kernel of v : Ω[F/k] → Ω[F/F₀]. Define the section
s(c) = sum_j c_j D k F (y_j). Its image under v is the relative basis expansion,
so v(s(c)) = b.equivFun.symm(c). Hence (x,c) ↦ u(x) + s(c) is injective: apply v
to determine c, then use injectivity of u to determine x. It is surjective:
for ω, take c = b.equivFun(v(ω)); then ω − s(c) lies in ker v = range u.
This gives the required canonical equivalence and formula. The argument works
in every characteristic and without a finite basis of the base differentials. -/
theorem exists_simple_transcendental_differential_decomposition
    (k : Type u) (F₀ : Type v) (F : Type w) [Field k] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra k F] [Algebra F₀ F] [IsScalarTower k F₀ F]
    (m : ℕ) (y : Fin m → F) (hm : m = 1)
    (hy : ∀ j, Transcendental F₀ (y j))
    (hgen : IntermediateField.adjoin F₀ (Set.range y) = ⊤) :
    ∃ E : ((F ⊗[F₀] KaehlerDifferential k F₀) × (Fin m → F)) ≃ₗ[F]
        KaehlerDifferential k F,
      ∀ (x : F ⊗[F₀] KaehlerDifferential k F₀) (c : Fin m → F),
        E (x, c) = mapBaseChange k F₀ F x + ∑ j, c j • D k F (y j) := by
  classical
  subst m
  have hind : AlgebraicIndependent F₀ y :=
    algebraicIndependent_unique_type_iff.mpr (hy default)
  let P := MvPolynomial (Fin 1) F₀
  let A := Algebra.adjoin F₀ (Set.range y)
  let e : P ≃ₐ[F₀] A := hind.aevalEquiv
  let : Algebra P F := (MvPolynomial.aeval y).toRingHom.toAlgebra
  have : IsScalarTower F₀ P F := IsScalarTower.of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  let : Algebra A F := A.val.toRingHom.toAlgebra
  have : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr Subtype.val_injective
  have : IsFractionRing A F := IsFractionRing.of_field _ _ fun f ↦ by
    have hf : f ∈ IntermediateField.adjoin F₀ (Set.range y) := by rw [hgen]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp hf
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  have : IsFractionRing P F := IsFractionRing.of_ringEquiv_left e.toRingEquiv fun p ↦ by
    change MvPolynomial.aeval y p = (e p : F)
    exact (hind.algebraMap_aevalEquiv p).symm
  have : Algebra.FormallyEtale P F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  let brel := ((mvPolynomialBasis F₀ (Fin 1)).baseChange F).map
    (tensorKaehlerEquivOfFormallyEtale F₀ P F)
  have hbrel (j : Fin 1) : brel j = D F₀ F (y j) := by
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
    change (tensorKaehlerEquivOfFormallyEtale F₀ P F)
      (1 ⊗ₜ[P] (mvPolynomialBasis F₀ (Fin 1)) j) = D F₀ F (y j)
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
      one_smul, mvPolynomialBasis_apply, map_D]
    congr 1
    exact MvPolynomial.aeval_X y j
  have : Algebra.FormallySmooth F₀ F :=
    Algebra.FormallySmooth.of_algebraicIndependent hind hgen
  let u := mapBaseChange k F₀ F
  let v := map k F₀ F F
  have hu : Function.Injective u := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (Algebra.H1Cotangent.exact_δ_mapBaseChange k F₀ F)).mpr
    ext x
    simp only [Subsingleton.elim x 0, map_zero]
  let s : (Fin 1 → F) →ₗ[F] KaehlerDifferential k F :=
    { toFun := fun c ↦ ∑ j, c j • D k F (y j)
      map_add' := by intro b c; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [mul_smul] }
  let q := brel.equivFun
  have hvs (c : Fin 1 → F) : v (s c) = q.symm c := by
    simp [s, v, Module.Basis.equivFun_symm_apply, q, hbrel]
  have hvu (x : F ⊗[F₀] KaehlerDifferential k F₀) : v (u x) = 0 :=
    (exact_mapBaseChange_map k F₀ F (u x)).mpr ⟨x, rfl⟩
  let f : ((F ⊗[F₀] KaehlerDifferential k F₀) × (Fin 1 → F)) →ₗ[F]
      KaehlerDifferential k F :=
    u.comp (LinearMap.fst F _ _) + s.comp (LinearMap.snd F _ _)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hc : x.2 = y.2 := q.symm.injective (by
        simpa only [f, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.fst_apply, LinearMap.snd_apply, map_add, hvu, hvs, zero_add]
          using congrArg v h)
      exact Prod.ext (hu (by
        simpa only [f, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.fst_apply, LinearMap.snd_apply, hc, add_left_inj] using h)) hc
    · intro ω
      let c := q (v ω)
      obtain ⟨x, hx⟩ := (exact_mapBaseChange_map k F₀ F (ω - s c)).mp (by
        rw [map_sub, hvs]; simp [c, v])
      exact ⟨(x, c), by
        change u x + s c = ω
        rw [hx, sub_add_cancel]⟩
  exact ⟨LinearEquiv.ofBijective f hf, fun x c ↦ rfl⟩

end KaehlerDifferential
