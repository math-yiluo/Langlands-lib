/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Basis.SMul
import WeilConjectures.RingTheory.ZeroVariableConormalStabilization

/-! Auxiliary stabilization result for localized conormal bases. -/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra

/-- Realize a stable trivialization by adjoining exactly `r` zero variables and choosing
initial relations whose localized conormal classes form a basis of rank exactly `q`.
No smoothness hypothesis or rank bound on the polynomial variables is used here.

Source: Stacks Project, Tag 07EZ, proof of part (e), stabilization and choice of relations
(blueprint: lem-weil-pbc-smooth-stable-conormal-basis-unbounded).

Proof: adjoin exactly r variables sent to zero using the zero-variable conormal
stabilization theorem. Its localized conormal module is the product of the old
localized conormal module and A_a^r. Compose that equivalence with the input stable
trivialization and transport the standard Fin q basis backwards. Mathlib identifies
the base-change map x ↦ 1 ⊗ x with module localization. Its fraction-surjectivity
property supplies, for each basis vector, a denominator s_j in the powers of a and
a conormal numerator x_j such that s_j times the vector equals 1 ⊗ x_j. Lift x_j
through the surjective conormal quotient map to g_j in the kernel. Each denominator
maps to a unit in A_a, so rescaling the basis by those units gives a basis whose
vectors are exactly 1 ⊗ [g_j]. Define the new relation list by these q numerators
followed by all m₀+r relations of the stabilized presentation. Every entry belongs
to the kernel and the appended subfamily already generates the kernel, so the full
list does as well. Keep the generators fixed, giving definitional equality of the
conormal modules, and index the list by Fin (q+(m₀+r)). The first q entries are the
numerators. Thus q≤m and all displayed basis equalities hold, including q=0 and zero
localizations. Only existential theorem data are produced. -/
theorem exists_stabilized_presentation_localized_conormal_basis
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A)
    {n₀ m₀ : ℕ} (P₀ : Presentation R A (Fin n₀) (Fin m₀)) (r q : ℕ)
    (hstable : Nonempty
      (((Localization.Away a ⊗[A] P₀.toExtension.Cotangent) ×
        (Fin r → Localization.Away a)) ≃ₗ[Localization.Away a]
        (Fin q → Localization.Away a))) :
    ∃ (m : ℕ) (P : Presentation R A (Fin (n₀ + r)) (Fin m)) (hc : q ≤ m)
      (b : Module.Basis (Fin q) (Localization.Away a)
        (Localization.Away a ⊗[A] P.toExtension.Cotangent)),
      ∀ j : Fin q, b j = 1 ⊗ₜ[A]
        (Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (Fin.castLE hc j),
            P.relation_mem_ker _⟩) := by
  classical
  obtain ⟨P₁, ⟨e⟩⟩ :=
    exists_zero_variable_presentation_localized_cotangent_equiv R A a P₀ r
  obtain ⟨e₀⟩ := hstable
  let b₀ := (Pi.basisFun (Localization.Away a) (Fin q)).map (e.trans e₀).symm
  let f := TensorProduct.mk A (Localization.Away a) P₁.toExtension.Cotangent 1
  have hlift (j : Fin q) : ∃ (g : P₁.toExtension.ker)
      (s : Submonoid.powers a), s • b₀ j = f (Extension.Cotangent.mk g) := by
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers a) f (b₀ j)
    obtain ⟨g, rfl⟩ := Extension.Cotangent.mk_surjective x
    exact ⟨g, s, hs⟩
  choose g s hs using hlift
  let w : Fin q → (Localization.Away a)ˣ := fun j =>
    (IsLocalization.map_units (Localization.Away a) (s j)).unit
  let b := b₀.unitsSMul w
  have hb (j : Fin q) : b j = 1 ⊗ₜ[A] Extension.Cotangent.mk (g j) := by
    rw [Module.Basis.unitsSMul_apply]
    change (↑(w j) : Localization.Away a) • b₀ j = f (Extension.Cotangent.mk (g j))
    simpa only [w, IsUnit.unit_spec, algebraMap_smul, Submonoid.smul_def] using hs j
  let rel : Fin (q + (m₀ + r)) → P₁.Ring :=
    Sum.elim (fun j => (g j).val) P₁.relation ∘ finSumFinEquiv.symm
  have hrel : Ideal.span (Set.range rel) = P₁.ker := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨i, rfl⟩
      dsimp only [rel, Function.comp_apply]
      cases finSumFinEquiv.symm i with
      | inl j => exact (g j).property
      | inr k => exact P₁.relation_mem_ker k
    · rw [← P₁.span_range_relation_eq_ker]
      apply Ideal.span_mono
      rintro x ⟨i, rfl⟩
      exact ⟨finSumFinEquiv (Sum.inr i), by simp [rel]⟩
  let P : Presentation R A (Fin (n₀ + r)) (Fin (q + (m₀ + r))) :=
    { toGenerators := P₁.toGenerators
      relation := rel
      span_range_relation_eq_ker := hrel }
  have hc : q ≤ q + (m₀ + r) := Nat.le_add_right _ _
  refine ⟨q + (m₀ + r), P, hc, b, ?_⟩
  intro j
  have hj : Fin.castLE hc j = Fin.castAdd (m₀ + r) j := rfl
  simpa only [P, hj, rel, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd,
    Sum.elim_inl] using hb j

end Algebra
