/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.CompleteLocalMapRegularPresentation
import WeilConjectures.RingTheory.CompleteLocalBaseChangeFiber
import WeilConjectures.RingTheory.FormallySmoothAdicBaseChange
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import WeilConjectures.RingTheory.RegularPresentationFlatFiber

/-!
# Lifting formally smooth complete local algebras from a residue field

Source: Stacks Project, More on Algebra, Lemma 07NR (lemma-lift-fs).
(blueprint: lem-weil-pbc-fs-adic-lift-from-residue-field)
-/

@[expose] public section

universe u v

namespace Algebra

/-- A formally smooth complete local algebra over a residue field lifts to one over
its complete local base (Stacks Project, More on Algebra, Lemma 07NR).
(blueprint: lem-weil-pbc-fs-adic-lift-from-residue-field)

Proof (following the six steps of the node):

1. Apply `lem-weil-pbc-complete-local-map-regular-presentation` to the local map
   A₀ → k₀ → E. Obtain compatible surjections q : R → A₀ and v : S → E and
   u : R → S. The residue field of R is k₀, and its parameters t₁, …, t_d form
   part of a regular system of parameters of S. Thus v induces a surjective
   k₀-algebra map from S̄ = S/(t₁, …, t_d) to E.
2. By `lem-weil-pbc-regular-local-generators-regular-sequence`, S̄ is regular local.
   By `lem-weil-pbc-fs-adic-field-geometrically-regular`, E is geometrically regular
   over k₀, hence regular local (the local case of `def-weil-regular-scheme`).
   By `lem-weil-pbc-regular-local-quotient-kernel-parameters`, the kernel of S̄ → E
   has generators x̄₁, …, x̄_r extending to parameters of S̄. Lift them to x_i in
   S; they lie in ker v.
3. The t-classes are independent in m_S/m_S², and the x-classes are independent
   modulo the t-classes. Hence their combined classes are independent. Extend
   them to a residue-field basis of m_S/m_S² and lift the remaining classes.
   `lem-weil-pbc-nakayama-local-generators` gives generators of m_S, and
   `lem-weil-pbc-regular-local-cotangent-dimension` gives their number as dim S.
   Consequently t₁, …, t_d, x₁, …, x_r extend to a regular system of parameters.
4. Put T = S/(x₁, …, x_r). Permuting the parameters and using
   `lem-weil-pbc-regular-local-generators-regular-sequence` makes T regular local
   with the t-images a regular sequence. By `lem-weil-pbc-flat-over-regular`,
   R → T is flat. By `lem-weil-pbc-complete-local-quotient`, T is complete
   Noetherian local. The induced map T/m_R T → E is a k₀-algebra isomorphism,
   since its presentation is S̄/(x̄₁, …, x̄_r) and this ideal is the kernel.
5. Transport the lifting property `theorem-finite-etale-covers-proper-henselian--2` from E to
   T/m_R T along that isomorphism, which identifies their maximal ideals.
   By `lem-weil-pbc-flat-formally-smooth-closed-fibre-adic`, the flat local map
   R → T is formally smooth for the maximal-ideal-adic topology.
6. Set I = ker q and C = T/IT. By `lem-weil-pbc-tensor-quotient-base-change`,
   this is T ⊗[R] A₀. Since IT lies in m_T, `lem-weil-pbc-complete-local-quotient`
   gives a complete Noetherian local ring C. The induced γ : A₀ → C is local:
   q maps m_R onto m₀ and those images land in m_C. By
   `lem-weil-pbc-fs-adic-base-change`, C is formally smooth over A₀ for the
   extended m_T-adic topology, which is the m_C-adic topology. Finally
   C/m₀C = T/m_R T ≅ E. This isomorphism is induced by v; for a in A₀ choose
   b in R with q(b) = a. The original diagram identifies v(u(b)) with the
   prescribed image of a in E, proving the required A₀-algebra compatibility. -/
theorem exists_formallySmoothAdic_lift_residue_field
    (A₀ : Type u) [CommRing A₀] [IsNoetherianRing A₀] [IsLocalRing A₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀]
    (E : Type v) [CommRing E] [IsNoetherianRing E] [IsLocalRing E]
    [IsAdicComplete (IsLocalRing.maximalIdeal E) E]
    [Algebra (IsLocalRing.ResidueField A₀) E]
    [Algebra A₀ E]
    [IsScalarTower A₀ (IsLocalRing.ResidueField A₀) E]
    (hE : FormallySmoothAdic (IsLocalRing.ResidueField A₀) E
      (IsLocalRing.maximalIdeal E)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : IsNoetherianRing C)
      (_ : IsLocalRing C) (_ : IsAdicComplete (IsLocalRing.maximalIdeal C) C)
      (_ : Algebra A₀ C) (γ : A₀ →+* C),
      algebraMap A₀ C = γ ∧ IsLocalHom γ ∧
      FormallySmoothAdic A₀ C (IsLocalRing.maximalIdeal C) ∧
      ∃ σ : (C ⧸ (IsLocalRing.maximalIdeal A₀).map γ) ≃ₐ[A₀] E,
        ∀ a : A₀,
          σ (Ideal.Quotient.mkₐ A₀ ((IsLocalRing.maximalIdeal A₀).map γ)
            (algebraMap A₀ C a)) = algebraMap A₀ E a := by
  have hlocalE : IsLocalHom (algebraMap A₀ E) := by
    have hcomp : (algebraMap (IsLocalRing.ResidueField A₀) E).comp
        (IsLocalRing.residue A₀) = algebraMap A₀ E := by
      ext a
      exact (IsScalarTower.algebraMap_apply A₀ (IsLocalRing.ResidueField A₀) E a).symm
    rw [← hcomp]
    infer_instance
  obtain ⟨R, S, _, _, _, _, hR, hS, q, v, u, hq, hqLocal, hv, hvLocal,
    huLocal, hcomm, hres, hparams, _, hfiber⟩ :=
    RingHom.exists_complete_local_map_regular_presentation (algebraMap A₀ E)
  have := hR
  have := hS
  have := hqLocal
  have := hvLocal
  have := huLocal
  obtain ⟨T, _, _, _, _, _, hTLocal, hTFlat, e, he, hTFiber⟩ :=
    RingHom.exists_flat_complete_model_of_regular_presentation A₀ E hE R S q v u
      hq hv hcomm hres hparams hfiber
  have := hTLocal
  have halg : (algebraMap R T).toAlgebra = (inferInstance : Algebra R T) := by
    apply Algebra.algebra_ext
    intro r
    rfl
  have hT : FormallySmoothAdic R T (IsLocalRing.maximalIdeal T) := by
    have h := RingHom.formallySmoothAdic_of_flat_closedFiber R T
      (algebraMap R T) hTFlat hTFiber
    rw [halg] at h
    exact h
  let : Algebra R A₀ := q.toAlgebra
  let : Algebra A₀ (TensorProduct R T A₀) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨hC, hCNoeth, hCComplete, hCLocal, hCMax, ⟨σ⟩⟩ :=
    complete_local_baseChange_closedFiber R A₀ T E hq e he
  have := hC
  have := hCNoeth
  have := hCComplete
  have hfs : FormallySmoothAdic A₀ (TensorProduct R T A₀)
      (IsLocalRing.maximalIdeal (TensorProduct R T A₀)) := by
    rw [← hCMax]
    exact formallySmoothAdic_tensorProduct R T A₀ (IsLocalRing.maximalIdeal T) hT
  refine ⟨TensorProduct R T A₀, inferInstance, hCNoeth, hC, hCComplete, inferInstance,
    algebraMap A₀ (TensorProduct R T A₀), rfl, hCLocal, hfs, σ, ?_⟩
  intro a
  exact σ.commutes a

end Algebra
