/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.PopescuDesingularize
import WeilConjectures.RingTheory.StrictlyStandardBaseChange
import WeilConjectures.RingTheory.SingularIdealMapEquiv

/-! # Desingularization with an annihilator bound

Source: Stacks Project, Tag 07CT, first paragraph of the proof, applying Tag 07CR.
(blueprint: lem-weil-pbc-desingularize-annihilator-construction).
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Construct a factorization with the relative annihilator bound, before any comparison
with the singular ideal of `D` over `R`. No annihilator equality in `R` is needed here.

Source: Stacks Project, Tag 07CT, first paragraph of the proof, applying Tag 07CR.

Proof: `D` is Noetherian since it is finitely presented over the Noetherian ring `R`.
Base change `A` to `D ⊗[R] A`, which is finitely presented over `D`. Give `Λ` its
`D`-algebra structure induced by `δ`. The tensor map sends `d ⊗ a` to `δ d * α a`.
Strict standardness is preserved by base change (Tag 07CC). The quotient map in `hquot`
induces the `D`-algebra section sending the class of `d ⊗ a` to `d` times the image of
`a` in `D/π⁴D`. On pure tensors its composite with the map to `Λ/π⁴Λ` agrees with the
tensor map by `hquot`; additive generation by pure tensors gives agreement everywhere.
Apply desingularization (Tag 07CR) over `D`. Retain its finite presentation over `D` and
its bound by the annihilator of `Ann_D(π²)/Ann_D(π)`. An element `r` is in that annihilator
exactly when `π_D² * x = 0` implies `r * π_D * x = 0` for every `x`. Restrict the tensor
factorization to the two factors and restrict the scalars of the map to `Λ` to `R`.
The structure map `dB` supplies the indicated `D`-algebra structure on `B`.
(blueprint: lem-weil-pbc-desingularize-annihilator-construction). -/
theorem exists_desingularization_annihilator_bound
    (R : Type u) (Λ : Type v) (A : Type w) (D : Type z)
    [CommRing R] [CommRing Λ] [CommRing A] [CommRing D]
    [Algebra R Λ] [Algebra R A] [Algebra R D] [IsNoetherianRing R]
    [FinitePresentation R A] [FinitePresentation R D]
    (π : R) (α : A →ₐ[R] Λ) (δ : D →ₐ[R] Λ)
    (hΛ : ∀ l : Λ, l * algebraMap R Λ π = 0 ↔
      l * (algebraMap R Λ π) ^ 2 = 0)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hquot : ∃ φ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
      ∀ (a : A) (d : D),
        φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d)) :
    ∃ (B : Type (max u v w z)) (_ : CommRing B) (_ : Algebra R B),
      ∃ (β : B →ₐ[R] Λ) (aB : A →ₐ[R] B) (dB : D →ₐ[R] B),
        @FinitePresentation D B _ _ dB.toRingHom.toAlgebra ∧
        β.comp aB = α ∧ β.comp dB = δ ∧
        Ideal.span (dB ''
          {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
            r * algebraMap R D π * x = 0}) ≤
          @singularIdeal D B _ _ dB.toRingHom.toAlgebra := by
  classical
  let : Algebra D Λ := δ.toRingHom.toAlgebra
  let : IsScalarTower R D Λ := IsScalarTower.of_algHom δ
  let : IsNoetherianRing D := FiniteType.isNoetherianRing R D
  let T := _root_.TensorProduct R D A
  let p := algebraMap R D π
  let α' : T →ₐ[D] Λ := AlgHom.liftEquiv R D A Λ α
  have hpΛ : algebraMap D Λ p = algebraMap R Λ π := δ.commutes π
  have hpT : algebraMap D T p = (_root_.TensorProduct.tmul R 1 (algebraMap R A π) : T) := by
    rw [← IsScalarTower.algebraMap_apply R D T]
    exact (TensorProduct.includeRight (R := R) (A := D) (B := A)).commutes π |>.symm
  have hstandard' : IsStrictlyStandardElement (R := D) (algebraMap D T p) := by
    rw [hpT]
    exact (standardElements_baseChange (R' := D) (algebraMap R A π)).2 hstandard
  obtain ⟨φ, hφ⟩ := hquot
  let ID := Ideal.span ({p ^ 4} : Set D)
  let IT := Ideal.span ({(algebraMap D T p) ^ 4} : Set T)
  let IL := Ideal.span ({(algebraMap R Λ π) ^ 4} : Set Λ)
  let f : A →ₐ[R] D ⧸ ID := φ.comp (Ideal.Quotient.mkₐ R _)
  let σ : T →ₐ[D] D ⧸ ID := AlgHom.liftEquiv R D A (D ⧸ ID) f
  have hσ : ∀ t ∈ IT, σ t = 0 := by
    change IT ≤ RingHom.ker σ
    apply Ideal.span_le.mpr
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    change σ ((algebraMap D T p) ^ 4) = 0
    rw [map_pow, σ.commutes]
    change Ideal.Quotient.mk ID p ^ 4 = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  let ρ : T ⧸ IT →ₐ[D] D ⧸ ID := Ideal.Quotient.liftₐ IT σ hσ
  let δq : D ⧸ ID →ₐ[D] Λ ⧸ IL :=
    Ideal.Quotient.liftₐ ID ((Ideal.Quotient.mkₐ D IL).comp (Algebra.ofId D Λ)) (by
      change ID ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro d hd
      rcases Set.mem_singleton_iff.mp hd with rfl
      change Ideal.Quotient.mk IL (algebraMap D Λ (p ^ 4)) = 0
      rw [map_pow, hpΛ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _))
  have hcompat : δq.comp σ = (Ideal.Quotient.mkₐ D IL).comp α' := by
    apply TensorProduct.ext_ring
    ext a
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (f a)
    have ha := hφ a d hd.symm
    change δq (σ (_root_.TensorProduct.tmul R 1 a)) =
      Ideal.Quotient.mk IL (α' (_root_.TensorProduct.tmul R 1 a))
    change δq ((1 : D) • f a) = Ideal.Quotient.mk IL ((1 : D) • α a)
    simp only [one_smul]
    rw [← hd]
    change Ideal.Quotient.mk IL (δ d) = Ideal.Quotient.mk IL (α a)
    exact ha.symm
  have hρ : ∃ ρ : T ⧸ IT →ₐ[D] D ⧸ ID,
      ∀ (t : T) (d : D),
        ρ (Ideal.Quotient.mk IT t) = Ideal.Quotient.mk ID d →
        Ideal.Quotient.mk IL (α' t) = Ideal.Quotient.mk IL (algebraMap D Λ d) := by
    refine ⟨ρ, ?_⟩
    intro t d htd
    have he := DFunLike.congr_fun hcompat t
    change δq (σ t) = Ideal.Quotient.mk IL (α' t) at he
    have ht : σ t = Ideal.Quotient.mk ID d := htd
    rw [ht] at he
    exact he.symm
  have hIL : Ideal.span ({(algebraMap D Λ p) ^ 4} : Set Λ) = IL := by
    rw [hpΛ]
  obtain ⟨B, instB, instDB, hfp, β, tB, hβ, hbound⟩ :=
    exists_desingularization D Λ T p α' (by simpa [hpΛ] using hΛ) hstandard'
      (by rw [hIL]; exact hρ)
  let : CommRing B := instB
  let : Algebra D B := instDB
  let : Algebra R B := (algebraMap D B).comp (algebraMap R D) |>.toAlgebra
  let : IsScalarTower R D B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let U := ULift.{max u v w z} B
  let e : B ≃ₐ[D] U := ULift.algEquiv.symm
  let βU : U →ₐ[R] Λ := (β.comp e.symm.toAlgHom).restrictScalars R
  let aU : A →ₐ[R] U :=
    ((e.toAlgHom.comp tB).restrictScalars R).comp TensorProduct.includeRight
  let dU : D →ₐ[R] U := (Algebra.ofId D U).restrictScalars R
  have hfpU : FinitePresentation D U := FinitePresentation.equiv e
  have haU : βU.comp aU = α := by
    ext a
    have ht := DFunLike.congr_fun hβ (_root_.TensorProduct.tmul R 1 a)
    change β (tB (_root_.TensorProduct.tmul R 1 a)) = α' (_root_.TensorProduct.tmul R 1 a) at ht
    change β (tB (_root_.TensorProduct.tmul R 1 a)) = α a
    change β (tB (_root_.TensorProduct.tmul R 1 a)) = (1 : D) • α a at ht
    simpa only [one_smul] using ht
  have hdU : βU.comp dU = δ := by
    ext d
    exact (β.comp e.symm.toAlgHom).commutes d
  have hboundU : Ideal.span ((algebraMap D U) ''
      {r : D | ∀ x : D, p ^ 2 * x = 0 → r * p * x = 0}) ≤ singularIdeal D U := by
    calc
      _ = Ideal.map e.toRingHom (Ideal.span ((algebraMap D B) ''
          {r : D | ∀ x : D, p ^ 2 * x = 0 → r * p * x = 0})) := by
        rw [Ideal.map_span, Set.image_image]
        congr 1
      _ ≤ Ideal.map e.toRingHom (singularIdeal D B) := Ideal.map_mono hbound
      _ ≤ singularIdeal D U := singularIdeal_map_equiv_le e
  refine ⟨U, inferInstance, inferInstance, βU, aU, dU, ?_, haU, hdU, ?_⟩
  · have heq : dU.toRingHom.toAlgebra = (inferInstance : Algebra D U) :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    rw [heq]
    exact hfpU
  · have heq : dU.toRingHom.toAlgebra = (inferInstance : Algebra D U) :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    rw [heq]
    exact hboundU

end Algebra
