/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Detecting surjectivity modulo a Jacobson ideal

Source: Stacks Project, More on Algebra, Tag 00DV.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- Surjectivity modulo an ideal in the Jacobson radical detects surjectivity onto a finite module.
Source: Stacks Project, Algebra, Tag 00DV, Nakayama's lemma, applied in Tag 0BCB
(blueprint: lem-sc-finite-module-surjective-mod-ideal).

Proof: The unit assumption puts I in the Jacobson radical. Identify extension of scalars
with M/IM and N/IN using the tensor-quotient equivalences. Surjectivity of the reduced
map gives surjectivity of M → N/IN. Apply Nakayama to the finite target N and the range
of f to conclude that the range is all of N. -/
theorem surjective_of_extendScalars_mod_ideal {R : Type u} [CommRing R]
    (I : Ideal R) (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    (M N : ModuleCat.{max u v} R) [Module.Finite R N] (f : M ⟶ N)
    (hf : Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)) :
    Function.Surjective f := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := by
    intro x hx
    apply Ideal.mem_jacobson_bot.mpr
    intro y
    simpa only [add_comm] using hunits ⟨x * y, I.mul_mem_right y hx⟩
  apply LinearMap.surjective_of_surjective_comp_mkQ f.hom I hI
  intro z
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) z
  let eM := TensorProduct.quotTensorEquivQuotSMul M I
  let eN := TensorProduct.quotTensorEquivQuotSMul N I
  obtain ⟨t, ht⟩ := hf ((1 : R ⧸ I) ⊗ₜ[R] n)
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) (eM t)
  change Submodule.Quotient.mk m = eM t at hm
  have ht' : t = (1 : R ⧸ I) ⊗ₜ[R] m := by
    apply eM.injective
    simpa only [eM, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using hm.symm
  refine ⟨m, ?_⟩
  rw [ht'] at ht
  have he := congrArg eN ht
  change eN ((LinearMap.baseChange (R ⧸ I) f.hom) ((1 : R ⧸ I) ⊗ₜ[R] m)) =
    eN ((1 : R ⧸ I) ⊗ₜ[R] n) at he
  simpa only [eN, LinearMap.baseChange_tmul,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, LinearMap.comp_apply,
    Submodule.mkQ_apply] using he

end ModuleCat
