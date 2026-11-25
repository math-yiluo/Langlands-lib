/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Tensor

/-!
# Flatness in short exact sequences

Let `0 ⟶ K ⟶ M ⟶ N ⟶ 0` be a short exact sequence of modules over a commutative ring `A`.
If `M` is flat and `K ⊗ A/I ⟶ M ⊗ A/I` is injective for every ideal `I`, then `N` is flat
(`Module.Flat.of_exact_of_lTensor_quotient_injective`): `Tor₁(A/I, N)` is the kernel of that map.

The proof is a diagram chase in the tensor products with `0 ⟶ I ⟶ A ⟶ A/I ⟶ 0`, using right
exactness of the tensor product.
-/

@[expose] public section

universe u

open TensorProduct

namespace Module.Flat

variable {A : Type u} [CommRing A] {K M N : Type u} [AddCommGroup K] [Module A K]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {f : K →ₗ[A] M} {g : M →ₗ[A] N}

omit [AddCommGroup N] [Module A N] in
/-- Tensoring on the left and on the right commute. -/
private lemma rTensor_lTensor_apply {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] (h : P →ₗ[A] Q) (f : K →ₗ[A] M) (x : P ⊗[A] K) :
    h.rTensor M (f.lTensor P x) = f.lTensor Q (h.rTensor K x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

/-- **`Tor₁(A/I, N)` as a kernel.** If `0 ⟶ K ⟶ M ⟶ N ⟶ 0` is exact, `M` is flat and
`A/I ⊗ K ⟶ A/I ⊗ M` is injective for every ideal `I`, then `N` is flat. -/
theorem of_exact_of_lTensor_quotient_injective [Flat A M] (hfg : Function.Exact f g)
    (hg : Function.Surjective g)
    (h : ∀ I : Ideal A, Function.Injective (f.lTensor (A ⧸ I))) : Flat A N := by
  rw [iff_rTensor_injective]
  intro I _
  rw [injective_iff_map_eq_zero]
  intro w hw
  let ι : I →ₗ[A] A := I.subtype
  let q : A →ₗ[A] A ⧸ I := I.mkQ
  have hιq : Function.Exact ι q := by
    intro x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have hq : Function.Surjective q := Submodule.mkQ_surjective I
  obtain ⟨cI, rfl⟩ := LinearMap.lTensor_surjective I hg w
  -- the image of `cI` in `A ⊗ M` comes from `A ⊗ K`
  have h₁ : g.lTensor A (ι.rTensor M cI) = 0 := by
    rw [← rTensor_lTensor_apply]
    exact hw
  obtain ⟨zA, hzA⟩ := ((_root_.lTensor_exact A hfg hg) _).1 h₁
  -- the image of `zA` in `A/I ⊗ K` vanishes
  have h₂ : q.rTensor K zA = 0 := by
    refine h I ?_
    rw [map_zero, ← rTensor_lTensor_apply, hzA, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      hιq.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨zI, hzI⟩ := ((_root_.rTensor_exact K hιq hq) _).1 h₂
  -- hence `cI` comes from `I ⊗ K`, as `I ⊗ M ⟶ A ⊗ M` is injective
  have h₃ : cI = f.lTensor I zI := by
    refine rTensor_preserves_injective_linearMap (M := M) ι Subtype.val_injective ?_
    rw [rTensor_lTensor_apply, hzI, hzA]
  rw [h₃, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hfg.linearMap_comp_eq_zero,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

end Module.Flat
