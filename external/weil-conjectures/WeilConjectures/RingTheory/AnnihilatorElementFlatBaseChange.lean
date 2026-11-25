/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Maps

/-! # Annihilator of an element under flat base change

Source: Stacks Project, Algebra, Lemma Tag 07T8 (`lemma-annihilator-flat-base-change`),
first assertion with `M = R` and `m = x`
(blueprint: lem-weil-pbc-annihilator-element-flat-base-change).
-/

@[expose] public section

universe u v

namespace RingHom

/--
Source: Stacks Project, Algebra, Lemma Tag 07T8, first assertion
(blueprint: lem-weil-pbc-annihilator-element-flat-base-change).

Let `φ : R →+* S` be flat and `x : R`. The annihilator ideal of the image of
`x` is the extension of the annihilator ideal of `x`. The proof tensors the
exact sequence given by multiplication by `x` with the flat `R`-module `S`.

1. Put `I = Ann_R(x)`. Multiplication by `x` has kernel `I`, so the sequence
   `0 → I → R → R`, with inclusion followed by multiplication by `x`, is exact.
2. Flatness (`def-weil-pbc-flat-ring-map`) preserves this exact sequence after
   tensoring with `S` (`lem-weil-pbc-flat-tensor-exact`). Identify `R ⊗[R] S`
   with `S` by `r ⊗ s ↦ φ(r)s`. Multiplication by `x` then becomes multiplication
   by `φ(x)`, and the inclusion becomes `α : I ⊗[R] S → S`,
   `a ⊗ s ↦ φ(a)s`. Thus the image of `α` is the annihilator of `φ(x)`.
3. The image of `α` consists of finite sums of `φ(a)s` with `a ∈ I` and `s ∈ S`.
   This is exactly `Ideal.map φ I`, giving the asserted equality.
-/
theorem annihilator_element_flat_base_change {R : Type u} {S : Type v}
    [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (x : R) :
    Module.annihilator S (Ideal.span ({φ x} : Set S)) =
      Ideal.map φ (Module.annihilator R (Ideal.span ({x} : Set R))) := by
  let : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  let f : R →ₗ[R] R := LinearMap.mulRight R x
  let I := LinearMap.ker f
  let e := TensorProduct.lid R S
  have hI : I = Module.annihilator R (Ideal.span ({x} : Set R)) := by
    ext r
    change r * x = 0 ↔ r ∈ (Submodule.span R ({x} : Set R)).annihilator
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have he (t : TensorProduct R R S) : e (f.rTensor S t) = e t * φ x := by
    induction t using TensorProduct.inductionOn with
    | tmul r s =>
      change φ (r * x) * s = (φ r * s) * φ x
      simp [mul_comm, mul_left_comm]
    | add t t' ht ht' => simp [ht, ht', add_mul]
  have hex := Module.Flat.rTensor_exact S (LinearMap.exact_subtype_ker_map f)
  apply le_antisymm
  · intro s hs
    have hsx : s * φ x = 0 := by
      change s ∈ (Submodule.span S ({φ x} : Set S)).annihilator at hs
      simpa only [smul_eq_mul] using
        (Submodule.mem_annihilator_span_singleton (φ x) s).mp hs
    have hz : f.rTensor S (TensorProduct.tmul R (1 : R) s) = 0 := by
      apply e.injective
      simpa [e, hsx] using he (TensorProduct.tmul R (1 : R) s)
    obtain ⟨t, ht⟩ := (hex (TensorProduct.tmul R (1 : R) s)).mp hz
    have hm : e (I.subtype.rTensor S t) ∈
        Ideal.map φ (Module.annihilator R (Ideal.span ({x} : Set R))) := by
      clear ht
      induction t using TensorProduct.inductionOn with
      | tmul r z =>
        have hr : (r : R) ∈ Module.annihilator R (Ideal.span ({x} : Set R)) :=
          hI ▸ r.property
        have hmap := Ideal.mem_map_of_mem φ hr
        change φ (r : R) * z ∈ _
        simpa only [mul_comm] using
          (Ideal.map φ (Module.annihilator R (Ideal.span ({x} : Set R)))).mul_mem_left z hmap
      | add t t' ht ht' => simpa using add_mem ht ht'
    change e (I.subtype.rTensor S t) ∈ _ at hm
    rw [ht] at hm
    simpa [e] using hm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ r ∈ (Submodule.span S ({φ x} : Set S)).annihilator
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, ← map_mul]
    have hrx : r * x = 0 := by
      change r ∈ (Submodule.span R ({x} : Set R)).annihilator at hr
      simpa only [smul_eq_mul] using
        (Submodule.mem_annihilator_span_singleton x r).mp hr
    rw [hrx, map_zero]

end RingHom
