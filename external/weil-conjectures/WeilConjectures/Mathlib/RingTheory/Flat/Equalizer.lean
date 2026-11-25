/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Extension of ideals along a flat ring map commutes with finite intersections

Since base change along a flat algebra preserves kernels, extending ideals along a flat ring
map `R → S` commutes with finite intersections: `(I ⊓ J) S = I S ⊓ J S`.

## Main results

- `Ideal.map_inf_of_flat`: the binary case.
- `Ideal.map_iInf_of_flat`: the case of a finite family.
- `Module.Flat.of_exact_of_flat_of_flat`, `Module.Flat.of_exact_of_flat_of_flat_right`: an
  extension of flat modules is flat, and the kernel of a surjection of flat modules is flat.
- `Module.Flat.lTensor_injective_ker_subtype`: the kernel of the first map of a complex of flat
  modules which is universally exact in the middle stays a submodule after any base change.
- `Ideal.Quotient.flat_span_singleton_mul`: if `v₁` is a non-zerodivisor and `B ⧸ (v₁)`,
  `B ⧸ (v₂)` are flat, then so is `B ⧸ (v₁ v₂)`.
- `Algebra.TensorProduct.includeLeftRingHom_mem_nonZeroDivisors_of_flat`: a non-zerodivisor
  `f ∈ B` with `B ⧸ (f)` flat over `A` stays a non-zerodivisor after any base change `A → A'`.
-/

@[expose] public section

universe u

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

namespace Ideal

/-- Extension of ideals along a flat ring map commutes with binary intersections. The ideal
`I ⊓ J` is the kernel of `R → R ⧸ I × R ⧸ J`, and base change along `S` preserves this
kernel. -/
theorem map_inf_of_flat (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (map_inf_le _) fun x hx ↦ ?_
  let f : R →ₗ[R] (R ⧸ I) × (R ⧸ J) := I.mkQ.prod J.mkQ
  have hker : LinearMap.ker f = I ⊓ J := by
    ext r; simp [f]
  have hvan (K : Ideal R) (y : S) (hy : y ∈ K.map (algebraMap R S)) :
      y ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ K) = 0 := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        mul_one, (Submodule.Quotient.mk_eq_zero K).mpr hk, tmul_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [add_tmul, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_eq_mul, ← smul_eq_mul, ← smul_tmul', hy, smul_zero]
  have h1 : x ⊗ₜ[R] (1 : R) ∈ LinearMap.ker (AlgebraTensorModule.lTensor S S f) := by
    have hf : f 1 = LinearMap.inl R _ _ (Submodule.Quotient.mk 1) +
        LinearMap.inr R _ _ (Submodule.Quotient.mk 1) := by
      simp [f]
    rw [LinearMap.mem_ker, AlgebraTensorModule.lTensor_tmul, hf, tmul_add,
      ← LinearMap.lTensor_tmul, ← LinearMap.lTensor_tmul, hvan I x hx.1, hvan J x hx.2,
      map_zero, map_zero, add_zero]
  rw [Module.Flat.ker_lTensor_eq] at h1
  obtain ⟨u, hu⟩ := h1
  have : x = AlgebraTensorModule.rid R S S (x ⊗ₜ[R] (1 : R)) := by simp
  rw [this, ← hu]
  clear hu this
  induction u using TensorProduct.inductionOn with
  | tmul s k =>
    have hk : (k : R) ∈ I ⊓ J := hker ▸ k.2
    simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype,
      AlgebraTensorModule.rid_tmul]
    rw [Algebra.smul_def]
    exact mul_mem_right _ _ (mem_map_of_mem _ hk)
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

/-- Extension of ideals along a flat ring map commutes with finite intersections. -/
theorem map_iInf_of_flat {ι : Type*} [Finite ι] (I : ι → Ideal R) :
    (⨅ i, I i).map (algebraMap R S) = ⨅ i, (I i).map (algebraMap R S) := by
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, (s.inf I).map (algebraMap R S) =
      s.inf fun i ↦ (I i).map (algebraMap R S) by
    simpa [Finset.inf_univ_eq_iInf] using H Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => exact map_top _
  | insert i s _ ih => rw [Finset.inf_insert, Finset.inf_insert, map_inf_of_flat, ih]

end Ideal

/-- **Extensions of flat modules are flat.** In a short exact sequence
`0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules with `M'` and `M''` flat, `M` is flat. -/
lemma Module.Flat.of_exact_of_flat_of_flat {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] [Module R M'] [Module R M]
    [Module R M''] [Module.Flat R M'] [Module.Flat R M''] (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ ι hι
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : g.lTensor N x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M'') ι hι
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx, map_zero, map_zero]
  obtain ⟨y, rfl⟩ := (_root_.lTensor_exact N H hg x).mp h1
  have h2 : ι.rTensor M' y = 0 := by
    apply LinearMap.lTensor_injective_of_exact_of_flat g hg f hf H P
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx, map_zero]
  have h3 : y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M') ι hι
    rw [h2, map_zero]
  rw [h3, map_zero]

/-- **Kernels of surjections of flat modules are flat.** In a short exact sequence
`0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules with `M` and `M''` flat, `M'` is flat.
(blueprint: `lem-weil-pbc-flat-ses-kernel-flat`) -/
lemma Module.Flat.of_exact_of_flat_of_flat_right {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] [Module R M'] [Module R M]
    [Module R M''] [Module.Flat R M] [Module.Flat R M''] (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.Flat R M' := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ ι hι
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : f.lTensor N x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) ι hι
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx, map_zero, map_zero]
  exact LinearMap.lTensor_injective_of_exact_of_flat g hg f hf H N (h1.trans (map_zero _).symm)

/-- **Universal left exactness of a complex of flat modules.** Let `C₀ ⟶ C₁ ⟶ C₂` be a complex
of `R`-modules with `C₁` and `C₂` flat, which stays exact at `C₁` after tensoring with every
`R`-module. Then the kernel `Z` of `d₀` stays a submodule of `C₀` after tensoring: for every
`R`-module `M`, the map `M ⊗ Z ⟶ M ⊗ C₀` is injective.

The cokernel `Q` of `d₀` embeds universally into `C₂`, hence is flat; so is the image of `d₀`,
as the kernel of `C₁ ⟶ Q`; and `0 ⟶ Z ⟶ C₀ ⟶ im d₀ ⟶ 0` stays exact after tensoring. -/
theorem Module.Flat.lTensor_injective_ker_subtype {R : Type u} [CommRing R]
    {C₀ C₁ C₂ : Type*} [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [Module R C₀]
    [Module R C₁] [Module R C₂] [Module.Flat R C₁] [Module.Flat R C₂] (d₀ : C₀ →ₗ[R] C₁)
    (d₁ : C₁ →ₗ[R] C₂) (hd : d₁ ∘ₗ d₀ = 0)
    (H : ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Function.Exact (d₀.lTensor M) (d₁.lTensor M))
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective ((LinearMap.ker d₀).subtype.lTensor M) := by
  let π := (LinearMap.range d₀).mkQ
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hdπ : Function.Exact d₀ π := LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  have hle : LinearMap.range d₀ ≤ LinearMap.ker d₁ := by
    rintro _ ⟨x, rfl⟩
    exact congr($hd x)
  let q := (LinearMap.range d₀).liftQ d₁ hle
  have hqπ : q ∘ₗ π = d₁ := Submodule.liftQ_mkQ _ _ _
  -- the cokernel of `d₀` embeds universally into `C₂`
  have hq (N : Type u) [AddCommGroup N] [Module R N] : Function.Injective (q.lTensor N) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective N hπ z
    have hw : d₁.lTensor N w = 0 := by
      rw [← hqπ, LinearMap.lTensor_comp, LinearMap.comp_apply, hz]
    obtain ⟨u, rfl⟩ := (H N w).mp hw
    exact (_root_.lTensor_exact N hdπ hπ _).mpr ⟨u, rfl⟩
  -- hence it is flat
  have : Module.Flat R (C₁ ⧸ LinearMap.range d₀) := by
    rw [Module.Flat.iff_rTensor_preserves_injective_linearMap'.{u}]
    intro N N' _ _ _ _ ι hι
    have h : (ι.rTensor C₂) ∘ₗ (q.lTensor N) = (q.lTensor N') ∘ₗ (ι.rTensor _) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    refine Function.Injective.of_comp (f := q.lTensor N') ?_
    rw [← LinearMap.coe_comp, ← h, LinearMap.coe_comp]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hι).comp (hq N)
  -- so is the image of `d₀`
  have : Module.Flat R (LinearMap.range d₀) :=
    Module.Flat.of_exact_of_flat_of_flat_right (LinearMap.range d₀).subtype π
      Subtype.val_injective hπ (by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype])
  exact LinearMap.lTensor_injective_of_exact_of_flat d₀.rangeRestrict d₀.surjective_rangeRestrict
    (LinearMap.ker d₀).subtype Subtype.val_injective
    (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]) M

section Quotient

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (v₁ v₂ : B)

/-- If `v₁` is a non-zerodivisor and `B ⧸ (v₁)`, `B ⧸ (v₂)` are flat over `R`, then so is
`B ⧸ (v₁ v₂)`. -/
lemma Ideal.Quotient.flat_span_singleton_mul (hv : v₁ ∈ nonZeroDivisors B)
    [Module.Flat R (B ⧸ Ideal.span {v₁})] [Module.Flat R (B ⧸ Ideal.span {v₂})] :
    Module.Flat R (B ⧸ Ideal.span {v₁ * v₂}) :=
  Module.Flat.of_exact_of_flat_of_flat _ _ (Ideal.Quotient.injective_mulSpanSingleton v₁ v₂ hv)
    (Ideal.Quotient.surjective_factorSpanSingleton v₁ v₂)
    (Ideal.Quotient.exact_mulSpanSingleton_factorSpanSingleton v₁ v₂)

end Quotient

/-- **Base change of a regular element with flat quotient.** Let `A → B` be a ring map and let
`f ∈ B` be a non-zerodivisor such that `B ⧸ (f)` is flat over `A` (here presented as a surjection
`q : B → C` with kernel `(f)`). Then for every `A`-algebra `A'`, the element `f ⊗ 1` is a
non-zerodivisor of `B ⊗[A] A'`: tensoring the exact sequence `0 → B → B → C → 0` (the first map
being multiplication by `f`) with `A'` stays exact on the left as `C` is flat over `A`. -/
theorem Algebra.TensorProduct.includeLeftRingHom_mem_nonZeroDivisors_of_flat
    {A B C A' : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [Algebra A B]
    [Algebra A A'] (q : B →+* C) (hq : Function.Surjective q) {f : B}
    (hker : RingHom.ker q = Ideal.span {f}) (hflat : (q.comp (algebraMap A B)).Flat)
    (hf : f ∈ nonZeroDivisors B) :
    (Algebra.TensorProduct.includeLeftRingHom f : B ⊗[A] A') ∈ nonZeroDivisors (B ⊗[A] A') := by
  let := (q.comp (algebraMap A B)).toAlgebra
  have : Module.Flat A C := hflat
  let qA : B →ₗ[A] C :=
    { toFun := q
      map_add' := map_add q
      map_smul' := fun a b ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  have hex : Function.Exact (LinearMap.mulLeft A f) qA := fun b ↦
    (RingHom.mem_ker (f := q)).symm.trans <| by
      rw [hker, Ideal.mem_span_singleton']
      simp [mul_comm]
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat qA hq (LinearMap.mulLeft A f)
    (isRegular_iff_mem_nonZeroDivisors.mpr hf).left hex A'
  have hcomm (x : B ⊗[A] A') :
      (LinearMap.mulLeft A f).lTensor A' (TensorProduct.comm A B A' x) =
        TensorProduct.comm A B A' (Algebra.TensorProduct.includeLeftRingHom f * x) := by
    induction x using TensorProduct.inductionOn with
    | tmul b a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add, map_add]
  have key (x : B ⊗[A] A') (hx : Algebra.TensorProduct.includeLeftRingHom f * x = 0) :
      x = 0 := by
    have := hcomm x
    rw [hx, map_zero, ← map_zero ((LinearMap.mulLeft A f).lTensor A')] at this
    simpa using hinj this
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx ↦ key x (by rwa [mul_comm])⟩
