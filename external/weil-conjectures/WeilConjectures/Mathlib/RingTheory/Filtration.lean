/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Tensor

/-!
# The local criterion for flatness

Let `R → S` be a map of noetherian rings, `I` an ideal of `R` with `I S` contained in the
Jacobson radical of `S`, and `M` a finite `S`-module. If `M ⧸ I M` is flat over `R ⧸ I` and
`M ⊗ I → M` is injective, then `M` is flat over `R`.

## Main results

- `Module.Flat.lTensor_inclusion_injective_of_smul_le`: if `M ⧸ I M` is flat over `R ⧸ I` and
  `M ⊗ I → M` is injective, then `Tor₁(N, M) = 0` for every module `N` killed by `I`, in the form
  of the injectivity of `M ⊗ L → M ⊗ L'` for `L ≤ L'` with `I • L' ≤ L`.
- `Module.Flat.of_flat_quotient_of_lTensor_injective`: the local criterion for flatness
  (Stacks, Tags 00MK and 0AS8; Matsumura, Theorem 22.3).
- `Module.Flat.lTensor_subtype_injective_of_forall_ker`: relative purity, the surjectivity
  statement of Stacks, Tag 00MO.
-/

@[expose] public section

open TensorProduct LinearMap

universe u

namespace Module.Flat

variable {R : Type u} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

/-- If `I` annihilates `N`, then `M ⊗ N → (M ⧸ I M) ⊗ N` is bijective. -/
lemma bijective_rTensor_mkQ_of_smul_eq_zero {N : Type*} [AddCommGroup N] [Module R N]
    (hN : ∀ i ∈ I, ∀ n : N, i • n = 0) :
    Function.Bijective ((I • (⊤ : Submodule R M)).mkQ.rTensor N) := by
  refine ⟨?_, rTensor_surjective _ (Submodule.mkQ_surjective _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hex := _root_.rTensor_exact N (LinearMap.exact_subtype_mkQ (I • (⊤ : Submodule R M)))
    (Submodule.mkQ_surjective _)
  obtain ⟨y, rfl⟩ := (hex x).1 hx
  clear hx hex
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp [hy, hz]
  | tmul m n =>
    obtain ⟨m, hm⟩ := m
    simp only [rTensor_tmul, Submodule.subtype_apply]
    induction hm using Submodule.smul_induction_on' with
    | smul r hr m _ => rw [smul_tmul, hN r hr n, tmul_zero]
    | add m _ m' _ h h' => rw [add_tmul, h, h', add_zero]

/-- **Purity for modules killed by `I`.** If `M ⧸ I M` is flat over `R ⧸ I`, `I` annihilates
`N` and `N' ≤ N`, then `M ⊗ N' → M ⊗ N` is injective. -/
lemma lTensor_subtype_injective_of_smul_eq_zero
    [Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] {N : Type*} [AddCommGroup N] [Module R N]
    (hN : ∀ i ∈ I, ∀ n : N, i • n = 0) (N' : Submodule R N) :
    Function.Injective (N'.subtype.lTensor M) := by
  set M' := M ⧸ I • (⊤ : Submodule R M)
  have hN' : ∀ i ∈ I, ∀ n : N', i • n = 0 := fun i hi n ↦ Subtype.ext (hN i hi n)
  have h₁ := bijective_rTensor_mkQ_of_smul_eq_zero (M := M) I hN
  have h₂ := bijective_rTensor_mkQ_of_smul_eq_zero (M := M) I hN'
  have hcomm : (N'.subtype.lTensor M').comp ((I • (⊤ : Submodule R M)).mkQ.rTensor N') =
      ((I • (⊤ : Submodule R M)).mkQ.rTensor N).comp (N'.subtype.lTensor M) := by
    ext; rfl
  suffices h : Function.Injective (N'.subtype.lTensor M') by
    intro x y hxy
    apply h₂.1
    apply h
    have hx := congr($hcomm x)
    have hy := congr($hcomm y)
    simp only [LinearMap.comp_apply] at hx hy
    rw [hx, hy, hxy]
  have hNt : Module.IsTorsionBySet R N I := fun n i ↦ hN i i.2 n
  have hN't : Module.IsTorsionBySet R N' I := fun n i ↦ hN' i i.2 n
  let := hNt.module
  let := hN't.module
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul R (R ⧸ I) M' N := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  have : CompatibleSMul R (R ⧸ I) M' N' := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let f : N' →ₗ[R ⧸ I] N :=
    { toFun := N'.subtype
      map_add' := by simp
      map_smul' := by
        rintro ⟨r⟩ n
        exact N'.subtype.map_smul r n }
  have hf : Function.Injective (f.lTensor M') :=
    Flat.lTensor_preserves_injective_linearMap f Subtype.val_injective
  let e := equivOfCompatibleSMul R (R ⧸ I) R M' N
  let e' := equivOfCompatibleSMul R (R ⧸ I) R M' N'
  have key : N'.subtype.lTensor M' = e.toLinearMap ∘ₗ (f.lTensor M').restrictScalars R ∘ₗ
      e'.symm.toLinearMap := by
    ext m n
    rfl
  rw [key]
  simpa using hf

/-- If `F` is flat and `M ⊗ I → M` is injective, then so is `M ⊗ I F → M ⊗ F`. -/
lemma lTensor_smul_top_subtype_injective {F : Type*} [AddCommGroup F] [Module R F] [Flat R F]
    (hI : Function.Injective (I.subtype.lTensor M)) :
    Function.Injective ((I • (⊤ : Submodule R F)).subtype.lTensor M) := by
  -- `u : I ⊗ F → F` is injective with range `I • F`.
  let u : I ⊗[R] F →ₗ[R] F := TensorProduct.lid R F ∘ₗ I.subtype.rTensor F
  have hu : Function.Injective u :=
    (TensorProduct.lid R F).injective.comp (Flat.rTensor_preserves_injective_linearMap _
      Subtype.val_injective)
  have hrange : LinearMap.range u = I • (⊤ : Submodule R F) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul i f => exact Submodule.smul_mem_smul i.2 trivial
    · rw [Submodule.smul_le]
      intro i hi f _
      exact ⟨⟨i, hi⟩ ⊗ₜ f, by simp [u]⟩
  let e : I ⊗[R] F ≃ₗ[R] ↥(I • (⊤ : Submodule R F)) :=
    (LinearEquiv.ofInjective u hu).trans (LinearEquiv.ofEq _ _ hrange)
  -- `M ⊗ (I ⊗ F) → M ⊗ F` is, up to isomorphisms, `(M ⊗ I → M) ⊗ F`.
  let v : M ⊗[R] (I ⊗[R] F) →ₗ[R] M ⊗[R] F :=
    (TensorProduct.rid R M).toLinearMap.rTensor F ∘ₗ (I.subtype.lTensor M).rTensor F ∘ₗ
      (TensorProduct.assoc R M I F).symm.toLinearMap
  have hv : Function.Injective v :=
    (Flat.rTensor_preserves_injective_linearMap _ (TensorProduct.rid R M).injective).comp
      ((Flat.rTensor_preserves_injective_linearMap _ hI).comp
        (TensorProduct.assoc R M I F).symm.injective)
  have hcomp : (I • (⊤ : Submodule R F)).subtype.lTensor M ∘ₗ e.toLinearMap.lTensor M = v := by
    ext m i f
    simp [e, u, v, LinearEquiv.ofInjective_apply, smul_tmul']
  have : (I • (⊤ : Submodule R F)).subtype.lTensor M =
      v ∘ₗ (e.symm.toLinearMap.lTensor M) := by
    rw [← hcomp, LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
    simp
  rw [this]
  exact hv.comp (LinearEquiv.injective (e.symm.lTensor M))

/-- Purity for `I`-torsion quotients of a flat module: if `F` is flat, `K ≤ F` contains `I F`,
`M ⧸ I M` is flat over `R ⧸ I` and `M ⊗ I → M` is injective, then `M ⊗ K → M ⊗ F` is
injective. -/
lemma lTensor_subtype_injective_of_flat
    (hQ : ∀ (N : Type u) [AddCommGroup N] [Module R N], (∀ i ∈ I, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R N, Function.Injective (N'.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module R F] [Flat R F]
    (hI : Function.Injective (I.subtype.lTensor M)) (K : Submodule R F)
    (hK : I • (⊤ : Submodule R F) ≤ K) :
    Function.Injective (K.subtype.lTensor M) := by
  set P := I • (⊤ : Submodule R F)
  let K' : Submodule R (F ⧸ P) := K.map P.mkQ
  let q : K →ₗ[R] K' := (P.mkQ.restrict fun x hx ↦ Submodule.mem_map_of_mem hx)
  have hq : Function.Surjective q := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hex : Function.Exact (Submodule.inclusion hK) q := by
    intro x
    constructor
    · intro h
      have : (x : F) ∈ P := by
        simpa [q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using congr(($h : F ⧸ P))
      exact ⟨⟨x, this⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simp [q, (Submodule.Quotient.mk_eq_zero P).mpr y.2]
  have hkill : ∀ i ∈ I, ∀ n : F ⧸ P, i • n = 0 := by
    intro i hi n
    induction n using Submodule.Quotient.induction_on with
    | H n =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hi trivial
  have hQ' := hQ _ hkill K'
  have hP := lTensor_smul_top_subtype_injective I (F := F) hI
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hcomm : K'.subtype ∘ₗ q = P.mkQ ∘ₗ K.subtype := by ext; rfl
  have h1 : q.lTensor M z = 0 := by
    apply hQ'
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz, map_zero]
  obtain ⟨u, rfl⟩ := ((_root_.lTensor_exact M hex hq) z).1 h1
  have h2 : P.subtype.lTensor M u = 0 := by
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  rw [hP (h2.trans (map_zero _).symm), map_zero]

/-- **Purity for modules killed by `I`.** If `M ⧸ I M` is flat over `R ⧸ I` and `M ⊗ I → M`
is injective, then for submodules `L ≤ L'` of any module with `I • L' ≤ L`, the map
`M ⊗ L → M ⊗ L'` is injective. This is the vanishing of `Tor₁(L' ⧸ L, M)` (Stacks, Tag 051C). -/
lemma lTensor_inclusion_injective_of_smul_le
    (hQ : ∀ (N : Type u) [AddCommGroup N] [Module R N], (∀ i ∈ I, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R N, Function.Injective (N'.subtype.lTensor M))
    (hI : Function.Injective (I.subtype.lTensor M)) {N : Type u} [AddCommGroup N] [Module R N]
    {L L' : Submodule R N} (hLL' : L ≤ L')
    (hI' : I • L' ≤ L) : Function.Injective ((Submodule.inclusion hLL').lTensor M) := by
  -- Present `L'` as a quotient of a free module `F`.
  obtain ⟨F, _, _, _, φ, hφ⟩ : ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Flat R F) (φ : F →ₗ[R] L'), Function.Surjective φ :=
    ⟨L' →₀ R, inferInstance, inferInstance, inferInstance, Finsupp.linearCombination R id,
      fun x ↦ ⟨Finsupp.single x 1, by rw [Finsupp.linearCombination_single, one_smul]; rfl⟩⟩
  let L₀ : Submodule R L' := L.comap L'.subtype
  let K : Submodule R F := L₀.comap φ
  have hK : I • (⊤ : Submodule R F) ≤ K := by
    rw [Submodule.smul_le]
    intro i hi f _
    change (φ (i • f) : N) ∈ L
    rw [map_smul, Submodule.coe_smul]
    exact hI' (Submodule.smul_mem_smul hi (φ f).2)
  have hKinj := lTensor_subtype_injective_of_flat I hQ hI K hK
  -- `L ≃ L₀`, and `K → L₀` is surjective with kernel `ker φ`.
  let eL : L₀ ≃ₗ[R] L := Submodule.comapSubtypeEquivOfLe hLL'
  let φK : K →ₗ[R] L₀ := φ.restrict fun x hx ↦ hx
  have hφK : Function.Surjective φK := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hcomm : (Submodule.inclusion hLL') ∘ₗ eL.toLinearMap = L₀.subtype := by
    ext x
    rfl
  suffices h : Function.Injective (L₀.subtype.lTensor M) by
    rw [← hcomm, LinearMap.lTensor_comp, LinearMap.coe_comp] at h
    have := h.of_comp
    rw [← LinearEquiv.coe_lTensor] at this
    intro x y hxy
    obtain ⟨x, rfl⟩ := (eL.lTensor M).surjective x
    obtain ⟨y, rfl⟩ := (eL.lTensor M).surjective y
    rw [h hxy]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨k, rfl⟩ := LinearMap.lTensor_surjective M hφK z
  have hsq : L₀.subtype ∘ₗ φK = φ ∘ₗ K.subtype := by ext; rfl
  have hk : φ.lTensor M (K.subtype.lTensor M k) = 0 := by
    rw [← LinearMap.comp_apply (φ.lTensor M), ← LinearMap.lTensor_comp, ← hsq,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz]
  have hexφ : Function.Exact (LinearMap.ker φ).subtype φ := LinearMap.exact_subtype_ker_map φ
  obtain ⟨w, hw⟩ := ((_root_.lTensor_exact M hexφ hφ) _).1 hk
  have hle : LinearMap.ker φ ≤ K := fun x hx ↦ by
    change φ x ∈ L₀
    rw [LinearMap.mem_ker.mp hx]
    exact zero_mem _
  have hk' : k = (Submodule.inclusion hle).lTensor M w := by
    apply hKinj
    rw [← hw, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  have hzero : φK ∘ₗ Submodule.inclusion hle = 0 := by
    ext x
    exact congr(($(LinearMap.mem_ker.mp x.2) : N))
  rw [hk', ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero]
  simp

/-- **Relative purity over a flat module.** Let `F` be flat, `K ≤ F` containing `I F`, and assume
`M ⊗ N' → M ⊗ N` is injective for `N' ≤ N` killed by `I`. Then every element of the kernel of
`M ⊗ K → M ⊗ F` is a sum of images of `k ⊗ f`, `k` in the kernel of `M ⊗ I → M`, under
`M ⊗ I → M ⊗ K`, `m ⊗ i ↦ m ⊗ i f`. We state this as: a linear map `ψ` out of `M ⊗ K` killing
all these images kills the kernel. -/
lemma map_eq_zero_of_lTensor_subtype_eq_zero_of_flat
    (hQ : ∀ (N : Type u) [AddCommGroup N] [Module R N], (∀ i ∈ I, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R N, Function.Injective (N'.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module R F] [Flat R F] (K : Submodule R F)
    (hK : I • (⊤ : Submodule R F) ≤ K) {X : Type*} [AddCommGroup X] [Module R X]
    (ψ : M ⊗[R] K →ₗ[R] X)
    (hψ : ∀ k : M ⊗[R] I, TensorProduct.rid R M (I.subtype.lTensor M k) = 0 → ∀ f : F,
      ψ ((((toSpanSingleton R F f) ∘ₗ I.subtype).codRestrict K
        fun i ↦ hK (Submodule.smul_mem_smul i.2 trivial)).lTensor M k) = 0)
    (z : M ⊗[R] K) (hz : K.subtype.lTensor M z = 0) : ψ z = 0 := by
  set P := I • (⊤ : Submodule R F)
  let K' : Submodule R (F ⧸ P) := K.map P.mkQ
  let q : K →ₗ[R] K' := (P.mkQ.restrict fun x hx ↦ Submodule.mem_map_of_mem hx)
  have hq : Function.Surjective q := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hex : Function.Exact (Submodule.inclusion hK) q := by
    intro x
    constructor
    · intro h
      have : (x : F) ∈ P := by
        simpa [q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using congr(($h : F ⧸ P))
      exact ⟨⟨x, this⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simp [q, (Submodule.Quotient.mk_eq_zero P).mpr y.2]
  have hkill : ∀ i ∈ I, ∀ n : F ⧸ P, i • n = 0 := by
    intro i hi n
    induction n using Submodule.Quotient.induction_on with
    | H n =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hi trivial
  have hQ' := hQ _ hkill K'
  have hcomm : K'.subtype ∘ₗ q = P.mkQ ∘ₗ K.subtype := by ext; rfl
  have h1 : q.lTensor M z = 0 := by
    apply hQ'
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz, map_zero]
  obtain ⟨u, rfl⟩ := ((_root_.lTensor_exact M hex hq) z).1 h1
  have h2 : P.subtype.lTensor M u = 0 := by
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  -- `ν : I ⊗ F → I F` is surjective.
  let ν : I ⊗[R] F →ₗ[R] P := (TensorProduct.lid R F ∘ₗ I.subtype.rTensor F).codRestrict P
    fun x ↦ by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul i f => exact Submodule.smul_mem_smul i.2 trivial
  have hν : Function.Surjective ν := by
    rintro ⟨y, hy⟩
    induction hy using Submodule.smul_induction_on' with
    | smul i hi f _ => exact ⟨⟨i, hi⟩ ⊗ₜ f, rfl⟩
    | add x hx y hy hx' hy' =>
      obtain ⟨a, ha⟩ := hx'
      obtain ⟨b, hb⟩ := hy'
      exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  obtain ⟨v, rfl⟩ := LinearMap.lTensor_surjective M hν u
  set μ : M ⊗[R] I →ₗ[R] M := (TensorProduct.rid R M).toLinearMap ∘ₗ I.subtype.lTensor M
  have hΦ : (P.subtype ∘ₗ ν).lTensor M ∘ₗ (TensorProduct.assoc R M I F).toLinearMap =
      μ.rTensor F := by
    ext m i f
    simp [ν, μ, smul_tmul]
  have hΨ : μ.rTensor F ((TensorProduct.assoc R M I F).symm v) = 0 := by
    rw [← hΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.lTensor_comp, LinearMap.comp_apply, h2]
  have hexμ : Function.Exact (LinearMap.ker μ).subtype μ := LinearMap.exact_subtype_ker_map μ
  obtain ⟨w, hw⟩ := ((rTensor_exact F hexμ) _).1 hΨ
  rw [← LinearEquiv.apply_symm_apply (TensorProduct.assoc R M I F) v, ← hw]
  have key (t : M ⊗[R] I) (f : F) :
      (Submodule.inclusion hK).lTensor M (ν.lTensor M (TensorProduct.assoc R M I F (t ⊗ₜ f))) =
        (((toSpanSingleton R F f) ∘ₗ I.subtype).codRestrict K
          fun i ↦ hK (Submodule.smul_mem_smul i.2 trivial)).lTensor M t := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [add_tmul, map_add, map_add, map_add, hx, hy, map_add]
    | tmul m i => rfl
  clear hw
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul k f =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, key]
    exact hψ k k.2 f

/-- **Relative purity** (the surjectivity in Stacks, Tag 00MO). Assume `M ⊗ N' → M ⊗ N` is
injective for `N' ≤ N` killed by `I`. Let `L ≤ N` contain `I N`, and suppose that for every `k` in
the kernel of `M ⊗ I → M` and every `n : N` the image of `k` under `M ⊗ I → M ⊗ L`,
`m ⊗ i ↦ m ⊗ i n`, vanishes. Then `M ⊗ L → M ⊗ N` is injective. -/
theorem lTensor_subtype_injective_of_forall_ker
    (hQ : ∀ (N : Type u) [AddCommGroup N] [Module R N], (∀ i ∈ I, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R N, Function.Injective (N'.subtype.lTensor M))
    {N : Type u} [AddCommGroup N] [Module R N] (L : Submodule R N)
    (hL : I • (⊤ : Submodule R N) ≤ L)
    (hK : ∀ k : M ⊗[R] I, TensorProduct.rid R M (I.subtype.lTensor M k) = 0 → ∀ n : N,
      (((toSpanSingleton R N n) ∘ₗ I.subtype).codRestrict L
        fun i ↦ hL (Submodule.smul_mem_smul i.2 trivial)).lTensor M k = 0) :
    Function.Injective (L.subtype.lTensor M) := by
  let F := N →₀ R
  let φ : F →ₗ[R] N := Finsupp.linearCombination R id
  have hφ : Function.Surjective φ := fun x ↦
    ⟨Finsupp.single x 1, by rw [Finsupp.linearCombination_single, one_smul]; rfl⟩
  let LF : Submodule R F := L.comap φ
  have hLF : I • (⊤ : Submodule R F) ≤ LF := by
    rw [Submodule.smul_le]
    intro i hi f _
    change φ (i • f) ∈ L
    rw [map_smul]
    exact hL (Submodule.smul_mem_smul hi trivial)
  let φL : LF →ₗ[R] L := φ.restrict fun x hx ↦ hx
  have hφL : Function.Surjective φL := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨⟨x, hy⟩, rfl⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective M hφL x
  have hsq : L.subtype ∘ₗ φL = φ ∘ₗ LF.subtype := by ext; rfl
  have hz : φ.lTensor M (LF.subtype.lTensor M y) = 0 := by
    rw [← LinearMap.comp_apply (φ.lTensor M), ← LinearMap.lTensor_comp, ← hsq,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hx]
  have hexφ : Function.Exact (LinearMap.ker φ).subtype φ := LinearMap.exact_subtype_ker_map φ
  obtain ⟨w, hw⟩ := ((_root_.lTensor_exact M hexφ hφ) _).1 hz
  have hle : LinearMap.ker φ ≤ LF := fun x hx ↦ by
    change φ x ∈ L
    rw [LinearMap.mem_ker.mp hx]
    exact zero_mem _
  have hzero : φL ∘ₗ Submodule.inclusion hle = 0 := by
    ext x
    exact congr(($(LinearMap.mem_ker.mp x.2) : N))
  have hw' : φL.lTensor M ((Submodule.inclusion hle).lTensor M w) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero]
    simp
  have hdiff : LF.subtype.lTensor M (y - (Submodule.inclusion hle).lTensor M w) = 0 := by
    rw [map_sub, sub_eq_zero, ← hw, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  have := map_eq_zero_of_lTensor_subtype_eq_zero_of_flat I hQ LF hLF (φL.lTensor M)
    (fun k hk f ↦ by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      convert hK k hk (φ f) using 3
      ext i
      simp [φL, φ, LinearMap.restrict_apply])
    _ hdiff
  rwa [map_sub, hw', sub_zero] at this

/-- If `M ⧸ I M` is flat over `R ⧸ I` and `M ⊗ I → M` is injective, then `M ⊗ L → M` is
injective for every ideal `L` containing a power of `I`. This is the vanishing of
`Tor₁(R ⧸ L, M)` (Stacks, Tag 051C). -/
lemma lTensor_subtype_injective_of_pow_le
    (hQ : ∀ (N : Type u) [AddCommGroup N] [Module R N], (∀ i ∈ I, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R N, Function.Injective (N'.subtype.lTensor M))
    (hI : Function.Injective (I.subtype.lTensor M))
    (n : ℕ) {L : Ideal R} (hL : I ^ n ≤ L) : Function.Injective (L.subtype.lTensor M) := by
  induction n generalizing L with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff] at hL
    subst hL
    have : (⊤ : Ideal R).subtype = (LinearEquiv.ofTop (⊤ : Ideal R) rfl).toLinearMap := rfl
    rw [this, ← LinearEquiv.coe_lTensor]
    exact LinearEquiv.injective _
  | succ n ih =>
    have hle : L ≤ L ⊔ I ^ n := le_sup_left
    have hsmul : I • (L ⊔ I ^ n) ≤ L := by
      rw [Submodule.smul_sup, smul_eq_mul, smul_eq_mul, ← pow_succ']
      exact sup_le (Ideal.mul_le.mpr fun a _ b hb ↦ L.mul_mem_left a hb) hL
    have h₁ := ih (L := L ⊔ I ^ n) le_sup_right
    have h₂ := lTensor_inclusion_injective_of_smul_le I hQ hI hle hsmul
    have : L.subtype = (L ⊔ I ^ n).subtype ∘ₗ Submodule.inclusion hle := rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.coe_comp]
    exact h₁.comp h₂

/-- The image of `M ⊗ I N → M ⊗ N` lies in `I • (M ⊗ N)`. -/
lemma range_lTensor_smul_top_subtype_le {N : Type*} [AddCommGroup N] [Module R N]
    (J : Ideal R) :
    LinearMap.range ((J • (⊤ : Submodule R N)).subtype.lTensor M) ≤
      J • (⊤ : Submodule R (M ⊗[R] N)) := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul m n =>
    obtain ⟨n, hn⟩ := n
    simp only [lTensor_tmul, Submodule.subtype_apply]
    induction hn using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      rw [tmul_smul]
      exact Submodule.smul_mem_smul hr trivial
    | add n _ n' _ h h' => rw [tmul_add]; exact Submodule.add_mem _ h h'

/-- **The local criterion for flatness**, with the flatness of `M ⧸ I M` over `R ⧸ I` replaced by
the purity it implies (see `lTensor_subtype_injective_of_smul_eq_zero`). Let `R → S` be a map of
noetherian rings, `I` an ideal of `R` with `I S` contained in the Jacobson radical of `S`, and `M`
a finite `S`-module. If `M ⊗ N' → M ⊗ N` is injective for all `N' ≤ N` with `N` killed by `I`,
and `M ⊗ I → M` is injective, then `M` is flat over `R`. -/
theorem of_lTensor_injective_of_forall {S : Type*} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] (hIS : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥)
    (hQ : ∀ (N : Type u) [AddCommGroup N] [Module R N], (∀ i ∈ I, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R N, Function.Injective (N'.subtype.lTensor M))
    (hI : Function.Injective (I.subtype.lTensor M)) : Flat R M := by
  rw [iff_lTensor_injective']
  intro J
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- Step 1: `x` lies in the image of `M ⊗ (J ∩ Iⁿ)` for every `n`.
  have step1 (n : ℕ) :
      x ∈ LinearMap.range ((Submodule.comap J.subtype (I ^ n)).subtype.lTensor M) := by
    set L := J ⊔ I ^ n
    have hJL : J ≤ L := le_sup_left
    have hL := lTensor_subtype_injective_of_pow_le I hQ hI n (L := L) le_sup_right
    have h0 : (Submodule.inclusion hJL).lTensor M x = 0 := by
      apply hL
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, map_zero]
      exact hx
    let π : J →ₗ[R] R ⧸ I ^ n := (I ^ n).mkQ ∘ₗ J.subtype
    let πJ : J →ₗ[R] LinearMap.range π := π.rangeRestrict
    have hπJ : Function.Surjective πJ := LinearMap.surjective_rangeRestrict π
    have hrange : ∀ y : L, (I ^ n).mkQ (y : R) ∈ LinearMap.range π := by
      rintro ⟨y, hy⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨a, ha⟩, ?_⟩
      simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hb]
    let πL : L →ₗ[R] LinearMap.range π :=
      ((I ^ n).mkQ ∘ₗ L.subtype).codRestrict _ hrange
    have hfac : πJ = πL ∘ₗ Submodule.inclusion hJL := rfl
    have hex : Function.Exact (Submodule.comap J.subtype (I ^ n)).subtype πJ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
      ext y
      simp [π, Ideal.Quotient.eq_zero_iff_mem]
    apply ((_root_.lTensor_exact M hex hπJ) x).1
    rw [hfac, LinearMap.lTensor_comp, LinearMap.comp_apply, h0, map_zero]
  -- Step 2: by Artin–Rees, `x ∈ Iⁿ (M ⊗ J)` for all `n`.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
  have step2 (n : ℕ) : x ∈ I ^ n • (⊤ : Submodule R (M ⊗[R] J)) := by
    have hle : Submodule.comap J.subtype (I ^ (n + k)) ≤ I ^ n • (⊤ : Submodule R J) := by
      intro y hy
      have hy' : (y : R) ∈ I ^ (n + k) • (⊤ : Ideal R) ⊓ J := by
        simpa [smul_eq_mul, Ideal.mul_top] using hy
      rw [hk _ (Nat.le_add_left k n), Nat.add_sub_cancel] at hy'
      have hy'' : (y : R) ∈ Submodule.map J.subtype (I ^ n • (⊤ : Submodule R J)) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
        exact Submodule.smul_mono le_rfl inf_le_right hy'
      obtain ⟨z, hz, hzy⟩ := hy''
      rwa [← Subtype.ext hzy]
    obtain ⟨y, rfl⟩ := step1 (n + k)
    have : (Submodule.comap J.subtype (I ^ (n + k))).subtype =
        (I ^ n • (⊤ : Submodule R J)).subtype ∘ₗ Submodule.inclusion hle := rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply]
    exact range_lTensor_smul_top_subtype_le (I ^ n) ⟨_, rfl⟩
  -- Step 3: Krull's intersection theorem over `S`.
  have : Module.Finite R J := IsNoetherian.finite R J
  have hfin : Module.Finite S (M ⊗[R] J) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J)
  have hkrull := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[R] J) _ hIS
  have : x ∈ (⨅ i : ℕ, I.map (algebraMap R S) ^ i • ⊤ : Submodule S (M ⊗[R] J)) := by
    rw [Submodule.mem_iInf]
    intro n
    have h := step2 n
    rw [← Ideal.map_pow]
    refine Submodule.smul_induction_on h (fun r hr y _ ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
    rw [← algebraMap_smul S r y]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  rwa [hkrull] at this

/-- **The local criterion for flatness** (Stacks, Tags 00MK and 0AS8; Matsumura, Theorem 22.3).
Let `R → S` be a map of noetherian rings, `I` an ideal of `R` with `I S` contained in the
Jacobson radical of `S`, and `M` a finite `S`-module. If `M ⧸ I M` is flat over `R ⧸ I` and
`M ⊗ I → M` is injective, then `M` is flat over `R`.
(blueprint: `lem-weil-pbc-flat-variant-local-criterion`) -/
theorem of_flat_quotient_of_lTensor_injective {S : Type*} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]
    (hIS : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥)
    (hI : Function.Injective (I.subtype.lTensor M)) : Flat R M :=
  of_lTensor_injective_of_forall I hIS
    (fun _ _ _ hN N' ↦ lTensor_subtype_injective_of_smul_eq_zero I hN N') hI

section Element

variable {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]

/-- An element `s` acting injectively on `M ⧸ I M`, `I` maximal and `M` flat, acts injectively on
`M ⊗ N` for every module `N` killed by `I`. -/
private lemma rTensor_toLinearMap_injective_of_smul_eq_zero [Flat R M] [I.IsMaximal] (s : S)
    (hs : ∀ m : M, s • m ∈ I • (⊤ : Submodule R M) → m ∈ I • (⊤ : Submodule R M))
    {N : Type*} [AddCommGroup N] [Module R N] (hN : ∀ i ∈ I, ∀ n : N, i • n = 0) :
    Function.Injective ((DistribSMul.toLinearMap R M s).rTensor N) := by
  let := Ideal.Quotient.field I
  set P := I • (⊤ : Submodule R M)
  set φ := DistribSMul.toLinearMap R M s
  have hφP : P ≤ P.comap φ := by
    rw [Submodule.smul_le]
    intro i hi m _
    change s • (i • m) ∈ P
    rw [smul_comm]
    exact Submodule.smul_mem_smul hi trivial
  let φ' : (M ⧸ P) →ₗ[R] (M ⧸ P) := P.mapQ P φ hφP
  have hφ' : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact hs m hx
  have hβ := bijective_rTensor_mkQ_of_smul_eq_zero (M := M) I hN
  have hcomm : (P.mkQ.rTensor N).comp (φ.rTensor N) = (φ'.rTensor N).comp (P.mkQ.rTensor N) := by
    ext; rfl
  suffices h : Function.Injective (φ'.rTensor N) by
    have := h.comp hβ.1
    rw [← LinearMap.coe_comp, ← hcomm, LinearMap.coe_comp] at this
    exact this.of_comp
  have hNt : Module.IsTorsionBySet R N I := fun n i ↦ hN i i.2 n
  let := hNt.module
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul R (R ⧸ I) (M ⧸ P) N :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let ψ : (M ⧸ P) →ₗ[R ⧸ I] (M ⧸ P) :=
    { toFun := φ'
      map_add' := by simp
      map_smul' := by
        rintro ⟨r⟩ n
        exact φ'.map_smul r n }
  have : Module.Free (R ⧸ I) N := Module.Free.of_divisionRing _ _
  have hψ : Function.Injective (ψ.rTensor N) :=
    Flat.rTensor_preserves_injective_linearMap ψ hφ'
  let e := equivOfCompatibleSMul R (R ⧸ I) R (M ⧸ P) N
  have key : φ'.rTensor N = e.toLinearMap ∘ₗ (ψ.rTensor N).restrictScalars R ∘ₗ
      e.symm.toLinearMap := by
    ext m n
    rfl
  rw [key]
  simpa using hψ

/-- **The local criterion for a single element** (Stacks, Tag 00ME). Let `R → S` be a map of
rings with `S` noetherian, `I` a maximal ideal of `R` with `I S` contained in the Jacobson
radical of `S`, `M` a finite `S`-module which is flat over `R`, and `s ∈ S` acting injectively
on `M ⧸ I M`. Then `s` acts injectively on `M ⊗ N` for every finite `R`-module `N`. -/
theorem rTensor_toLinearMap_injective [IsNoetherianRing S] [Module.Finite S M] [Flat R M]
    [I.IsMaximal] (hIS : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥) (s : S)
    (hs : ∀ m : M, s • m ∈ I • (⊤ : Submodule R M) → m ∈ I • (⊤ : Submodule R M))
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Function.Injective ((DistribSMul.toLinearMap R M s).rTensor N) := by
  set φ := DistribSMul.toLinearMap R M s
  -- Step 1: modules killed by a power of `I`.
  have step1 (n : ℕ) : ∀ (N : Type u_3) [AddCommGroup N] [Module R N],
      (∀ i ∈ I ^ n, ∀ x : N, i • x = 0) → Function.Injective (φ.rTensor N) := by
    induction n with
    | zero =>
      intro N _ _ hN
      have : Subsingleton N := ⟨fun x y ↦ by
        rw [← one_smul R x, ← one_smul R y, hN 1 (by simp) x, hN 1 (by simp) y]⟩
      intro x y _
      exact Subsingleton.elim _ _
    | succ n ih =>
      intro N _ _ hN
      set N₁ := I • (⊤ : Submodule R N)
      have hN₁ : ∀ i ∈ I ^ n, ∀ x : N₁, i • x = 0 := by
        rintro i hi ⟨x, hx⟩
        apply Subtype.ext
        change i • x = 0
        induction hx using Submodule.smul_induction_on' with
        | smul r hr x _ =>
          rw [smul_smul]
          exact hN _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hi hr) x
        | add x _ y _ hx hy => rw [smul_add, hx, hy, add_zero]
      have hN₂ : ∀ i ∈ I, ∀ x : N ⧸ N₁, i • x = 0 := by
        intro i hi x
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem_smul hi trivial
      have h₁ := ih N₁ hN₁
      have h₂ := rTensor_toLinearMap_injective_of_smul_eq_zero I s hs hN₂
      have hinc : Function.Injective (N₁.subtype.lTensor M) :=
        Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
      have hex := _root_.lTensor_exact M (LinearMap.exact_subtype_mkQ N₁)
        (Submodule.mkQ_surjective N₁)
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : φ.rTensor _ (N₁.mkQ.lTensor M x) = 0 := by
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
          ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
      obtain ⟨y, rfl⟩ := (hex x).1 (h₂ (hx'.trans (map_zero _).symm))
      have hy : φ.rTensor _ y = 0 := by
        apply hinc
        rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
          ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hx]
      rw [h₁ (hy.trans (map_zero _).symm), map_zero]
  -- Step 2: Krull's intersection theorem.
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 (n : ℕ) : x ∈ I ^ n • (⊤ : Submodule R (M ⊗[R] N)) := by
    set Nn := I ^ n • (⊤ : Submodule R N)
    have hNn : ∀ i ∈ I ^ n, ∀ y : N ⧸ Nn, i • y = 0 := by
      intro i hi y
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hi trivial
    have hinj := step1 n (N ⧸ Nn) hNn
    have hex := _root_.lTensor_exact M (LinearMap.exact_subtype_mkQ Nn)
      (Submodule.mkQ_surjective Nn)
    have h0 : Nn.mkQ.lTensor M x = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨y, rfl⟩ := (hex x).1 h0
    exact range_lTensor_smul_top_subtype_le (I ^ n) ⟨y, rfl⟩
  have hfin : Module.Finite S (M ⊗[R] N) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N)
  have hkrull := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[R] N) _ hIS
  have : x ∈ (⨅ i : ℕ, I.map (algebraMap R S) ^ i • ⊤ : Submodule S (M ⊗[R] N)) := by
    rw [Submodule.mem_iInf]
    intro n
    rw [← Ideal.map_pow]
    refine Submodule.smul_induction_on (h2 n) (fun r hr y _ ↦ ?_)
      (fun _ _ ↦ Submodule.add_mem _)
    rw [← algebraMap_smul S r y]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  rwa [hkrull] at this

end Element

/-- Elements of `I M` are the images of `M ⊗ I → M`. -/
lemma exists_rid_lTensor_eq_of_mem_smul_top {m : M} (hm : m ∈ I • (⊤ : Submodule R M)) :
    ∃ y : M ⊗[R] I, TensorProduct.rid R M (I.subtype.lTensor M y) = m := by
  induction hm using Submodule.smul_induction_on' with
  | smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
  | add m _ m' _ h h' =>
    obtain ⟨y, hy⟩ := h
    obtain ⟨y', hy'⟩ := h'
    exact ⟨y + y', by rw [map_add, map_add, hy, hy']⟩

/-- **Flatness of a cokernel** (Stacks, Tag 00HD). If `M` is flat and `φ : M → M` stays injective
modulo every ideal, i.e. `φ m ∈ J M` implies `m ∈ J M`, then `M ⧸ φ(M)` is flat. -/
theorem quotient_range [Flat R M] (φ : M →ₗ[R] M)
    (h : ∀ (J : Ideal R) (m : M), φ m ∈ J • (⊤ : Submodule R M) → m ∈ J • (⊤ : Submodule R M)) :
    Flat R (M ⧸ LinearMap.range φ) := by
  rw [iff_lTensor_injective']
  intro J
  set C := M ⧸ LinearMap.range φ
  set π := (LinearMap.range φ).mkQ
  have hnat (y : M ⊗[R] J) : π (TensorProduct.rid R M (J.subtype.lTensor M y)) =
      TensorProduct.rid R C (J.subtype.lTensor C (π.rTensor J y)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' h h' => simp only [map_add] at h h' ⊢; rw [h, h']
    | tmul m j => simp
  have hφnat (y : M ⊗[R] J) : φ (TensorProduct.rid R M (J.subtype.lTensor M y)) =
      TensorProduct.rid R M (J.subtype.lTensor M (φ.rTensor J y)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' h h' => simp only [map_add] at h h' ⊢; rw [h, h']
    | tmul m j => simp
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective J (Submodule.mkQ_surjective (LinearMap.range φ)) z
  have hα : Function.Injective (J.subtype.lTensor M) :=
    Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  set a := TensorProduct.rid R M (J.subtype.lTensor M y)
  have ha : a ∈ LinearMap.range φ := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    change π a = 0
    rw [hnat, hz, map_zero]
  obtain ⟨m, hm⟩ := ha
  have haJ : a ∈ J • (⊤ : Submodule R M) := by
    have hy : J.subtype.lTensor M y ∈ J • (⊤ : Submodule R (M ⊗[R] R)) := by
      have hJ : (J • (⊤ : Submodule R R)) = J := by simp [smul_eq_mul]
      have : J.subtype = (J • (⊤ : Submodule R R)).subtype ∘ₗ
          (LinearEquiv.ofEq _ _ hJ.symm).toLinearMap := rfl
      rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply]
      exact range_lTensor_smul_top_subtype_le (M := M) J ⟨_, rfl⟩
    have := Submodule.smul_top_le_comap_smul_top J (TensorProduct.rid R M).toLinearMap hy
    simpa [a] using this
  obtain ⟨y', hy'⟩ := exists_rid_lTensor_eq_of_mem_smul_top J (h J m (hm ▸ haJ))
  have hyy' : y = φ.rTensor J y' := by
    apply hα
    apply (TensorProduct.rid R M).injective
    change a = _
    rw [← hm, ← hy', hφnat]
  rw [hyy', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have : π ∘ₗ φ = 0 := by
    ext m
    simp [π]
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]

end Module.Flat
