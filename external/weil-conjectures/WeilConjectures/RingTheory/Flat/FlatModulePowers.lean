/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.Mathlib.RingTheory.Filtration

/-!
# Flatness from flatness modulo every power of an ideal

Source: Stacks Project, Algebra, Lemma 10.99.11 (Tag 0523)
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v w

namespace Module.Flat

/-- Stacks Project, Algebra, Lemma 10.99.11 (Tag 0523)
(blueprint: theorem-finite-etale-covers-proper-henselian--2). The algebra structure represents the
ring map `R → S`, and the scalar tower says that the `R`-action on `M` is its restriction.

Proof (the Artin–Rees argument of Stacks Tag 0523, applied to every ideal):
1. For an ideal `J`, a tensor `x` in the kernel of `M ⊗ J → M` maps to zero in
   `M ⊗ (R/I^k)`. Flatness of `M/I^k M` gives purity for modules killed by `I^k`.
   Thus `x` maps to zero in the tensor with the image of `J → R/I^k`. Tensor
   right exactness puts `x` in the image of `M ⊗ (J ∩ I^k)`.
2. Artin–Rees for `J ≤ R` gives `J ∩ I^(n+c) ≤ I^n J`. Moving scalars across
   tensors therefore puts `x` in `I^n (M ⊗ J)` for every `n`.
3. `M ⊗ J` is finite over `S`, since `J` is finite over `R`. After transferring
   ideal powers to `S`, Mathlib's elementwise Krull-intersection theorem gives
   `r ∈ IS` with `r • x = x`. Hence `1-r` annihilates `x` and lies outside `q`.
4. Tensor-localization compatibility and the kernel criterion for localization
   give injectivity of `M_q ⊗ J → M_q`: clear the denominator of an element's
   image first, then apply steps 1–3. The ideal criterion gives flatness of `M_q`.
5. In a local ring all elements outside the maximal ideal are units. The identity
   on `M` is therefore itself a localization map there; its localization
   equivalence, restricted to `R`, transfers flatness back to `M`. -/
theorem flat_of_flat_quotients_powers {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M] (I : Ideal R)
    (hflat : ∀ n : ℕ, 1 ≤ n →
      Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n) • (⊤ : Submodule R M))) :
    (∀ (q : Ideal S) [q.IsPrime], I.map (algebraMap R S) ≤ q →
      Module.Flat R (LocalizedModule q.primeCompl M)) ∧
    (∀ [IsLocalRing S], I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S →
      Module.Flat R M) := by
  -- Flat quotient purity and Artin–Rees control every ideal's tensor kernel.
  have hker (J : Ideal R) (x : TensorProduct R M J) (hx : J.subtype.lTensor M x = 0)
      (n : ℕ) : x ∈ I ^ n • (⊤ : Submodule R (TensorProduct R M J)) := by
    have step1 (k : ℕ) (hk : 1 ≤ k) :
        x ∈ LinearMap.range ((Submodule.comap J.subtype (I ^ k)).subtype.lTensor M) := by
      let := hflat k hk
      let π : J →ₗ[R] R ⧸ I ^ k := (I ^ k).mkQ ∘ₗ J.subtype
      let πJ : J →ₗ[R] LinearMap.range π := π.rangeRestrict
      have hπJ : Function.Surjective πJ := LinearMap.surjective_rangeRestrict π
      have hN : ∀ i ∈ I ^ k, ∀ y : R ⧸ I ^ k, i • y = 0 := by
        intro i hi y
        induction y using Submodule.Quotient.induction_on with
        | H r =>
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact (I ^ k).mul_mem_right r hi
      have hinj := lTensor_subtype_injective_of_smul_eq_zero (M := M) (I ^ k) hN
        (LinearMap.range π)
      have hzero : πJ.lTensor M x = 0 := by
        apply hinj
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        change π.lTensor M x = 0
        rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hx, map_zero]
      have hex : Function.Exact (Submodule.comap J.subtype (I ^ k)).subtype πJ := by
        rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
        ext y
        simp [π, Ideal.Quotient.eq_zero_iff_mem]
      exact ((_root_.lTensor_exact M hex hπJ) x).1 hzero
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
    cases n with
    | zero => simp
    | succ n =>
      have hle : Submodule.comap J.subtype (I ^ (n + 1 + k)) ≤
          I ^ (n + 1) • (⊤ : Submodule R J) := by
        intro y hy
        have hy' : (y : R) ∈ I ^ (n + 1 + k) • (⊤ : Ideal R) ⊓ J := by
          simpa [smul_eq_mul, Ideal.mul_top] using hy
        rw [hk _ (Nat.le_add_left k (n + 1)), Nat.add_sub_cancel] at hy'
        have hy'' : (y : R) ∈ Submodule.map J.subtype
            (I ^ (n + 1) • (⊤ : Submodule R J)) := by
          rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
          exact Submodule.smul_mono le_rfl inf_le_right hy'
        obtain ⟨z, hz, hzy⟩ := hy''
        rwa [← Subtype.ext hzy]
      obtain ⟨y, rfl⟩ := step1 (n + 1 + k) (by omega)
      have : (Submodule.comap J.subtype (I ^ (n + 1 + k))).subtype =
          (I ^ (n + 1) • (⊤ : Submodule R J)).subtype ∘ₗ Submodule.inclusion hle := rfl
      rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply]
      exact range_lTensor_smul_top_subtype_le (M := M) (I ^ (n + 1)) ⟨_, rfl⟩
  have hloc : ∀ (q : Ideal S) [q.IsPrime], I.map (algebraMap R S) ≤ q →
      Module.Flat R (LocalizedModule q.primeCompl M) := by
    intro q _ hIq
    -- Clear denominators, then annihilate the resulting kernel element outside q.
    let L := LocalizedModule q.primeCompl M
    let ℓ : M →ₗ[S] L := LocalizedModule.mkLinearMap q.primeCompl M
    rw [iff_lTensor_injective']
    intro J
    change Function.Injective (TensorProduct.AlgebraTensorModule.lTensor S L J.subtype)
    apply IsLocalizedModule.injective_of_map_zero q.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R J ℓ)
    intro x hx
    have hcomm : (TensorProduct.AlgebraTensorModule.lTensor S L J.subtype) ∘ₗ
        (TensorProduct.AlgebraTensorModule.rTensor R J ℓ) =
        (TensorProduct.AlgebraTensorModule.rTensor R R ℓ) ∘ₗ
        (TensorProduct.AlgebraTensorModule.lTensor S M J.subtype) := by
      ext m j
      rfl
    have hx' : TensorProduct.AlgebraTensorModule.rTensor R R ℓ (J.subtype.lTensor M x) = 0 := by
      change TensorProduct.AlgebraTensorModule.rTensor R R ℓ
        (TensorProduct.AlgebraTensorModule.lTensor S M J.subtype x) = 0
      rw [← LinearMap.comp_apply, ← hcomm]
      exact hx
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R R ℓ)).mp hx'
    have hxs : J.subtype.lTensor M (s.1 • x) = 0 := by
      change TensorProduct.AlgebraTensorModule.lTensor S M J.subtype (s.1 • x) = 0
      change s.1 • TensorProduct.AlgebraTensorModule.lTensor S M J.subtype x = 0 at hs
      rwa [map_smul]
    have : Module.Finite R J := IsNoetherian.finite R J
    have : Module.Finite S (TensorProduct R M J) :=
      Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J)
    have hmem : s.1 • x ∈
        (⨅ n : ℕ, I.map (algebraMap R S) ^ n • ⊤ : Submodule S (TensorProduct R M J)) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [← Ideal.map_pow]
      refine Submodule.smul_induction_on (hker J (s.1 • x) hxs n)
        (fun r hr y _ ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
      rw [← algebraMap_smul S r y]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    obtain ⟨r, hr⟩ := ((I.map (algebraMap R S)).mem_iInf_smul_pow_eq_bot_iff
      (s.1 • x)).mp hmem
    have ht : 1 - r.1 ∉ q := by
      intro ht
      have hone : (1 : S) ∈ q := by
        have := q.add_mem ht (hIq r.2)
        simpa using this
      exact (Ideal.IsPrime.ne_top inferInstance) (q.eq_top_of_isUnit_mem hone isUnit_one)
    have hzero : (1 - r.1) • (s.1 • x) = 0 := by
      rw [sub_smul, one_smul, hr, sub_self]
    apply (IsLocalizedModule.eq_zero_iff q.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R J ℓ)).mpr
    exact ⟨⟨(1 - r.1) * s.1, q.primeCompl.mul_mem ht s.2⟩, by
      simpa only [Submonoid.smul_def, mul_smul] using hzero⟩
  refine ⟨hloc, ?_⟩
  intro _ hI
  let q := IsLocalRing.maximalIdeal S
  let := hloc q hI
  let : IsLocalizedModule q.primeCompl (LinearMap.id : M →ₗ[S] M) :=
    { map_units := fun s ↦ (IsLocalRing.notMem_maximalIdeal.mp s.2).map
        (algebraMap S (Module.End S M))
      surj := fun m ↦ ⟨⟨m, 1⟩, one_smul _ _⟩
      exists_of_eq := fun h ↦ ⟨1, by simpa using h⟩ }
  exact of_linearEquiv
    ((IsLocalizedModule.iso q.primeCompl (LinearMap.id : M →ₗ[S] M)).symm.restrictScalars R)

end Module.Flat
