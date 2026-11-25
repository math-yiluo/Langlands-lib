/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Flatness of modules descends to a finite stage

Let `R₀` be a noetherian ring, `S₀` a finite type `R₀`-algebra, `M₀` a finite `S₀`-module and
`A` an `R₀`-algebra such that `A ⊗[R₀] M₀` is flat over `A`. Then there is a finitely generated
`R₀`-subalgebra `R₁` of `A` such that `R ⊗[R₀] M₀` is flat over `R` for every subalgebra
`R₁ ≤ R ≤ A` (Stacks, Tags 00R6 and 02JO; EGA IV₃, 11.2.6).

This is the module version of `Module.exists_fg_flat_localization_tensor` and
`PrimeSpectrum.exists_fg_forall_flat_localization_tensor_of_isCompact`, which treat `M₀ = S₀`.

## Main results

- `Module.flat_localizedModule_baseChange_of_forall`: flatness at a prime of a finite stage, by
  the local criterion (Stacks, Tag 00MO).
- `Module.exists_fg_flat_localizedModule_baseChange`: flatness at a prime descends to a finitely
  generated subalgebra (Stacks, Tag 00R6).
- `Module.exists_fg_forall_flat_tensorProduct`: flatness descends to a finitely generated
  subalgebra (Stacks, Tag 02JO).

## Implementation notes

For an `R₀`-algebra `R` we write `B R = R ⊗[R₀] S₀`, an `S₀`-algebra by
`Algebra.TensorProduct.rightAlgebra`, and `N R = B R ⊗[S₀] M₀`, which is a `B R`-module and an
`R`-module; flatness is checked at the localizations of `N R` at primes of `B R`. The key tool is
the identification `N R ⊗[R] K ≃ M₀ ⊗[R₀] K` (`Module.baseChangeTensorEquiv`).
-/

@[expose] public section

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Module

section Equiv

variable {R₀ R₁ S₀ M₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

variable (M₀) in
/-- `((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] K ≃ M₀ ⊗[R₀] K` for an `R₁`-module `K`. -/
noncomputable def baseChangeTensorEquiv (K : Type*) [AddCommGroup K] [Module R₀ K] [Module R₁ K]
    [IsScalarTower R₀ R₁ K] :
    ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] K ≃ₗ[S₀] M₀ ⊗[R₀] K :=
  ((AlgebraTensorModule.rightComm R₁ S₀ (R₁ ⊗[R₀] S₀) (R₁ ⊗[R₀] S₀) M₀ K).restrictScalars
    S₀).trans <|
  (TensorProduct.congr
    ({ Algebra.TensorProduct.tensorCancelEquiv (R₁ := R₁) (S₀ := S₀) K with
      map_smul' := fun s y ↦ by
        rw [← algebraMap_smul (R₁ ⊗[R₀] S₀) s y]
        exact Algebra.TensorProduct.tensorCancelEquiv_smul K s y } :
      (R₁ ⊗[R₀] S₀) ⊗[R₁] K ≃ₗ[S₀] S₀ ⊗[R₀] K)
    (LinearEquiv.refl S₀ M₀)).trans <|
  (TensorProduct.comm S₀ _ M₀).trans (AlgebraTensorModule.cancelBaseChange R₀ S₀ S₀ M₀ K)

variable (K : Type*) [AddCommGroup K] [Module R₀ K] [Module R₁ K] [IsScalarTower R₀ R₁ K]

@[simp]
lemma baseChangeTensorEquiv_tmul (r : R₁) (s : S₀) (m : M₀) (k : K) :
    baseChangeTensorEquiv M₀ K (((r ⊗ₜ[R₀] s) ⊗ₜ[S₀] m) ⊗ₜ[R₁] k) = (s • m) ⊗ₜ (r • k) :=
  rfl

lemma baseChangeTensorEquiv_lTensor {K' : Type*} [AddCommGroup K'] [Module R₀ K'] [Module R₁ K']
    [IsScalarTower R₀ R₁ K'] (f : K' →ₗ[R₁] K) (y : ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] K') :
    baseChangeTensorEquiv M₀ K (f.lTensor _ y) =
      (f.restrictScalars R₀).lTensor M₀ (baseChangeTensorEquiv M₀ K' y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x k =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b m =>
      induction b using TensorProduct.inductionOn with
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul r s => simp

lemma baseChangeTensorEquiv_smul (r : R₁) (s : S₀) (y : ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] K) :
    baseChangeTensorEquiv M₀ K ((r ⊗ₜ[R₀] s : R₁ ⊗[R₀] S₀) • y) =
      s • (DistribSMul.toLinearMap R₀ K r).lTensor M₀ (baseChangeTensorEquiv M₀ K y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, map_add, smul_add]
  | tmul x k =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
    | tmul b m =>
      induction b using TensorProduct.inductionOn with
      | add x y hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
      | tmul r' s' =>
        rw [smul_tmul', smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
          baseChangeTensorEquiv_tmul, baseChangeTensorEquiv_tmul, LinearMap.lTensor_tmul,
          smul_tmul', DistribSMul.toLinearMap_apply, mul_smul, mul_smul]

lemma baseChangeTensorEquiv_algebraMap_smul (s : S₀)
    (y : ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] K) :
    baseChangeTensorEquiv M₀ K (algebraMap S₀ (R₁ ⊗[R₀] S₀) s • y) =
      s • baseChangeTensorEquiv M₀ K y := by
  rw [algebraMap_smul, map_smul]

/-- Injectivity of `N ⊗ K' → N ⊗ K` for `N = (R₁ ⊗[R₀] S₀) ⊗[S₀] M₀` is injectivity of
`M₀ ⊗ K' → M₀ ⊗ K` over `R₀`. -/
lemma lTensor_baseChange_injective_iff {K' : Type*} [AddCommGroup K'] [Module R₀ K']
    [Module R₁ K'] [IsScalarTower R₀ R₁ K'] (f : K' →ₗ[R₁] K) :
    Function.Injective (f.lTensor ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) ↔
      Function.Injective ((f.restrictScalars R₀).lTensor M₀) := by
  have : ⇑(f.lTensor ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) = (baseChangeTensorEquiv M₀ K).symm ∘
      ((f.restrictScalars R₀).lTensor M₀) ∘ (baseChangeTensorEquiv M₀ K') := by
    funext y
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply, baseChangeTensorEquiv_lTensor]
  rw [this, EquivLike.comp_injective, EquivLike.injective_comp]

/-- **Flatness of a base change in terms of `M₀`.** The module `(R₁ ⊗[R₀] S₀) ⊗[S₀] M₀` is flat
over `R₁` if and only if `M₀ ⊗ J → M₀ ⊗ R₁` is injective for every ideal `J` of `R₁`. -/
lemma flat_baseChange_iff :
    Flat R₁ ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ↔
      ∀ J : Ideal R₁, Function.Injective ((J.subtype.restrictScalars R₀).lTensor M₀) := by
  rw [Flat.iff_lTensor_injective']
  exact forall_congr' fun J ↦ lTensor_baseChange_injective_iff R₁ J.subtype

end Equiv

section Localization

variable {R₀ R₁ S₀ M₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- Injectivity of `N_{q₁} ⊗ K' → N_{q₁} ⊗ K` at the localization of `N = (R₁ ⊗[R₀] S₀) ⊗[S₀] M₀`
at a prime `q₁` follows from the injectivity over `R₀` at the localization of `M₀` at the prime
below. -/
theorem lTensor_injective_localizedModule_baseChange (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    {K K' : Type*} [AddCommGroup K] [Module R₀ K] [Module R₁ K] [IsScalarTower R₀ R₁ K]
    [AddCommGroup K'] [Module R₀ K'] [Module R₁ K'] [IsScalarTower R₀ R₁ K'] (f : K' →ₗ[R₁] K)
    (h : Function.Injective ((f.restrictScalars R₀).lTensor
      (LocalizedModule (q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))).primeCompl M₀))) :
    Function.Injective
      (f.lTensor (LocalizedModule q₁.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀))) := by
  set q₀ := q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))
  rw [lTensor_injective_iff_of_isLocalizedModule (S := S₀) q₀.primeCompl
    (LocalizedModule.mkLinearMap q₀.primeCompl M₀)] at h
  rw [lTensor_injective_iff_of_isLocalizedModule (S := R₁ ⊗[R₀] S₀) q₁.primeCompl
    (LocalizedModule.mkLinearMap q₁.primeCompl _)]
  intro y hy
  obtain ⟨t, ht, hty⟩ := h (baseChangeTensorEquiv M₀ K' y) (by
    rw [← baseChangeTensorEquiv_lTensor, hy, map_zero])
  refine ⟨algebraMap S₀ (R₁ ⊗[R₀] S₀) t, ht, ?_⟩
  apply (baseChangeTensorEquiv M₀ K').injective
  rw [baseChangeTensorEquiv_algebraMap_smul, hty, map_zero]

end Localization

section LocalCriterion

universe u

variable {R₀ R₁ S₀ M₀ : Type u} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- **Flatness at a prime of a finite stage** (Stacks, Tag 00R6, via Tag 00MO), module version of
`Module.flat_localization_tensor_of_forall`. Let `R₁` be a noetherian `R₀`-algebra, `S₀` a finite
type `R₀`-algebra, `M₀` a finite `S₀`-module and `q₁` a prime of `R₁ ⊗[R₀] S₀` lying over the
primes `q₀` of `S₀` and `p₀` of `R₀`. If every element of the kernel of `M₀ ⊗ p₀ → M₀` vanishes in
`M₀ ⊗ p₀ R₁`, then the localization of `(R₁ ⊗[R₀] S₀) ⊗[S₀] M₀` at `q₁` is flat over `R₁`. -/
theorem flat_localizedModule_baseChange_of_forall [IsNoetherianRing R₀] [IsNoetherianRing R₁]
    [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀] (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    (h : ∀ ξ : M₀ ⊗[R₀] ((q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))).comap (algebraMap R₀ S₀)),
      TensorProduct.rid R₀ M₀ (Submodule.subtype _ |>.lTensor M₀ ξ) = 0 →
      (((Algebra.linearMap R₀ R₁) ∘ₗ Submodule.subtype _).codRestrict
        ((((q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))).comap
          (algebraMap R₀ S₀)).map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun a ↦ Ideal.mem_map_of_mem _ a.2)).lTensor M₀ ξ = 0) :
    Flat R₁ (LocalizedModule q₁.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  classical
  set q₀ := q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))
  set p₀ := q₀.comap (algebraMap R₀ S₀)
  set I₁ : Ideal R₁ := p₀.map (algebraMap R₀ R₁)
  set L := I₁.restrictScalars R₀
  set σ : p₀ →ₗ[R₀] L := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict L
    (fun a ↦ Ideal.mem_map_of_mem _ a.2)
  set M₀' := LocalizedModule q₀.primeCompl M₀
  set M₁ := LocalizedModule q₁.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  have : IsNoetherianRing (R₁ ⊗[R₀] S₀) := Algebra.FiniteType.isNoetherianRing R₁ _
  -- Elements of `R₀` outside `p₀` act bijectively on `M₀'`.
  have hbij : ∀ r ∉ p₀, Function.Bijective (fun m : M₀' ↦ r • m) := by
    intro r hr
    have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap q₀.primeCompl M₀)
      (⟨algebraMap R₀ S₀ r, hr⟩ : q₀.primeCompl)
    rw [Module.End.isUnit_iff] at hu
    convert hu using 1
    ext m
    simp [Module.algebraMap_end_apply, algebraMap_smul]
  have hQ₀ : ∀ (N : Type u) [AddCommGroup N] [Module R₀ N], (∀ i ∈ p₀, ∀ n : N, i • n = 0) →
      ∀ N' : Submodule R₀ N, Function.Injective (N'.subtype.lTensor M₀') :=
    fun N _ _ hN N' ↦ Flat.lTensor_subtype_injective_of_bijective_smul p₀ hbij hN N'
  -- The kernel of `M₀' ⊗ p₀ → M₀'` dies in `M₀' ⊗ p₀ R₁`.
  have hloc : ∀ k : M₀' ⊗[R₀] p₀, TensorProduct.rid R₀ M₀' (p₀.subtype.lTensor M₀' k) = 0 →
      σ.lTensor M₀' k = 0 := by
    intro k hk
    let ℓ : M₀ →ₗ[S₀] M₀' := LocalizedModule.mkLinearMap q₀.primeCompl M₀
    let g' : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀' ⊗[R₀] p₀ := AlgebraTensorModule.rTensor R₀ p₀ ℓ
    let gL : M₀ ⊗[R₀] L →ₗ[S₀] M₀' ⊗[R₀] L := AlgebraTensorModule.rTensor R₀ L ℓ
    have : IsLocalizedModule q₀.primeCompl g' := IsLocalizedModule.rTensor (A := S₀) _ ℓ
    have : IsLocalizedModule q₀.primeCompl gL := IsLocalizedModule.rTensor (A := S₀) _ ℓ
    let μ₀ : M₀' ⊗[R₀] p₀ →ₗ[S₀] M₀' := (AlgebraTensorModule.rid R₀ S₀ M₀').toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ M₀' p₀.subtype
    let μ' : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀ := (AlgebraTensorModule.rid R₀ S₀ M₀).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ M₀ p₀.subtype
    have hnat1 (x : M₀ ⊗[R₀] p₀) : μ₀ (g' x) = ℓ (μ' x) := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul m a =>
        simp only [μ₀, μ', g', ℓ, LinearMap.comp_apply, AlgebraTensorModule.rTensor_tmul,
          AlgebraTensorModule.lTensor_tmul, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
          Submodule.subtype_apply]
        rw [← algebraMap_smul S₀ (a : R₀) m, map_smul, algebraMap_smul]
    have hnat2 (x : M₀ ⊗[R₀] p₀) : AlgebraTensorModule.lTensor S₀ M₀' σ (g' x) =
        gL (AlgebraTensorModule.lTensor S₀ M₀ σ x) := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul s a => rfl
    obtain ⟨⟨k', s⟩, hs⟩ := IsLocalizedModule.surj q₀.primeCompl g' k
    simp only [Submonoid.smul_def] at hs
    have h1 : ℓ (μ' k') = 0 := by
      rw [← hnat1, ← hs, map_smul]
      change (s : S₀) • (TensorProduct.rid R₀ M₀' (p₀.subtype.lTensor M₀' k)) = 0
      rw [hk, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff q₀.primeCompl (f := ℓ)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    have h3 : AlgebraTensorModule.lTensor S₀ M₀ σ ((t : S₀) • k') = 0 := h _ ht
    have h4 : ((t : S₀) * s) • AlgebraTensorModule.lTensor S₀ M₀' σ k = 0 := by
      rw [mul_smul, ← map_smul, hs, ← map_smul, ← map_smul g', hnat2, h3, map_zero]
    have hu := IsLocalizedModule.map_units gL ⟨t * s, mul_mem t.2 s.2⟩
    refine (Module.End.isUnit_iff _).mp hu |>.1 ?_
    rw [map_zero, Module.algebraMap_end_apply]
    exact h4
  have hI₀ : Function.Injective (L.subtype.lTensor M₀') := by
    have hL : p₀ • (⊤ : Submodule R₀ R₁) ≤ L := by
      rw [Submodule.smul_le]
      intro a ha n _
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    refine Flat.lTensor_subtype_injective_of_forall_ker p₀ hQ₀ L hL fun k hk n ↦ ?_
    let mn : L →ₗ[R₀] L := (DistribSMul.toLinearMap R₁ I₁ n).restrictScalars R₀
    have : ((LinearMap.toSpanSingleton R₀ R₁ n) ∘ₗ p₀.subtype).codRestrict L
        (fun i ↦ hL (Submodule.smul_mem_smul i.2 trivial)) = mn ∘ₗ σ := by
      ext a
      simp [σ, Algebra.smul_def, mul_comm]
      rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hloc k hk, map_zero]
  -- The local criterion over `R₁` with the ideal `I₁`.
  have hIS : I₁.map (algebraMap R₁ (Localization.AtPrime q₁)) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap,
      Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap,
      IsScalarTower.algebraMap_apply R₁ (R₁ ⊗[R₀] S₀) (Localization.AtPrime q₁),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q₁) q₁,
      ← IsScalarTower.algebraMap_apply R₀ R₁ (R₁ ⊗[R₀] S₀),
      ← (Algebra.TensorProduct.includeRight : S₀ →ₐ[R₀] R₁ ⊗[R₀] S₀).commutes a]
    exact ha
  refine Flat.of_lTensor_injective_of_forall (S := Localization.AtPrime q₁) (M := M₁) I₁ hIS
    ?_ ?_
  · intro N _ _ hN N'
    let : Module R₀ N := Module.compHom N (algebraMap R₀ R₁)
    have : IsScalarTower R₀ R₁ N := ⟨fun r s n ↦ by
      change (r • s) • n = algebraMap R₀ R₁ r • s • n
      rw [Algebra.smul_def, mul_smul]⟩
    apply lTensor_injective_localizedModule_baseChange q₁ N'.subtype
    exact hQ₀ N (fun i hi n ↦ hN _ (Ideal.mem_map_of_mem _ hi) n) (N'.restrictScalars R₀)
  · exact lTensor_injective_localizedModule_baseChange q₁ I₁.subtype hI₀

end LocalCriterion

section FiniteStage

variable {R₀ A M₀ : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A] [AddCommGroup M₀]
  [Module R₀ M₀]

/-- **Elements of `Tor₁` die at a finite stage** (the first step of Stacks, Tag 00R6), module
version of `Module.exists_finset_lTensor_eq_zero`. Let `p` be an ideal of the noetherian ring `R₀`
such that `M₀ ⊗ p A → M₀ ⊗ A` is injective (e.g. if `A ⊗[R₀] M₀` is flat over `A`), and `ξ` in
the kernel of `M₀ ⊗ p → M₀`. Then there is a finite subset `T` of `A` such that `ξ` vanishes in
`M₀ ⊗ p R₁` for every subalgebra `R₁ ⊆ A` containing `T`. -/
theorem exists_finset_lTensor_eq_zero_of_injective [IsNoetherianRing R₀] (p : Ideal R₀)
    (hp : Function.Injective
      (((p.map (algebraMap R₀ A)).subtype.restrictScalars R₀).lTensor M₀))
    (ξ : M₀ ⊗[R₀] p) (hξ : TensorProduct.rid R₀ M₀ (p.subtype.lTensor M₀ ξ) = 0) :
    ∃ T : Finset A, ∀ R₁ : Subalgebra R₀ A, (T : Set A) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ p.subtype).codRestrict
        ((p.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun a ↦ Ideal.mem_map_of_mem _ a.2)).lTensor M₀ ξ = 0 := by
  classical
  set J := p.map (algebraMap R₀ A)
  let τ : p →ₗ[R₀] J :=
    { toFun := fun a ↦ ⟨algebraMap R₀ A a, Ideal.mem_map_of_mem _ a.2⟩
      map_add' := fun a b ↦ Subtype.ext (by simp)
      map_smul' := fun r a ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  -- `J ⊗[R₀] M₀ → A ⊗[R₀] M₀` is injective.
  have hinj : Function.Injective (AlgebraTensorModule.rTensor R₀ M₀ J.subtype) := by
    have : ⇑(AlgebraTensorModule.rTensor R₀ M₀ J.subtype) = (TensorProduct.comm R₀ M₀ A) ∘
        ((J.subtype.restrictScalars R₀).lTensor M₀) ∘ (TensorProduct.comm R₀ J M₀) := by
      funext x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy, Function.comp_apply]
      | tmul j m => rfl
    rw [this]
    exact (TensorProduct.comm R₀ M₀ A).injective.comp
      (hp.comp (TensorProduct.comm R₀ J M₀).injective)
  have himage : ∀ x : M₀ ⊗[R₀] p, AlgebraTensorModule.rTensor R₀ M₀ J.subtype
      (τ.rTensor M₀ (TensorProduct.comm R₀ M₀ p x)) =
        (1 : A) ⊗ₜ TensorProduct.rid R₀ M₀ (p.subtype.lTensor M₀ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, tmul_add]
    | tmul s a =>
      simp [τ, Algebra.algebraMap_eq_smul_one, smul_tmul]
  set P := LinearMap.range τ
  have hPfg : P.FG := by
    change (LinearMap.range τ).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map τ
  set t := τ.rangeRestrict.rTensor M₀ (TensorProduct.comm R₀ M₀ p ξ)
  have ht : P.subtype.rTensor M₀ t = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply (P.subtype.rTensor M₀), ← LinearMap.rTensor_comp]
    change AlgebraTensorModule.rTensor R₀ M₀ J.subtype
      (τ.rTensor M₀ (TensorProduct.comm R₀ M₀ p ξ)) = 0
    rw [himage, hξ, tmul_zero]
  obtain ⟨Q, hPQ, ⟨G, hG⟩, hQ⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hPfg ht
  have hrep : ∀ g : J, ∃ (n : ℕ) (c : Fin n → A) (d : Fin n → p),
      ∑ i, c i * algebraMap R₀ A (d i) = g := by
    intro g
    obtain ⟨n, c, d, hcd⟩ := Submodule.mem_span_set'.mp g.2
    choose a ha had using fun i ↦ (d i).2
    exact ⟨n, c, fun i ↦ ⟨a i, ha i⟩, by rw [← hcd]; simp [had, smul_eq_mul]⟩
  choose n c d hcd using hrep
  refine ⟨G.biUnion fun g ↦ Finset.univ.image (c g), fun R₁ hT ↦ ?_⟩
  set I₁ := (p.map (algebraMap R₀ R₁)).restrictScalars R₀
  have hmem : ∀ x ∈ I₁, ((x : R₁) : A) ∈ J := by
    intro x hx
    have := Ideal.mem_map_of_mem R₁.val.toRingHom hx
    rwa [Ideal.map_map, show R₁.val.toRingHom.comp (algebraMap R₀ R₁) = algebraMap R₀ A from
      RingHom.ext fun r ↦ by simp] at this
  let κ : I₁ →ₗ[R₀] J :=
    { toFun := fun x ↦ ⟨((x : R₁) : A), hmem x x.2⟩
      map_add' := fun x y ↦ rfl
      map_smul' := fun r x ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  have hκ : Function.Injective κ := fun x y h ↦
    Subtype.ext (Subtype.ext congr(($h : A)))
  have hQκ : Q ≤ LinearMap.range κ := by
    rw [← hG, Submodule.span_le]
    intro g hg
    have hc : ∀ i, c g i ∈ R₁ := fun i ↦
      hT (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    refine ⟨⟨∑ i, ⟨c g i, hc i⟩ * algebraMap R₀ R₁ (d g i), ?_⟩, Subtype.ext ?_⟩
    · exact Submodule.sum_mem _ fun i _ ↦
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (d g i).2)
    · simp [κ, ← hcd g]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Q →ₗ[R₀] I₁, ψ ∘ₗ Submodule.inclusion hPQ ∘ₗ τ.rangeRestrict =
      ((Algebra.linearMap R₀ R₁) ∘ₗ p.subtype).codRestrict I₁
        (fun a ↦ Ideal.mem_map_of_mem _ a.2) := by
    refine ⟨(LinearEquiv.ofInjective κ hκ).symm.toLinearMap ∘ₗ Submodule.inclusion hQκ,
      LinearMap.ext fun a ↦ hκ ?_⟩
    change κ ((LinearEquiv.ofInjective κ hκ).symm _) = _
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have key : (ψ ∘ₗ Submodule.inclusion hPQ ∘ₗ τ.rangeRestrict).rTensor M₀
      (TensorProduct.comm R₀ M₀ p ξ) = ψ.rTensor M₀ ((Submodule.inclusion hPQ).rTensor M₀ t) := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [← hψ, ← (TensorProduct.comm R₀ p M₀).apply_symm_apply ξ, TensorProduct.comm_symm,
    LinearMap.lTensor_comm, key, hQ, LinearMap.map_zero, LinearEquiv.map_zero]


end FiniteStage

/-- A tensor product `M ⊗[R] N` with `M` finite over an `R`-algebra `S` and `N` finite over `R`
is finite over `S`. -/
lemma finite_tensorProduct_of_finite {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [AddCommGroup N]
    [Module R N] [Module.Finite S M] [Module.Finite R N] : Module.Finite S (M ⊗[R] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  exact Module.Finite.of_surjective
    ((AlgebraTensorModule.lTensor S M f).comp
      (TensorProduct.piScalarRight R S M (Fin n)).symm.toLinearMap)
    ((LinearMap.lTensor_surjective M hf).comp (LinearEquiv.surjective _))

section AtPrime

universe u

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- **Noetherian approximation of flatness at a prime** (Stacks, Tag 00R6), module version of
`Module.exists_fg_flat_localization_tensor`. Let `R₀` be noetherian, `S₀` a finite type
`R₀`-algebra, `M₀` a finite `S₀`-module and `A` an `R₀`-algebra such that `(A ⊗[R₀] S₀) ⊗[S₀] M₀`
is flat over `A`. For a prime `q` of `A ⊗[R₀] S₀` there is a finitely generated subalgebra `R₁` of
`A` such that `(R₁ ⊗[R₀] S₀) ⊗[S₀] M₀` is flat over `R₁` at the prime below `q`. -/
theorem exists_fg_flat_localizedModule_baseChange {A : Type u} [CommRing A] [Algebra R₀ A]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀]
    (hA : Flat A ((A ⊗[R₀] S₀) ⊗[S₀] M₀)) (q : Ideal (A ⊗[R₀] S₀)) [q.IsPrime] :
    ∃ R₁ : Subalgebra R₀ A, R₁.FG ∧ IsNoetherianRing R₁ ∧
      Flat R₁ (LocalizedModule
        (q.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
        ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  classical
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  set q₀ : Ideal S₀ := q.comap (algebraMap S₀ (A ⊗[R₀] S₀))
  set p₀ : Ideal R₀ := q₀.comap (algebraMap R₀ S₀)
  let μ' : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀ := (AlgebraTensorModule.rid R₀ S₀ M₀).toLinearMap ∘ₗ
    AlgebraTensorModule.lTensor S₀ M₀ p₀.subtype
  have : Module.Finite S₀ (M₀ ⊗[R₀] p₀) := finite_tensorProduct_of_finite
  obtain ⟨Ξ, hΞ⟩ : (LinearMap.ker μ').FG := IsNoetherian.noetherian _
  have hV : ∀ ξ ∈ Ξ, ∃ T : Finset A, ∀ R₁ : Subalgebra R₀ A, (T : Set A) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
        ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun a ↦ Ideal.mem_map_of_mem _ a.2)).lTensor M₀ ξ = 0 := fun ξ hξ ↦
    exists_finset_lTensor_eq_zero_of_injective p₀ (flat_baseChange_iff.mp hA _) ξ (by
      have h : ξ ∈ LinearMap.ker μ' := hΞ ▸ Submodule.subset_span hξ
      exact h)
  choose! T hT using hV
  set R₁ := Algebra.adjoin R₀ ((Ξ.biUnion T : Finset A) : Set A)
  have : Algebra.FiniteType R₀ R₁ := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  refine ⟨R₁, Subalgebra.fg_adjoin_finset _, this, ?_⟩
  set q₁ := q.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom
  have hq : q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀)) = q₀ := by
    rw [Ideal.comap_comap]
    congr 1
  apply flat_localizedModule_baseChange_of_forall q₁
  rw [hq]
  intro ξ hξ
  have hξ' : ξ ∈ Submodule.span S₀ (Ξ : Set (M₀ ⊗[R₀] p₀)) := hΞ ▸ LinearMap.mem_ker.mpr hξ
  set σ := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
    ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀) (fun a ↦ Ideal.mem_map_of_mem _ a.2)
  change AlgebraTensorModule.lTensor S₀ M₀ σ ξ = 0
  clear hξ
  induction hξ' using Submodule.span_induction with
  | mem x hx =>
    exact hT x hx R₁ (subset_trans (Finset.subset_biUnion_of_mem T hx) Algebra.subset_adjoin)
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

end AtPrime

section Global

universe u

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- **Flatness at a point along a map of the base**, module version of
`Module.Flat.localization_tensorProduct_map`. Let `f : R → R'` be a map of `R₀`-algebras and `Q`
a prime of `R' ⊗[R₀] S₀`. If `(R ⊗[R₀] S₀) ⊗[S₀] M₀` is flat over `R` at the prime below `Q`, then
`(R' ⊗[R₀] S₀) ⊗[S₀] M₀` is flat over `R'` at `Q`. -/
theorem flat_localizedModule_baseChange_map {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R₀ R] [Algebra R₀ R'] (f : R →ₐ[R₀] R') (Q : Ideal (R' ⊗[R₀] S₀)) [Q.IsPrime]
    (P : Ideal (R ⊗[R₀] S₀)) [P.IsPrime]
    (hPQ : Q.comap (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom = P)
    (h : Flat R (LocalizedModule P.primeCompl ((R ⊗[R₀] S₀) ⊗[S₀] M₀))) :
    Flat R' (LocalizedModule Q.primeCompl ((R' ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  subst hPQ
  let : Algebra R R' := f.toAlgebra
  have : IsScalarTower R₀ R R' := .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  set φ := Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)
  rw [Flat.iff_lTensor_injective']
  intro J
  rw [lTensor_injective_iff_of_isLocalizedModule (S := R' ⊗[R₀] S₀) Q.primeCompl
    (LocalizedModule.mkLinearMap Q.primeCompl _)]
  intro y hy
  have hR := (lTensor_injective_iff_of_isLocalizedModule (R := R) (S := R ⊗[R₀] S₀)
    (Q.comap φ.toRingHom).primeCompl
    (LocalizedModule.mkLinearMap (Q.comap φ.toRingHom).primeCompl ((R ⊗[R₀] S₀) ⊗[S₀] M₀))
    (J.subtype.restrictScalars R)).1
    (Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  set e := baseChangeTensorEquiv (R₀ := R₀) (R₁ := R) (S₀ := S₀) M₀ J
  set e' := baseChangeTensorEquiv (R₀ := R₀) (R₁ := R') (S₀ := S₀) M₀ J
  set z := e.symm (e' y)
  obtain ⟨t, ht, htz⟩ := hR z (by
    apply (baseChangeTensorEquiv (R₀ := R₀) (R₁ := R) (S₀ := S₀) M₀ R').injective
    rw [baseChangeTensorEquiv_lTensor, LinearEquiv.apply_symm_apply, map_zero]
    have := congrArg (baseChangeTensorEquiv (R₀ := R₀) (R₁ := R') (S₀ := S₀) M₀ R') hy
    rw [baseChangeTensorEquiv_lTensor, map_zero] at this
    exact this)
  refine ⟨φ t, ht, ?_⟩
  apply e'.injective
  rw [map_zero]
  have key : ∀ t : R ⊗[R₀] S₀, e' (φ t • y) = e (t • z) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, add_smul, map_add, ha, hb, add_smul, map_add]
    | tmul r s =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeTensorEquiv_smul,
        baseChangeTensorEquiv_smul, LinearEquiv.apply_symm_apply]
      congr 2
  rw [key, htz, map_zero]

/-- **Flatness is local on the algebra.** If `N` is a module over an `R`-algebra `S` whose
localizations at all primes of `S` are flat over `R`, then `N` is flat over `R`. -/
theorem flat_of_forall_flat_localizedModule {R S N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : ∀ (Q : Ideal S) [Q.IsPrime], Flat R (LocalizedModule Q.primeCompl N)) : Flat R N := by
  rw [Flat.iff_lTensor_injective']
  intro J
  rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hne
  have hI : LinearMap.ker (LinearMap.toSpanSingleton S _ y) ≠ ⊤ := by
    intro htop
    apply hne
    have : (1 : S) ∈ LinearMap.ker (LinearMap.toSpanSingleton S _ y) := htop ▸ Submodule.mem_top
    simpa using this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨t, ht, hty⟩ := (lTensor_injective_iff_of_isLocalizedModule m.primeCompl
    (LocalizedModule.mkLinearMap m.primeCompl N) J.subtype).1
    (Flat.iff_lTensor_injective'.1 (h m) J) y hy
  exact ht (hle (LinearMap.mem_ker.2 hty))

omit [Module R₀ M₀] [IsScalarTower R₀ S₀ M₀] in
/-- **Openness of the flat locus of a base change** (Stacks, Tag 00RC). -/
theorem isOpen_setOf_flat_localizedModule_baseChange [Algebra.FiniteType R₀ S₀]
    [Module.Finite S₀ M₀] (R : Type u) [CommRing R] [Algebra R₀ R] [IsNoetherianRing R] :
    IsOpen {Q : PrimeSpectrum (R ⊗[R₀] S₀) |
      Flat R (LocalizedModule Q.asIdeal.primeCompl ((R ⊗[R₀] S₀) ⊗[S₀] M₀))} := by
  rw [isOpen_iff_forall_mem_open]
  intro Q (hQ : Flat R _)
  obtain ⟨g, hg, hopen⟩ := Flat.exists_notMem_forall_flat_localizedModule (R := R)
    (S := R ⊗[R₀] S₀) (M := (R ⊗[R₀] S₀) ⊗[S₀] M₀) Q.asIdeal hQ
  exact ⟨PrimeSpectrum.basicOpen g, fun Q' hQ' ↦ hopen Q'.asIdeal hQ',
    PrimeSpectrum.isOpen_basicOpen, hg⟩

omit [Module R₀ M₀] [IsScalarTower R₀ S₀ M₀] in
/-- The primes of `A ⊗[R₀] S₀` lying over the flat locus of a noetherian subalgebra `R` of `A`
form an open set. -/
theorem isOpen_setOf_flat_localizedModule_comap [Algebra.FiniteType R₀ S₀]
    [Module.Finite S₀ M₀] {A : Type u} [CommRing A] [Algebra R₀ A] (R : Subalgebra R₀ A)
    [IsNoetherianRing R] :
    IsOpen {q : PrimeSpectrum (A ⊗[R₀] S₀) | Flat R (LocalizedModule
      (q.asIdeal.comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
      ((R ⊗[R₀] S₀) ⊗[S₀] M₀))} :=
  (isOpen_setOf_flat_localizedModule_baseChange (M₀ := M₀) R).preimage
    (PrimeSpectrum.continuous_comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)).toRingHom)

lemma map_val_map_inclusion {A : Type u} [CommRing A] [Algebra R₀ A] {R R' : Subalgebra R₀ A}
    (h : R ≤ R') (x : R ⊗[R₀] S₀) :
    Algebra.TensorProduct.map R'.val (AlgHom.id R₀ S₀)
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id R₀ S₀) x) =
      Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀) x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a s => rfl

lemma map_inclusion_map_inclusion {A : Type u} [CommRing A] [Algebra R₀ A]
    {R R' R'' : Subalgebra R₀ A} (h : R ≤ R') (h' : R' ≤ R'') (x : R ⊗[R₀] S₀) :
    Algebra.TensorProduct.map (Subalgebra.inclusion h') (AlgHom.id R₀ S₀)
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id R₀ S₀) x) =
      Algebra.TensorProduct.map (Subalgebra.inclusion (h.trans h')) (AlgHom.id R₀ S₀) x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a s => rfl

lemma map_eq_rTensor {A : Type u} [CommRing A] [Algebra R₀ A] {R R' : Subalgebra R₀ A}
    (h : R ≤ R') (x : R ⊗[R₀] S₀) :
    Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id R₀ S₀) x =
      LinearMap.rTensor S₀ (Subalgebra.inclusion h).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a s => rfl

lemma map_val_eq_rTensor {A : Type u} [CommRing A] [Algebra R₀ A] {R : Subalgebra R₀ A}
    (x : R ⊗[R₀] S₀) :
    Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀) x =
      LinearMap.rTensor S₀ R.val.toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a s => rfl

/-- Compactness gives one finite stage that is flat at every prime coming from `A`. -/
private lemma exists_fg_forall_flat_localizedModule_baseChange {A : Type u} [CommRing A]
    [Algebra R₀ A] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀]
    (hA : Flat A ((A ⊗[R₀] S₀) ⊗[S₀] M₀)) :
    ∃ R : Subalgebra R₀ A, R.FG ∧ ∀ q : PrimeSpectrum (A ⊗[R₀] S₀),
      Flat R (LocalizedModule
        (q.asIdeal.comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
        ((R ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  classical
  -- The set of primes of `A ⊗[R₀] S₀` at which `R` is flat.
  let W (R : Subalgebra R₀ A) : Set (PrimeSpectrum (A ⊗[R₀] S₀)) :=
    {q | Flat R (LocalizedModule
      (q.asIdeal.comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
      ((R ⊗[R₀] S₀) ⊗[S₀] M₀))}
  have hcomap {R R' : Subalgebra R₀ A} (h : R ≤ R') (q : Ideal (A ⊗[R₀] S₀)) :
      (q.comap (Algebra.TensorProduct.map R'.val (AlgHom.id R₀ S₀)).toRingHom).comap
        (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id R₀ S₀)).toRingHom =
      q.comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)).toRingHom := by
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun x ↦ map_val_map_inclusion h x
  have hW {R R' : Subalgebra R₀ A} (h : R ≤ R') : W R ⊆ W R' := by
    intro q hq
    apply flat_localizedModule_baseChange_map (M₀ := M₀)
      (Subalgebra.inclusion h) _ _ (hcomap h q.asIdeal)
    exact hq
  have hWopen (R : {R : Subalgebra R₀ A // R.FG}) : IsOpen (W R.1) := by
    have : Algebra.FiniteType R₀ R.1 := (Subalgebra.fg_iff_finiteType _).mp R.2
    have : IsNoetherianRing R.1 := Algebra.FiniteType.isNoetherianRing R₀ R.1
    exact isOpen_setOf_flat_localizedModule_comap (M₀ := M₀) R.1
  have hWcov (q : PrimeSpectrum (A ⊗[R₀] S₀)) :
      ∃ R : {R : Subalgebra R₀ A // R.FG}, q ∈ W R.1 := by
    obtain ⟨R, hR, -, hflat⟩ := exists_fg_flat_localizedModule_baseChange hA q.asIdeal
    exact ⟨⟨R, hR⟩, hflat⟩
  have : Nonempty {R : Subalgebra R₀ A // R.FG} := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  obtain ⟨⟨R₁, hR₁⟩, hK⟩ := isCompact_univ.elim_directed_cover (fun R ↦ W R.1) hWopen
    (fun q _ ↦ Set.mem_iUnion.mpr (hWcov q))
    fun (R R' : {R : Subalgebra R₀ A // R.FG}) ↦ ⟨⟨R.1 ⊔ R'.1, R.2.sup R'.2⟩,
      hW le_sup_left, hW le_sup_right⟩
  exact ⟨R₁, hR₁, fun q ↦ hK (Set.mem_univ q)⟩

/-- **Flatness descends to a finitely generated subalgebra** (Stacks, Tag 02JO; EGA IV₃, 11.2.6).
Let `R₀` be noetherian, `S₀` a finite type `R₀`-algebra, `M₀` a finite `S₀`-module and `A` an
`R₀`-algebra such that `(A ⊗[R₀] S₀) ⊗[S₀] M₀` is flat over `A`. Then there is a finitely
generated subalgebra `R₁` of `A` such that `(R ⊗[R₀] S₀) ⊗[S₀] M₀` is flat over `R` for every
subalgebra `R` of `A` containing `R₁`.

Every prime of `A ⊗[R₀] S₀` has a neighbourhood on which flatness holds at some finite stage
(`Module.exists_fg_flat_localizedModule_baseChange` and openness of the flat locus), so by
quasi-compactness flatness holds at a finite stage `R₁` at every prime coming from
`A ⊗[R₀] S₀`. The complement of the flat locus of `R₁` is a closed set `V(I)` with
`I (A ⊗[R₀] S₀) = (1)`; the relation `1 = ∑ cᵢ fᵢ` with `fᵢ ∈ I` holds at a finite stage `R₂`, and
then every prime of `R ⊗[R₀] S₀` for `R ≥ R₂` lies over the flat locus of `R₁`. -/
theorem exists_fg_forall_flat_baseChange {A : Type u} [CommRing A] [Algebra R₀ A]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀]
    (hA : Flat A ((A ⊗[R₀] S₀) ⊗[S₀] M₀)) :
    ∃ R₁ : Subalgebra R₀ A, R₁.FG ∧
      ∀ R : Subalgebra R₀ A, R₁ ≤ R → Flat R ((R ⊗[R₀] S₀) ⊗[S₀] M₀) := by
  classical
  obtain ⟨R₁, hR₁, hK⟩ := exists_fg_forall_flat_localizedModule_baseChange hA
  -- Elaborate the flat locus over an abstract algebra, then specialize to subalgebras.
  let F (R : Type u) [CommRing R] [Algebra R₀ R] : Set (PrimeSpectrum (R ⊗[R₀] S₀)) :=
    {Q | Flat R (LocalizedModule Q.asIdeal.primeCompl ((R ⊗[R₀] S₀) ⊗[S₀] M₀))}
  -- The flat locus `U` of `R₁` and its closed complement `Z = V(I)`.
  have : Algebra.FiniteType R₀ R₁ := (Subalgebra.fg_iff_finiteType _).mp hR₁
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  set U : Set (PrimeSpectrum (R₁ ⊗[R₀] S₀)) := F R₁
  have hU : IsOpen U := isOpen_setOf_flat_localizedModule_baseChange (M₀ := M₀) R₁
  set Z := Uᶜ
  set I := PrimeSpectrum.vanishingIdeal Z
  set φ₁ := Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)
  have hZ : ∀ P : PrimeSpectrum (R₁ ⊗[R₀] S₀), I ≤ P.asIdeal → P ∈ Z := by
    intro P hP
    have : P ∈ PrimeSpectrum.zeroLocus (I : Set (R₁ ⊗[R₀] S₀)) := hP
    rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq] at this
  have hI : I.map φ₁ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmZ := hZ (PrimeSpectrum.comap φ₁.toRingHom ⟨m, hm.isPrime⟩)
      (Ideal.map_le_iff_le_comap.mp hle)
    apply hmZ
    exact hK ⟨m, hm.isPrime⟩
  -- Descend the unit ideal to a finite stage.
  obtain ⟨R₂, hR₁₂, hR₂fg, hI₂⟩ :=
    Subalgebra.exists_map_tensorProduct_inclusion_eq_top hR₁ I hI
  refine ⟨R₂, hR₂fg, fun R hR ↦ ?_⟩
  -- Every prime of `R ⊗[R₀] S₀` lies over the flat locus of `R₁`.
  have h₁ : R₁ ≤ R := hR₁₂.trans hR
  set ρ := Algebra.TensorProduct.map (Subalgebra.inclusion h₁) (AlgHom.id R₀ S₀)
  have hIR : I.map ρ = ⊤ := by
    have hcomp : ρ.toRingHom =
        (Algebra.TensorProduct.map (Subalgebra.inclusion hR) (AlgHom.id R₀ S₀)).toRingHom.comp
          (Algebra.TensorProduct.map (Subalgebra.inclusion hR₁₂)
            (AlgHom.id R₀ S₀)).toRingHom :=
      RingHom.ext fun x ↦ (map_inclusion_map_inclusion hR₁₂ hR x).symm
    change I.map (Algebra.TensorProduct.map (Subalgebra.inclusion hR₁₂)
      (AlgHom.id R₀ S₀)).toRingHom = ⊤ at hI₂
    change I.map ρ.toRingHom = ⊤
    rw [hcomp, ← Ideal.map_map, hI₂, Ideal.map_top]
  apply flat_of_forall_flat_localizedModule (S := R ⊗[R₀] S₀)
  intro Q _
  apply flat_localizedModule_baseChange_map (M₀ := M₀) (Subalgebra.inclusion h₁) Q
    (Q.comap ρ.toRingHom) rfl
  by_contra hP
  have hPZ : (⟨Q.comap ρ.toRingHom, inferInstance⟩ : PrimeSpectrum (R₁ ⊗[R₀] S₀)) ∈ Z := hP
  have hIQ : I ≤ Q.comap ρ.toRingHom :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal Z I).mpr le_rfl hPZ
  have hQ : I.map ρ ≤ Q := Ideal.map_le_iff_le_comap.mpr hIQ
  rw [hIR] at hQ
  exact (Ideal.IsPrime.ne_top ‹_›) (top_le_iff.mp hQ)

end Global

end Module
