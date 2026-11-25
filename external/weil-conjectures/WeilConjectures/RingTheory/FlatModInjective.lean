/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.Mathlib.RingTheory.Filtration

/-! # Injectivity modulo the maximal ideal into a flat module (Noetherian local)

Source: literature/stacks-project/algebra.tex, Lemma Tag 00ME
(blueprint: lem-weil-pbc-flat-mod-injective)
-/

@[expose] public section

open TensorProduct LinearMap in
private theorem rTensor_injective_of_maximal_annihilates
    {R N M : Type*} [CommRing R] [AddCommGroup N] [AddCommGroup M]
    [Module R N] [Module R M] (I : Ideal R) [I.IsMaximal]
    (u : N →ₗ[R] M)
    (hu : Function.Injective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) u
        (Submodule.smul_top_le_comap_smul_top I u)))
    {X : Type*} [AddCommGroup X] [Module R X]
    (hX : ∀ i ∈ I, ∀ x : X, i • x = 0) :
    Function.Injective (u.rTensor X) := by
  let := Ideal.Quotient.field I
  set PN := I • (⊤ : Submodule R N)
  set PM := I • (⊤ : Submodule R M)
  let v : (N ⧸ PN) →ₗ[R] (M ⧸ PM) :=
    PN.mapQ PM u (Submodule.smul_top_le_comap_smul_top I u)
  have hN := Module.Flat.bijective_rTensor_mkQ_of_smul_eq_zero (M := N) I hX
  have hM := Module.Flat.bijective_rTensor_mkQ_of_smul_eq_zero (M := M) I hX
  have hcomm : (PM.mkQ.rTensor X).comp (u.rTensor X) =
      (v.rTensor X).comp (PN.mkQ.rTensor X) := by
    ext; rfl
  suffices h : Function.Injective (v.rTensor X) by
    have hinj := h.comp hN.1
    rw [← LinearMap.coe_comp, ← hcomm, LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  have hXt : Module.IsTorsionBySet R X I := fun x i ↦ hX i i.2 x
  let := hXt.module
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul R (R ⧸ I) (N ⧸ PN) X :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  have : CompatibleSMul R (R ⧸ I) (M ⧸ PM) X :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let w : (N ⧸ PN) →ₗ[R ⧸ I] (M ⧸ PM) :=
    { toFun := v
      map_add' := by simp
      map_smul' := by
        rintro ⟨r⟩ x
        exact v.map_smul r x }
  have : Module.Free (R ⧸ I) X := Module.Free.of_divisionRing _ _
  have hw : Function.Injective (w.rTensor X) :=
    Module.Flat.rTensor_preserves_injective_linearMap w hu
  let e := equivOfCompatibleSMul R (R ⧸ I) R (M ⧸ PM) X
  let e' := equivOfCompatibleSMul R (R ⧸ I) R (N ⧸ PN) X
  have key : v.rTensor X = e.toLinearMap ∘ₗ (w.rTensor X).restrictScalars R ∘ₗ
      e'.symm.toLinearMap := by
    ext x y
    rfl
  rw [key]
  simpa using hw

open TensorProduct LinearMap in
private theorem rTensor_injective_of_maximal_pow_annihilates
    {R N M : Type*} [CommRing R] [AddCommGroup N] [AddCommGroup M]
    [Module R N] [Module R M] [Module.Flat R M] (I : Ideal R) [I.IsMaximal]
    (u : N →ₗ[R] M)
    (hu : Function.Injective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) u
        (Submodule.smul_top_le_comap_smul_top I u)))
    (n : ℕ) {X : Type*} [AddCommGroup X] [Module R X]
    (hX : ∀ i ∈ I ^ n, ∀ x : X, i • x = 0) :
    Function.Injective (u.rTensor X) := by
  induction n generalizing X with
  | zero =>
    have : Subsingleton X := ⟨fun x y ↦ by
      rw [← one_smul R x, ← one_smul R y, hX 1 (by simp) x, hX 1 (by simp) y]⟩
    intro x y _
    exact Subsingleton.elim _ _
  | succ n ih =>
    set X₁ := I • (⊤ : Submodule R X)
    have hX₁ : ∀ i ∈ I ^ n, ∀ x : X₁, i • x = 0 := by
      rintro i hi ⟨x, hx⟩
      apply Subtype.ext
      change i • x = 0
      induction hx using Submodule.smul_induction_on' with
      | smul r hr x _ =>
        rw [smul_smul]
        exact hX _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hi hr) x
      | add x _ y _ hx hy => rw [smul_add, hx, hy, add_zero]
    have hX₂ : ∀ i ∈ I, ∀ x : X ⧸ X₁, i • x = 0 := by
      intro i hi x
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hi trivial
    have h₁ := ih hX₁
    have h₂ := rTensor_injective_of_maximal_annihilates I u hu hX₂
    have hinc : Function.Injective (X₁.subtype.lTensor M) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    have hex := _root_.lTensor_exact N (LinearMap.exact_subtype_mkQ X₁)
      (Submodule.mkQ_surjective X₁)
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : u.rTensor _ (X₁.mkQ.lTensor N x) = 0 := by
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨y, rfl⟩ := (hex x).1 (h₂ (hx'.trans (map_zero _).symm))
    have hy : u.rTensor _ y = 0 := by
      apply hinc
      rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hx]
    rw [h₁ (hy.trans (map_zero _).symm), map_zero]

open TensorProduct LinearMap in
private theorem rTensor_injective_of_residue_injective
    {R S N M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [AddCommGroup M] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module R M] [IsNoetherianRing S]
    [Module.Finite S N] [Module.Flat R M] (I : Ideal R) [I.IsMaximal]
    (hIS : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥)
    (u : N →ₗ[R] M)
    (hu : Function.Injective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) u
        (Submodule.smul_top_le_comap_smul_top I u)))
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    Function.Injective (u.rTensor X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 (n : ℕ) : x ∈ I ^ n • (⊤ : Submodule R (N ⊗[R] X)) := by
    set Xn := I ^ n • (⊤ : Submodule R X)
    have hXn : ∀ i ∈ I ^ n, ∀ y : X ⧸ Xn, i • y = 0 := by
      intro i hi y
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hi trivial
    have hinj := rTensor_injective_of_maximal_pow_annihilates I u hu n hXn
    have hex := _root_.lTensor_exact N (LinearMap.exact_subtype_mkQ Xn)
      (Submodule.mkQ_surjective Xn)
    have h0 : Xn.mkQ.lTensor N x = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨y, rfl⟩ := (hex x).1 h0
    exact Module.Flat.range_lTensor_smul_top_subtype_le (I ^ n) ⟨y, rfl⟩
  have hfin : Module.Finite S (N ⊗[R] X) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N X)
  have hkrull := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := N ⊗[R] X) _ hIS
  have : x ∈ (⨅ i : ℕ, I.map (algebraMap R S) ^ i • ⊤ : Submodule S (N ⊗[R] X)) := by
    rw [Submodule.mem_iInf]
    intro n
    rw [← Ideal.map_pow]
    refine Submodule.smul_induction_on (h2 n) (fun r hr y _ ↦ ?_)
      (fun _ _ ↦ Submodule.add_mem _)
    rw [← algebraMap_smul S r y]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  rwa [hkrull] at this

open TensorProduct LinearMap in
private theorem flat_quotient_range_of_ideal_preimage
    {R N M : Type*} [CommRing R] [AddCommGroup N] [AddCommGroup M]
    [Module R N] [Module R M] [Module.Flat R M] (φ : N →ₗ[R] M)
    (h : ∀ (J : Ideal R) (m : N), φ m ∈ J • (⊤ : Submodule R M) → m ∈ J • (⊤ : Submodule R N)) :
    Module.Flat R (M ⧸ LinearMap.range φ) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  set C := M ⧸ LinearMap.range φ
  set π := (LinearMap.range φ).mkQ
  have hnat (y : M ⊗[R] J) : π (TensorProduct.rid R M (J.subtype.lTensor M y)) =
      TensorProduct.rid R C (J.subtype.lTensor C (π.rTensor J y)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' h h' => simp only [map_add] at h h' ⊢; rw [h, h']
    | tmul m j => simp
  have hφnat (y : N ⊗[R] J) : φ (TensorProduct.rid R N (J.subtype.lTensor N y)) =
      TensorProduct.rid R M (J.subtype.lTensor M (φ.rTensor J y)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' h h' => simp only [map_add] at h h' ⊢; rw [h, h']
    | tmul m j => simp
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective J (Submodule.mkQ_surjective (LinearMap.range φ)) z
  have hα : Function.Injective (J.subtype.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
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
      exact Module.Flat.range_lTensor_smul_top_subtype_le (M := M) J ⟨_, rfl⟩
    have := Submodule.smul_top_le_comap_smul_top J (TensorProduct.rid R M).toLinearMap hy
    simpa [a] using this
  obtain ⟨y', hy'⟩ := Module.Flat.exists_rid_lTensor_eq_of_mem_smul_top J (h J m (hm ▸ haJ))
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


/--
The local injectivity criterion for a map from a finite module into a flat module.
Source: Algebra, Lemma Tag 00ME (blueprint: lem-weil-pbc-flat-mod-injective).
The proof follows the blueprint steps: induction on powers of the maximal ideal using
flat tensor exactness; Krull intersection gives injectivity; and the Tor criterion,
applied after quotienting by each ideal, gives flatness of the cokernel.
The hypothesis `hu` is injectivity of the induced map `N/𝔪N → M/𝔪M`, with `N`
an `R`-module through `φ`.
-/
theorem flat_mod_injective
    {R S N M : Type*}
    [CommRing R] [CommRing S] [AddCommGroup N] [AddCommGroup M]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S)
    (hφ : ∀ x : R, x ∈ IsLocalRing.maximalIdeal R →
      φ x ∈ IsLocalRing.maximalIdeal S)
    [Module S N] [Module R M]
    [Module.Finite S N] [Module.Flat R M]
    (u : (letI : Module R N := Module.compHom N φ; N →ₗ[R] M))
    (hu : (letI : Module R N := Module.compHom N φ;
      Function.Injective
        ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)).mapQ
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) u
          (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) u))))
    : (letI : Module R N := Module.compHom N φ;
      Function.Injective u ∧ Module.Flat R (M ⧸ (LinearMap.range u))) :=
  open TensorProduct LinearMap in by
  let : Algebra R S := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  let : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  have hIS : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson ⊥ := by
    apply le_trans _ (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))
    rw [Ideal.map_le_iff_le_comap]
    exact hφ
  have hpure (J : Ideal R) (x : N) (hx : u x ∈ J • (⊤ : Submodule R M)) :
      x ∈ J • (⊤ : Submodule R N) := by
    have hzero : u.rTensor (R ⧸ J) (x ⊗ₜ[R] (1 : R ⧸ J)) = 0 := by
      apply (tensorQuotEquivQuotSMul M J).injective
      rw [map_zero, LinearMap.rTensor_tmul]
      change tensorQuotEquivQuotSMul M J (u x ⊗ₜ[R] Ideal.Quotient.mk J 1) = 0
      rw [tensorQuotEquivQuotSMul_tmul_mk, one_smul, Submodule.Quotient.mk_eq_zero]
      exact hx
    have hinj := rTensor_injective_of_residue_injective
      (IsLocalRing.maximalIdeal R) hIS u hu (R ⧸ J)
    have hzero' := hinj (hzero.trans (map_zero _).symm)
    have := congrArg (tensorQuotEquivQuotSMul N J) hzero'
    change tensorQuotEquivQuotSMul N J (x ⊗ₜ[R] Ideal.Quotient.mk J 1) =
      tensorQuotEquivQuotSMul N J 0 at this
    simpa only [tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero,
      Submodule.Quotient.mk_eq_zero] using this
  refine ⟨?_, flat_quotient_range_of_ideal_preimage u hpure⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := hpure ⊥ x (by simp [hx])
  simpa using this
