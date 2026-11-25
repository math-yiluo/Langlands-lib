/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.RingTheory.BertiniSmoothAux

/-!
# Smooth hypersurface sections

Let `A` be a smooth algebra of finite type over an algebraically closed field `k`, and let
`f : A` lie outside `m²` for every maximal ideal `m` containing it. Then `A ⧸ (f)` is again
smooth over `k`, and when `A` is a domain of relative dimension `e + 1` and `A ⧸ (f)` is a domain,
the relative dimension of `A ⧸ (f)` is `e`. This is the step "a hypersurface section which is
smooth at each of its points is smooth" of the Bertini argument (blueprint
`lemma-curve-preserving-finite-cover--1`).

## Main results

- `Algebra.exists_derivation_sub_one_mem_span`: some derivation `D` has `D f ≡ 1 mod f`.
- `Algebra.FormallySmooth.quotient_span_singleton_of_derivation`: if `D f ≡ 1 mod f` for a
  derivation `D` of a formally smooth algebra, then `A ⧸ (f)` is formally smooth.
- `Algebra.Smooth.quotient_span_singleton`: the hypersurface section `A ⧸ (f)` is smooth of
  relative dimension one less.
-/

@[expose] public section

universe u

open scoped TensorProduct

open KaehlerDifferential

/-- The rank of a finite flat module over a domain is preserved by base change to a domain. -/
theorem Module.finrank_baseChange_of_flat {R S M : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R M] : Module.finrank S (S ⊗[R] M) = Module.finrank R M := by
  rw [← (⊥ : Ideal S).finrank_fiber_eq_finrank, Ideal.finrank_fiber_eq_rankAtStalk,
    Module.rankAtStalk_baseChange, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]



/-- If a derivation `D` of a formally smooth `k`-algebra `A` satisfies `D f ≡ 1 mod f`, then the
hypersurface `A ⧸ (f)` is formally smooth over `k`: the conormal map `(f)/(f²) → B ⊗ Ω[A⁄k]` is
split by `b ⊗ ω ↦ b · D(ω) · f`. -/
theorem Algebra.FormallySmooth.quotient_span_singleton_of_derivation {k A : Type*} [CommRing k]
    [CommRing A] [Algebra k A] [FormallySmooth k A] {f : A} (D : Derivation k A A)
    (hD : D f - 1 ∈ Ideal.span {f}) : FormallySmooth k (A ⧸ Ideal.span {f}) := by
  set B := A ⧸ Ideal.span {f}
  set I := RingHom.ker (algebraMap A B)
  have hI : I = Ideal.span {f} := Ideal.mk_ker
  have hfI : f ∈ I := hI ▸ Ideal.mem_span_singleton_self f
  let g : B →ₗ[A] I.Cotangent :=
    (Ideal.span {f}).liftQ (LinearMap.toSpanSingleton A _ (I.toCotangent ⟨f, hfI⟩)) <| by
      rw [Ideal.span_le]
      rintro _ rfl
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul,
        Ideal.toCotangent_eq_zero, SetLike.mk_smul_mk]
      simpa [sq] using Ideal.pow_mem_pow hfI 2
  have hg1 : g 1 = I.toCotangent ⟨f, hfI⟩ :=
    (Submodule.liftQ_apply _ _ (1 : A)).trans (one_smul A _)
  refine (FormallySmooth.iff_split_injection Ideal.Quotient.mk_surjective).mpr
    ⟨g ∘ₗ (_root_.TensorProduct.rid A B).toLinearMap ∘ₗ D.liftKaehlerDifferential.lTensor B, ?_⟩
  ext x
  obtain ⟨⟨x, hx⟩, rfl⟩ := I.toCotangent_surjective x
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (hI ▸ hx)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hD
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe,
    id_eq]
  rw [kerCotangentToTensor_toCotangent, LinearMap.lTensor_tmul,
    Derivation.liftKaehlerDifferential_comp_D, _root_.TensorProduct.rid_tmul, map_smul, hg1,
    ← map_smul, Ideal.toCotangent_eq]
  refine Ideal.pow_right_mono hI.ge 2 ?_
  simp only [Submodule.coe_smul, smul_eq_mul]
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton', Derivation.leibniz, smul_eq_mul,
    smul_eq_mul]
  exact ⟨a * c + D a, by linear_combination a * f * hc⟩

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- If `f` lies outside `m²` at every maximal ideal `m` containing it, then some `k`-derivation
`D` of the smooth algebra `A` satisfies `D f ≡ 1 mod f`. -/
theorem Algebra.exists_derivation_sub_one_mem_span [FormallySmooth k A] {f : A}
    (hf : ∀ m : Ideal A, m.IsMaximal → f ∈ m → f ∉ m ^ 2) :
    ∃ D : Derivation k A A, D f - 1 ∈ Ideal.span {f} := by
  have hJ : Ideal.span {f} ⊔ Ideal.span (Set.range fun D : Derivation k A A ↦ D f) = ⊤ := by
    by_contra hJ
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
    have hfm : f ∈ m := hJm (Ideal.mem_sup_left (Ideal.mem_span_singleton_self f))
    obtain ⟨D, hD⟩ := exists_derivation_notMem_of_notMem_sq (k := k) m hfm (hf m hm hfm)
    exact hD (hJm (Ideal.mem_sup_right (Ideal.subset_span ⟨D, rfl⟩)))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top (x := (1 : A)))
  obtain ⟨D, rfl⟩ : ∃ D : Derivation k A A, D f = z := by
    clear hyz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨D₁, rfl⟩ := hx
      obtain ⟨D₂, rfl⟩ := hy
      exact ⟨D₁ + D₂, rfl⟩
    | smul a x _ hx =>
      obtain ⟨D, rfl⟩ := hx
      exact ⟨a • D, rfl⟩
  refine ⟨D, ?_⟩
  rw [← hyz, sub_add_cancel_right]
  exact neg_mem hy

/-- (D) A hypersurface section `A ⧸ (f)` of a smooth domain `A` of finite type over an
algebraically closed field, such that `f ∉ m²` at every maximal ideal `m` containing `f`, is
smooth, and its relative dimension is one less than that of `A` (when it is a domain).
Part of the Bertini argument, blueprint `lemma-curve-preserving-finite-cover--1`. -/
theorem Algebra.Smooth.quotient_span_singleton [IsDomain A] [Algebra.Smooth k A] {e : ℕ}
    (he : Module.rank A Ω[A⁄k] = e + 1) (f : A)
    (hf : ∀ m : Ideal A, m.IsMaximal → f ∈ m → f ∉ m ^ 2) :
    Algebra.Smooth k (A ⧸ Ideal.span {f}) ∧ (IsDomain (A ⧸ Ideal.span {f}) →
      Module.rank (A ⧸ Ideal.span {f}) Ω[(A ⧸ Ideal.span {f})⁄k] = e) := by
  set B := A ⧸ Ideal.span {f}
  obtain ⟨D, hD⟩ := exists_derivation_sub_one_mem_span (k := k) hf
  have hs : Function.Surjective (algebraMap A B) := Ideal.Quotient.mk_surjective
  have : FiniteType k B := FiniteType.of_surjective (IsScalarTower.toAlgHom k A B) hs
  have : FormallySmooth k B := FormallySmooth.quotient_span_singleton_of_derivation D hD
  refine ⟨⟨inferInstance, FinitePresentation.of_finiteType.mp inferInstance⟩, fun _ ↦ ?_⟩
  set x₀ : B ⊗[A] Ω[A⁄k] := 1 ⊗ₜ KaehlerDifferential.D k A f
  have hker : LinearMap.ker (mapBaseChange k A B) = Submodule.span B {x₀} := by
    refine le_antisymm (fun x hx ↦ ?_) ?_
    · obtain ⟨y, rfl⟩ : x ∈ LinearMap.range (kerCotangentToTensor k A B) := by
        rw [range_kerCotangentToTensor k A B hs]
        exact hx
      obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← algebraMap_smul B a,
        ← algebraMap_smul B f, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_singleton_self,
        zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₀)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        mapBaseChange_tmul, map_D, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.mk_singleton_self, map_zero, smul_zero]
  let ℓ : B ⊗[A] Ω[A⁄k] →ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
      D.liftKaehlerDifferential.baseChange B
  have hℓ : ℓ x₀ = 1 := by
    simp only [ℓ, x₀, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
      Derivation.liftKaehlerDifferential_comp_D, LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
    exact (Ideal.Quotient.eq.mpr hD).trans (map_one _)
  have hli : LinearIndependent B fun _ : Unit ↦ x₀ := by
    refine LinearIndependent.of_comp ℓ ?_
    rw [Function.comp_def, hℓ, linearIndependent_unique_iff]
    exact one_ne_zero
  have hrank := (mapBaseChange k A B).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.mpr (mapBaseChange_surjective k A B hs), rank_top, hker,
    ← Set.range_const (ι := Unit) (c := x₀), rank_span hli, Set.range_const, Cardinal.mk_singleton,
    ← Module.finrank_eq_rank (R := B) (M := B ⊗[A] Ω[A⁄k]), Module.finrank_baseChange_of_flat,
    Module.finrank_eq_rank, he] at hrank
  exact Cardinal.eq_of_add_eq_add_right hrank Cardinal.one_lt_aleph0


