/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Refining weakly étale algebras over a w-strictly local cover

This file generalises the construction of `Algebra.WeaklyEtale.refinement` (Stacks 097Z):
instead of the w-strict localization `WStrictLocalization R` of `R`, we allow any flat
`R`-algebra `C` which is w-strictly local and such that every prime of `R` is the image of a
closed point of `Spec C`.

Let `S` be a weakly étale `R`-algebra and let `J ⊆ C` be the ideal cutting out the closed
points of `Spec C`. The w-localization `D` of `C ⊗[R] S` along `J · (C ⊗[R] S)` is w-local,
the map `C → D` is w-local and bijective on stalks (by Olivier's theorem), and `S → D` is
faithfully flat.

## Main results

- `Algebra.WeaklyEtale.exists_bijectiveOnStalks_of_isWStrictlyLocalRing`
-/

@[expose] public section

universe u

open PrimeSpectrum TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Let `C` be a flat, w-strictly local `R`-algebra such that every prime of `R` is the image of
a closed point of `Spec C`, and let `S` be a weakly étale `R`-algebra. Then there exist a w-local
`C`-algebra `D` such that `C → D` is w-local and bijective on stalks, and a faithfully flat ring
map `f : S → D` compatible with the maps from `R`. This is the main step of the proof of
Stacks 097Z (`Algebra.WeaklyEtale.indEtale_faithfullyFlat_refinement`), with
`WStrictLocalization R` replaced by `C`. -/
theorem Algebra.WeaklyEtale.exists_bijectiveOnStalks_of_isWStrictlyLocalRing
    (R C S : Type u) [CommRing R] [CommRing C] [CommRing S] [Algebra R C] [Algebra R S]
    [Module.Flat R C] [IsWStrictlyLocalRing C] [Algebra.WeaklyEtale R S]
    (hC : ∀ p : PrimeSpectrum R, ∃ x ∈ closedPoints (PrimeSpectrum C),
      PrimeSpectrum.comap (algebraMap R C) x = p) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D) (f : S →+* D),
      IsWLocalRing D ∧ Algebra.BijectiveOnStalks C D ∧ (algebraMap C D).IsWLocal ∧
        f.FaithfullyFlat ∧ f.comp (algebraMap R S) = (algebraMap C D).comp (algebraMap R C) := by
  classical
  -- The ideal `J` of closed points of `Spec C`.
  set J : Ideal C := vanishingIdeal (closedPoints (PrimeSpectrum C)) with hJdef
  have hJ : zeroLocus (J : Set C) = closedPoints (PrimeSpectrum C) := by
    rw [hJdef, zeroLocus_vanishingIdeal_eq_closure,
      IsClosed.closure_eq IsWLocalRing.wLocalSpace_primeSepectrum.isClosed_closedPoints]
  -- The base change `D' = C ⊗[R] S` and its w-localization `D` along `J`.
  set D' := C ⊗[R] S with hD'
  set K : Ideal D' := J.map (algebraMap C D') with hKdef
  set D := K.WLocalization with hDdef
  have : Algebra.WeaklyEtale C D' := inferInstance
  have hres : ∀ (m : Ideal C) (q' : Ideal D') [q'.LiesOver m] [m.IsMaximal] [q'.IsPrime]
      [Algebra (Localization.AtPrime m) (Localization.AtPrime q')]
      [IsScalarTower C (Localization.AtPrime m) (Localization.AtPrime q')],
      Algebra.IsAlgebraic m.ResidueField q'.ResidueField := by
    intro m q' _ hm _ _ _
    have : m.IsPrime := hm.isPrime
    exact Algebra.WeaklyEtale.isAlgebraic_residueField_of_liesOver m q'
  -- Stacks 097A: closed points of `Spec D` are the preimage of those of `Spec C`.
  have hDclosed : zeroLocus ((J.map (algebraMap C D) : Ideal D) : Set D) =
      closedPoints (PrimeSpectrum D) :=
    Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq hJ hres
  have : Algebra.WeaklyEtale D' D := inferInstance
  have : Algebra.WeaklyEtale C D := Algebra.WeaklyEtale.trans C D' D
  -- Every maximal ideal of `D` lies over a maximal ideal of `C`.
  have hmaxC (n : Ideal D) [n.IsMaximal] : (n.comap (algebraMap C D)).IsMaximal := by
    have hn_mem : (⟨n, inferInstance⟩ : PrimeSpectrum D) ∈ closedPoints (PrimeSpectrum D) :=
      mem_closedPoints_iff.mpr ((isClosed_singleton_iff_isMaximal _).mpr inferInstance)
    rw [← hDclosed] at hn_mem
    have hJle : J ≤ n.comap (algebraMap C D) := by
      rw [← Ideal.map_le_iff_le_comap]
      exact (mem_zeroLocus _ _).mp hn_mem
    have : (n.comap (algebraMap C D)).IsPrime := Ideal.IsPrime.comap _
    have hmem : (⟨n.comap (algebraMap C D), inferInstance⟩ : PrimeSpectrum C) ∈
        closedPoints (PrimeSpectrum C) := by
      rw [← hJ]
      exact (mem_zeroLocus _ _).mpr hJle
    exact (isClosed_singleton_iff_isMaximal _).mp (mem_closedPoints_iff.mp hmem)
  -- `C → D` is bijective on stalks, by Olivier's theorem.
  have hbos : Algebra.BijectiveOnStalks C D := by
    apply Algebra.WeaklyEtale.bijectiveOnStalks
    intro q hq
    obtain ⟨n, hn_max, hqn⟩ := q.exists_le_maximal hq.ne_top
    refine ⟨n, hn_max.isPrime, hqn, ?_⟩
    have : (n.comap (algebraMap C D)).IsMaximal := hmaxC n
    exact IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization _
  -- `Spec D → Spec C` is w-local.
  have hwloc : (algebraMap C D).IsWLocal := by
    rw [RingHom.isWLocal_iff_isMaximal_of_isMaximal]
    intro n hn
    exact hmaxC n
  -- The `S`-algebra structure on `D`.
  let : Algebra S D := ((algebraMap D' D).comp (algebraMap S D')).toAlgebra
  have : IsScalarTower S D' D := .of_algebraMap_eq' rfl
  have hSD'_flat : (algebraMap S D').Flat :=
    RingHom.Flat.isStableUnderBaseChange R C S D'
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Module.Flat S D' := RingHom.flat_algebraMap_iff.mp hSD'_flat
  have : Module.Flat S D := Module.Flat.trans S D' D
  -- `S → D` is surjective on spectra.
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap S D)) := by
    -- `Spec (C ⧸ J) → Spec R` is surjective.
    have hC₀ : Function.Surjective (PrimeSpectrum.comap (algebraMap R (C ⧸ J))) := by
      intro p
      obtain ⟨x, hx_mem, hx⟩ := hC p
      rw [← hJ] at hx_mem
      have hker : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
        exact hx_mem
      obtain ⟨x', hx'⟩ := hker
      refine ⟨x', ?_⟩
      rw [IsScalarTower.algebraMap_eq R C (C ⧸ J), PrimeSpectrum.comap_comp_apply]
      rw [Ideal.Quotient.algebraMap_eq, hx']
      exact hx
    -- base change: `Spec (S ⊗[R] (C ⧸ J)) → Spec S` is surjective.
    have hSC₀ := PrimeSpectrum.comap_surjective_tensorProduct_left S hC₀
    intro q
    obtain ⟨Q₀, hQ₀⟩ := hSC₀ q
    -- transport `Q₀` to a prime of `D'` containing `K` and lying over `q`.
    let π : D' →ₐ[R] (S ⊗[R] (C ⧸ J)) :=
      (Algebra.TensorProduct.comm R (C ⧸ J) S).toAlgHom.comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R S))
    set Q : PrimeSpectrum D' := PrimeSpectrum.comap π.toRingHom Q₀ with hQdef
    have hQK : Q ∈ zeroLocus (K : Set D') := by
      rw [mem_zeroLocus, hKdef, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
      intro j hj
      have hπj : π (algebraMap C D' j) = 0 := by
        change (Algebra.TensorProduct.comm R (C ⧸ J) S)
            ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R S))
              ((j : C) ⊗ₜ[R] (1 : S))) = 0
        rw [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.mpr hj, TensorProduct.zero_tmul, map_zero]
      change π (algebraMap C D' j) ∈ Q₀.asIdeal
      rw [hπj]
      exact zero_mem _
    have hQq : PrimeSpectrum.comap (algebraMap S D') Q = q := by
      have hcomp : π.toRingHom.comp (algebraMap S D') = algebraMap S (S ⊗[R] (C ⧸ J)) := by
        refine RingHom.ext fun s ↦ ?_
        change (Algebra.TensorProduct.comm R (C ⧸ J) S)
            ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R S))
              ((1 : C) ⊗ₜ[R] s)) = s ⊗ₜ[R] (1 : C ⧸ J)
        rw [Algebra.TensorProduct.map_tmul, map_one]
        simp [Algebra.TensorProduct.comm_tmul]
      rw [hQdef, ← PrimeSpectrum.comap_comp_apply, hcomp, hQ₀]
    -- pull `Q` back along the w-localization `D' → D`.
    have hK_sub : zeroLocus (K : Set D') ⊆ closedPoints (PrimeSpectrum D') := by
      rw [hKdef]
      exact zeroLocus_map_algebraMap_subset_closedPoints hres hJ.le
    obtain ⟨P, -, hP⟩ := (Ideal.WLocalization.bijOn_zeroLocus_map K hK_sub).surjOn hQK
    refine ⟨P, ?_⟩
    have hP' : PrimeSpectrum.comap (algebraMap D' D) P = Q := hP
    rw [IsScalarTower.algebraMap_eq S D' D, PrimeSpectrum.comap_comp_apply, hP', hQq]
  have : Module.FaithfullyFlat S D := Module.FaithfullyFlat.of_comap_surjective hsurj
  refine ⟨D, inferInstance, inferInstance, algebraMap S D, inferInstance, hbos, hwloc,
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance, ?_⟩
  refine RingHom.ext fun r ↦ ?_
  change algebraMap D' D (1 ⊗ₜ[R] algebraMap R S r) =
    algebraMap C D (algebraMap R C r)
  rw [IsScalarTower.algebraMap_apply C D' D, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rfl
