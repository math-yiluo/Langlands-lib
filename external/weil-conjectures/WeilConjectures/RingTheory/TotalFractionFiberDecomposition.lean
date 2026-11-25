/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.TensorProduct.Pi

/-! # The total-fraction localization as a product of residue-field fibres
Source: Stacks Project, Algebra, Tag 02LX; Smoothing Ring Maps, proof of Tag 07F5.
-/

@[expose] public section

open scoped nonZeroDivisors TensorProduct
universe u v

/-- The localization of an algebra over a reduced Noetherian ring decomposes over its
minimal-prime residue fields, compatibly with the decomposition of the base ring.
Source: Stacks Project, Algebra, Lemma Tag 02LX; Smoothing Ring Maps, Lemma Tag 07F5,
third paragraph of its proof.
(blueprint: lem-weil-pbc-total-fraction-fiber-decomposition).

Proof: Apply reduced_noetherian_total_ring_fractions to enumerate the minimal primes.
Its unique maps to the prime localizations combine to a bijective R-algebra map from
Q to their product. The canonical maps from these localizations to their residue
fields are bijective, giving an R-algebra isomorphism Q with the product of residue
fields. Base change identifies the localization of A with Q tensor_R A. Tensor
symmetry, distribution over the finite product, and tensor symmetry on each factor
give the displayed target ring isomorphism. On a scalar q in Q these maps send
q tensor 1 to the family e(q)_i tensor 1, proving compatibility. No regularity or
Noetherianity of A is used. For the zero base ring the empty product is permitted. -/
theorem total_fraction_fiber_decomposition
    (R : Type u) (A : Type (max u v)) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsReduced R] :
    ∃ (n : ℕ) (q : Fin n ≃ {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R})
      (e : Localization R⁰ ≃+* ∀ i, (q i).val.asIdeal.ResidueField)
      (f : Localization (Algebra.algebraMapSubmonoid A R⁰) ≃+*
        ∀ i, (q i).val.asIdeal.Fiber A),
      ∀ r i, f (algebraMap (Localization R⁰)
          (Localization (Algebra.algebraMapSubmonoid A R⁰)) r) i =
        algebraMap ((q i).val.asIdeal.ResidueField) ((q i).val.asIdeal.Fiber A) (e r i) := by
  classical
  obtain ⟨n, q, _, _, hbij, _, hex, hpi⟩ :=
    reduced_noetherian_total_ring_fractions (R := R)
  choose φ hφ using fun i ↦ (hex i).exists
  let φA : Localization R⁰ →ₐ[R] ∀ i, Localization.AtPrime (q i).val.asIdeal :=
    { __ := RingHom.pi φ
      commutes' := fun r ↦ funext fun i ↦ DFunLike.congr_fun (hφ i) r }
  let e : Localization R⁰ ≃ₐ[R] ∀ i, (q i).val.asIdeal.ResidueField :=
    (AlgEquiv.ofBijective φA (hpi φ hφ)).trans
      (AlgEquiv.piCongrRight fun i ↦ AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom R (Localization.AtPrime (q i).val.asIdeal)
          (q i).val.asIdeal.ResidueField) (hbij i))
  let f : Localization (Algebra.algebraMapSubmonoid A R⁰) ≃+*
      ∀ i, (q i).val.asIdeal.Fiber A :=
    (Localization.tensorRightAlgEquiv R⁰ A).symm.toRingEquiv.trans
      ((Algebra.TensorProduct.comm R (Localization R⁰) A).toRingEquiv.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R] A) e).toRingEquiv.trans
          ((Algebra.TensorProduct.piRight R R A
            (fun i ↦ (q i).val.asIdeal.ResidueField)).toRingEquiv.trans
            (AlgEquiv.piCongrRight fun i ↦
              Algebra.TensorProduct.comm R A (q i).val.asIdeal.ResidueField).toRingEquiv)))
  refine ⟨n, q, e.toRingEquiv, f, ?_⟩
  intro r i
  simp [f, Algebra.TensorProduct.algebraMap_apply]
