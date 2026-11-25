/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# Flat localized kernel intersection

Source: Stacks Project, Tag 00SY, proof of (3) implies (2), flatness paragraph.
(blueprint: lem-weil-pbc-syntomic-local-kernel-intersection).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

/-- Flatness identifies the intersection of the localized presentation kernel with
base-prime multiples. Source: Stacks Project, Tag 00SY, proof of (3) implies (2),
flatness paragraph.
(blueprint: lem-weil-pbc-syntomic-local-kernel-intersection).

Proof: Put p = q ∩ R, Q = φ⁻¹(q), A = P_Q and B = S_q. The localized surjection
A → B has kernel IA, by exactness of localization and the quotient-localization
comparison. Give A and B their compatible R_p-algebra structures. The hypothesis
makes B flat over R_p. Apply the flat-kernel identity K ∩ mA = mK to the surjective
R_p-linear map A → B and m = pR_p. This identity follows by tensoring its short
exact sequence with R_p/m: flatness of B makes the kernel tensor injective.
The image of m in A is pA. The R_p-submodule mK is the underlying submodule of
the ideal product (pA)K, since K is an A-ideal. Thus IA ∩ pA = (pA)(IA).
No finite-generation or complete-intersection hypothesis is needed. -/
theorem syntomic_local_kernel_intersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat) :
    Ideal.map (algebraMap _
      (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) ⊓
      Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap φ.toRingHom)))
        (q.asIdeal.comap (algebraMap R S)) =
    Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap φ.toRingHom)))
        (q.asIdeal.comap (algebraMap R S)) *
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) := by
  let P := MvPolynomial (Fin n) R
  let p := q.asIdeal.comap (algebraMap R S)
  let Q := q.asIdeal.comap φ.toRingHom
  let Rp := Localization.AtPrime p
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime q.asIdeal
  have hpQ : p = Q.comap (algebraMap R P) := by
    ext r
    change (algebraMap R S) r ∈ q.asIdeal ↔
      φ (algebraMap R (MvPolynomial (Fin n) R) r) ∈ q.asIdeal
    rw [φ.commutes]
  let a : Rp →+* A := Localization.localRingHom p Q (algebraMap R P) hpQ
  let b : Rp →+* B :=
    Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  let l : A →+* B := Localization.localRingHom Q q.asIdeal φ.toRingHom rfl
  let : Algebra Rp A := a.toAlgebra
  let : Algebra Rp B := b.toAlgebra
  let : IsScalarTower R Rp A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    exact (Localization.localRingHom_to_map p Q (algebraMap R P) hpQ r).symm
  let : Module.Flat Rp B := hflat
  have hla : l.comp a = b := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    change l (a (algebraMap R Rp r)) = b (algebraMap R Rp r)
    rw [show a (algebraMap R Rp r) = algebraMap P A (algebraMap R P r) from
      Localization.localRingHom_to_map p Q (algebraMap R P) hpQ r]
    rw [show l (algebraMap P A (algebraMap R P r)) =
        algebraMap S B (φ (algebraMap R P r)) from
      Localization.localRingHom_to_map Q q.asIdeal φ.toRingHom rfl _]
    rw [φ.commutes]
    exact (Localization.localRingHom_to_map p q.asIdeal (algebraMap R S) rfl r).symm
  let g : A →ₐ[Rp] B :=
    { l with commutes' := fun r ↦ RingHom.congr_fun hla r }
  have hsurj : Function.Surjective g :=
    (RingHom.surjectiveOnStalks_of_surjective hφ).localRingHom_surjective
      Q q.asIdeal rfl
  have hk : RingHom.ker l = Ideal.map (algebraMap P A) (RingHom.ker φ.toRingHom) := by
    exact IsLocalization.ker_map B φ.toRingHom
      (Ideal.map_primeCompl_comap_of_surjective φ.toRingHom hφ q.asIdeal)
  let I : Ideal A := Ideal.map (algebraMap P A) (RingHom.ker φ.toRingHom)
  let m : Ideal Rp := IsLocalRing.maximalIdeal Rp
  have hm : m.map (algebraMap Rp A) = p.map (algebraMap R A) := by
    dsimp only [m]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, Ideal.map_map]
    rw [← IsScalarTower.algebraMap_eq]
  have hker : g.toLinearMap.ker = I.restrictScalars Rp := by
    ext x
    change l x = 0 ↔ x ∈ Ideal.map (algebraMap P A) (RingHom.ker φ.toRingHom)
    rw [← hk]
    rfl
  have h := LinearMap.ker_inf_smul_top_eq_smul_of_flat m g.toLinearMap hsurj
  rw [hker, Ideal.smul_top_eq_map, ← Ideal.smul_restrictScalars, hm] at h
  exact Submodule.restrictScalars_injective Rp A A h

end Algebra
