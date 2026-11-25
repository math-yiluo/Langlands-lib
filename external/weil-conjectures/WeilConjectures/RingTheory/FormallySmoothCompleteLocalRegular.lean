/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.FormallySmoothAdicClosedFiber
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalGenericFiber
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Regularity of formally smooth maps of complete local rings

Source: Stacks Project, More on Algebra, Proposition 07PM, implication (4) to (1)
(blueprint: lem-weil-pbc-formally-smooth-complete-local-regular).
-/

@[expose] public section

universe u v

namespace RingHom

private theorem geometricallyRegular_of_algEquiv
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S)
    (h : Algebra.IsGeometricallyRegular k R) : Algebra.IsGeometricallyRegular k S := by
  have := h.1
  refine ⟨isNoetherianRing_of_ringEquiv R e.toRingEquiv, ?_⟩
  intro k' _ _ _ _
  have := h.2 k'
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k' ≃ₐ[k'] k') e).toRingEquiv

private theorem formallySmoothAdic_quotient
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (n : Ideal B) (hfs : Algebra.FormallySmoothAdic A B n) :
    letI : Algebra (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Algebra.FormallySmoothAdic (A ⧸ p) (B ⧸ p.map (algebraMap A B))
      (n.map (Ideal.Quotient.mk (p.map (algebraMap A B)))) := by
  let I := p.map (algebraMap A B)
  let : Algebra (A ⧸ p) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  intro D _ _ J hJ g hg
  let : Algebra A D := ((algebraMap (A ⧸ p) D).comp (Ideal.Quotient.mk p)).toAlgebra
  have : IsScalarTower A (A ⧸ p) D := IsScalarTower.of_algebraMap_eq' rfl
  let g₀ : B →ₐ[A] D ⧸ J :=
    (g.restrictScalars A).comp (Ideal.Quotient.mkₐ A I)
  obtain ⟨k, hk, hgk⟩ := hg
  have hg₀ : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g₀ x = 0 := by
    refine ⟨k, hk, ?_⟩
    intro x hx
    apply hgk
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨f, hf⟩ := hfs J hJ g₀ hg₀
  have hkill : I ≤ RingHom.ker f.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f (algebraMap A B a) = 0
    rw [f.commutes]
    change algebraMap (A ⧸ p) D (Ideal.Quotient.mk p a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let f₀ : B ⧸ I →ₐ[A] D := Ideal.Quotient.liftₐ I f (fun x hx ↦ hkill hx)
  let f' : B ⧸ I →ₐ[A ⧸ p] D :=
    f₀.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  refine ⟨f', ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun hf b

/-- A local map between complete Noetherian local rings, formally smooth for the maximal-ideal
adic topology of the target, is regular. Source: Stacks Project, More on Algebra,
Proposition 07PM, implication (4) to (1).
(blueprint: lem-weil-pbc-formally-smooth-complete-local-regular)

Proof plan:
1. By fs-adic-flat-geometrically-regular-closed-fibre, the map is flat and its closed fibre
   is geometrically regular. Fix a prime p of A; we must establish geometric regularity
   and Noetherianity of its fibre, as in theorem-finite-etale-covers-proper-henselian--2.
2. Replace A and B by A/p and B/pB using complete-local-quotient and fs-adic-base-change.
   The new base is a complete local domain with fraction field kappa(p). By tensor
   associativity, it suffices to show regularity after each finite purely inseparable
   extension of this fraction field.
3. By complete-local-domain-finite-over-regular, choose a complete regular coefficient
   subring A0, finite in A and with the same residue field. Base change makes the closed
   fibre formally smooth. By fs-adic-lift-over-finite-coefficient-map, lift it to a
   complete Noetherian local A0-algebra C with B isomorphic to C tensor over A0 with A.
4. Localizing A at the nonzero elements of A0 gives its fraction field, finite over the
   fraction field K0 of A0 (localization-base-change). Tensor associativity reduces the
   task to geometric regularity of C tensor over A0 with K0, using
   geometrically-regular-finitely-generated-extensions.
5. By fs-adic-flat-geometrically-regular-closed-fibre and
   flat-over-regular-with-regular-fibre, C is regular. Its localization at K0 is regular
   and Noetherian by localization-of-regular-ring.
6. In characteristic zero there are no nontrivial finite purely inseparable extensions;
   this includes the Cohen-ring coefficient case. Step 5 therefore suffices there.
7. In characteristic p, induct on the degree of a finite purely inseparable extension.
   By purely-inseparable-pth-root-tower the last step adjoins a pth root of f. Clear
   denominators to obtain a finite A0-subalgebra A' of the intermediate field, with that
   field as fraction field, and f in A'.
8. By derivation-nonzero-on-non-pth-power choose a derivation D of A' nonzero on f.
   Base change preserves formal smoothness; finite-module-complete-over-complete-noetherian
   gives completeness of C tensor A'. By fs-adic-lift-derivation extend D to this ring,
   then use derivation-extends to localize. Its value on f is now a unit.
9. By degree-p-extension-regular the pth-root extension of the inductively regular ring
   is regular. Tensor associativity identifies it with the required base change. This
   proves geometric regularity and Noetherianity at every prime; with step 1 the map
   is regular. -/
theorem isRegular_of_formallySmoothAdic
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (φ : A →+* B) [IsLocalHom φ]
    (hfs : letI : Algebra A B := φ.toAlgebra
      Algebra.FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) :
    φ.IsRegular := by
  let : Algebra A B := φ.toAlgebra
  change φ.Flat ∧ ∀ (p : Ideal A) [p.IsPrime],
    Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber B)
  refine ⟨(flat_and_isGeometricallyRegular_closedFiber_of_formallySmoothAdic φ hfs).1, ?_⟩
  intro p hp
  let I := p.map φ
  have hI : I ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    exact (Ideal.map_mono (IsLocalRing.le_maximalIdeal hp.ne_top)).trans
      (IsLocalRing.map_maximalIdeal_le φ)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalRing (A ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : Algebra (A ⧸ p) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hA := quotient_complete_local A p hp.ne_top
  have hB := quotient_complete_local B I hI
  have := hA.2.2.2
  have := hB.2.2.2
  have hqfs : Algebra.FormallySmoothAdic (A ⧸ p) (B ⧸ I)
      (IsLocalRing.maximalIdeal (B ⧸ I)) := by
    rw [hB.2.2.1]
    exact formallySmoothAdic_quotient p (IsLocalRing.maximalIdeal B) hfs
  have hlocal : IsLocalHom (algebraMap (A ⧸ p) (B ⧸ I)) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 4 1).mp
    rw [hA.2.2.1, Ideal.map_le_iff_le_comap]
    intro a ha
    change Ideal.Quotient.mk I (φ a) ∈ IsLocalRing.maximalIdeal (B ⧸ I)
    rw [hB.2.2.1]
    exact Ideal.mem_map_of_mem _ (map_nonunit φ a ha)
  have := hlocal
  have hgeneric := Algebra.isGeometricallyRegular_genericFiber_of_formallySmoothAdic
    (A := A ⧸ p) (B := B ⧸ I) (K := p.ResidueField) hqfs
  let e := (Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField]
      p.ResidueField) (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p)).trans
    (Algebra.TensorProduct.cancelBaseChange A (A ⧸ p) p.ResidueField p.ResidueField B)
  exact geometricallyRegular_of_algEquiv e hgeneric

end RingHom
