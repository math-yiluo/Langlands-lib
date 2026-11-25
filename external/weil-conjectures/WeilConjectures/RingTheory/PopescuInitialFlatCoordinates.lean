/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.GeometricallyRegularOverFieldFlat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.CharP.Defs

/-!
# Initial flat differential coordinates at a prime

Source: Stacks Project, More on Algebra, Tag 07E6, lemma-geometrically-regular-over-field;
Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo, differential-coordinate construction.
-/

@[expose] public section

set_option autoImplicit false
universe u v w
namespace Algebra

private theorem geometricallyRegular_atPrime
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    (q : Ideal Λ) [q.IsPrime] (hreg : IsGeometricallyRegular k Λ) :
    IsGeometricallyRegular k (Localization.AtPrime q) := by
  let : IsNoetherianRing Λ := hreg.1
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  let L := Localization.AtPrime q
  let R := TensorProduct k k' Λ
  let T := TensorProduct k k' L
  let f : R →ₐ[k'] T := Algebra.TensorProduct.map
    (AlgHom.id k' k') (IsScalarTower.toAlgHom k Λ L)
  let : Algebra R T := f.toRingHom.toAlgebra
  let : IsScalarTower k' R T := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  have H : (algebraMap R T).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap Λ L) := by
    ext x
    change f (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] algebraMap Λ L x
    exact Algebra.TensorProduct.map_tmul (AlgHom.id k' k')
      (IsScalarTower.toAlgHom k Λ L) 1 x
  let M := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := k) (A := k'))
  have : IsLocalization M T :=
    IsLocalization.tensorProduct_tensorProduct_right k k' q.primeCompl L H
  let : IsRegularRing R := hreg.2 k'
  have : IsRegularRing (Localization M) := by
    apply isRegularRing_iff.mpr
    intro p hp
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv M (Localization M) T).toRingEquiv

private theorem differential_map_bijective
    (k : Type u) (F : Type v) (E : Type w)
    [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    (e : F ≃ₐ[k] E) :
    let := e.toAlgHom.toAlgebra
    let : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
    Function.Bijective (KaehlerDifferential.map k k F E) := by
  let := e.toAlgHom.toAlgebra
  let : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  have hinj : Function.Injective (algebraMap F E) := e.injective
  have hsurj : Function.Surjective (algebraMap F E) := e.surjective
  refine ⟨?_, KaehlerDifferential.map_surjective_of_surjective k k F E hsurj⟩
  apply LinearMap.ker_eq_bot.mp
  rw [KaehlerDifferential.ker_map_of_surjective k F E hsurj]
  have h : Function.Injective
      ((Finsupp.mapRange.linearMap (Algebra.linearMap F E)).comp
        (Finsupp.lmapDomain F F (algebraMap F E))) :=
    (Finsupp.mapRange_injective _ (map_zero (algebraMap F E)) hinj).comp
      (Finsupp.mapDomain_injective hinj)
  simp only [LinearMap.ker_eq_bot.mpr h, Submodule.map_bot]

/-- The first differential coordinates give a flat local map with regular closed fibre.
Source: Stacks Project, More on Algebra, Tag 07E6, lemma-geometrically-regular-over-field;
Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo, before appending parameters.
(blueprint: lem-weil-pbc-popescu-initial-flat-coordinates).

Proof: Put L = Λ_q. For every finite purely inseparable extension k'/k, the ring
k' ⊗ L is the localization of k' ⊗ Λ at the image of q's complement, by localization
base change. The latter ring is regular by hreg, so its localization is regular.
Thus L is geometrically regular and Noetherian. Positive characteristic of a field
is prime, supplying the prime-characteristic instance required by 07E6.

Let E be the image intermediate field of ι. The injective field map ι identifies F
with E. Essential finite type says that F/k is finitely generated as a field;
transport this through F ≃ₐ[k] E. Functoriality of Kähler differentials under this
isomorphism transports b to an E-basis consisting of the differentials of the
images of a. The residue equations ha give the equations in 07E6 for the map
k[X_j] → L, X_j ↦ xs j/1. Apply
exists_flat_polynomialLocalization_of_isGeometricallyRegular to obtain flatness
and the regular local closed fibre. The maximal ideal of L contracts to q, so
the polynomial prime is exactly q.comap (aeval xs). Uniqueness of a localization
map identifies the map supplied by 07E6 with Localization.localRingHom.
The equality of the extended polynomial ideals then identifies the quotient
in its conclusion with the quotient displayed here. This argument includes
an empty differential basis and an arbitrary, possibly infinite, residue field. -/
theorem popescu_initial_flat_coordinates
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (F : Type w) [Field F] [Algebra k F] [EssFiniteType k F]
    (ι : F →ₐ[k] q.ResidueField)
    (t : ℕ) (xs : Fin t → Λ) (a : Fin t → F)
    (ha : ∀ j, ι (a j) = IsLocalRing.residue (Localization.AtPrime q)
      (algebraMap Λ (Localization.AtPrime q) (xs j)))
    (b : Module.Basis (Fin t) F (KaehlerDifferential k F))
    (hb : ∀ j, b j = KaehlerDifferential.D k F (a j)) :
    let φ₀ : MvPolynomial (Fin t) k →ₐ[k] Λ := MvPolynomial.aeval xs
    (Localization.localRingHom (q.comap φ₀.toRingHom) q φ₀.toRingHom rfl).Flat ∧
      IsRegularLocalRing (Localization.AtPrime q ⧸
        (q.comap φ₀.toRingHom).map
          ((algebraMap Λ (Localization.AtPrime q)).comp φ₀.toRingHom)) := by
  let L := Localization.AtPrime q
  let E := ι.fieldRange
  let e : F ≃ₐ[k] E := ι.equivFieldRange
  let : Algebra F E := e.toAlgHom.toAlgebra
  let : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  have hbij : Function.Bijective (KaehlerDifferential.map k k F E) :=
    differential_map_bijective k F E e
  let b₀ := b.map (LinearEquiv.ofBijective (KaehlerDifferential.map k k F E) hbij)
  let bE : Module.Basis (Fin t) E (KaehlerDifferential k E) :=
    b₀.mapCoeffs e.toRingEquiv (fun c x ↦ IsScalarTower.algebraMap_smul E c x)
  have hbE : ∀ j, bE j = KaehlerDifferential.D k E (e (a j)) := by
    intro j
    simp only [bE, Module.Basis.mapCoeffs_apply, b₀, Module.Basis.map_apply,
      LinearEquiv.ofBijective_apply, hb, KaehlerDifferential.map_D]
    rfl
  let : EssFiniteType k E := EssFiniteType.of_surjective e.toAlgHom e.surjective
  have hE : E.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  let φ₀ : MvPolynomial (Fin t) k →ₐ[k] Λ := MvPolynomial.aeval xs
  let φL : MvPolynomial (Fin t) k →ₐ[k] L :=
    (IsScalarTower.toAlgHom k Λ L).comp φ₀
  have haE : ∀ j, (e (a j) : q.ResidueField) =
      IsLocalRing.residue L (φL (MvPolynomial.X j)) := by
    intro j
    calc
      (e (a j) : q.ResidueField) = ι (a j) :=
        AlgHom.equivFieldRange_apply_coe ι (a j)
      _ = IsLocalRing.residue L (φL (MvPolynomial.X j)) := by
        simpa [φL, φ₀] using ha j
  have hpprime : p.Prime := CharP.char_prime_of_ne_zero k (Nat.ne_of_gt hp)
  let : Fact p.Prime := ⟨hpprime⟩
  have hinitial := exists_flat_polynomialLocalization_of_isGeometricallyRegular
    k L p (geometricallyRegular_atPrime k Λ q hreg) E hE t φL (fun j ↦ e (a j)) haE bE hbE
  have hprime : (IsLocalRing.maximalIdeal L).comap φL.toRingHom =
      q.comap φ₀.toRingHom := by
    change ((IsLocalRing.maximalIdeal L).comap
      ((algebraMap Λ L).comp φ₀.toRingHom)) = _
    have hq : (IsLocalRing.maximalIdeal L).comap (algebraMap Λ L) = q :=
      Localization.AtPrime.under_maximalIdeal
    rw [← Ideal.comap_comap, hq]
  have hinitial' : ∃ hP : (q.comap φ₀.toRingHom).IsPrime,
      letI := hP
      ∃ ψ : Localization.AtPrime (q.comap φ₀.toRingHom) →+* L,
        ψ.comp (algebraMap (MvPolynomial (Fin t) k)
          (Localization.AtPrime (q.comap φ₀.toRingHom))) = φL.toRingHom ∧
        ψ.Flat ∧ IsRegularLocalRing (L ⧸ (q.comap φ₀.toRingHom).map φL.toRingHom) := by
    rw [← hprime]
    exact ⟨inferInstance, hinitial⟩
  obtain ⟨hP, ψ, hψ, hflat, hregular⟩ := hinitial'
  have hcanonical : Localization.localRingHom (q.comap φ₀.toRingHom) q φ₀.toRingHom rfl =
      ψ := by
    apply Localization.localRingHom_unique
    intro f
    exact DFunLike.congr_fun hψ f
  exact ⟨hcanonical.symm ▸ hflat, hregular⟩

end Algebra
