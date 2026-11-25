/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localization of N-1 and Japanese domains

Source: Stacks Project, Algebra, Lemma 10.161.3 (Tag 032G), using Lemma 10.36.11
(Tag 0307) (blueprint: lem-weil-pbc-localization-n2-domain).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

/-- The finite-generation step in Stacks Tags 032G and 0307
(blueprint: lem-weil-pbc-localization-n2-domain).
The inclusion of integral closures is obtained by extending the base ring. Since the
chosen denominators are units in `L`, `L` is its own localization. Integral closure
commutes with localization, and the images of a finite generating set still generate. -/
private theorem finite_integralClosure_localization
    (R : Type u) (Rf : Type w) (L : Type v)
    [CommRing R] [CommRing Rf] [Field L]
    [Algebra R Rf] [Algebra R L] [Algebra Rf L] [IsScalarTower R Rf L]
    (S : Submonoid R) [IsLocalization S Rf]
    (hunits : ∀ s : S, IsUnit (algebraMap R L s))
    [Module.Finite R (integralClosure R L)] :
    Module.Finite Rf (integralClosure Rf L) := by
  let f : integralClosure R L →ₐ[R] integralClosure Rf L :=
    (integralClosure R L).val.codRestrict
      ((integralClosure Rf L).restrictScalars R) fun x => x.property.tower_top
  let : Algebra (integralClosure R L) (integralClosure Rf L) := f.toAlgebra
  have : IsScalarTower R (integralClosure R L) (integralClosure Rf L) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower (integralClosure R L) (integralClosure Rf L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid L S) L :=
    IsLocalization.of_le_isUnit <| by
      rintro _ ⟨s, hs, rfl⟩
      exact hunits ⟨s, hs⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) S)
      (integralClosure Rf L) := IsLocalization.integralClosure S
  exact Module.Finite.of_isLocalization R (integralClosure R L) S

/-- Localizing a domain away from zero preserves its fraction field and the N-1 and N-2
conditions. Source: Stacks Project, Algebra, Tag 032G, using Tag 0307
(blueprint: lem-weil-pbc-localization-n2-domain).

Proof: Since `0 ∉ S`, the localization embeds in `K` by `r/s ↦ r/s`, so it is a domain.
Every nonzero `r/s` is invertible in `K`, and every fraction of elements of `R` is a
fraction of their images in the localization. Thus `K` is still the fraction field.
For any extension field `L/K`, elements of `S` are already units in `L`, so localizing
`L` at `S` leaves it unchanged. Tag 0307
(`lem-weil-pbc-integral-closure-commutes-localization`) therefore identifies the integral
closure of the localized ring in `L` with the localization of `integralClosure R L`.
If `c₁, …, cₙ` generate that closure over `R`, their images generate its localization:
`c/s = ∑ᵢ (rᵢ/s)(cᵢ/1)` whenever `c = ∑ᵢ rᵢ cᵢ`. This uses
`def-weil-finitely-generated-module` and `def-weil-pbc-module-localization`.
Apply this first with `L = K` for N-1, then with every finite extension `L/K` for N-2,
as in `def-weil-pbc-japanese-domain`. No Noetherian or separability assumption is needed.
The existential algebra structure is pinned down by the displayed fraction formula;
it supplies the canonical map rather than assuming the conclusions as instances. -/
theorem localization_isN1_isN2 (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Submonoid R) (hS : (0 : R) ∉ S) :
    ∃ (hD : IsDomain (Localization S)) (a : Algebra (Localization S) K),
      letI := hD
      letI := a
      ∃ (hF : IsFractionRing (Localization S) K),
        letI := hF
        IsScalarTower R (Localization S) K ∧
        Function.Injective (algebraMap (Localization S) K) ∧
        (∀ (r : R) (s : S),
          algebraMap (Localization S) K (IsLocalization.mk' (Localization S) r s) =
            algebraMap R K r / algebraMap R K (s : R)) ∧
        (IsN1 R K → IsN1 (Localization S) K) ∧
        (IsN2 R K → IsN2 (Localization S) K) := by
  have hS' : S ≤ nonZeroDivisors R := le_nonZeroDivisors_of_noZeroDivisors hS
  let hD : IsDomain (Localization S) := IsLocalization.isDomain_localization hS'
  let a : Algebra (Localization S) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization S) K S
      (nonZeroDivisors R) hS'
  have hT : IsScalarTower R (Localization S) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization S) K S (nonZeroDivisors R) hS'
  have hF : IsFractionRing (Localization S) K :=
    IsFractionRing.isFractionRing_of_isLocalization S (Localization S) K hS'
  refine ⟨hD, a, hF, hT, IsFractionRing.injective (Localization S) K, ?_, ?_, ?_⟩
  · intro r s
    apply (eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (K := K) (hS' s.property))).mpr
    simp only [IsScalarTower.algebraMap_apply R (Localization S) K]
    rw [← map_mul]
    rw [IsLocalization.mk'_spec]
  · intro hN1
    have : Module.Finite R (integralClosure R K) := hN1
    exact finite_integralClosure_localization R (Localization S) K S fun s =>
      IsLocalization.map_units K (⟨s.1, hS' s.property⟩ : nonZeroDivisors R)
  · intro hN2 L _ _ _ _ _
    let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower R (Localization S) L :=
      IsScalarTower.of_algebraMap_eq' <| by
        ext r
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        rw [IsScalarTower.algebraMap_apply R (Localization S) K]
        rw [IsScalarTower.algebraMap_apply (Localization S) K L]
    have : Module.Finite R (integralClosure R L) := hN2 L
    exact finite_integralClosure_localization R (Localization S) L S fun s =>
      (IsLocalization.map_units K (⟨s.1, hS' s.property⟩ : nonZeroDivisors R)).map (algebraMap K L)
