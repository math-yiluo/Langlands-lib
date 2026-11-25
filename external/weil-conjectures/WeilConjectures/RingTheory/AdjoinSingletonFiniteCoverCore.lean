/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdjoinSingletonSplittingCover

/-! # Structural finite cover for a fractional monogenic algebra
Source: Stacks Project, Algebra, Tag 0334, Step 5. -/

@[expose] public section

universe u v

/-- Clearing one denominator identifies a principal open of `R[x]` with one of `R`. -/
private theorem adjoin_singleton_integrallyClosed_away (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) :
    ∃ f : Algebra.adjoin R ({x} : Set K), f ≠ 0 ∧
      IsIntegrallyClosed (Localization.Away f) := by
  classical
  obtain ⟨b, a, hx⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have ha : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.property
  let S := Algebra.adjoin R ({x} : Set K)
  let M := Submonoid.powers (a : R)
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  let T := Localization.subalgebra K M hM
  have hxT : x ∈ T := by
    refine ⟨b, a, Submonoid.mem_powers _, ?_⟩
    exact hx.symm
  have hST : S ≤ T := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxT)
  let : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let f : S := algebraMap R S a
  have hf : f ≠ 0 := by
    intro h
    apply ha
    apply IsFractionRing.injective R K
    have := congrArg (fun z : S ↦ (z : K)) h
    simpa only [f, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero, map_zero] using this
  let : IsLocalization.Away f T := by
    refine IsLocalization.Away.mk f ?_ ?_ ?_
    · change IsUnit (algebraMap R T a)
      exact IsLocalization.Away.algebraMap_isUnit (a : R)
    · intro t
      obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (a : R) t
      exact ⟨n, algebraMap R S r, hr⟩
    · intro c d h
      have hcd : c = d := Subtype.ext (congrArg (fun z : T ↦ (z : K)) h)
      exact ⟨0, by simp [hcd]⟩
  let : IsIntegrallyClosed T := isIntegrallyClosed_of_isLocalization T M hM
  let e : T ≃ₐ[S] Localization.Away f :=
    IsLocalization.algEquiv (Submonoid.powers f) T (Localization.Away f)
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let : IsIntegrallyClosed (Localization.Away f) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  exact ⟨f, hf, inferInstance⟩

/-- A normal principal open stays normal at primes after any domain localization. -/
private theorem integrallyClosed_atPrime_of_normal_away
    (S : Type*) [CommRing S] [IsDomain S] (f : S) (hf0 : f ≠ 0)
    [IsIntegrallyClosed (Localization.Away f)] (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q) (C : Type*) [CommRing C] [IsDomain C] [Algebra S C]
    [IsLocalization.AtPrime C q] : IsIntegrallyClosed C := by
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf0
  have hle : Submonoid.powers f ≤ q.primeCompl := by
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact q.primeCompl.pow_mem hf n
  let : Algebra (Localization.Away f) C :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  let : IsScalarTower S (Localization.Away f) C :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  let : IsLocalization (q.primeCompl.map (algebraMap S (Localization.Away f))) C :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  apply isIntegrallyClosed_of_isLocalization C
    (q.primeCompl.map (algebraMap S (Localization.Away f)))
  rintro a ⟨b, hb, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have hu := IsLocalization.map_units C (⟨b, hb⟩ : q.primeCompl)
  have hz : algebraMap S C b = 0 := by
    rw [IsScalarTower.algebraMap_apply S (Localization.Away f) C, h, map_zero]
  exact hu.ne_zero hz

/-- Every domain localization of a fractional monogenic algebra has a normal principal open. -/
private theorem adjoin_singleton_localization_normal_away
    (R : Type*) (K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (M : Submonoid (Algebra.adjoin R ({x} : Set K)))
    (hM : M ≤ nonZeroDivisors (Algebra.adjoin R ({x} : Set K))) :
    ∃ f : Localization M, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let S := Algebra.adjoin R ({x} : Set K)
  let B := Localization M
  let : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  obtain ⟨a, ha, hnormal⟩ := adjoin_singleton_integrallyClosed_away R K x
  let : IsIntegrallyClosed (Localization.Away a) := hnormal
  let f : B := algebraMap S B a
  have hf : f ≠ 0 := by
    intro h
    apply ha
    apply IsLocalization.injective B hM
    exact h.trans (map_zero (algebraMap S B)).symm
  refine ⟨f, hf, ?_⟩
  intro p hp
  let C := Localization.AtPrime p
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let : IsDomain C := inferInstance
  let qB : Ideal B := p.comap (algebraMap B (Localization.Away f))
  let qS : Ideal S := qB.comap (algebraMap S B)
  let : qB.IsPrime := inferInstance
  let : qS.IsPrime := inferInstance
  let : IsLocalization.AtPrime C qB := inferInstance
  let : IsLocalization.AtPrime C qS :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M C qB
  have hnot : a ∉ qS := by
    intro h
    have hu : IsUnit (algebraMap B (Localization.Away f) f) :=
      IsLocalization.Away.algebraMap_isUnit f
    exact hp.ne_top (p.eq_top_of_isUnit_mem h hu)
  exact ⟨inferInstance, integrallyClosed_atPrime_of_normal_away S a ha qS hnot C⟩

/-- Subtracting a coefficient does not change the monogenic algebra or its local rings. -/
private theorem adjoin_singleton_shift_local_presentation
    (R : Type*) (K : Type*) [CommRing R] [Field K] [Algebra R K]
    (z : K) (n0 : Ideal (Algebra.adjoin R ({z} : Set K))) [n0.IsMaximal]
    (r : R) (hr : (⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ :
      Algebra.adjoin R ({z} : Set K)) - algebraMap R _ r ∈ n0) :
    ∃ (y : K) (n : Ideal (Algebra.adjoin R ({y} : Set K))) (_ : n.IsMaximal),
      (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
        Algebra.adjoin R ({y} : Set K)) ∈ n ∧
      Nonempty (Localization.AtPrime n0 ≃+* Localization.AtPrime n) := by
  let y := z - algebraMap R K r
  have heq : Algebra.adjoin R ({z} : Set K) = Algebra.adjoin R ({y} : Set K) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      change z ∈ Algebra.adjoin R ({y} : Set K)
      have h := (Algebra.adjoin R ({y} : Set K)).add_mem
        (Algebra.subset_adjoin (Set.mem_singleton y))
        (Subalgebra.algebraMap_mem _ r)
      simpa only [y, sub_add_cancel] using h
    · apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      exact (Algebra.adjoin R ({z} : Set K)).sub_mem
        (Algebra.subset_adjoin (Set.mem_singleton z)) (Subalgebra.algebraMap_mem _ r)
  let e := (Subalgebra.equivOfEq _ _ heq).toRingEquiv
  let n := n0.comap e.symm.toRingHom
  let : n.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hn : n0 = n.comap e.toRingHom := by
    ext a
    change a ∈ n0 ↔ e.symm (e a) ∈ n0
    rw [e.symm_apply_apply]
  refine ⟨y, n, inferInstance, ?_, ⟨Localization.localRingEquiv n0 n e hn⟩⟩
  change e.symm ⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ ∈ n0
  convert hr using 1
  apply Subtype.ext
  rfl

/-- The splitting-field construction gives a finite cover and monogenic local presentations.
Source: Stacks Project, Algebra, Tag 0334, Step 5, lines 46137--46173.
(blueprint: lem-weil-pbc-monogenic-maximal-finite-cover-core).

Proof: Contract the chosen maximal ideal to R. Zariski's lemma makes the residue of x
algebraic over the contracted residue field. Lift its monic minimal polynomial and invert
one product of coefficient denominators outside the contracted prime. Take a finite
splitting field L of the lifted polynomial and the integral closure R' of the localized R
in L. Nagata finiteness makes R' finite, normal, Noetherian and Nagata, with fraction field
L. The ring R'[x] is finite over the localized R[x]. Localize it at R[x] minus m to obtain
B. Localization preserves finiteness, injectivity and the domain property. At every maximal
ideal of B, integrality identifies its local ring with R'[x] at a maximal ideal over m.
The split polynomial evaluates into that ideal, so some root r satisfies x-r in the ideal.
The equality R'[x]=R'[x-r] gives the stated local presentation with y=x-r. The construction
through the maximal contraction and root witness is isolated in
`exists_adjoin_singleton_splitting_cover`. Noetherianity, the shift of generator and the
local ring isomorphisms are proved here. Finally write the image z of x as b/a over R'.
Inverting the nonzero image of a turns R'[z] into R'_a.
The corresponding principal open in B, and all its prime localizations, are normal domains.
The constructions use finite extensions and localizations in Type(max u v), with universe
lifts for R and K if necessary. No analytic-unramified assertion is used here. -/
theorem exists_finite_cover_adjoin_singleton_core
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsDomain B)
      (_ : Algebra (Localization.AtPrime m) B) (_ : IsNoetherianRing B),
      Function.Injective (algebraMap (Localization.AtPrime m) B) ∧
      Module.Finite (Localization.AtPrime m) B ∧
      (∃ f : B, f ≠ 0 ∧ ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      (∀ (q : Ideal B) [q.IsMaximal],
        ∃ (R' K' : Type (max u v)) (_ : CommRing R') (_ : IsDomain R')
          (_ : IsIntegrallyClosed R') (_ : IsNoetherianRing R') (_ : Field K')
          (_ : Algebra R' K') (_ : IsFractionRing R' K'),
          IsNagataRing R' ∧ ∃ (y : K')
            (_ : IsNoetherianRing (Algebra.adjoin R' ({y} : Set K')))
            (n : Ideal (Algebra.adjoin R' ({y} : Set K'))) (_ : n.IsMaximal),
            (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
              Algebra.adjoin R' ({y} : Set K')) ∈ n ∧
              Nonempty (Localization.AtPrime q ≃+* Localization.AtPrime n)) := by
  obtain ⟨R', K', _, _, _, _, _, _, hR', z, M, hM, hA, hinj, hfinite, hlocal⟩ :=
    exists_adjoin_singleton_splitting_cover R K hR x m
  let B := Localization M
  let : Algebra (Localization.AtPrime m) B := hA
  let : Module.Finite (Localization.AtPrime m) B := hfinite
  let : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  let : IsNoetherianRing R := hR.1
  let : Algebra.FiniteType R (Algebra.adjoin R ({x} : Set K)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing (Algebra.adjoin R ({x} : Set K)) :=
    Algebra.FiniteType.isNoetherianRing R (Algebra.adjoin R ({x} : Set K))
  let : IsNoetherianRing (Localization.AtPrime m) := inferInstance
  let : IsNoetherianRing B := IsNoetherianRing.of_finite (Localization.AtPrime m) B
  refine ⟨B, inferInstance, inferInstance, hA, inferInstance, hinj, hfinite, ?_, ?_⟩
  · exact adjoin_singleton_localization_normal_away R' K' z M hM
  · intro q hq
    let T := Algebra.adjoin R' ({z} : Set K')
    let n0 : Ideal T := q.comap (algebraMap T B)
    obtain ⟨hn0, r, hr⟩ := hlocal q
    let : n0.IsMaximal := hn0
    obtain ⟨y, n, hn, hy, e⟩ :=
      adjoin_singleton_shift_local_presentation R' K' z n0 r hr
    let e0 : Localization.AtPrime q ≃+* Localization.AtPrime n0 :=
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).symm.toRingEquiv
    let : IsNoetherianRing R' := hR'.1
    let : Algebra.FiniteType R' (Algebra.adjoin R' ({y} : Set K')) :=
      Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
    let : IsNoetherianRing (Algebra.adjoin R' ({y} : Set K')) :=
      Algebra.FiniteType.isNoetherianRing R' (Algebra.adjoin R' ({y} : Set K'))
    exact ⟨R', K', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, hR', y, inferInstance, n, hn, hy,
      ⟨e0.trans e.some⟩⟩
