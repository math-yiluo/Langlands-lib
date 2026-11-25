/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Localizing a finite extension of a principal open at a maximal ideal
Source: Stacks Project, Algebra, Tag 0334, Step 5.
(blueprint: lem-weil-pbc-finite-away-maximal-localization). -/

@[expose] public section

universe u v

set_option backward.isDefEq.respectTransparency false in
/-- Localize a finite extension after inverting one element outside a maximal ideal.
Source: Stacks Project, Algebra, Tag 0334, Step 5, localization of S subset S'.
(blueprint: lem-weil-pbc-finite-away-maximal-localization).

Proof: Put S0 = S_s and p = mS0. Since s is outside m, p is maximal, its contraction
is m, and (S0)_p is canonically S_m. Put h = g composed with S -> S0 and invert the
image M = h(S minus m) in T. The localization universal property gives the canonical
map S_m -> M^-1 T. It is injective since S -> S0 and g are injective. Localizing the
finite set of S0-module generators of T gives finite generation over S_m, because s
is already invertible there. Thus this map is integral. Every maximal ideal q of M^-1 T
contracts to the unique maximal ideal of S_m. The contraction n0 of q to T is prime,
and its contraction to S0 is p. Indeed the elements of m map into q by the contraction
to S_m, and every element outside m maps to a unit; clearing powers of s gives the
assertion on S0. Since T is integral over S0 and p is maximal, n0 is maximal. The same
contraction identity gives m.map h <= n0. -/
theorem exists_finite_away_maximal_localization
    (S : Type u) (T : Type v) [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    (m : Ideal S) [m.IsMaximal] (s : S) (hs : s ∉ m)
    (g : Localization.Away s →+* T) (hg : Function.Injective g) (hfin : g.Finite) :
    let h := g.comp (algebraMap S (Localization.Away s))
    let M := m.primeCompl.map h
    ∃ (_ : Algebra (Localization.AtPrime m) (Localization M)),
      Function.Injective (algebraMap (Localization.AtPrime m) (Localization M)) ∧
      Module.Finite (Localization.AtPrime m) (Localization M) ∧
      ∀ (q : Ideal (Localization M)) [q.IsMaximal],
        (q.comap (algebraMap T (Localization M))).IsMaximal ∧
        m.map h ≤ q.comap (algebraMap T (Localization M)) := by
  classical
  let S0 := Localization.Away s
  let A := Localization.AtPrime m
  let h : S →+* T := g.comp (algebraMap S S0)
  let M := m.primeCompl.map h
  let B := Localization M
  let j : A →+* B := IsLocalization.map B h m.primeCompl.le_comap_map
  let : Algebra A B := j.toAlgebra
  have hle : Submonoid.powers s ≤ m.primeCompl := Submonoid.powers_le.mpr hs
  let : Algebra S0 A :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S0 A _ _ hle
  have : IsScalarTower S S0 A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S0 A _ _ hle
  let : Algebra S0 T := g.toAlgebra
  let : Algebra S0 B := ((algebraMap T B).comp g).toAlgebra
  let : SMul T B := (inferInstance : Algebra T B).toSMul
  let : SMul S0 B := (inferInstance : Algebra S0 B).toSMul
  have : IsScalarTower S0 T B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower S0 A B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext r
    symm
    change j ((algebraMap S0 A) (algebraMap S S0 r)) =
      (algebraMap T B) (g (algebraMap S S0 r))
    rw [← IsScalarTower.algebraMap_apply S S0 A]
    exact IsLocalization.map_eq m.primeCompl.le_comap_map r
  let N := m.primeCompl.map (algebraMap S S0)
  have : IsLocalization N A :=
    IsLocalization.isLocalization_of_submonoid_le S0 A _ _ hle
  have hMN : N.map g = M := by
    ext t
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨algebraMap S S0 b, ⟨b, hb, rfl⟩, rfl⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid T N) B := by
    change IsLocalization (N.map g) B
    rw [hMN]
    infer_instance
  have : Module.Finite S0 T := hfin
  have hf : Module.Finite A B := Module.Finite.of_isLocalization S0 T N
  have hs0 : s ≠ 0 := fun e ↦ hs (e ▸ m.zero_mem)
  have hinj : Function.Injective h := hg.comp
    (IsLocalization.injective S0 (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr hs0)))
  have hi : Function.Injective j :=
    IsLocalization.map_injective_of_injective m.primeCompl A B hinj
  refine ⟨inferInstance, hi, hf, ?_⟩
  intro q hq
  have hqA : (q.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q
  have hqAeq : q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hqA
  have hcomp : (algebraMap T B).comp h = (algebraMap A B).comp (algebraMap S A) := by
    ext r
    exact (IsLocalization.map_eq (S := A) (Q := B) (g := h) m.primeCompl.le_comap_map r).symm
  have hcontract : (q.comap (algebraMap T B)).comap h = m := by
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hqAeq]
    exact IsLocalization.AtPrime.under_maximalIdeal A m
  have hmem : m.map h ≤ q.comap (algebraMap T B) := by
    rw [Ideal.map_le_iff_le_comap, hcontract]
  let J := (q.comap (algebraMap T B)).comap g
  have hJ : J.comap (algebraMap S S0) = m := by
    simpa only [J, h, Ideal.comap_comap, RingHom.comp_assoc] using hcontract
  have : (J.comap (algebraMap S S0)).IsMaximal := hJ.symm ▸ inferInstance
  have hJmax : J.IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_under (Submonoid.powers s) S0 J
  have : (q.comap (algebraMap T B)).IsPrime := Ideal.comap_isPrime _ q
  exact ⟨Ideal.isMaximal_of_isIntegral_of_isMaximal_comap g hfin.to_isIntegral
    (q.comap (algebraMap T B)) hJmax, hmem⟩

