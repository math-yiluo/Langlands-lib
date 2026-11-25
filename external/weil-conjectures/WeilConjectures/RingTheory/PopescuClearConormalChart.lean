/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.ConormalSpanClearing
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Etale.Kaehler

/-! # Clearing the relations on one conormal chart

Source: Stacks Project, Tag 07CP, preparation (3)--(4).
(blueprint: lem-weil-pbc-popescu-clear-conormal-chart).
-/

@[expose] public section

universe u

namespace Algebra

private theorem away_pow {B T : Type*} [CommRing B] [CommRing T] [Algebra B T]
    (x : B) (s : ℕ) (hs : 0 < s) [IsLocalization.Away (x ^ s) T] :
    IsLocalization.Away x T := by
  refine IsLocalization.Away.mk x ?_ ?_ ?_
  · apply (isUnit_pow_iff hs.ne').mp
    simpa only [map_pow] using
      (IsLocalization.Away.algebraMap_isUnit (S := T) (x ^ s))
  · intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (x ^ s) z
    exact ⟨s * n, a, by simpa only [map_pow, ← pow_mul] using ha⟩
  · intro a b hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x ^ s) hab
    exact ⟨s * n, by simpa only [← pow_mul] using hn⟩

private theorem module_away_pow {B : Type*} [CommRing B]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (f : M →ₗ[B] N) (x : B) (s : ℕ) (hs : 0 < s)
    [IsLocalizedModule.Away (x ^ s) f] : IsLocalizedModule.Away x f := by
  refine IsLocalizedModule.Away.mk ?_ ?_ ?_
  · apply (isUnit_pow_iff hs.ne').mp
    simpa only [map_pow] using
      (IsLocalizedModule.Away.isUnit_algebraMap f (x ^ s))
  · intro z
    obtain ⟨n, a, ha⟩ := IsLocalizedModule.Away.surj f (x ^ s) z
    exact ⟨s * n, a, by simpa only [← pow_mul] using ha⟩
  · intro a b hab
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (x ^ s) hab
    exact ⟨s * n, by simpa only [← pow_mul] using hn⟩

private theorem transfer_chart
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {M : Type u} [AddCommGroup M] [Module B M] {ι κ : Type}
    (x y : B) (s : ℕ) (hs : 0 < s) (hy : y = x ^ s) (v : ι → M)
    (hsm : Algebra.Smooth R (Localization.Away x))
    (hb : ∃ b : Module.Basis ι (Localization.Away x) (LocalizedModule.Away x M),
      ∀ i, b i = LocalizedModule.mkLinearMap (Submonoid.powers x) M (v i))
    (hd : Nonempty (Module.Basis κ (Localization.Away x)
      (KaehlerDifferential R (Localization.Away x)))) :
    Algebra.Smooth R (Localization.Away y) ∧
    (∃ b : Module.Basis ι (Localization.Away y) (LocalizedModule.Away y M),
      ∀ i, b i = LocalizedModule.mkLinearMap (Submonoid.powers y) M (v i)) ∧
    Nonempty (Module.Basis κ (Localization.Away y)
      (KaehlerDifferential R (Localization.Away y))) := by
  subst y
  let S := Localization.Away x
  let T := Localization.Away (x ^ s)
  have : IsLocalization.Away x T := away_pow x s hs
  let e : S ≃ₐ[B] T := IsLocalization.algEquiv (Submonoid.powers x) S T
  have : Algebra.Smooth R S := hsm
  refine ⟨Algebra.Smooth.of_equiv (e.restrictScalars R), ?_, ?_⟩
  · let f := LocalizedModule.mkLinearMap (Submonoid.powers x) M
    let g := LocalizedModule.mkLinearMap (Submonoid.powers (x ^ s)) M
    have : IsLocalizedModule.Away x g := module_away_pow g x s hs
    let em := IsLocalizedModule.linearEquiv (Submonoid.powers x) f g
    let : Algebra S T := e.toAlgHom.toAlgebra
    have : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq (fun r ↦ (e.commutes r).symm)
    let : Module S (LocalizedModule.Away (x ^ s) M) :=
      Module.compHom _ (algebraMap S T)
    have : IsScalarTower B S (LocalizedModule.Away (x ^ s) M) := by
      constructor
      intro r a z
      change (algebraMap S T (r • a)) • z = r • (algebraMap S T a) • z
      rw [Algebra.smul_def]
      rw [map_mul, mul_smul]
      change e (algebraMap B S r) • _ = _
      rw [e.commutes]
      exact algebraMap_smul T r _
    let emS := em.extendScalarsOfIsLocalization (Submonoid.powers x) S
    obtain ⟨b, hb⟩ := hb
    let bS := b.map emS
    let bT := bS.mapCoeffs e.toRingEquiv (fun c z ↦ by
      change e c • z = (algebraMap S T c) • z
      rfl)
    refine ⟨bT, fun i ↦ ?_⟩
    dsimp only [bT]
    rw [Module.Basis.mapCoeffs_apply]
    dsimp only [bS]
    rw [Module.Basis.map_apply]
    change em (b i) = g (v i)
    rw [hb i]
    exact IsLocalizedModule.linearEquiv_apply _ _ _ _
  · let : Algebra S T := e.toAlgHom.toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq
      (fun r ↦ ((e.restrictScalars R).commutes r).symm)
    have : IsLocalization (Submonoid.powers (1 : S)) T :=
      IsLocalization.of_le_isUnit_of_bijective (by
        rintro z ⟨a, ⟨n, rfl⟩, rfl⟩
        simp) e.bijective
    obtain ⟨b⟩ := hd
    exact ⟨b.ofIsLocalizedModule T (Submonoid.powers (1 : S))
      (KaehlerDifferential.map R R S T)⟩


/-- A selected conormal basis can be refined to exact polynomial relations modulo π².

Source: Stacks Project, Tag 07CP, proof between preparations (2) and (4).
(blueprint: lem-weil-pbc-popescu-clear-conormal-chart).

Proof: Write Pbar = (R/π²)[x], I = (reduced f), and I_E = (reduced f_j, j in E).
The prescribed basis spans the localized conormal module. Apply
Ideal.exists_conormal_span_clearing: lift the spanning combinations to I_E and
clear their localization equalities to obtain a0^k_l*f_l in I_E+I². In Pbar_a0,
Nakayama (Tag 00DV) gives e with e-1 in the localized I and e*I contained in I_E.
Clear the denominator of e-1, writing (e-1)*a0^N=b with b in I. Then
(a0^N+b)*f_l lies in the localized I_E. Clear these finitely many memberships
and choose K=1+max_l k_l. The reduced multiplier abar=a0^K*(a0^N+b) satisfies
abar*f_l in I_E and has quotient image val(a0)^(K+N), with K+N positive.
Express each membership using the selected generators, and lift abar and all
coefficients to R[x]. The residual polynomial maps to zero under reduction,
so it is divisible by C(π²), giving the polynomial g_l and the exact identity.
Localization at a positive power is canonically localization at the original element;
transport smoothness, the prescribed conormal basis, and the differential basis
along the algebra and module localization equivalences. The equivalences commute
with the localization maps, so they preserve the prescribed conormal generators.
For m=0 the empty maximum is zero and K=1. For E empty Nakayama still applies.
The argument also works in the zero ring and when π is zero or a unit. -/
theorem exists_popescu_cleared_conormal_chart
    {R : Type u} [CommRing R] (π : R) (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (a0 : MvPolynomial (Fin n) R) (E : Finset (Fin m)) :
    let red := MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R)))
    let I := Ideal.span (Set.range (fun j ↦ red (f j)))
    let val := fun a ↦ Ideal.Quotient.mk I (red a)
    Smooth (R ⧸ Ideal.span ({π ^ 2} : Set R)) (Localization.Away (val a0)) →
    (∃ b : Module.Basis E (Localization.Away (val a0))
        (LocalizedModule.Away (val a0) I.Cotangent),
      ∀ j : E, b j = LocalizedModule.mkLinearMap (Submonoid.powers (val a0))
        I.Cotangent (I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩)) →
    Nonempty (Module.Basis (Fin (n - E.card)) (Localization.Away (val a0))
      (KaehlerDifferential (R ⧸ Ideal.span ({π ^ 2} : Set R)) (Localization.Away (val a0)))) →
    ∃ (a : MvPolynomial (Fin n) R)
      (h : Fin m → Fin m → MvPolynomial (Fin n) R)
      (g : Fin m → MvPolynomial (Fin n) R) (s : ℕ),
      0 < s ∧ val a = val a0 ^ s ∧
      Smooth (R ⧸ Ideal.span ({π ^ 2} : Set R)) (Localization.Away (val a)) ∧
      (∃ b : Module.Basis E (Localization.Away (val a))
        (LocalizedModule.Away (val a) I.Cotangent),
      ∀ j : E, b j = LocalizedModule.mkLinearMap (Submonoid.powers (val a))
        I.Cotangent (I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩)) ∧
      Nonempty (Module.Basis (Fin (n - E.card)) (Localization.Away (val a))
      (KaehlerDifferential (R ⧸ Ideal.span ({π ^ 2} : Set R)) (Localization.Away (val a)))) ∧
      ∀ l : Fin m,
        a * f l = ∑ j ∈ E, h l j * f j + MvPolynomial.C (π ^ 2) * g l := by
  classical
  dsimp only
  intro hsm hb hd
  let J := Ideal.span ({π ^ 2} : Set R)
  let red := MvPolynomial.map (Ideal.Quotient.mk J) (σ := Fin n)
  let I := Ideal.span (Set.range (fun j ↦ red (f j)))
  let q := Ideal.Quotient.mk I
  have hspan : Submodule.span (Localization.Away (q (red a0)))
      (Set.range (fun j : E ↦ LocalizedModule.mkLinearMap
        (Submonoid.powers (q (red a0))) I.Cotangent
        (I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩))) = ⊤ := by
    obtain ⟨b, hb⟩ := hb
    have hfun : (fun j : E ↦ LocalizedModule.mkLinearMap
        (Submonoid.powers (q (red a0))) I.Cotangent
        (I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩)) = b :=
      funext (fun j ↦ (hb j).symm)
    rw [hfun]
    exact b.span_eq
  obtain ⟨abar, hbar, s, hs, ha, hrel⟩ :=
    Ideal.exists_conormal_span_clearing m (fun j ↦ red (f j)) (red a0) E hspan
  have hsurj : Function.Surjective red :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a, ha'⟩ := hsurj abar
  choose h hh using (fun l j ↦ hsurj (hbar l j))
  have hzero (l : Fin m) : red (a * f l - ∑ j ∈ E, h l j * f j) = 0 := by
    simp only [map_sub, map_mul, map_sum, ha', hh]
    exact sub_eq_zero.mpr (hrel l)
  have hdiv (l : Fin m) : MvPolynomial.C (π ^ 2) ∣
      a * f l - ∑ j ∈ E, h l j * f j := by
    apply (MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk J) (π ^ 2)
      (fun r ↦ (Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton)) _).mpr
    exact hzero l
  choose g hg using hdiv
  have haval : q (red a) = q (red a0) ^ s := by rw [ha']; exact ha
  obtain ⟨hsm', hb', hd'⟩ := transfer_chart (q (red a0)) (q (red a)) s hs haval
    (fun j : E ↦ I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩) hsm hb hd
  refine ⟨a, h, g, s, hs, haval, hsm', hb', hd', fun l ↦ ?_⟩
  exact (sub_eq_iff_eq_add.mp (hg l)).trans (add_comm _ _)


end Algebra
