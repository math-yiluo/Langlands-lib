/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Flat.Stability

/-!
# Selecting generators as a basis of a localized direct summand

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07C6;
Algebra, Tags 00NX and 0GWM.
-/

@[expose] public section

universe u v

namespace Module

private theorem selected_basis_of_split
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (n m : ℕ) (x : Fin m → M) (hx : Submodule.span A (Set.range x) = ⊤)
    (p : Ideal A) [p.IsPrime]
    (d : M →ₗ[A] (Fin n → A)) (l : (Fin n → A) →ₗ[A] M)
    (hld : l.comp d = LinearMap.id) :
    ∃ t : A, t ∉ p ∧ ∃ (V : Finset (Fin m)) (c : ℕ),
      V.card = c ∧ c ≤ min n m ∧
      ∃ e : Fin c ≃ V,
        ∃ bs : Module.Basis (Fin c) (Localization.Away t) (LocalizedModule.Away t M),
          ∀ j : Fin c, bs j =
            LocalizedModule.mkLinearMap (Submonoid.powers t) M (x (e j).1) := by
  classical
  have : Module.Finite A M := Module.Finite.of_fg_top
    (hx ▸ Submodule.fg_span (Set.finite_range x))
  have : Module.Projective A M := Module.Projective.of_split d l hld
  have : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  let L := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  let loc : M →ₗ[A] N := LocalizedModule.mkLinearMap p.primeCompl M
  have hspan : Submodule.span L (Set.range (loc ∘ x)) = ⊤ := by
    rw [Set.range_comp]
    exact span_eq_top_of_isLocalizedModule L p.primeCompl loc hx
  obtain ⟨κ, a, bp, hbp⟩ := Module.exists_basis_of_span_of_flat (loc ∘ x) hspan
  have : Finite κ := Module.Finite.finite_basis bp
  let : Fintype κ := Fintype.ofFinite κ
  have ha : Function.Injective a := by
    intro i j h
    apply bp.injective
    rw [hbp, hbp, h]
  let c := Fintype.card κ
  let V : Finset (Fin m) := Finset.univ.image a
  let ek : Fin c ≃ κ := (Fintype.equivFin κ).symm
  let ea : κ ≃ V := Equiv.ofBijective
    (fun i ↦ ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h ↦ ha (congrArg Subtype.val h), by
      rintro ⟨j, hj⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, rfl⟩⟩
  let e : Fin c ≃ V := ek.trans ea
  let bc : Module.Basis (Fin c) L N := bp.reindex ek.symm
  have hbc : ∀ j, bc j = loc (x (e j).1) := by
    intro j
    simp only [bc, Module.Basis.reindex_apply, Equiv.symm_symm, hbp]
    rfl
  have hcV : V.card = c := by
    simpa [V, c] using Finset.card_image_of_injective Finset.univ ha
  have hcm : c ≤ m := by
    simpa [c] using Fintype.card_le_of_injective a ha
  have hd : Function.Injective d := by
    intro z w h
    have hh := congrArg l h
    simpa only [← LinearMap.comp_apply, hld, LinearMap.id_apply] using hh
  have hcn : c ≤ n := by
    have hdim := LinearMap.finrank_le_finrank_of_injective
      (LocalizedModule.map_injective p.primeCompl d hd)
    let bq := (Pi.basisFun A (Fin n)).ofIsLocalizedModule L p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (Fin n → A))
    change Module.finrank L N ≤
      Module.finrank L (LocalizedModule p.primeCompl (Fin n → A)) at hdim
    rw [Module.finrank_eq_card_basis bc, Module.finrank_eq_card_basis bq] at hdim
    simpa only [Fintype.card_fin] using hdim
  let y : Fin c → M := fun j ↦ x (e j).1
  let φ : (Fin c →₀ A) →ₗ[A] M := Finsupp.linearCombination A y
  let l₁ : (Fin c →₀ A) →ₗ[A] (Fin c →₀ L) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A L)
  let φp : (Fin c →₀ L) →ₗ[L] N :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ loc L φ
  have hφp : φp = bc.repr.symm.toLinearMap := by
    apply LinearMap.restrictScalars_injective A
    rw [show (φp.restrictScalars A) =
      IsLocalizedModule.map p.primeCompl l₁ loc φ from rfl]
    rw [IsLocalizedModule.map_linearCombination]
    ext j
    simp [y, ← hbc]
  have hbij : Function.Bijective φp := by
    rw [hφp]
    exact bc.repr.symm.bijective
  obtain ⟨t, ht, hφt⟩ := Module.FinitePresentation.exists_notMem_bijective φ p l₁ loc hbij
  let l₁t : (Fin c →₀ A) →ₗ[A] (Fin c →₀ Localization.Away t) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.Away t))
  let loct : M →ₗ[A] LocalizedModule.Away t M :=
    LocalizedModule.mkLinearMap (Submonoid.powers t) M
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁t loct] at hφt
  let φt : (Fin c →₀ Localization.Away t) →ₗ[Localization.Away t]
      LocalizedModule.Away t M :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers t) l₁t loct (Localization.Away t) φ
  let et := LinearEquiv.ofBijective φt hφt
  refine ⟨t, ht, V, c, hcV, le_min hcn hcm, e, Module.Basis.ofRepr et.symm, ?_⟩
  intro j
  change φt (Finsupp.single j 1) = loct (y j)
  change IsLocalizedModule.map (Submonoid.powers t) l₁t loct φ
    (Finsupp.single j 1) = loct (y j)
  rw [IsLocalizedModule.map_linearCombination]
  simp

/-- A finite spanning family of a module which is a direct summand of `A_b^n` contains
 a basis after a further principal localization near a specified prime.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07C6 (selection and shrinking);
Algebra, Tags 00NX and 0GWM.
(blueprint: lem-weil-pbc-selected-basis-of-localized-split)

Proof: The split injection exhibits `M_b` as a direct summand of the finite free
module `A_b^n`, so it is finite projective, hence finitely presented (00NX). The prime
`p`, which avoids `b`, extends to a prime of `A_b`. Localizing the split injection
at this prime makes `M_p` a finite projective module over the local ring `A_p`,
hence free. The given generators span its residue vector space. Select a subset
which is a residue basis and enumerate it by `Fin c`. Its cardinality is at most
`m`, and the split injection after residue base change makes it at most `n`.
Nakayama makes these prescribed lifts generate `M_p`. A surjective map between
finite free modules of the same rank is bijective, so these lifts are a basis
at `p`. Finite presentation of `M_b` spreads this isomorphism to a principal
neighbourhood of the extended prime (0GWM, in its prescribed-lifts form).
Write its localization element as `t / b^k`. Since it avoids the extended prime,
`t` avoids `p`. The iterated localization is the localization at `b * t`;
transport the basis along the localization equivalences. They send each original
`x i` divided by one to itself divided by one, giving the displayed basis values.
No global finite presentation of `M` is required. -/
theorem exists_selected_basis_away_mul_of_split
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (n m : ℕ) (x : Fin m → M) (hx : Submodule.span A (Set.range x) = ⊤)
    (p : Ideal A) [p.IsPrime] (b : A) (hb : b ∉ p)
    (d : LocalizedModule.Away b M →ₗ[Localization.Away b] (Fin n → Localization.Away b))
    (l : (Fin n → Localization.Away b) →ₗ[Localization.Away b] LocalizedModule.Away b M)
    (hld : l.comp d = LinearMap.id) :
    ∃ t : A, t ∉ p ∧ ∃ (V : Finset (Fin m)) (c : ℕ),
      V.card = c ∧ c ≤ min n m ∧
      ∃ e : Fin c ≃ V,
        ∃ bs : Module.Basis (Fin c) (Localization.Away (b * t))
            (LocalizedModule.Away (b * t) M),
          ∀ j : Fin c, bs j =
            LocalizedModule.mkLinearMap (Submonoid.powers (b * t)) M (x (e j).1) := by
  classical
  -- Select the prescribed generators over the ring where the splitting is given.
  let B := Localization.Away b
  let Mb := LocalizedModule.Away b M
  let f : M →ₗ[A] Mb := LocalizedModule.mkLinearMap (Submonoid.powers b) M
  let q : Ideal B := p.map (algebraMap A B)
  have hdisj := (p.disjoint_powers_iff_notMem_of_isPrime b).mpr hb
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers b) B p inferInstance hdisj
  have hspan : Submodule.span B (Set.range (f ∘ x)) = ⊤ := by
    rw [Set.range_comp]
    exact span_eq_top_of_isLocalizedModule B (Submonoid.powers b) f hx
  obtain ⟨s, hs, V, c, hcV, hc, e, bs, hbs⟩ :=
    selected_basis_of_split n m (f ∘ x) hspan q d l hld
  -- Clear the denominator of the shrinking element and keep its numerator outside p.
  obtain ⟨k, t, ht⟩ := IsLocalization.Away.surj b s
  have htp : t ∉ p := by
    intro h
    apply hs
    have hmem : algebraMap A B t ∈ q := Ideal.mem_map_of_mem _ h
    rw [← ht] at hmem
    exact (q.unit_mul_mem_iff_mem
      ((IsLocalization.Away.algebraMap_isUnit (S := B) b).pow k)).mp
        (by simpa only [mul_comm] using hmem)
  let C := Localization.Away s
  let N := LocalizedModule.Away s Mb
  let g : Mb →ₗ[B] N := LocalizedModule.mkLinearMap (Submonoid.powers s) Mb
  have hassoc : Associated (algebraMap A B t) s := by
    rw [← ht]
    exact (associated_mul_unit_right s _
      ((IsLocalization.Away.algebraMap_isUnit (S := B) b).pow k)).symm
  have : IsLocalization.Away (b * t) C :=
    IsLocalization.Away.mul_of_associated b t s hassoc
  have : IsLocalizedModule.Away (algebraMap A B t) g :=
    IsLocalizedModule.Away.of_associated hassoc.symm
  let fg : M →ₗ[A] N := (g.restrictScalars A).comp f
  -- Verify the universal localization conditions for the composite module map.
  have : IsLocalizedModule.Away (b * t) fg := by
    refine IsLocalizedModule.Away.mk ?_ ?_ ?_
    · rw [Module.End.isUnit_iff]
      change Function.Bijective (fun z : N ↦ (b * t) • z)
      simpa only [algebraMap_smul] using
        (IsLocalization.Away.algebraMap_isUnit (S := C) (b * t)).smul_bijective (β := N)
    · intro z
      obtain ⟨i, w, hw⟩ := IsLocalizedModule.Away.surj g (algebraMap A B t) z
      obtain ⟨j, v, hv⟩ := IsLocalizedModule.Away.surj f b w
      refine ⟨i + j, (b ^ i * t ^ j) • v, ?_⟩
      calc
        (b * t) ^ (i + j) • z =
            (b ^ i * t ^ j) • (b ^ j • ((algebraMap A B t) ^ i • z)) := by
          rw [← map_pow, algebraMap_smul]
          simp only [← mul_smul, mul_pow, pow_add]
          congr 1
          ring
        _ = (b ^ i * t ^ j) • (b ^ j • g w) := by rw [hw]
        _ = (b ^ i * t ^ j) • g (b ^ j • w) := by rw [g.map_smul_of_tower]
        _ = fg ((b ^ i * t ^ j) • v) := by
          rw [hv]
          simp only [fg, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
            map_smul]
    · intro v w hvw
      change g (f v) = g (f w) at hvw
      obtain ⟨i, hi⟩ := IsLocalizedModule.Away.exists_of_eq
        (f := g) (algebraMap A B t) hvw
      have heq : f (t ^ i • v) = f (t ^ i • w) := by
        simpa only [map_smul, ← map_pow, algebraMap_smul] using hi
      obtain ⟨j, hj⟩ := IsLocalizedModule.Away.exists_of_eq b heq
      refine ⟨i + j, ?_⟩
      have h := congrArg (fun z : M ↦ (b ^ i * t ^ j) • z) hj
      convert h using 1 <;> simp only [← mul_smul, mul_pow, pow_add] <;>
        congr 1 <;> ring
  -- Transport both the coefficient ring and the module, preserving the original lifts.
  let T := Localization.Away (b * t)
  let h := LocalizedModule.mkLinearMap (Submonoid.powers (b * t)) M
  let er : C ≃ₐ[A] T := IsLocalization.algEquiv (Submonoid.powers (b * t)) C T
  let : Algebra C T := er.toAlgHom.toAlgebra
  have : IsScalarTower A C T := IsScalarTower.of_algebraMap_eq
    (fun a ↦ (er.commutes a).symm)
  let : Module C (LocalizedModule.Away (b * t) M) := Module.compHom _ (algebraMap C T)
  have : IsScalarTower A C (LocalizedModule.Away (b * t) M) := by
    constructor
    intro a r z
    change (algebraMap C T (a • r)) • z = a • (algebraMap C T r) • z
    rw [Algebra.smul_def, map_mul, mul_smul]
    change er (algebraMap A C a) • _ = _
    rw [er.commutes]
    exact algebraMap_smul T a _
  let em := IsLocalizedModule.linearEquiv (Submonoid.powers (b * t)) fg h
  let emC := em.extendScalarsOfIsLocalization (Submonoid.powers (b * t)) C
  let bsC := bs.map emC
  let bsT := bsC.mapCoeffs er.toRingEquiv (fun r z ↦ by rfl)
  refine ⟨t, htp, V, c, hcV, hc, e, bsT, fun j ↦ ?_⟩
  rw [Module.Basis.mapCoeffs_apply, Module.Basis.map_apply, hbs]
  exact IsLocalizedModule.linearEquiv_apply _ _ _ _

end Module
