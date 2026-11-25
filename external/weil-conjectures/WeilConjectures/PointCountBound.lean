/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization

/-!
# Linear growth of the point count of an affine curve

For an affine scheme `X` of finite type and of dimension at most one over a finite field `k`
with `q` elements, the number of points of `X` rational over the degree `n` extension of `k`
grows at most linearly in `q ^ n`: there is a constant `d` with `#X(𝔽_(q ^ n)) ≤ d q ^ n`
for all `n ≥ 1`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_mul_pow`
-/

@[expose] public section

universe u

open CategoryTheory

/-- Ring homomorphisms `R →+* L` into a field which restrict to a fixed homomorphism `ψ` on `A`,
where `R` is spanned by `d` elements as an `A`-module, are finite in number, and there are at
most `d` of them: their value vectors on the generators are linearly independent over `L`, by
the linear independence of characters. -/
theorem finite_ringHom_comp_eq_and_natCard_le {A R L : Type*} [CommRing A] [CommRing R]
    [Field L] [Algebra A R] {d : ℕ} (r : Fin d → R) (hr : Submodule.span A (Set.range r) = ⊤)
    (ψ : A →+* L) :
    Finite {φ : R →+* L // φ.comp (algebraMap A R) = ψ} ∧
      Nat.card {φ : R →+* L // φ.comp (algebraMap A R) = ψ} ≤ d := by
  classical
  have ha (x : R) : ∃ a : Fin d → A, ∑ i, a i • r i = x :=
    (Submodule.mem_span_range_iff_exists_fun A).mp (hr ▸ Submodule.mem_top)
  choose a ha using ha
  let E : (Fin d → L) →ₗ[L] R → L :=
    LinearMap.pi fun x ↦ ∑ i, ψ (a x i) • LinearMap.proj i
  let w : {φ : R →+* L // φ.comp (algebraMap A R) = ψ} → Fin d → L := fun φ i ↦ φ.1 (r i)
  have hEw : E ∘ w = fun φ ↦ ⇑(φ.1 : R →* L) := by
    funext φ x
    calc E (w φ) x = ∑ i, ψ (a x i) * φ.1 (r i) := by simp [E, w]
      _ = φ.1 (∑ i, a x i • r i) := by simp [Algebra.smul_def, ← φ.2]
      _ = φ.1 x := by rw [ha]
  have hinj : Function.Injective
      fun φ : {φ : R →+* L // φ.comp (algebraMap A R) = ψ} ↦ (φ.1 : R →* L) :=
    fun φ φ' h ↦ Subtype.ext (RingHom.ext fun x ↦ DFunLike.congr_fun h x)
  have hli : LinearIndependent L w := by
    have h := (linearIndependent_monoidHom R L).comp _ hinj
    refine LinearIndependent.of_comp E ?_
    rw [hEw]
    exact h
  have hfin := hli.finite
  let := Fintype.ofFinite {φ : R →+* L // φ.comp (algebraMap A R) = ψ}
  refine ⟨hfin, ?_⟩
  rw [Nat.card_eq_fintype_card]
  simpa using hli.fintype_card_le_finrank

/-- If `R` is spanned by `d` elements as a module over a `k`-algebra `A`, then there are at
most `d` times as many `k`-algebra maps `R → L` into a field as `k`-algebra maps `A → L`; in
particular, there are finitely many if there are finitely many `k`-algebra maps `A → L`. -/
theorem natCard_algHom_le_mul_natCard_algHom {k A R L : Type*} [CommRing k] [CommRing A]
    [CommRing R] [Field L] [Algebra k A] [Algebra k R] [Algebra k L] [Algebra A R]
    [IsScalarTower k A R] [Finite (A →ₐ[k] L)] {d : ℕ} (r : Fin d → R)
    (hr : Submodule.span A (Set.range r) = ⊤) :
    Finite (R →ₐ[k] L) ∧ Nat.card (R →ₐ[k] L) ≤ d * Nat.card (A →ₐ[k] L) := by
  classical
  let F : (R →ₐ[k] L) → (A →ₐ[k] L) := fun φ ↦ φ.comp (IsScalarTower.toAlgHom k A R)
  have hfib (ψ : A →ₐ[k] L) : Finite {φ // F φ = ψ} ∧ Nat.card {φ // F φ = ψ} ≤ d := by
    obtain ⟨h₁, h₂⟩ := finite_ringHom_comp_eq_and_natCard_le r hr ψ.toRingHom
    let j : {φ // F φ = ψ} → {φ : R →+* L // φ.comp (algebraMap A R) = ψ.toRingHom} :=
      fun φ ↦ ⟨φ.1.toRingHom, by
        ext x
        simp [← φ.2, F]⟩
    have hj : Function.Injective j := fun φ φ' h ↦
      Subtype.ext (AlgHom.ext fun x ↦ DFunLike.congr_fun (congrArg Subtype.val h) x)
    exact ⟨Finite.of_injective j hj, (Nat.card_le_card_of_injective j hj).trans h₂⟩
  let := Fintype.ofFinite (A →ₐ[k] L)
  have := fun ψ ↦ (hfib ψ).1
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv F), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma]
  calc ∑ ψ, Nat.card {φ // F φ = ψ} ≤ ∑ _ψ : A →ₐ[k] L, d :=
        Finset.sum_le_sum fun ψ _ ↦ (hfib ψ).2
    _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]

/-- There are finitely many, namely at most `#L ^ s`, `k`-algebra maps from a polynomial ring in
`s` variables to a finite `k`-algebra `L`. -/
theorem finite_mvPolynomial_algHom_and_natCard_le (k L : Type*) [CommRing k] [CommRing L]
    [Algebra k L] [Finite L] (s : ℕ) :
    Finite (MvPolynomial (Fin s) k →ₐ[k] L) ∧
      Nat.card (MvPolynomial (Fin s) k →ₐ[k] L) ≤ Nat.card L ^ s := by
  let j : (MvPolynomial (Fin s) k →ₐ[k] L) → Fin s → L := fun φ i ↦ φ (MvPolynomial.X i)
  have hj : Function.Injective j := fun φ φ' h ↦
    MvPolynomial.algHom_ext fun i ↦ congrFun h i
  refine ⟨Finite.of_injective j hj, ?_⟩
  simpa [Nat.card_fun] using Nat.card_le_card_of_injective j hj

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The `K`-rational points of an affine scheme `X` over `k` inject into the `k`-algebra maps
`Γ(X, ⊤) → K`, where `Γ(X, ⊤)` is a `k`-algebra via the structure morphism. -/
theorem Hom.exists_injective_fieldPoints_algHom [IsAffine X] (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K] :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    ∃ j : f.fieldPoints K → (Γ(X, ⊤) →ₐ[k] K), Function.Injective j := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hcomp (g : f.fieldPoints K) :
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ Spec.preimage (g.1 ≫ X.isoSpec.hom) =
        CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Category.assoc,
      Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id, g.2]
  refine ⟨fun g ↦ ⟨(Spec.preimage (g.1 ≫ X.isoSpec.hom)).hom,
    fun c ↦ congr(CommRingCat.Hom.hom $(hcomp g) c)⟩, fun g₁ g₂ e ↦ ?_⟩
  have he : Spec.preimage (g₁.1 ≫ X.isoSpec.hom) = Spec.preimage (g₂.1 ≫ X.isoSpec.hom) :=
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom e)
  have h := congrArg Spec.map he
  rw [Spec.map_preimage, Spec.map_preimage] at h
  exact Subtype.ext ((cancel_mono X.isoSpec.hom).mp h)

variable [Finite k]

/-- Blueprint `lemma-point-count-bound--1`: Linear growth of the point count on an affine
curve.

Let `X` be an affine scheme of finite type and of dimension at most one over a finite field `k`
with `q` elements. Then there is a constant `d` such that `#X(𝔽_(q ^ n)) ≤ d q ^ n` for every
`n ≥ 1`.

By Noether normalization, `R = Γ(X, ⊤)` is a finite module, generated by `d` elements, over a
polynomial ring `k[t]` (or over `k`, if `X` is finite). A point of `X` with values in
`k_n = 𝔽_(q ^ n)` is a `k`-algebra map `R → k_n`; there are at most `q ^ n` choices for the
image of `t`, and the maps with a given image of `t` are distinct characters of `R` which are
determined by their values on the `d` module generators, so by the linear independence of
characters there are at most `d` of them. -/
theorem Hom.exists_pointCount_le_mul_pow [IsAffine X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) :
    ∃ d : ℕ, ∀ n : ℕ, n ≠ 0 → f.pointCount n ≤ d * Nat.card k ^ n := by
  classical
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hL (n : ℕ) (hn : n ≠ 0) : Finite (FiniteField.galoisExtension k n) :=
    Nat.finite_of_card_ne_zero
      (by simp [FiniteField.nat_card_galoisExtension k n hn, Nat.card_pos.ne'])
  cases subsingleton_or_nontrivial Γ(X, ⊤) with
  | inl hΓ =>
    refine ⟨0, fun n hn ↦ ?_⟩
    obtain ⟨j, hj⟩ := f.exists_injective_fieldPoints_algHom (FiniteField.galoisExtension k n)
    have : IsEmpty (Γ(X, ⊤) →ₐ[k] FiniteField.galoisExtension k n) :=
      ⟨fun φ ↦ one_ne_zero (by rw [← map_one φ, Subsingleton.elim (1 : Γ(X, ⊤)) 0, map_zero])⟩
    simpa [Hom.pointCount] using Nat.card_le_card_of_injective j hj
  | inr hΓ =>
    have hft : Algebra.FiniteType k Γ(X, ⊤) := by
      have hf : f.appTop.hom.FiniteType :=
        (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹_›
      exact hf.comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
    have hdim : ringKrullDim Γ(X, ⊤) ≤ 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact (IsHomeomorph.topologicalKrullDim_eq _
        X.isoSpec.hom.homeomorph.isHomeomorph).symm.trans_le hX
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k Γ(X, ⊤)
    have hs : s ≤ 1 := by
      rw [ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin] at hdim
      exact_mod_cast hdim
    algebraize [g.toRingHom]
    have : Module.Finite (MvPolynomial (Fin s) k) Γ(X, ⊤) := hfin
    obtain ⟨d, r, hr⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin s) k) (M := Γ(X, ⊤))
    refine ⟨d, fun n hn ↦ ?_⟩
    have := hL n hn
    obtain ⟨hA, hAcard⟩ := finite_mvPolynomial_algHom_and_natCard_le k
      (FiniteField.galoisExtension k n) s
    obtain ⟨hR, hRcard⟩ := natCard_algHom_le_mul_natCard_algHom
      (L := FiniteField.galoisExtension k n) (k := k) r hr
    obtain ⟨j, hj⟩ := f.exists_injective_fieldPoints_algHom (FiniteField.galoisExtension k n)
    have hpow : Nat.card (FiniteField.galoisExtension k n) ^ s ≤
        Nat.card (FiniteField.galoisExtension k n) := by
      interval_cases s
      · simp [Nat.one_le_iff_ne_zero, FiniteField.nat_card_galoisExtension k n hn,
          Nat.card_pos.ne']
      · simp
    calc f.pointCount n ≤ Nat.card (Γ(X, ⊤) →ₐ[k] FiniteField.galoisExtension k n) :=
          Nat.card_le_card_of_injective j hj
      _ ≤ d * Nat.card (FiniteField.galoisExtension k n) ^ s :=
          hRcard.trans (Nat.mul_le_mul_left d hAcard)
      _ ≤ d * Nat.card k ^ n := by
          rw [← FiniteField.nat_card_galoisExtension k n hn]
          exact Nat.mul_le_mul_left d hpow


/-- On an affine scheme of finite type and dimension at most one over a finite field `k` with
`q` elements, the closed points of degree `e` number at most `A q ^ e`, in any finite set of
them (a form of `lemma-point-count-bound--1`): each contributes `deg x ≥ 1` points over
`𝔽_(q ^ e)`. -/
theorem Hom.exists_card_filter_degreeOver_le [IsAffine X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) :
    ∃ A : ℝ, ∀ (T : Set X.finitePoints) (t : Finset T) (e : ℕ),
      ((t.filter fun x ↦ f.degreeOver x.1.1 = e).card : ℝ) ≤ A * (Nat.card k : ℝ) ^ e := by
  classical
  obtain ⟨d, hd⟩ := f.exists_pointCount_le_mul_pow hX
  refine ⟨d, fun T t e ↦ ?_⟩
  rcases eq_or_ne e 0 with rfl | he
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ↦
      f.degreeOver_ne_zero x.1.2)]
    simp
  set S := (t.filter fun x ↦ f.degreeOver x.1.1 = e).image Subtype.val
  have hS : S.card = (t.filter fun x ↦ f.degreeOver x.1.1 = e).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  set T' := (f.finite_setOf_degreeOver_le e).toFinset
  have hcount := f.pointCount_eq_sum he (T := T') fun y hy ↦ by
    simpa [T'] using Nat.le_of_dvd (Nat.pos_of_ne_zero he) hy
  have hST : S ⊆ T'.filter fun y ↦ f.degreeOver y.1 ∣ e := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hxe := (Finset.mem_filter.1 hx).2
    simp [T', hxe]
  have hle : S.card ≤ f.pointCount e := by
    rw [hcount]
    calc S.card = ∑ y ∈ S, 1 := by simp
      _ ≤ ∑ y ∈ S, f.degreeOver y.1 := Finset.sum_le_sum fun y _ ↦
          Nat.one_le_iff_ne_zero.2 (f.degreeOver_ne_zero y.2)
      _ ≤ _ := Finset.sum_le_sum_of_subset hST
  rw [← hS]
  exact_mod_cast hle.trans (hd e he)

end AlgebraicGeometry.Scheme
