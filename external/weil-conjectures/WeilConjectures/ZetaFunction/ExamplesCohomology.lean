/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.Examples

/-!
# Compactly supported cohomology of the affine line and of the multiplicative group

Let `C₀` be a smooth geometrically connected affine curve over the finite field `k₀ = 𝔽_q`. The
compactly supported cohomology `H_cⁱ(C₀ ⊗ k̄, ℚ̄_ℓ)` vanishes outside degrees `1` and `2`, is
`ι`-pure of weight `2` in degree `2` and `ι`-mixed of weights at most `1` in degree `1`. Together
with the Grothendieck–Lefschetz trace formula this determines it from the point counts when they
are as simple as those of `𝔸¹` and `𝔾_m`:

* `H_c²(𝔸¹ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-1)` and all other `H_cⁱ` vanish (blueprint `prose-12-31`);
* `H_c¹(𝔾_m ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, `H_c²(𝔾_m ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-1)` and all other `H_cⁱ` vanish
  (blueprint `ex-weil-multiplicative-group`).

Indeed the reciprocal roots of `det(1 - T F | H_c²)` have absolute value `q` under every
embedding `ι`, those of `det(1 - T F | H_c¹)` at most `q^{1/2}`, and the trace formula gives
`Z(C₀, T) det(1 - T F | H_c²) = det(1 - T F | H_c¹)`; comparing with `Z(𝔸¹, T) = (1 - qT)⁻¹` and
`Z(𝔾_m, T) = (1 - T)/(1 - qT)` leaves no room for cancellation.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_of_curve`,
  `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two_adicConstant`:
  vanishing and purity for a smooth geometrically connected affine curve.
- `AlgebraicGeometry.compactlySupportedCohomology_affineLine`: `prose-12-31`.
- `AlgebraicGeometry.compactlySupportedCohomology_multiplicativeGroup`:
  `ex-weil-multiplicative-group`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace LinearMap

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] {V W : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Separating eigenvalues by a predicate.** Let `f`, `g` be automorphisms with
`(1 - a T) det(1 - T f) = ∏_{c ∈ S} (1 - c T) · det(1 - T g)` for a nonzero `a` and a multiset `S`
of nonzero scalars. If a predicate `P` holds for `a` and for every eigenvalue of `g`, but fails for
every eigenvalue of `f` and every element of `S`, then the eigenvalues of `g` are `a`, once, and
those of `f` are the elements of `S`, with multiplicity. -/
theorem charpoly_roots_eq_of_mul_charpolyRev_eq (f : Module.End K V) (g : Module.End K W)
    (hf : IsUnit (LinearMap.det f)) (hg : IsUnit (LinearMap.det g)) {a : K} (ha : a ≠ 0)
    {S : Multiset K} (hS : (0 : K) ∉ S)
    (h : (1 - C a * X) * f.charpolyRev = (S.map fun c ↦ 1 - C c * X).prod * g.charpolyRev)
    (P : K → Prop) (hPa : P a) (hPg : ∀ α, g.HasEigenvalue α → P α)
    (hPf : ∀ α, f.HasEigenvalue α → ¬ P α) (hPS : ∀ c ∈ S, ¬ P c) :
    g.charpoly.roots = {a} ∧ f.charpoly.roots = S := by
  classical
  have hrf := (reciprocal_roots_eigenvalues f hf).1
  have hrg := (reciprocal_roots_eigenvalues g hg).1
  have ha' : (0 : K) ∉ ({a} : Multiset K) := by simpa using ha.symm
  have h1 : (1 - C a * X : K[X]) = (({a} : Multiset K).map fun c ↦ 1 - C c * X).prod := by simp
  have hrev := congrArg Polynomial.reverse h
  rw [reverse_mul_of_domain, reverse_mul_of_domain, h1, reverse_multiset_prod_one_sub_C_mul_X ha',
    reverse_multiset_prod_one_sub_C_mul_X hS] at hrev
  have hne (u : Multiset K) (p : K[X]) (hp : p.coeff 0 = 1) :
      (u.map fun c ↦ X - C c).prod * p.reverse ≠ 0 := by
    refine mul_ne_zero (Multiset.prod_ne_zero fun h0 ↦ ?_) ?_
    · obtain ⟨c, -, hc⟩ := Multiset.mem_map.1 h0
      exact X_sub_C_ne_zero c hc
    · rw [Ne, reverse_eq_zero]
      rintro rfl
      simp at hp
  have hroots := congrArg Polynomial.roots hrev
  rw [roots_mul (hne _ _ (coeff_zero_charpolyRev f)),
    roots_mul (hne _ _ (coeff_zero_charpolyRev g)),
    roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C, hrf, hrg] at hroots
  have hmemf : ∀ x ∈ f.charpoly.roots, ¬ P x := fun x hx ↦
    hPf x ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (isRoot_of_mem_roots hx))
  have hmemg : ∀ x ∈ g.charpoly.roots, P x := fun x hx ↦
    hPg x ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (isRoot_of_mem_roots hx))
  have e1 := congrArg (Multiset.filter P) hroots
  have e2 := congrArg (Multiset.filter (fun x ↦ ¬ P x)) hroots
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_eq_self.2 hmemg,
    Multiset.filter_eq_nil.2 hmemf, Multiset.filter_eq_nil.2 hPS, Multiset.filter_singleton,
    ite_eq_left hPa, add_zero, zero_add] at e1
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_singleton,
    ite_eq_right (not_not.2 hPa),
    Multiset.filter_eq_self.2 hmemf, Multiset.filter_eq_self.2 hPS,
    Multiset.filter_eq_nil.2 fun x hx hn ↦ hn (hmemg x hx), Multiset.empty_eq_zero, zero_add,
    add_zero] at e2
  exact ⟨e1.symm, e2⟩

/-- Over an algebraically closed field, an endomorphism whose only eigenvalue is `a`, with
algebraic multiplicity one, is the homothety `a` of a line. -/
theorem finrank_eq_one_and_eq_smul_one_of_charpoly_roots_eq (f : Module.End K V) {a : K}
    (h : f.charpoly.roots = {a}) : Module.finrank K V = 1 ∧ f = a • 1 := by
  have hcard : Module.finrank K V = 1 := by
    rw [← LinearMap.charpoly_natDegree f, ← (splits_iff_card_roots.1 (IsAlgClosed.splits _)), h,
      Multiset.card_singleton]
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hcard f
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hcard
  have hev : f.HasEigenvalue c := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, hc]
    exact ⟨rfl, hv⟩
  have hroot : c ∈ f.charpoly.roots :=
    (mem_roots (LinearMap.charpoly_monic f).ne_zero).2
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1 hev)
  rw [h, Multiset.mem_singleton] at hroot
  subst hroot
  exact ⟨hcard, hc.trans (by rw [Module.End.one_eq_id])⟩

/-- Over an algebraically closed field, an endomorphism without eigenvalues lives on the zero
space. -/
theorem subsingleton_of_charpoly_roots_eq_zero (f : Module.End K V) (h : f.charpoly.roots = 0) :
    Subsingleton V := by
  have hcard : Module.finrank K V = 0 := by
    rw [← LinearMap.charpoly_natDegree f, ← (splits_iff_card_roots.1 (IsAlgClosed.splits _)), h,
      Multiset.card_zero]
  exact Module.finrank_zero_iff.1 hcard

end LinearMap

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth curve over `k₀` is locally of finite type over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

variable (k₀ l C)

/-- The compactly supported cohomology of the constant Weil sheaf on a smooth geometrically
connected affine curve vanishes outside degrees `1` and `2`: the pushforward of the constant sheaf
along the identity is the constant sheaf (`AlgebraicGeometry.WeilSheaf.lowerStarIdIso`), so this
is the case `j = 𝟙` of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
and `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant_of_curve {r : ℤ} (hr : r ≠ 1)
    (hr' : r ≠ 2) :
    Subsingleton ((adicConstant k₀ l C).compactlySupportedCohomology r).carrier := by
  have e := compactlySupportedCohomologyEquivOfIso
    ((lowerStarIdIso k₀ l C).app (adicConstant k₀ l C)) r
  have hF := isLisse_adicConstant k₀ l C
  rcases lt_trichotomy r 0 with h | rfl | h
  · have := subsingleton_compactlySupportedCohomology_directImage (𝟙 C) _ hF (r := r) (Or.inl h)
    exact e.toLinearEquiv.symm.subsingleton
  · have := subsingleton_compactlySupportedCohomology_directImage_zero (𝟙 C) _ hF
    exact e.toLinearEquiv.symm.subsingleton
  · have := subsingleton_compactlySupportedCohomology_directImage (𝟙 C) _ hF (r := r)
      (Or.inr (by omega))
    exact e.toLinearEquiv.symm.subsingleton

/-- The top compactly supported cohomology `H_c²(C₀ ⊗ k̄, ℚ̄_ℓ)` of a smooth geometrically
connected affine curve is `ι`-pure of weight `2`: this is the case `j = 𝟙` of
`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`, the constant
sheaf being lisse and punctually pure of weight `0`. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_adicConstant
    (ι : PadicAlgCl l →+* ℂ) :
    ((adicConstant k₀ l C).compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι 2 := by
  have e := compactlySupportedCohomologyEquivOfIso
    ((lowerStarIdIso k₀ l C).app (adicConstant k₀ l C)) 2
  have h := isPureOfWeightOver_compactlySupportedCohomology_directImage_two (j := 𝟙 C)
    (F := adicConstant k₀ l C) ι (isLisse_adicConstant k₀ l C)
    (isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := C) (ι := ι))
  rw [zero_add] at h
  exact fun α hα ↦ h α (e.symm.hasEigenvalue hα)

variable [IsSeparated (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]

/-- The trace formula on a smooth geometrically connected affine curve `C₀`: since the compactly
supported cohomology is concentrated in degrees `1` and `2`,
`Z(C₀, T) det(1 - T F | H_c²) = det(1 - T F | H_c¹)` in `ℚ̄_ℓ⟦T⟧`. This is the trace-to-determinant
identity of a trace datum (`TraceDatum.zeta_mul_prod_even_eq_prod_odd`) formed by the groups
`H_c⁰, H_c¹, H_c²`, the first of which vanishes. -/
theorem map_zetaSeries_mul_charpolyRev_two_of_curve :
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (C ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (((adicConstant k₀ l C).compactlySupportedCohomology 2).frobeniusEnd.charpolyRev :
          PowerSeries (PadicAlgCl l)) =
      (((adicConstant k₀ l C).compactlySupportedCohomology 1).frobeniusEnd.charpolyRev :
        PowerSeries (PadicAlgCl l)) := by
  set H := (adicConstant k₀ l C).compactlySupportedCohomology
  have hvan (i : ℤ) (h1 : i ≠ 1) (h2 : i ≠ 2) : Subsingleton (H i).carrier :=
    subsingleton_compactlySupportedCohomology_adicConstant_of_curve k₀ l C h1 h2
  let D : TraceDatum.{0, u + 1} (PadicAlgCl l) 2 :=
    { V := fun i ↦ (H (i : ℕ)).carrier
      F := fun i ↦ (H (i : ℕ)).frobeniusEnd
      N := fun n ↦ ((C ↘ Spec (CommRingCat.of k₀)).pointCount n : ℤ)
      trace_eq := fun n hn ↦ by
        rw [Int.cast_natCast, pointCount_eq_finsum_trace_compactlySupportedCohomology k₀ l C hn,
          finsum_eq_sum_of_support_subset (s := (Finset.range 3).map Nat.castEmbedding) _ ?_,
          Finset.sum_map, Finset.sum_range]
        · refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Nat.castEmbedding_apply, Int.coe_negOnePow_natCast, zsmul_eq_mul]
          push_cast
          rfl
        · intro i hi
          by_contra h
          have hi' : i ≠ 1 ∧ i ≠ 2 := by
            constructor <;> rintro rfl <;> exact h (Finset.mem_map.2 ⟨_, Finset.mem_range.2
              (by norm_num : _ < 3), rfl⟩)
          have := hvan i hi'.1 hi'.2
          exact hi (by
            dsimp only
            rw [Subsingleton.elim ((H i).frobeniusEnd ^ n) 0, map_zero, smul_zero]) }
  have hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l))
      (C ↘ Spec (CommRingCat.of k₀)).zetaSeries = D.zeta := D.map_zetaSeries _ fun _ ↦ rfl
  have key := D.zeta_mul_prod_even_eq_prod_odd
  have he : Finset.univ.filter (fun i : Fin (2 + 1) ↦ Even (i : ℕ)) = {0, 2} := by decide
  have ho : Finset.univ.filter (fun i : Fin (2 + 1) ↦ Odd (i : ℕ)) = {1} := by decide
  rw [he, ho, Finset.prod_pair (by decide), Finset.prod_singleton] at key
  have hP0 : D.P 0 = 1 := by
    have : Subsingleton (D.V 0) := hvan 0 (by decide) (by decide)
    exact LinearMap.charpolyRev_of_subsingleton _
  rw [hP0, Polynomial.coe_one, one_mul, ← hZ] at key
  exact key

open _root_.Polynomial in
/-- On a smooth geometrically connected affine curve `C₀` whose zeta function is
`Z(C₀, T) = ∏_{c ∈ S} (1 - c T) / (1 - q T)`, with `S` a multiset of nonzero scalars of absolute
value different from `q` under some embedding `ι`, the Frobenius eigenvalues on `H_c²` and `H_c¹`
are `q` (once) and the elements of `S`: the eigenvalues on `H_c²` have absolute value `q` and
those on `H_c¹` at most `q^{1/2}`, so there is no cancellation in
`Z(C₀, T) det(1 - T F | H_c²) = det(1 - T F | H_c¹)`. -/
theorem charpoly_roots_compactlySupportedCohomology_of_curve {S : Multiset (PadicAlgCl l)}
    (ι : PadicAlgCl l →+* ℂ) (hS : ∀ c ∈ S, c ≠ 0 ∧ ‖ι c‖ ≠ Nat.card k₀)
    (hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (C ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        ((1 - Polynomial.C (Nat.card k₀ : PadicAlgCl l) * X : (PadicAlgCl l)[X]) :
          PowerSeries (PadicAlgCl l)) =
      ((S.map fun c ↦ 1 - Polynomial.C c * X).prod : (PadicAlgCl l)[X])) :
    ((adicConstant k₀ l C).compactlySupportedCohomology 2).frobeniusEnd.charpoly.roots =
        {(Nat.card k₀ : PadicAlgCl l)} ∧
      ((adicConstant k₀ l C).compactlySupportedCohomology 1).frobeniusEnd.charpoly.roots = S := by
  set H := (adicConstant k₀ l C).compactlySupportedCohomology
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  have hid := map_zetaSeries_mul_charpolyRev_two_of_curve k₀ l C
  have hpoly :
      (1 - Polynomial.C (Nat.card k₀ : PadicAlgCl l) * X) * (H 1).frobeniusEnd.charpolyRev =
      (S.map fun c ↦ 1 - Polynomial.C c * X).prod * (H 2).frobeniusEnd.charpolyRev := by
    refine Polynomial.coe_inj.1 ?_
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hid, ← hZ]
    ring
  refine LinearMap.charpoly_roots_eq_of_mul_charpolyRev_eq _ _
    (LinearEquiv.isUnit_det' (H 1).frobenius) (LinearEquiv.isUnit_det' (H 2).frobenius)
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (fun h0 ↦ (hS 0 h0).1 rfl) hpoly
    (fun x ↦ ‖ι x‖ = Nat.card k₀) (by simp) (fun α hα ↦ ?_) (fun α hα h ↦ ?_)
    (fun c hc ↦ (hS c hc).2)
  · have := isPureOfWeightOver_compactlySupportedCohomology_two_adicConstant k₀ l C ι α hα
    rw [this, div_self two_ne_zero, Real.rpow_one]
  · have := hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant k₀ l C ι 1 α hα
    rw [h, Int.cast_one] at this
    have h2 : (Nat.card k₀ : ℝ) ^ ((1 : ℝ) / 2) < Nat.card k₀ ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hq (by norm_num)
    rw [Real.rpow_one] at h2
    exact absurd this (not_le.2 h2)

end WeilSheaf

section Examples

open WeilSheaf

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]

open _root_.Polynomial in
/-- Blueprint `prose-12-31` (compactly supported cohomology of the affine line):
`H_c²(𝔸¹ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-1)` is a line on which the geometric Frobenius acts by `q`, and all
other `H_cⁱ(𝔸¹ ⊗ k̄, ℚ̄_ℓ)` vanish. With the trace formula this recovers `#𝔸¹(𝔽_{qⁿ}) = qⁿ` and
`Z(𝔸¹, T) = (1 - qT)⁻¹` (`AlgebraicGeometry.pointCount_affineLine`,
`AlgebraicGeometry.zetaSeries_affineLine`), from which it is derived. -/
theorem compactlySupportedCohomology_affineLine :
    (∀ i : ℤ, i ≠ 2 → Subsingleton
      ((adicConstant k l (affineLine k)).compactlySupportedCohomology i).carrier) ∧
    Module.finrank (PadicAlgCl l)
      ((adicConstant k l (affineLine k)).compactlySupportedCohomology 2).carrier = 1 ∧
    ((adicConstant k l (affineLine k)).compactlySupportedCohomology 2).frobeniusEnd =
      (Nat.card k : PadicAlgCl l) • 1 := by
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  have hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (affineLine k ↘ Spec (.of k)).zetaSeries *
      ((1 - C (Nat.card k : PadicAlgCl l) * X : (PadicAlgCl l)[X]) : PowerSeries (PadicAlgCl l)) =
      ((((0 : Multiset (PadicAlgCl l)).map fun c ↦ 1 - C c * X).prod : (PadicAlgCl l)[X])) := by
    have hc (n : ℕ) : ((n : (PadicAlgCl l)[X]) : PowerSeries (PadicAlgCl l)) = n :=
      map_natCast (Polynomial.coeToPowerSeries.ringHom (R := PadicAlgCl l)) n
    have := congrArg (PowerSeries.map (algebraMap ℚ (PadicAlgCl l))) (zetaSeries_affineLine k)
    simpa [hc] using this
  obtain ⟨h2, h1⟩ := WeilSheaf.charpoly_roots_compactlySupportedCohomology_of_curve k l
    (affineLine k) ι (by simp) hZ
  obtain ⟨hd2, hf2⟩ := LinearMap.finrank_eq_one_and_eq_smul_one_of_charpoly_roots_eq _ h2
  have hs1 := LinearMap.subsingleton_of_charpoly_roots_eq_zero _ h1
  refine ⟨fun i hi ↦ ?_, hd2, hf2⟩
  by_cases hi1 : i = 1
  · subst hi1
    exact hs1
  · exact WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_of_curve k l _ hi1 hi

open _root_.Polynomial in
/-- Blueprint `ex-weil-multiplicative-group` (compactly supported cohomology of the multiplicative
group): `H_c¹(𝔾_m ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` is a line on which the geometric Frobenius acts trivially,
`H_c²(𝔾_m ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-1)` is a line on which it acts by `q`, and all other
`H_cⁱ(𝔾_m ⊗ k̄, ℚ̄_ℓ)` vanish. With the trace formula this recovers `#𝔾_m(𝔽_{qⁿ}) = qⁿ - 1` and
`Z(𝔾_m, T) = (1 - T) / (1 - qT)` (`AlgebraicGeometry.pointCount_multiplicativeGroup`,
`AlgebraicGeometry.zetaSeries_multiplicativeGroup`), from which it is derived. -/
theorem compactlySupportedCohomology_multiplicativeGroup :
    (∀ i : ℤ, i ≠ 1 → i ≠ 2 → Subsingleton
      ((adicConstant k l (multiplicativeGroup k)).compactlySupportedCohomology i).carrier) ∧
    Module.finrank (PadicAlgCl l)
      ((adicConstant k l (multiplicativeGroup k)).compactlySupportedCohomology 1).carrier =
        1 ∧
    ((adicConstant k l (multiplicativeGroup k)).compactlySupportedCohomology 1).frobeniusEnd =
      1 ∧
    Module.finrank (PadicAlgCl l)
      ((adicConstant k l (multiplicativeGroup k)).compactlySupportedCohomology 2).carrier =
        1 ∧
    ((adicConstant k l (multiplicativeGroup k)).compactlySupportedCohomology 2).frobeniusEnd =
      (Nat.card k : PadicAlgCl l) • 1 := by
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  have hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l))
      (multiplicativeGroup k ↘ Spec (.of k)).zetaSeries *
      ((1 - C (Nat.card k : PadicAlgCl l) * X : (PadicAlgCl l)[X]) : PowerSeries (PadicAlgCl l)) =
      (((({1} : Multiset (PadicAlgCl l)).map fun c ↦ 1 - C c * X).prod : (PadicAlgCl l)[X])) := by
    have hc (n : ℕ) : ((n : (PadicAlgCl l)[X]) : PowerSeries (PadicAlgCl l)) = n :=
      map_natCast (Polynomial.coeToPowerSeries.ringHom (R := PadicAlgCl l)) n
    have := congrArg (PowerSeries.map (algebraMap ℚ (PadicAlgCl l)))
      (zetaSeries_multiplicativeGroup k)
    simpa [hc] using this
  have hq : (1 : ℝ) < Nat.card k := by exact_mod_cast Finite.one_lt_card
  obtain ⟨h2, h1⟩ := WeilSheaf.charpoly_roots_compactlySupportedCohomology_of_curve k l
    (multiplicativeGroup k) ι (fun c hc ↦ by
      rw [Multiset.mem_singleton] at hc
      subst hc
      exact ⟨one_ne_zero, by rw [map_one, norm_one]; exact hq.ne⟩) hZ
  obtain ⟨hd2, hf2⟩ := LinearMap.finrank_eq_one_and_eq_smul_one_of_charpoly_roots_eq _ h2
  obtain ⟨hd1, hf1⟩ := LinearMap.finrank_eq_one_and_eq_smul_one_of_charpoly_roots_eq _ h1
  exact ⟨fun i hi1 hi2 ↦
    WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_of_curve k l _ hi1 hi2, hd1,
    hf1.trans (one_smul _ _), hd2, hf2⟩

end Examples

end AlgebraicGeometry
