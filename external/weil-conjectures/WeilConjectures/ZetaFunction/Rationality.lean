/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaIntegrality
public import WeilConjectures.ZetaLinearAlgebra.Rationality

/-!
# Rationality of the zeta function

Let `X₀` be a scheme of finite type over the finite field `k₀ = 𝔽_q`. Then its zeta series
`Z(X₀, T)` is a rational function: `B(T) Z(X₀, T) = A(T)` for integer polynomials `A, B` with
`B(0) = 1` (blueprint `corollary-point-counting-zeta-function--7`).

For `X₀` separated, the Grothendieck–Lefschetz trace formula with compact supports
(`AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology`) writes
the point counts as alternating traces on the finitely many nonzero groups
`H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)`, so `Z(X₀, T)` is an alternating product of determinants over `ℚ̄_ℓ`; its
coefficients are integers by the Euler product, and the Hankel rank criterion descends
rationality from `ℚ̄_ℓ` to `ℚ` (`AlgebraicGeometry.Scheme.Hom.zetaSeries_rational_of_traceDatum`).
A general `X₀` of finite type is a finite union of affine opens. For opens `W, U` of `X₀` the
point counts satisfy the inclusion-exclusion `N(W ∪ U) + N(W ∩ U) = N(W) + N(U)`, so
`Z(W ∪ U) Z(W ∩ U) = Z(W) Z(U)`; if `U` is affine then `U` and `W ∩ U` are separated, and
rationality propagates to `W ∪ U`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.zetaSeries_mul_zetaSeries_eq`: multiplicativity of the zeta
  series with respect to additive relations between point counts.
- `AlgebraicGeometry.Scheme.Hom.pointCount_sup_add_pointCount_inf`: inclusion-exclusion for the
  point counts of open subschemes.
- `AlgebraicGeometry.Scheme.Hom.exists_int_mul_zetaSeries_eq_of_isSeparated`: rationality of the
  zeta series in the separated case, via the trace formula.
- `AlgebraicGeometry.Scheme.Hom.exists_int_mul_zetaSeries_eq`: rationality of the zeta series of
  a scheme of finite type over a finite field (`corollary-point-counting-zeta-function--7`).
- `AlgebraicGeometry.Scheme.Hom.finiteDimensional_shiftSpan_zetaSeries_and_exists_rat`
  (`corollary-point-counting-zeta-function--7`) and
  `AlgebraicGeometry.Scheme.Hom.exists_int_zetaSeries_and_exists_rat_mul_eq`
  (`prose-19-06`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

section Multiplicativity

/-- The zeta series only depends on the point counts in positive degrees. -/
theorem Hom.zetaSeries_congr {Y Y' : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (g' : Y' ⟶ Spec (.of k)) (h : ∀ n, n ≠ 0 → g.pointCount n = g'.pointCount n) :
    g.zetaSeries = g'.zetaSeries := by
  unfold Hom.zetaSeries
  congr 2
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, h n hn]

/-- The logarithmic derivative of a product of two zeta series is the generating series of the
sums of the point counts. -/
private lemma X_mul_derivative_zetaSeries_mul {Y Y' : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (g' : Y' ⟶ Spec (.of k)) :
    PowerSeries.X * PowerSeries.derivative (R := ℚ) (g.zetaSeries * g'.zetaSeries) =
      PowerSeries.mk (fun n ↦ if n = 0 then (0 : ℚ) else
        ((g.pointCount n + g'.pointCount n : ℕ) : ℚ)) * (g.zetaSeries * g'.zetaSeries) := by
  have hs : PowerSeries.mk (fun n ↦ if n = 0 then (0 : ℚ) else
      ((g.pointCount n + g'.pointCount n : ℕ) : ℚ)) =
      PowerSeries.mk (fun n ↦ if n = 0 then (0 : ℚ) else g.pointCount n) +
        PowerSeries.mk (fun n ↦ if n = 0 then (0 : ℚ) else g'.pointCount n) := by
    ext n
    by_cases hn : n = 0 <;> simp [hn]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hs]
  linear_combination g'.zetaSeries * g.X_mul_derivative_zetaSeries +
    g.zetaSeries * g'.X_mul_derivative_zetaSeries

/-- **Multiplicativity of the zeta series**: if the point counts satisfy
`N₁ + N₂ = N₃ + N₄` in every positive degree, then `Z₁ Z₂ = Z₃ Z₄`. -/
theorem Hom.zetaSeries_mul_zetaSeries_eq {Y₁ Y₂ Y₃ Y₄ : Scheme.{u}} (g₁ : Y₁ ⟶ Spec (.of k))
    (g₂ : Y₂ ⟶ Spec (.of k)) (g₃ : Y₃ ⟶ Spec (.of k)) (g₄ : Y₄ ⟶ Spec (.of k))
    (h : ∀ n, n ≠ 0 →
      g₁.pointCount n + g₂.pointCount n = g₃.pointCount n + g₄.pointCount n) :
    g₁.zetaSeries * g₂.zetaSeries = g₃.zetaSeries * g₄.zetaSeries := by
  have h₁₂ := X_mul_derivative_zetaSeries_mul g₁ g₂
  have h₃₄ := X_mul_derivative_zetaSeries_mul g₃ g₄
  have hfun : (fun n ↦ if n = 0 then (0 : ℚ) else
      ((g₁.pointCount n + g₂.pointCount n : ℕ) : ℚ)) = fun n ↦ if n = 0 then (0 : ℚ) else
      ((g₃.pointCount n + g₄.pointCount n : ℕ) : ℚ) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ite_false, h n hn]
  rw [hfun] at h₁₂
  have hconst : PowerSeries.constantCoeff (g₁.zetaSeries * g₂.zetaSeries) =
      PowerSeries.constantCoeff (g₃.zetaSeries * g₄.zetaSeries) := by
    simp [Hom.constantCoeff_zetaSeries]
  ext n
  exact PowerSeries.coeff_eq_of_X_mul_derivative_eq h₁₂ h₃₄ hconst (by simp) (m := n)
    (fun _ _ ↦ rfl) n le_rfl

end Multiplicativity

section Opens

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The `K`-points of an open subscheme `W ⊆ X` are the `K`-points of `X` whose (unique) point
lies in `W`. -/
noncomputable def Hom.fieldPointsOpensEquiv (W : X.Opens) (K : Type u) [Field K]
    [Algebra k K] :
    (W.ι ≫ f).fieldPoints K ≃ {g : f.fieldPoints K // g.1 default ∈ W} where
  toFun h := ⟨⟨h.1 ≫ W.ι, by rw [Category.assoc]; exact h.2⟩, by
    have : W.ι (h.1 default) ∈ Set.range W.ι := ⟨_, rfl⟩
    rw [Opens.range_ι] at this
    exact this⟩
  invFun g := ⟨IsOpenImmersion.lift W.ι g.1.1 (by
      rintro - ⟨y, rfl⟩
      rw [Unique.eq_default y, Opens.range_ι]
      exact g.2), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact g.1.2⟩
  left_inv h := Subtype.ext <| by
    rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac]
  right_inv g := Subtype.ext <| Subtype.ext <| IsOpenImmersion.lift_fac _ _ _

/-- The point counts of an open subscheme `W ⊆ X`, as the number of points of `X` lying in
`W`. -/
theorem Hom.pointCount_opens_ι_comp (W : X.Opens) (n : ℕ) :
    (W.ι ≫ f).pointCount n =
      {g : f.fieldPoints (FiniteField.galoisExtension k n) | g.1 default ∈ W}.ncard := by
  rw [Hom.pointCount, Nat.card_congr (f.fieldPointsOpensEquiv W _)]
  rfl

/-- The point counts of the open subscheme `⊤` are those of `X`. -/
theorem Hom.pointCount_top_ι_comp (n : ℕ) :
    ((⊤ : X.Opens).ι ≫ f).pointCount n = f.pointCount n := by
  rw [Hom.pointCount_opens_ι_comp, Hom.pointCount, ← Set.ncard_univ]
  congr 1

/-- **Inclusion-exclusion for point counts** of open subschemes:
`N(W ∪ U) + N(W ∩ U) = N(W) + N(U)`. -/
theorem Hom.pointCount_sup_add_pointCount_inf [Finite k] [QuasiCompact f]
    [LocallyOfFiniteType f] (W U : X.Opens) (n : ℕ) :
    ((W ⊔ U).ι ≫ f).pointCount n + ((W ⊓ U).ι ≫ f).pointCount n =
      (W.ι ≫ f).pointCount n + (U.ι ≫ f).pointCount n := by
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  have := f.finite_fieldPoints (FiniteField.galoisExtension k n)
  simp only [Hom.pointCount_opens_ι_comp]
  rw [← Set.ncard_union_add_ncard_inter
    {g : f.fieldPoints (FiniteField.galoisExtension k n) | g.1 default ∈ W}
    {g | g.1 default ∈ U}]
  congr 2

end Opens

/-- A power series over `ℚ` is a normalized fraction of integer polynomials. -/
private def IsIntFraction (Z : PowerSeries ℚ) : Prop :=
  ∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
    Z * (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
      (A.map (Int.castRingHom ℚ) : PowerSeries ℚ)

/-- If `Z₁ Z₂ = Z₃ Z₄` with `Z₂, Z₃, Z₄` normalized integer fractions and `Z₂(0) = 1`, then `Z₁`
is a normalized integer fraction. -/
private lemma IsIntFraction.of_mul_eq {Z₁ Z₂ Z₃ Z₄ : PowerSeries ℚ} (h : Z₁ * Z₂ = Z₃ * Z₄)
    (h₂ : PowerSeries.constantCoeff Z₂ = 1) (r₂ : IsIntFraction Z₂) (r₃ : IsIntFraction Z₃)
    (r₄ : IsIntFraction Z₄) : IsIntFraction Z₁ := by
  obtain ⟨A₂, B₂, hB₂, hA₂⟩ := r₂
  obtain ⟨A₃, B₃, hB₃, hA₃⟩ := r₃
  obtain ⟨A₄, B₄, hB₄, hA₄⟩ := r₄
  have hA₂0 : A₂.coeff 0 = 1 := by
    have hc := congrArg PowerSeries.constantCoeff hA₂
    rw [map_mul, h₂, one_mul, Polynomial.constantCoeff_coe, Polynomial.constantCoeff_coe,
      Polynomial.coeff_map, Polynomial.coeff_map, hB₂] at hc
    simpa using hc.symm
  refine ⟨A₃ * A₄ * B₂, A₂ * B₃ * B₄, by simp [Polynomial.mul_coeff_zero, hA₂0, hB₃, hB₄], ?_⟩
  simp only [Polynomial.map_mul, Polynomial.coe_mul]
  set a₂ : PowerSeries ℚ := (A₂.map (Int.castRingHom ℚ) : PowerSeries ℚ)
  set a₃ : PowerSeries ℚ := (A₃.map (Int.castRingHom ℚ) : PowerSeries ℚ)
  set a₄ : PowerSeries ℚ := (A₄.map (Int.castRingHom ℚ) : PowerSeries ℚ)
  set b₂ : PowerSeries ℚ := (B₂.map (Int.castRingHom ℚ) : PowerSeries ℚ)
  set b₃ : PowerSeries ℚ := (B₃.map (Int.castRingHom ℚ) : PowerSeries ℚ)
  set b₄ : PowerSeries ℚ := (B₄.map (Int.castRingHom ℚ) : PowerSeries ℚ)
  linear_combination (b₂ * b₃ * b₄) * h + (Z₄ * b₄ * b₂) * hA₃ + (a₃ * b₂) * hA₄ -
    (Z₁ * b₃ * b₄) * hA₂

/-- An open subscheme of an affine open is separated over the base. -/
private lemma isSeparated_ι_comp {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {V U : X.Opens}
    (hU : IsAffineOpen U) (hVU : V ≤ U) : IsSeparated (V.ι ≫ f) := by
  have : IsAffine U := hU
  have : IsSeparated (U.ι ≫ f) := IsSeparated.of_isAffineHom _
  rw [← X.homOfLE_ι hVU, Category.assoc]
  infer_instance

variable [Finite k]

/-- Rationality of the zeta series of a **separated** scheme of finite type over a finite field
`k`, via the Grothendieck–Lefschetz trace formula with compact supports for a prime
`ℓ ≠ char k`: the point counts are the alternating traces of Frobenius on the finitely many
nonzero groups `H_c^i(X ⊗ k̄, ℚ̄_ℓ)`, which form a trace datum
(`AlgebraicGeometry.Scheme.Hom.zetaSeries_rational_of_traceDatum`). -/
theorem Hom.exists_int_mul_zetaSeries_eq_of_isSeparated {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
      g.zetaSeries * (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (A.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  have : Fact l.Prime := ⟨hlp⟩
  have : Fact (ringChar k ≠ l) := ⟨by omega⟩
  let : Y.Over (Spec (.of k)) := ⟨g⟩
  have : IsSeparated (Y ↘ Spec (.of k)) := ‹IsSeparated g›
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType g›
  have : QuasiCompact (Y ↘ Spec (.of k)) := ‹QuasiCompact g›
  let H : ℤ → FrobeniusModule (PadicAlgCl l) := fun i ↦
    (WeilSheaf.adicConstant k l Y).compactlySupportedCohomology i
  obtain ⟨a, b, hab⟩ := WeilComplex.exists_subsingleton_compactlySupportedCohomology
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k l Y))
  set a₀ : ℤ := 2 * (a / 2) with ha₀
  have ha₀a : a₀ ≤ a := by omega
  have hev : Even a₀ := ⟨a / 2, by omega⟩
  set r : ℕ := (b - a₀).toNat with hr
  have hbr : b ≤ a₀ + r := by omega
  have hzero : ∀ (i : ℤ) (n : ℕ), (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
      ((H i).frobeniusEnd ^ n) ≠ 0 → a₀ ≤ i ∧ i ≤ a₀ + r := by
    intro i n h
    by_contra hi
    have : Subsingleton (H i).carrier := hab i (by omega)
    apply h
    rw [Subsingleton.elim ((H i).frobeniusEnd ^ n) 0, map_zero, smul_zero]
  let D : TraceDatum (PadicAlgCl l) r :=
    { V := fun j ↦ (H (a₀ + (j : ℕ))).carrier
      F := fun j ↦ (H (a₀ + (j : ℕ))).frobeniusEnd
      N := fun n ↦ (g.pointCount n : ℤ)
      trace_eq := fun n hn ↦ by
        have h := WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology k l Y hn
        rw [Int.cast_natCast]
        refine h.trans ?_
        rw [finsum_eq_sum_of_support_subset
          (s := Finset.univ.image fun j : Fin (r + 1) ↦ a₀ + (j : ℕ)) _ ?_]
        · rw [Finset.sum_image fun j _ j' _ hjj' ↦ Fin.ext (by simpa using hjj')]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Int.negOnePow_add, Int.negOnePow_even _ hev, one_mul,
            Int.coe_negOnePow_natCast, zsmul_eq_mul]
          push_cast
          rfl
        · intro i hi
          obtain ⟨h₁, h₂⟩ := hzero i n hi
          simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
          exact ⟨⟨(i - a₀).toNat, by omega⟩, by simp; omega⟩ }
  exact Hom.zetaSeries_rational_of_traceDatum g D fun n ↦ rfl

/-- Blueprint `corollary-point-counting-zeta-function--7` (rationality of the zeta series): for a
scheme `X₀` of finite type (quasi-compact and locally of finite type) over a finite field `k`, there
are integer polynomials `A, B` with `B(0) = 1` and `B(T) Z(X₀, T) = A(T)` in `ℚ⟦T⟧`.

The separated case is `Hom.exists_int_mul_zetaSeries_eq_of_isSeparated`; in general `X₀` is a
finite union of affine opens, and the zeta series is multiplicative for the inclusion-exclusion
`N(W ∪ U) + N(W ∩ U) = N(W) + N(U)` of point counts of opens, where `U` is affine and `W ∩ U`
is separated as an open subscheme of `U`. -/
theorem Hom.exists_int_mul_zetaSeries_eq {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
      f.zetaSeries * (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (A.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hsep : ∀ {V U : X.Opens}, IsAffineOpen U → V ≤ U →
      IsIntFraction (V.ι ≫ f).zetaSeries := fun hU hVU ↦ by
    have := isSeparated_ι_comp f hU hVU
    exact Hom.exists_int_mul_zetaSeries_eq_of_isSeparated _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have : Fintype 𝒰.I₀ := inferInstanceAs (Fintype X.affineCover.finiteSubcover.I₀)
  have : ∀ i, IsAffine (𝒰.X i) := fun i ↦ inferInstanceAs (IsAffine (X.affineCover.X _))
  have key : ∀ s : Finset 𝒰.I₀,
      IsIntFraction ((⨆ i ∈ s, (𝒰.f i).opensRange).ι ≫ f).zetaSeries := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      rw [show (⨆ i ∈ (∅ : Finset 𝒰.I₀), (𝒰.f i).opensRange) = ⊥ by simp]
      exact hsep (isAffineOpen_bot X) le_rfl
    | insert a s ha ih =>
      rw [Finset.iSup_insert]
      have hU := isAffineOpen_opensRange (𝒰.f a)
      exact IsIntFraction.of_mul_eq (Hom.zetaSeries_mul_zetaSeries_eq _ _ _ _
        fun n _ ↦ f.pointCount_sup_add_pointCount_inf _ _ n) (Hom.constantCoeff_zetaSeries _)
        (hsep hU inf_le_left) (hsep hU le_rfl) ih
  have htop : (⨆ i ∈ (Finset.univ : Finset 𝒰.I₀), (𝒰.f i).opensRange) = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    simp only [Finset.mem_univ, iSup_pos, TopologicalSpace.Opens.mem_iSup]
    exact ⟨𝒰.idx x, 𝒰.covers x⟩
  have h := key Finset.univ
  rw [htop, Hom.zetaSeries_congr _ f fun n _ ↦ f.pointCount_top_ι_comp n] at h
  exact h

/-- Blueprint `corollary-point-counting-zeta-function--7` (rational descent of the zeta series): the
zeta series `Z(X₀, T) = ∑ zₙ Tⁿ` of a scheme `X₀` of finite type over a finite field has a Hankel
matrix of finite rank over `ℚ`, i.e. the span of the shifts of its coefficient sequence is
finite-dimensional, and `Z(X₀, T) ∈ ℚ(T)`, i.e. `B(T) Z(X₀, T) = A(T)` for rational polynomials
with `B(0) = 1`.

The blueprint states this for `X₀` smooth, proper and geometrically connected, assuming the
Euler product, the trace-to-determinant identity and the finiteness of the Hankel rank; these
hypotheses are theorems here and the statement holds for any `X₀` of finite type. -/
theorem Hom.finiteDimensional_shiftSpan_zetaSeries_and_exists_rat {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    FiniteDimensional ℚ (shiftSpan ℚ fun n ↦ PowerSeries.coeff n f.zetaSeries) ∧
      ∃ A B : Polynomial ℚ, B.coeff 0 = 1 ∧
        f.zetaSeries * (B : PowerSeries ℚ) = (A : PowerSeries ℚ) := by
  have h : ∃ A B : Polynomial ℚ, B.coeff 0 = 1 ∧
      f.zetaSeries * (B : PowerSeries ℚ) = (A : PowerSeries ℚ) := by
    obtain ⟨A, B, hB, hAB⟩ := f.exists_int_mul_zetaSeries_eq
    exact ⟨A.map (Int.castRingHom ℚ), B.map (Int.castRingHom ℚ), by simp [hB], hAB⟩
  exact ⟨(PowerSeries.exists_normalized_fraction_iff_finiteDimensional_shiftSpan _).1 h, h⟩

/-- Blueprint `prose-19-06` (the zeta series is integral and rational): the
zeta series of a scheme `X₀` of finite type over a finite field lies in
`(1 + T ℤ⟦T⟧) ∩ ℚ(T)`.

The blueprint states this in the situation of `corollary-point-counting-zeta-function--7` (`X₀`
smooth, proper and geometrically connected); it holds for any `X₀` of finite type. -/
theorem Hom.exists_int_zetaSeries_and_exists_rat_mul_eq {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    (∃ Z : PowerSeries ℤ, PowerSeries.constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries) ∧
      ∃ A B : Polynomial ℚ, B.coeff 0 = 1 ∧
        f.zetaSeries * (B : PowerSeries ℚ) = (A : PowerSeries ℚ) := by
  obtain ⟨Z, hZ⟩ := f.exists_int_zetaSeries
  exact ⟨⟨Z, f.constantCoeff_of_map_eq_zetaSeries hZ, hZ⟩,
    (f.finiteDimensional_shiftSpan_zetaSeries_and_exists_rat).2⟩

end AlgebraicGeometry.Scheme
