/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.EffectiveDivisorCount
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.ClosedPoints
public import WeilConjectures.EulerProduct
public import WeilConjectures.ZetaFunction.CurveFactorDegree

/-!
# The zeta function of a curve and the degree of its middle factor

For a scheme of finite type over a finite field `k` with `q` elements, the `n`-th coefficient of
the zeta function is the number of effective zero-cycles of degree `n`. For a smooth proper
integral curve `C` with `H⁰(C, 𝒪_C) = k` and genus `g`, these are the effective divisors of
degree `n`; grouping them by their class in `Pic(C)` and counting each class with Riemann–Roch
gives, for `n ≥ 2 g - 1`,

`(q - 1) Z_n = #{c ∈ Pic(C) | deg c = -n} · (q^{n + 1 - g} - 1)`,

where the number of classes is `h = #Pic⁰(C)` if `n` lies in the subgroup `δ ℤ` of degrees of
line bundles and `0` otherwise. With the Riemann hypothesis for the middle factor `P₁` of a Weil
factorization `Z = P₁ / ((1 - T) (1 - q T))` this forces `deg P₁ = 2 g`
(`AlgebraicGeometry.IsWeilFactorization.natDegree_eq_two_mul_of_coeff`). This is
F. K. Schmidt's argument; it gives Step 4 of the blueprint proof of
`corollary-point-count-estimates--2`, `dim H¹(C ⊗ k̄, ℚ̄_ℓ) = 2 g`, without `ℓ`-adic cohomology.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.coeff_zetaSeries_eq_natCard_closedPoints`: `Z_n` is the number of
  effective zero-cycles of degree `n`.
- `AlgebraicGeometry.Scheme.Divisor.sub_one_mul_card_effective_eq`: the count of effective
  divisors of degree `n ≥ 2 g - 1`.
- `AlgebraicGeometry.Scheme.natDegree_eq_two_mul_arithmeticGenus_of_isWeilFactorization`:
  `deg P₁ = 2 g`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

universe u

open CategoryTheory

variable {k : Type u} [Field k] [Finite k]

/-- **The zeta function counts effective zero-cycles.** For a scheme `X` of finite type over a
finite field `k`, the `n`-th coefficient of `Z(X, T)` is the number of effective zero-cycles
`∑ m_x [x]` of degree `∑ m_x [κ(x) : k] = n`. -/
theorem Hom.coeff_zetaSeries_eq_natCard {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    PowerSeries.coeff n f.zetaSeries =
      Nat.card {m : X.finitePoints →₀ ℕ // (m.sum fun x i ↦ i * f.degreeOver x.1) = n} := by
  rw [f.zetaSeries_eq_tprod]
  exact PowerSeries.coeff_tprod_inv_one_sub_X_pow_eq_natCard (fun x ↦ f.degreeOver_ne_zero x.2)
    f.finite_setOf_degreeOver_le n

/-- **The zeta function counts effective divisors of a given degree.** For a scheme `X` of
finite type over a finite field `k`, the `n`-th coefficient of `Z(X, T)` is the number of
`E : closedPoints X →₀ ℕ` with `∑_P E(P) [κ(P) : k] = n`. -/
theorem Hom.coeff_zetaSeries_eq_natCard_closedPoints {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    PowerSeries.coeff n f.zetaSeries =
      Nat.card {E : closedPoints X →₀ ℕ // (E.sum fun P i ↦ i * f.degreeOver P.1) = n} := by
  rw [f.coeff_zetaSeries_eq_natCard]
  congr 1
  let e : X.finitePoints ≃ closedPoints X :=
    Set.equivOfEq (f.finitePoints_eq_closedPoints)
  refine Nat.card_congr ((Finsupp.equivCongrLeft e).subtypeEquiv fun m ↦ ?_)
  rw [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _]
  rfl

/-- There are only finitely many effective divisors of a given degree on a scheme of finite type
over a finite field. -/
theorem Hom.finite_setOf_sum_degreeOver_eq {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    Finite {E : closedPoints X →₀ ℕ // (E.sum fun P i ↦ i * f.degreeOver P.1) = n} := by
  classical
  have hcl := f.finitePoints_eq_closedPoints
  have hmem {x : X} : x ∈ X.finitePoints ↔ x ∈ closedPoints X := by rw [hcl]
  set S : Set (closedPoints X) := {P | f.degreeOver P.1 ≤ n} with hS
  have hSfin : S.Finite := by
    have := (f.finite_setOf_degreeOver_le n).image (fun x ↦ (⟨x.1, hmem.1 x.2⟩ : closedPoints X))
    refine this.subset fun P hP ↦ ⟨⟨P.1, hmem.2 P.2⟩, hP, rfl⟩
  have : Finite S := hSfin
  -- an effective divisor of degree `n` is supported on `S` with multiplicities at most `n`
  have hbound (E : {E : closedPoints X →₀ ℕ // (E.sum fun P i ↦ i * f.degreeOver P.1) = n})
      (P : closedPoints X) (hP : E.1 P ≠ 0) : P ∈ S ∧ E.1 P ≤ n := by
    have hle : E.1 P * f.degreeOver P.1 ≤ n := by
      refine le_trans ?_ E.2.le
      exact Finset.single_le_sum (f := fun P ↦ E.1 P * f.degreeOver P.1)
        (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.2 hP)
    have hd : 1 ≤ f.degreeOver P.1 :=
      Nat.one_le_iff_ne_zero.2 (f.degreeOver_ne_zero (hmem.2 P.2))
    have h1 : 1 ≤ E.1 P := Nat.one_le_iff_ne_zero.2 hP
    exact ⟨by change f.degreeOver P.1 ≤ n; nlinarith, by nlinarith⟩
  refine Finite.of_injective (β := S → Fin (n + 1))
    (fun E P ↦ ⟨min (E.1 P) n, Nat.lt_succ_of_le (min_le_right _ _)⟩) fun E E' h ↦ ?_
  refine Subtype.ext (Finsupp.ext fun P ↦ ?_)
  by_cases hP : P ∈ S
  · have := congrArg (fun F ↦ (F ⟨P, hP⟩ : ℕ)) h
    simp only at this
    by_cases hE : E.1 P = 0
    · by_cases hE' : E'.1 P = 0
      · rw [hE, hE']
      · rw [hE, min_eq_left (hbound E' P hE').2] at this; simp at this; omega
    · rw [min_eq_left (hbound E P hE).2] at this
      by_cases hE' : E'.1 P = 0
      · rw [hE', Nat.zero_min] at this; exact absurd this hE
      · rwa [min_eq_left (hbound E' P hE').2] at this
  · rw [show E.1 P = 0 by by_contra h0; exact hP (hbound E P h0).1,
      show E'.1 P = 0 by by_contra h0; exact hP (hbound E' P h0).1]

section Curve

open MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))] [IsIntegral C]
  [GlobalSectionsBijective k C]

variable (k) in
/-- The class in `Pic(C)` of the ideal sheaf `𝒪_C(-E)` of an effective divisor `E`. -/
noncomputable def Divisor.idealSheafClass (E : closedPoints C →₀ ℕ) : C.Pic :=
  haveI := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E).isInvertible_toModules
  Pic.ofIsInvertible (Divisor.idealSheaf E).toModules

omit [Finite k] [IsIntegral C] [GlobalSectionsBijective k C] in
/-- The ideal sheaf `𝒪_C(-E)` has degree `-∑_P E(P) [κ(P) : k]`. -/
theorem Divisor.picDegreeHom_idealSheafClass (E : closedPoints C →₀ ℕ) :
    picDegreeHom k C (Divisor.idealSheafClass k E) =
      .ofAdd (-((E.sum fun P i ↦ i * (C ↘ Spec (.of k)).degreeOver P.1 : ℕ) : ℤ)) := by
  have hJ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E
  have := hJ.isInvertible_toModules
  have := hJ.isInvertible_dual_toModules
  rw [Divisor.idealSheafClass, picDegreeHom_ofIsInvertible]
  congr 1
  have h := Modules.degree_dual (k := k) (Divisor.idealSheaf E).toModules
  rw [hJ.degree_dual_toModules, Divisor.finrankΓ_subschemeι_idealSheaf] at h
  omega

/-- **The effective divisors in a class of large degree.** If `c ∈ Pic(C)` has degree `-n`
with `n ≥ 2 g - 1`, then the effective divisors `E` with `[𝒪_C(-E)] = c` number
`(q^{n + 1 - g} - 1) / (q - 1)`: they are the points of the complete linear system of a line
bundle of degree `n`, whose `h⁰` is `n + 1 - g` by Riemann–Roch. -/
theorem Divisor.sub_one_mul_card_idealSheafClass_eq (c : C.Pic) {n : ℕ}
    (hc : picDegreeHom k C c = .ofAdd (-(n : ℤ)))
    (hn : 2 * (arithmeticGenus k C : ℤ) - 1 ≤ n) :
    (Nat.card k - 1) * Nat.card {E : closedPoints C →₀ ℕ // Divisor.idealSheafClass k E = c} =
      Nat.card k ^ (n + 1 - arithmeticGenus k C) - 1 := by
  have := isNoetherian_of_locallyOfFiniteType (C ↘ Spec (.of k))
  set M := (fromSkeleton C.Modules).obj c.val with hM
  have hMc : Pic.ofIsInvertible M = c := Pic.ofIsInvertible_fromSkeleton c
  have e₁ : {E : closedPoints C →₀ ℕ // Divisor.idealSheafClass k E = c} ≃
      {E : closedPoints C →₀ ℕ // Nonempty ((Divisor.idealSheaf E).toModules ≅ M)} := by
    refine Equiv.subtypeEquivRight fun E ↦ ?_
    have := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E).isInvertible_toModules
    exact ⟨fun h ↦ Pic.nonempty_iso_of_ofIsInvertible_eq (h.trans hMc.symm),
      fun ⟨e⟩ ↦ (Pic.ofIsInvertible_eq_of_iso e).trans hMc⟩
  rw [Nat.card_congr e₁, Divisor.sub_one_mul_card_idealSheaf_iso M]
  congr 2
  -- `h⁰(Mᵛ) = n + 1 - g` by Riemann–Roch
  have hdeg : Mᵛ.degree k = n := by
    rw [Modules.degree_dual]
    have h := picDegreeHom_ofIsInvertible (k := k) M
    rw [hMc, hc] at h
    have := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd] at this
    omega
  have hRR := finrankH_zero_eq (k := k) Mᵛ (by rw [hdeg]; exact hn)
  rw [hdeg] at hRR
  omega

/-- **Counting effective divisors of large degree.** For `n ≥ 2 g - 1`, the classes of degree
`-n` in `Pic(C)` are finite in number, and the number `A_n` of effective divisors of degree `n`
satisfies `(q - 1) A_n = #{c ∈ Pic(C) | deg c = -n} · (q^{n + 1 - g} - 1)`. -/
theorem Divisor.sub_one_mul_card_effective_eq {n : ℕ} (hn : 2 * (arithmeticGenus k C : ℤ) - 1 ≤ n) :
    Finite {c : C.Pic // picDegreeHom k C c = .ofAdd (-(n : ℤ))} ∧
    (Nat.card k - 1) * Nat.card {E : closedPoints C →₀ ℕ //
        (E.sum fun P i ↦ i * (C ↘ Spec (.of k)).degreeOver P.1) = n} =
      Nat.card {c : C.Pic // picDegreeHom k C c = .ofAdd (-(n : ℤ))} *
        (Nat.card k ^ (n + 1 - arithmeticGenus k C) - 1) := by
  classical
  set g := arithmeticGenus k C
  set q := Nat.card k
  have hq : 2 ≤ q := Finite.one_lt_card
  set D := {E : closedPoints C →₀ ℕ // (E.sum fun P i ↦ i * (C ↘ Spec (.of k)).degreeOver P.1) = n}
  set Pn := {c : C.Pic // picDegreeHom k C c = .ofAdd (-(n : ℤ))}
  have hD : Finite D := Hom.finite_setOf_sum_degreeOver_eq (C ↘ Spec (.of k)) n
  have hpos : 0 < q ^ (n + 1 - g) - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))
  let F : D → Pn := fun E ↦ ⟨Divisor.idealSheafClass k E.1, by
    rw [Divisor.picDegreeHom_idealSheafClass, E.2]⟩
  -- every class of degree `-n` contains an effective divisor
  have hsurj : Function.Surjective F := by
    intro c
    have h := Divisor.sub_one_mul_card_idealSheafClass_eq c.1 c.2 hn
    have hne : Nat.card {E : closedPoints C →₀ ℕ // Divisor.idealSheafClass k E = c.1} ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h
      exact hpos.ne' h.symm
    obtain ⟨E, hE⟩ := (Nat.card_ne_zero.1 hne).1
    have hdeg := Divisor.picDegreeHom_idealSheafClass (k := k) E
    rw [hE, c.2] at hdeg
    have := congrArg Multiplicative.toAdd hdeg
    simp only [toAdd_ofAdd, neg_inj, Nat.cast_inj] at this
    exact ⟨⟨E, this.symm⟩, Subtype.ext hE⟩
  have hPn : Finite Pn := Finite.of_surjective F hsurj
  refine ⟨hPn, ?_⟩
  have := Fintype.ofFinite Pn
  -- the fibre of `F` over a class `c` is the set of effective divisors in `c`
  have hfib (c : Pn) : {E : D // F E = c} ≃
      {E : closedPoints C →₀ ℕ // Divisor.idealSheafClass k E = c.1} :=
    { toFun E := ⟨E.1.1, congrArg Subtype.val E.2⟩
      invFun E := ⟨⟨E.1, by
          have hdeg := Divisor.picDegreeHom_idealSheafClass (k := k) E.1
          rw [E.2, c.2] at hdeg
          have := congrArg Multiplicative.toAdd hdeg
          simp only [toAdd_ofAdd, neg_inj, Nat.cast_inj] at this
          exact this.symm⟩, Subtype.ext E.2⟩
      left_inv E := rfl
      right_inv E := rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ ↦ by
    rw [Nat.card_congr (hfib c), Divisor.sub_one_mul_card_idealSheafClass_eq c.1 c.2 hn]]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card (α := Pn)]

/-- **The degree of the middle Weil factor of a curve is twice the genus** (F. K. Schmidt). Let
`C` be a smooth proper integral curve over a finite field `k` with `H⁰(C, 𝒪_C) = k`, of genus
`g = h¹(C, 𝒪_C)`. If its zeta function has a Weil factorization `Z = P₁ / ((1 - T) (1 - q T))`
whose middle factor satisfies the Riemann hypothesis, then `deg P₁ = 2 g`.

By Riemann–Roch the number `A_n` of effective divisors of degree `n ≥ 2 g - 1` is
`h (q^{n + 1 - g} - 1) / (q - 1)` if `n` lies in the subgroup `δ ℤ` of degrees of line bundles,
where `h = #Pic⁰(C)`, and `0` otherwise; and `A_n` is the `n`-th coefficient of `Z`. The
arithmetic of `IsWeilFactorization.natDegree_eq_two_mul_of_coeff` concludes. -/
theorem natDegree_eq_two_mul_arithmeticGenus_of_isWeilFactorization
    {P : Fin (2 * 1 + 1) → Polynomial ℤ}
    (hfact : IsWeilFactorization (Nat.card k) 1 (C ↘ Spec (.of k)).zetaSeries P)
    (hrh : WeilRiemannHypothesis (Nat.card k) 1 P) :
    (P 1).natDegree = 2 * arithmeticGenus k C := by
  classical
  set g := arithmeticGenus k C
  set q := Nat.card k
  have hq : 1 < q := Finite.one_lt_card
  -- the subgroup `δ ℤ` of degrees of line bundles
  let H : AddSubgroup ℤ :=
    { carrier := {m | ∃ c : C.Pic, picDegreeHom k C c = .ofAdd m}
      add_mem' := by
        rintro _ _ ⟨c, hc⟩ ⟨d, hd⟩
        exact ⟨c * d, by rw [map_mul, hc, hd]; rfl⟩
      zero_mem' := ⟨1, by rw [map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨c, hc⟩
        exact ⟨c⁻¹, by rw [map_inv, hc]; rfl⟩ }
  obtain ⟨a, ha⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp H.isAddCyclic
  set δ := a.natAbs
  have hmem (m : ℤ) : (∃ c : C.Pic, picDegreeHom k C c = .ofAdd m) ↔ (δ : ℤ) ∣ m := by
    change m ∈ H ↔ _
    rw [← ha, Int.mem_zmultiples_iff, Int.natAbs_dvd]
  -- `δ > 0`: a closed point has positive degree
  have hδ : 0 < δ := by
    obtain ⟨x, hx⟩ := (C ↘ Spec (.of k)).exists_mem_finitePoints
    have hcl : x ∈ closedPoints C := by
      rwa [← (C ↘ Spec (.of k)).finitePoints_eq_closedPoints]
    have h1 := Divisor.picDegreeHom_idealSheafClass (k := k) (Finsupp.single ⟨x, hcl⟩ 1)
    rw [Finsupp.sum_single_index (zero_mul _), one_mul] at h1
    have hd0 := (C ↘ Spec (.of k)).degreeOver_ne_zero hx
    obtain ⟨b, hb⟩ := (hmem _).1 ⟨_, h1⟩
    by_contra h0
    rw [show δ = 0 by omega, Nat.cast_zero, zero_mul, neg_eq_zero, Nat.cast_eq_zero] at hb
    exact hd0 hb
  -- all fibres of the degree over `δ ℤ` have the cardinality `h` of `Pic⁰(C)`
  have hfibre (m : ℤ) (c₀ : C.Pic) (hc₀ : picDegreeHom k C c₀ = .ofAdd m) :
      {c : C.Pic // picDegreeHom k C c = .ofAdd m} ≃
        {c : C.Pic // picDegreeHom k C c = .ofAdd 0} :=
    { toFun c := ⟨c.1 * c₀⁻¹, by rw [map_mul, map_inv, c.2, hc₀, mul_inv_cancel, ofAdd_zero]⟩
      invFun c := ⟨c.1 * c₀, by rw [map_mul, c.2, hc₀, ofAdd_zero, one_mul]⟩
      left_inv c := Subtype.ext (inv_mul_cancel_right c.1 c₀)
      right_inv c := Subtype.ext (mul_inv_cancel_right c.1 c₀) }
  set h := Nat.card {c : C.Pic // picDegreeHom k C c = .ofAdd 0}
  have hcard (n : ℕ) (hn : 2 * g ≤ n) :
      Nat.card {c : C.Pic // picDegreeHom k C c = .ofAdd (-(n : ℤ))} = if δ ∣ n then h else 0 := by
    split_ifs with hdvd
    · obtain ⟨c₀, hc₀⟩ := (hmem (-(n : ℤ))).2 (by rw [dvd_neg]; exact_mod_cast hdvd)
      exact Nat.card_congr (hfibre _ c₀ hc₀)
    · refine Nat.card_eq_zero.2 (Or.inl ⟨fun c ↦ hdvd ?_⟩)
      have := (hmem (-(n : ℤ))).1 ⟨c.1, c.2⟩
      rw [dvd_neg] at this
      exact_mod_cast this
  -- `Pic⁰(C)` is finite and nonempty
  have hh : 0 < h := by
    set n := δ * (2 * g + 1)
    have hn : 2 * g ≤ n := by
      have : 2 * g + 1 ≤ δ * (2 * g + 1) := Nat.le_mul_of_pos_left _ hδ
      omega
    obtain ⟨hfin, -⟩ := Divisor.sub_one_mul_card_effective_eq (k := k) (C := C) (n := n) (by omega)
    obtain ⟨c₀, hc₀⟩ := (hmem (-(n : ℤ))).2 (by rw [dvd_neg]; exact_mod_cast dvd_mul_right δ _)
    have : Finite {c : C.Pic // picDegreeHom k C c = .ofAdd 0} :=
      Finite.of_equiv _ (hfibre _ c₀ hc₀)
    have : Nonempty {c : C.Pic // picDegreeHom k C c = .ofAdd 0} :=
      ⟨⟨1, by rw [map_one, ofAdd_zero]⟩⟩
    exact Nat.card_pos
  -- the coefficients of the zeta function
  have hcoeff (n : ℕ) (hn : 2 * g ≤ n) :
      ((q : ℚ) - 1) * PowerSeries.coeff n (C ↘ Spec (.of k)).zetaSeries =
        if δ ∣ n then (h : ℚ) * ((q : ℚ) ^ (n + 1 - g) - 1) else 0 := by
    obtain ⟨-, hcount⟩ :=
      Divisor.sub_one_mul_card_effective_eq (k := k) (C := C) (n := n) (by omega)
    rw [hcard n hn] at hcount
    rw [Hom.coeff_zetaSeries_eq_natCard_closedPoints]
    have h1 : ((q - 1 : ℕ) : ℚ) = q - 1 := by rw [Nat.cast_sub hq.le, Nat.cast_one]
    have h2 : ((q ^ (n + 1 - g) - 1 : ℕ) : ℚ) = (q : ℚ) ^ (n + 1 - g) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
    have := congrArg (Nat.cast : ℕ → ℚ) hcount
    rw [Nat.cast_mul, Nat.cast_mul, h1, h2] at this
    rw [this]
    split_ifs <;> simp
  exact IsWeilFactorization.natDegree_eq_two_mul_of_coeff hfact hrh hq hδ
    (by exact_mod_cast hh) hcoeff

end Curve

end AlgebraicGeometry.Scheme
