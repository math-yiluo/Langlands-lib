/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow

/-!

# Tame extensions of a henselian discrete valuation ring and pro-`p` Galois groups

Let `R` be a henselian discrete valuation ring with separably closed residue field `k`,
fraction field `F` and uniformizer `π`. A finite separable extension `L` of `F` of degree `d`
invertible in `k` is totally ramified, so contains a `d`-th root `ρ` of `π`
(`IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`); since `Xᵈ - π` is
irreducible over `F` (Eisenstein), `L = F(ρ)`.

Consequently (`IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem`), if `p` is a prime such
that every natural number vanishing in `k` is divisible by `p`, `Ω` is an algebraic closure of
`F` and `L ⊆ Ω` is an intermediate field containing all roots `ρ` of `π` of order invertible
in `k`, then `Gal(M / L)` is a `p`-group for every finite Galois extension `M / L` in `Ω`: this is
the Sylow argument `IntermediateField.isPGroup_of_forall_mem`.

This generalises the `K⟦X⟧`-specific results of
`WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow`.

## Main statements

- `IsDiscreteValuationRing.irreducible_X_pow_sub_C_algebraMap`: `Xᵈ - π` is irreducible over `F`.
- `IsDiscreteValuationRing.exists_pow_eq_algebraMap_and_mem_adjoin`: a separable element `γ`
  of degree `d` invertible in `k` lies in `F(ρ)` for some `d`-th root `ρ` of `π`.
- `IntermediateField.isPGroup_of_forall_mem_range`: the Sylow argument
  `IntermediateField.isPGroup_of_forall_mem` over a field `L` which is not an intermediate field.
- `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem`: the pro-`p` statement, and its variant
  `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem'` for an arbitrary field `L ⟶ Ω`.
- `IsDiscreteValuationRing.exists_finrank_eq_pow_of_forall_pow_eq_mem`: finite Galois
  subextensions of `E / L` have `p`-power degree.

-/

@[expose] public section

open Polynomial IntermediateField Module IsLocalRing

universe u

/-- **Pro-`p` Galois groups by a Sylow argument**, for a base field `L` which is not an
intermediate field: let `Ω` be an algebraic closure of `F`, `p` a prime and `F ⟶ L ⟶ Ω` a tower
such that `L` contains every element of `Ω` separable over `F` of degree prime to `p`. Then every
finite Galois extension `M` of `L` in `Ω` has a `p`-group as Galois group. This is
`IntermediateField.isPGroup_of_forall_mem` with the same proof. -/
theorem IntermediateField.isPGroup_of_forall_mem_range {F L Ω : Type*} [Field F] [Field L]
    [Field Ω] [Algebra F L] [Algebra L Ω] [Algebra F Ω] [IsScalarTower F L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] {p : ℕ} [Fact p.Prime]
    (H : ∀ γ : Ω, IsSeparable F γ → ¬ p ∣ (minpoly F γ).natDegree → γ ∈ (algebraMap L Ω).range)
    (M : IntermediateField L Ω) [FiniteDimensional L M] [IsGalois L M] :
    IsPGroup p Gal(M/L) := by
  have : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element L M
  set b : Ω := algebraMap M Ω β
  -- a separable power `c = b ^ q ^ m` of `b`
  set q := ringExpChar Ω
  have : ExpChar (separableClosure F Ω) q :=
    (algebraMap (separableClosure F Ω) Ω).expChar Subtype.val_injective q
  obtain ⟨m, s, hs⟩ := IsPurelyInseparable.pow_mem (separableClosure F Ω) q b
  set c : Ω := b ^ q ^ m
  have hc : IsSeparable F c := by
    rw [← hs]
    exact mem_separableClosure_iff.1 s.2
  -- the Galois closure `N` of `F(c)` (the splitting field of its minimal polynomial)
  set f := minpoly F c
  set N := adjoin F (f.rootSet Ω)
  have hroot : ∀ x ∈ f.rootSet Ω, IsSeparable F x := fun x hx ↦
    hc.of_dvd (minpoly.dvd F x (mem_rootSet.1 hx).2)
  have : Algebra.IsSeparable F N := (isSeparable_adjoin_iff_isSeparable F _).2 hroot
  have : Normal F N := Normal.of_isSplittingField (p := f)
    (hFEp := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _))
  have : FiniteDimensional F N :=
    finiteDimensional_adjoin fun x hx ↦ (hroot x hx).isIntegral
  have : IsGalois F N := isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  have hcN : c ∈ N :=
    subset_adjoin F _ (mem_rootSet.2 ⟨minpoly.ne_zero hc.isIntegral, minpoly.aeval F c⟩)
  -- a Sylow subgroup `P` of `Gal(N / F)` and its fixed field `E`
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p Gal(N/F)))
  set E := fixedField (P : Subgroup Gal(N/F))
  -- `E` has degree prime to `p`, so it lies in `L`
  have hE : finrank F E = (P : Subgroup Gal(N/F)).index := by
    have h1 := Module.finrank_mul_finrank F E N
    rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F N,
      ← (P : Subgroup Gal(N/F)).index_mul_card] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hEL : ∀ x : E, algebraMap N Ω (x : N) ∈ (algebraMap L Ω).range := by
    intro x
    have hmin : minpoly F (algebraMap N Ω (x : N)) = minpoly F x := by
      rw [minpoly.algebraMap_eq (algebraMap N Ω).injective]
      exact minpoly.algebraMap_eq (algebraMap E N).injective x
    refine H _ ?_ ?_
    · unfold IsSeparable
      rw [minpoly.algebraMap_eq (algebraMap N Ω).injective]
      exact Algebra.IsSeparable.isSeparable F (x : N)
    · rw [hmin]
      intro hdvd
      exact P.not_dvd_index (hE ▸ hdvd.trans (minpoly.degree_dvd (Algebra.IsIntegral.isIntegral x)))
  intro σ
  have : IsAlgClosure L Ω :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) L⟩
  let τ : Gal(Ω/L) := σ.liftNormal Ω
  let τN : Gal(N/F) := (τ.restrictScalars F).restrictNormal N
  have hτN : ∀ x : N, algebraMap N Ω (τN x) = τ (algebraMap N Ω x) := fun x ↦
    AlgEquiv.restrictNormal_commutes (τ.restrictScalars F) N x
  -- `τN` fixes `N^P`, hence lies in `P`
  have hτP : τN ∈ (P : Subgroup Gal(N/F)) := by
    rw [← fixingSubgroup_fixedField (P : Subgroup Gal(N/F))]
    rintro ⟨x, hx⟩
    apply (algebraMap N Ω).injective
    obtain ⟨l, hl⟩ := hEL ⟨x, hx⟩
    rw [AlgEquiv.smul_def, hτN]
    exact hl ▸ τ.commutes l
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨τN, hτP⟩
  have hk' : τN ^ p ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  -- `σ ^ p ^ k` fixes `β`
  have hfix : (σ ^ p ^ k) β = β := by
    apply (algebraMap M Ω).injective
    apply iterateFrobenius_inj Ω q m
    simp only [iterateFrobenius_def]
    rw [← AlgEquiv.algebraMap_pow_apply_of_commutes (fun x ↦ σ.liftNormal_commutes Ω x),
      ← map_pow]
    have hcb : algebraMap N Ω ⟨c, hcN⟩ = b ^ q ^ m := rfl
    rw [← hcb, AlgEquiv.algebraMap_pow_apply_of_commutes (fun x ↦ (hτN x).symm), hk']
    rfl
  have key : ((σ ^ p ^ k : Gal(M/L)) : M →ₐ[L] M).comp (⊤ : IntermediateField L M).val =
      (AlgHom.id L M).comp (⊤ : IntermediateField L M).val :=
    algHom_ext_of_eq_adjoin L hβ.symm (by
      rintro x (rfl : x = β)
      exact hfix)
  ext x
  exact congr($key ⟨x, mem_top⟩)

namespace IsDiscreteValuationRing

/-- **Eisenstein's criterion for `Xᵈ - π`**: for a uniformizer `π` of a discrete valuation ring
`R` and `d > 0`, the polynomial `Xᵈ - π` is irreducible over the fraction field of `R`. -/
theorem irreducible_X_pow_sub_C_algebraMap {R F : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] {π : R}
    (hπ : Irreducible π) {d : ℕ} (hd : 0 < d) :
    Irreducible ((Polynomial.X : F[X]) ^ d - Polynomial.C (algebraMap R F π)) := by
  have hmon := Polynomial.monic_X_pow_sub_C π hd.ne'
  have heis : ((Polynomial.X : R[X]) ^ d - Polynomial.C π).IsEisensteinAt
      (Ideal.span {π}) := by
    refine hmon.isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
    · exact (Ideal.span_singleton_eq_top).not.mpr hπ.not_isUnit
    · intro n hn
      rw [Polynomial.natDegree_X_pow_sub_C] at hn
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right hn.ne, zero_sub]
      by_cases hn0 : n = 0
      · subst n
        simp [Polynomial.coeff_C]
      · simp [Polynomial.coeff_C, hn0]
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right hd.ne,
        Polynomial.coeff_C_zero, zero_sub, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        dvd_neg]
      simpa only [pow_one] using
        (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).not.mpr (by omega : ¬ 2 ≤ 1)
  have hprime : (Ideal.span {π}).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr (irreducible_iff_prime.mp hπ)
  have hirr := heis.irreducible hprime hmon.isPrimitive
    (by simpa only [Polynomial.natDegree_X_pow_sub_C] using hd)
  have := (hmon.irreducible_iff_irreducible_map_fraction_map (K := F)).1 hirr
  simpa using this

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- **Tame elements over a henselian discrete valuation ring**: let `Ω` be an extension of the
fraction field `F` of `R` and `γ ∈ Ω` separable over `F` of degree `d` invertible in the
(separably closed) residue field of `R`. Then `γ ∈ F(ρ)` for a `d`-th root `ρ` of a given
uniformizer `π`. -/
theorem exists_pow_eq_algebraMap_and_mem_adjoin {Ω : Type u} [Field Ω] [Algebra F Ω]
    [Algebra R Ω] [IsScalarTower R F Ω] {π : R} (hπ : Irreducible π) {γ : Ω}
    (hγ : IsSeparable F γ) (hd : ((minpoly F γ).natDegree : ResidueField R) ≠ 0) :
    ∃ ρ : Ω, ρ ^ (minpoly F γ).natDegree = algebraMap R Ω π ∧ γ ∈ F⟮ρ⟯ := by
  set d := (minpoly F γ).natDegree
  have : Algebra.IsSeparable F F⟮γ⟯ := (isSeparable_adjoin_simple_iff_isSeparable F Ω).2 hγ
  have : FiniteDimensional F F⟮γ⟯ := adjoin.finiteDimensional hγ.isIntegral
  have hfin : finrank F F⟮γ⟯ = d := adjoin.finrank hγ.isIntegral
  obtain ⟨ρ, hρ⟩ := exists_pow_eq_algebraMap_of_dvd_finrank R F F⟮γ⟯ (N := d) hd
    (hfin ▸ dvd_rfl) hπ
  have hρ' : (ρ : Ω) ^ d = algebraMap R Ω π := by
    rw [← IntermediateField.coe_pow, hρ, IsScalarTower.algebraMap_apply R F F⟮γ⟯,
      IsScalarTower.algebraMap_apply R F Ω]
    rfl
  refine ⟨ρ, hρ', ?_⟩
  have hd0 : 0 < d := minpoly.natDegree_pos hγ.isIntegral
  have hle : F⟮(ρ : Ω)⟯ ≤ F⟮γ⟯ := adjoin_simple_le_iff.2 ρ.2
  have hroot : Polynomial.aeval (ρ : Ω)
      ((Polynomial.X : F[X]) ^ d - Polynomial.C (algebraMap R F π)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply, hρ', sub_self]
  have hmin := minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C_algebraMap hπ hd0)
    hroot (monic_X_pow_sub_C _ hd0.ne')
  have hρint : IsIntegral F (ρ : Ω) := (IsIntegral.of_finite F ρ).map F⟮γ⟯.val
  have heq : F⟮(ρ : Ω)⟯ = F⟮γ⟯ := by
    refine eq_of_le_of_finrank_eq hle ?_
    rw [adjoin.finrank hρint, ← hmin, natDegree_X_pow_sub_C, hfin]
  rw [heq]
  exact mem_adjoin_simple_self F γ

/-- **Pro-`p` Galois groups over a henselian trait**: let `R` be a henselian discrete valuation
ring with separably closed residue field `k` and fraction field `F`, `Ω` an algebraic closure of
`F`, `π` a uniformizer, `p` a prime such that every natural number vanishing in `k` is divisible
by `p`, and `L ⊆ Ω` an intermediate field containing every `n`-th root of `π` for `n` invertible
in `k`. Then every finite Galois extension `M` of `L` in `Ω` has a `p`-group as Galois group. -/
theorem isPGroup_of_forall_pow_eq_mem {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω]
    [IsScalarTower R F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] {π : R} (hπ : Irreducible π)
    (L : IntermediateField F Ω) {p : ℕ} [Fact p.Prime]
    (hp : ∀ n : ℕ, (n : ResidueField R) = 0 → p ∣ n)
    (hL : ∀ (n : ℕ) (ρ : Ω), (n : ResidueField R) ≠ 0 → ρ ^ n = algebraMap R Ω π → ρ ∈ L)
    (M : IntermediateField L Ω) [FiniteDimensional L M] [IsGalois L M] :
    IsPGroup p Gal(M/L) := by
  refine IntermediateField.isPGroup_of_forall_mem _ (fun γ hγ hdeg ↦ ?_) M
  have hd : ((minpoly F γ).natDegree : ResidueField R) ≠ 0 := fun h ↦ hdeg (hp _ h)
  obtain ⟨ρ, hρ, hγρ⟩ := exists_pow_eq_algebraMap_and_mem_adjoin hπ hγ hd
  exact adjoin_simple_le_iff.2 (hL _ ρ hd hρ) hγρ


/-- A ring homomorphism `F →+* L` through which `F →+* Ω` factors, if the image of `F` lies in
that of the (injective) map `L →+* Ω`. -/
theorem _root_.RingHom.exists_comp_eq_of_range_le {F L Ω : Type*} [Field F] [Field L]
    [Field Ω] (f : F →+* Ω) (g : L →+* Ω) (h : ∀ x, f x ∈ g.range) :
    ∃ φ : F →+* L, g.comp φ = f := by
  choose φ hφ using h
  refine ⟨{ toFun := φ
            map_one' := g.injective (by rw [hφ, map_one, map_one])
            map_mul' := fun a b ↦ g.injective (by rw [hφ, map_mul, map_mul, hφ, hφ])
            map_zero' := g.injective (by rw [hφ, map_zero, map_zero])
            map_add' := fun a b ↦ g.injective (by rw [hφ, map_add, map_add, hφ, hφ]) }, ?_⟩
  ext x
  exact hφ x

/-- Variant of `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem` for a field `L` with a
map to `Ω` whose image contains `F` and all roots of `π` of order invertible in the residue
field: every finite Galois extension `M` of `L` in `Ω` has a `p`-group as Galois group. -/
theorem isPGroup_of_forall_pow_eq_mem' {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω]
    [IsScalarTower R F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] {π : R} (hπ : Irreducible π)
    {p : ℕ} [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R) = 0 → p ∣ n)
    {L : Type u} [Field L] [Algebra L Ω]
    (hF : ∀ x : F, algebraMap F Ω x ∈ (algebraMap L Ω).range)
    (hL : ∀ (n : ℕ) (ρ : Ω), (n : ResidueField R) ≠ 0 → ρ ^ n = algebraMap R Ω π →
      ρ ∈ (algebraMap L Ω).range)
    (M : IntermediateField L Ω) [FiniteDimensional L M] [IsGalois L M] :
    IsPGroup p Gal(M/L) := by
  obtain ⟨φ, hφ⟩ := RingHom.exists_comp_eq_of_range_le _ _ hF
  let : Algebra F L := φ.toAlgebra
  have : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq' hφ.symm
  refine IntermediateField.isPGroup_of_forall_mem_range (F := F) (fun γ hγ hdeg ↦ ?_) M
  have hd : ((minpoly F γ).natDegree : ResidueField R) ≠ 0 := fun h ↦ hdeg (hp _ h)
  obtain ⟨ρ, hρ, hγρ⟩ := exists_pow_eq_algebraMap_and_mem_adjoin hπ hγ hd
  let LF : IntermediateField F Ω := (IsScalarTower.toAlgHom F L Ω).fieldRange
  have hρL : ρ ∈ LF := hL _ ρ hd hρ
  obtain ⟨l, hl⟩ := adjoin_simple_le_iff.2 hρL hγρ
  exact ⟨l, hl⟩

/-- **Degree form** of `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem'`: under the same
hypotheses, every finite Galois subextension `L'` of an extension `E / L` inside `Ω` has degree a
power of `p`. -/
theorem exists_finrank_eq_pow_of_forall_pow_eq_mem {Ω : Type u} [Field Ω] [Algebra F Ω]
    [Algebra R Ω] [IsScalarTower R F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] {π : R}
    (hπ : Irreducible π) {p : ℕ} [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R) = 0 → p ∣ n)
    {L : Type u} [Field L] [Algebra L Ω]
    (hF : ∀ x : F, algebraMap F Ω x ∈ (algebraMap L Ω).range)
    (hL : ∀ (n : ℕ) (ρ : Ω), (n : ResidueField R) ≠ 0 → ρ ^ n = algebraMap R Ω π →
      ρ ∈ (algebraMap L Ω).range)
    (E : IntermediateField L Ω) (L' : IntermediateField L E) [FiniteDimensional L L']
    [IsGalois L L'] : ∃ k : ℕ, finrank L L' = p ^ k := by
  let e := L'.equivMap E.val
  have : FiniteDimensional L (L'.map E.val) := e.toLinearEquiv.finiteDimensional
  have : IsGalois L (L'.map E.val) := IsGalois.of_algEquiv e
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := Gal(L'.map E.val/L))).1
    (isPGroup_of_forall_pow_eq_mem' hπ hp hF hL _)
  rw [IsGalois.card_aut_eq_finrank, ← e.toLinearEquiv.finrank_eq] at hk
  exact ⟨k, hk⟩

end IsDiscreteValuationRing
