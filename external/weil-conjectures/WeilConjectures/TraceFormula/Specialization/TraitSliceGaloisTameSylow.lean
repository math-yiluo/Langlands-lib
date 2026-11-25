/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import WeilConjectures.RingTheory.HenselianDVRExtension
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTame

/-!

# `Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group

Let `F = k'((t))`, `F_K = K((t))` with `K` algebraically closed, `Ω_K = F_K^alg` and
`L' = F_K·F^sep ⊆ Ω_K` (`AlgebraicGeometry.traitGenericSepCompositum`). We prove that
`Gal(F_K^sep / L')` is a pro-`p` group, `p` the characteristic exponent, i.e. that every finite
Galois extension of `L'` in `Ω_K` has a `p`-group as Galois group
(`AlgebraicGeometry.isPGroup_traitGenericSepCompositum_of_dvd`), without any tameness hypothesis.

* **Sylow reduction** (`IntermediateField.isPGroup_of_forall_mem`): let `Ω / F` be an algebraic
  closure and `L` an intermediate field containing every separable element of `Ω` of degree prime
  to `p` over `F`. Then `Gal(M / L)` is a `p`-group for every finite Galois `M / L`. Indeed, for
  `σ ∈ Gal(M / L)` and `M = L(β)`, let `N` be the Galois closure over `F` of a separable power
  `β^{q^m}` and `P` a Sylow `p`-subgroup of `Gal(N / F)`. The fixed field `N^P` has degree prime
  to `p`, so it lies in `L`; an extension of `σ` to `Ω` restricts to an element of
  `Gal(N / N^P) = P`, whence `σ^{p^k}` fixes `β^{q^m}`, hence `β`.
* **Tame extensions of `K((t))`** (`PowerSeries.exists_pow_finrank_eq_X` and
  `PowerSeries.exists_pow_eq_X_and_mem_adjoin`): a finite separable extension `L` of `K((t))` of
  degree `d` invertible in `K` contains a `d`-th root `ρ` of `t`, so that `L = K((t))(ρ)`. This
  is the total ramification of `L`
  (`IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`)
  together with Eisenstein's criterion for `Xᵈ - t`.

-/

@[expose] public section

open Polynomial IntermediateField Module

/-- Powers of a lift to a normal extension: if `τ` extends `σ`, then `τⁿ` extends `σⁿ`. -/
lemma AlgEquiv.algebraMap_pow_apply_of_commutes {F F' K₁ E : Type*} [Field F] [Field F'] [Field K₁]
    [Field E] [Algebra F K₁] [Algebra F' E] [Algebra K₁ E] {σ : K₁ ≃ₐ[F] K₁} {τ : E ≃ₐ[F'] E}
    (h : ∀ x, τ (algebraMap K₁ E x) = algebraMap K₁ E (σ x)) (n : ℕ) (x : K₁) :
    (τ ^ n) (algebraMap K₁ E x) = algebraMap K₁ E ((σ ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, h, ih, AlgEquiv.mul_apply]

/-- **Pro-`p` Galois groups by a Sylow argument**: let `Ω` be an algebraic closure of `F`, `p` a
prime and `L` an intermediate field containing every element of `Ω` separable over `F` of degree
prime to `p`. Then every finite Galois extension `M` of `L` in `Ω` has a `p`-group as Galois
group. -/
theorem IntermediateField.isPGroup_of_forall_mem {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] (L : IntermediateField F Ω) {p : ℕ} [Fact p.Prime]
    (H : ∀ γ : Ω, IsSeparable F γ → ¬ p ∣ (minpoly F γ).natDegree → γ ∈ L)
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
  have hEL : ∀ x : E, algebraMap N Ω (x : N) ∈ L := by
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
    change algebraMap N Ω (τN x) = algebraMap N Ω x
    rw [hτN]
    exact τ.commutes ⟨_, hEL ⟨x, hx⟩⟩
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
    change (τ ^ p ^ k) (algebraMap N Ω ⟨c, hcN⟩) = c
    rw [AlgEquiv.algebraMap_pow_apply_of_commutes (fun x ↦ (hτN x).symm), hk']
    rfl
  have key : ((σ ^ p ^ k : Gal(M/L)) : M →ₐ[L] M).comp (⊤ : IntermediateField L M).val =
      (AlgHom.id L M).comp (⊤ : IntermediateField L M).val :=
    algHom_ext_of_eq_adjoin L hβ.symm (by
      rintro x (rfl : x = β)
      exact hfix)
  ext x
  exact congr($key ⟨x, mem_top⟩)

namespace PowerSeries

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **Tame extensions of `K((t))` are totally ramified**: a finite separable extension `L` of
`K((t))`, `K` algebraically closed, whose degree `d` is invertible in `K` contains a `d`-th root
of `t`. -/
theorem exists_pow_finrank_eq_X {L : Type u} [Field L] [Algebra (FractionRing K⟦X⟧) L]
    [Algebra K⟦X⟧ L] [IsScalarTower K⟦X⟧ (FractionRing K⟦X⟧) L]
    [FiniteDimensional (FractionRing K⟦X⟧) L] [Algebra.IsSeparable (FractionRing K⟦X⟧) L]
    (hd : (finrank (FractionRing K⟦X⟧) L : K) ≠ 0) :
    ∃ ρ : L, ρ ^ finrank (FractionRing K⟦X⟧) L = algebraMap K⟦X⟧ L X := by
  have : IsSepClosed (IsLocalRing.ResidueField K⟦X⟧) := .of_ringEquiv (residueFieldEquiv K)
  have hN : ((finrank (FractionRing K⟦X⟧) L : ℕ) : IsLocalRing.ResidueField K⟦X⟧) ≠ 0 := by
    rw [← map_natCast (residueFieldEquiv K)]
    exact (_root_.map_ne_zero _).2 hd
  exact IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank K⟦X⟧
    (FractionRing K⟦X⟧) L hN dvd_rfl
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer X).2 maximalIdeal_eq_span_X)

/-- **Eisenstein's criterion for `Xᵈ - t`**: for `d > 0`, the polynomial `Xᵈ - t` is irreducible
over `K((t))`. -/
theorem irreducible_X_pow_sub_C_X {k : Type*} [Field k] {d : ℕ} (hd : 0 < d) :
    Irreducible ((Polynomial.X : (FractionRing k⟦X⟧)[X]) ^ d -
      Polynomial.C (algebraMap k⟦X⟧ (FractionRing k⟦X⟧) X)) := by
  have hpi : Irreducible (X : k⟦X⟧) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer X).2 maximalIdeal_eq_span_X
  have hmon := Polynomial.monic_X_pow_sub_C (X : k⟦X⟧) hd.ne'
  have heis : ((Polynomial.X : k⟦X⟧[X]) ^ d - Polynomial.C X).IsEisensteinAt
      (Ideal.span {X}) := by
    refine hmon.isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
    · exact (Ideal.span_singleton_eq_top).not.mpr hpi.not_isUnit
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
        (pow_dvd_pow_iff hpi.ne_zero hpi.not_isUnit).not.mpr (by omega : ¬ 2 ≤ 1)
  have hprime : (Ideal.span {(X : k⟦X⟧)}).IsPrime :=
    (Ideal.span_singleton_prime hpi.ne_zero).mpr (irreducible_iff_prime.mp hpi)
  have hirr := heis.irreducible hprime hmon.isPrimitive
    (by simpa only [Polynomial.natDegree_X_pow_sub_C] using hd)
  have := (hmon.irreducible_iff_irreducible_map_fraction_map (K := FractionRing k⟦X⟧)).1 hirr
  simpa using this

/-- **Tame elements over `K((t))`**: let `Ω` be an extension of `K((t))`, `K` algebraically
closed, and `γ ∈ Ω` separable of degree `d` invertible in `K`. Then `K((t))(γ) = K((t))(ρ)` for
a `d`-th root `ρ` of `t`. -/
theorem exists_pow_eq_X_and_mem_adjoin {Ω : Type u} [Field Ω] [Algebra (FractionRing K⟦X⟧) Ω]
    [Algebra K⟦X⟧ Ω] [IsScalarTower K⟦X⟧ (FractionRing K⟦X⟧) Ω] {γ : Ω}
    (hγ : IsSeparable (FractionRing K⟦X⟧) γ)
    (hd : ((minpoly (FractionRing K⟦X⟧) γ).natDegree : K) ≠ 0) :
    ∃ ρ : Ω, ρ ^ (minpoly (FractionRing K⟦X⟧) γ).natDegree = algebraMap K⟦X⟧ Ω X ∧
      γ ∈ (FractionRing K⟦X⟧)⟮ρ⟯ := by
  set F := FractionRing K⟦X⟧
  set d := (minpoly F γ).natDegree
  have : Algebra.IsSeparable F F⟮γ⟯ := (isSeparable_adjoin_simple_iff_isSeparable F Ω).2 hγ
  have : FiniteDimensional F F⟮γ⟯ := adjoin.finiteDimensional hγ.isIntegral
  have hfin : finrank F F⟮γ⟯ = d := adjoin.finrank hγ.isIntegral
  obtain ⟨ρ, hρ⟩ := exists_pow_finrank_eq_X (K := K) (L := F⟮γ⟯) (by rwa [hfin])
  rw [hfin] at hρ
  have hρ' : (ρ : Ω) ^ d = algebraMap K⟦X⟧ Ω X := by
    rw [← IntermediateField.coe_pow, hρ]
    rfl
  refine ⟨ρ, hρ', ?_⟩
  have hd0 : 0 < d := minpoly.natDegree_pos hγ.isIntegral
  have hle : F⟮(ρ : Ω)⟯ ≤ F⟮γ⟯ := adjoin_simple_le_iff.2 ρ.2
  have hroot : Polynomial.aeval (ρ : Ω)
      ((Polynomial.X : F[X]) ^ d - Polynomial.C (algebraMap K⟦X⟧ F X)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply, hρ', sub_self]
  have hmin := minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C_X (k := K) hd0) hroot
    (monic_X_pow_sub_C _ hd0.ne')
  have hρint : IsIntegral F (ρ : Ω) := (IsIntegral.of_finite F ρ).map F⟮γ⟯.val
  have heq : F⟮(ρ : Ω)⟯ = F⟮γ⟯ := by
    refine eq_of_le_of_finrank_eq hle ?_
    rw [adjoin.finrank hρint, ← hmin, natDegree_X_pow_sub_C, hfin]
  rw [heq]
  exact mem_adjoin_simple_self F γ

end PowerSeries

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsAlgClosed K]

/-- **`Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group**: let `p` be a prime such that every
natural number vanishing in `k'` is divisible by `p` (e.g. `p` the characteristic of `k'`, or any
prime if `k'` has characteristic zero). Then every finite Galois extension `M` of
`L' = F_K·F^sep` in `Ω_K` has a `p`-group as Galois group. -/
theorem isPGroup_traitGenericSepCompositum_of_dvd {p : ℕ} (hp : p.Prime)
    (hpk : ∀ n : ℕ, (n : k') = 0 → p ∣ n)
    (M : IntermediateField (traitGenericSepCompositum k' K) (traitGenericField K))
    [FiniteDimensional (traitGenericSepCompositum k' K) M]
    [IsGalois (traitGenericSepCompositum k' K) M] :
    IsPGroup p Gal(M/traitGenericSepCompositum k' K) := by
  have := Fact.mk hp
  refine IntermediateField.isPGroup_of_forall_mem _ (fun γ hγ hdeg ↦ ?_) M
  have hd : ((minpoly (FractionRing (PowerSeries K)) γ).natDegree : k') ≠ 0 :=
    fun h ↦ hdeg (hpk _ h)
  have hdK : ((minpoly (FractionRing (PowerSeries K)) γ).natDegree : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k' K)]
    exact (_root_.map_ne_zero _).2 hd
  obtain ⟨ρ, hρ, hγρ⟩ := PowerSeries.exists_pow_eq_X_and_mem_adjoin hγ hdK
  exact adjoin_simple_le_iff.2 (mem_traitGenericSepCompositum_of_pow_eq hd hρ) hγρ

/-- `AlgebraicGeometry.isPGroup_traitGenericSepCompositum_of_dvd` for `p` the characteristic of
`k'`: `Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group. -/
theorem isPGroup_traitGenericSepCompositum_of_charP {p : ℕ} (hp : p.Prime) [CharP k' p]
    (M : IntermediateField (traitGenericSepCompositum k' K) (traitGenericField K))
    [FiniteDimensional (traitGenericSepCompositum k' K) M]
    [IsGalois (traitGenericSepCompositum k' K) M] :
    IsPGroup p Gal(M/traitGenericSepCompositum k' K) :=
  isPGroup_traitGenericSepCompositum_of_dvd hp (fun n hn ↦ (CharP.cast_eq_zero_iff k' p n).1 hn) M

end AlgebraicGeometry
