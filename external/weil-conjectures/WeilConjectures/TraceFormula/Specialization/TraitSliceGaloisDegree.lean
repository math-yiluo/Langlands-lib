/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow
public import WeilConjectures.TraceFormula.Specialization.TraitSliceTraitAlgebra

/-!

# The Galois extension `L^sep / L` of the slice trait is pro-`p`

Let `L = Ω(K⟦t⟧) ⊆ Ω_K` be the compositum of the image of `Ω = (Frac k'⟦t⟧)^alg` and of `K⟦t⟧`
(`AlgebraicGeometry.traitTensorCompositum`), `K` algebraically closed, and `L^sep` its separable
closure in `Ω_K`. Every finite Galois subextension `L₁ / L` of `L^sep / L` has `p`-power degree,
`p` the characteristic exponent of `k'`
(`AlgebraicGeometry.exists_finrank_traitTensorCompositum_eq_pow`); in particular its degree is
invertible in every ring in which `p` is invertible
(`AlgebraicGeometry.isUnit_finrank_traitTensorCompositum`).

The proof is the Sylow argument of `IntermediateField.isPGroup_of_forall_mem`, stated here for an
abstract tower `F ⟶ L ⟶ Ω` (`isPGroup_of_forall_mem_range`): `L` contains the compositum
`F_K·F^sep` (`F = k'((t))`, `F_K = K((t))`), which contains every element of `Ω_K` separable of
degree prime to `p` over `F_K` (`PowerSeries.exists_pow_eq_X_and_mem_adjoin`,
`AlgebraicGeometry.mem_traitGenericSepCompositum_of_pow_eq`).

-/

@[expose] public section

open Polynomial IntermediateField Module

/-- **Pro-`p` Galois groups by a Sylow argument**, for an abstract tower `F ⟶ L ⟶ Ω`: let `Ω` be
an algebraic closure of `F`, `p` a prime and `L` a field between `F` and `Ω` whose image contains
every element of `Ω` separable over `F` of degree prime to `p`. Then every finite Galois
extension `M` of `L` embedded in `Ω` over `L` has a `p`-group as Galois group. -/
theorem isPGroup_of_forall_mem_range {F L M Ω : Type*} [Field F] [Field L] [Field M] [Field Ω]
    [Algebra F Ω] [Algebra F L] [Algebra L Ω] [IsScalarTower F L Ω] [Algebra L M] [Algebra M Ω]
    [IsScalarTower L M Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] {p : ℕ} [Fact p.Prime]
    (H : ∀ γ : Ω, IsSeparable F γ → ¬ p ∣ (minpoly F γ).natDegree →
      γ ∈ (algebraMap L Ω).range)
    [FiniteDimensional L M] [IsGalois L M] :
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
    obtain ⟨y, hy⟩ := hEL ⟨x, hx⟩
    rw [AlgEquiv.smul_def, hτN]
    refine (congrArg τ hy.symm).trans ((τ.commutes y).trans hy)
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
    have hcb : algebraMap M Ω β ^ q ^ m = algebraMap N Ω ⟨c, hcN⟩ := rfl
    rw [hcb, AlgEquiv.algebraMap_pow_apply_of_commutes (fun x ↦ (hτN x).symm), hk']
    rfl
  have key : ((σ ^ p ^ k : Gal(M/L)) : M →ₐ[L] M).comp (⊤ : IntermediateField L M).val =
      (AlgHom.id L M).comp (⊤ : IntermediateField L M).val :=
    algHom_ext_of_eq_adjoin L hβ.symm (by
      rintro x (rfl : x = β)
      exact hfix)
  ext x
  exact congr($key ⟨x, mem_top⟩)

/-- **`p`-power degrees from the Sylow argument**: under the hypotheses of
`isPGroup_of_forall_mem_range`, every finite Galois subextension `L₁` of the separable closure of
`L` in `Ω` has `p`-power degree over `L`. -/
theorem exists_finrank_eq_pow_of_forall_mem_range {F L Ω : Type*} [Field F] [Field L] [Field Ω]
    [Algebra F Ω] [Algebra F L] [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] {p : ℕ} [Fact p.Prime]
    (H : ∀ γ : Ω, IsSeparable F γ → ¬ p ∣ (minpoly F γ).natDegree →
      γ ∈ (algebraMap L Ω).range)
    (L₁ : FiniteGaloisIntermediateField L (separableClosure L Ω)) :
    ∃ n : ℕ, finrank L L₁ = p ^ n := by
  let : Algebra L₁ Ω :=
    ((separableClosure L Ω).val.toRingHom.comp L₁.toIntermediateField.val.toRingHom).toAlgebra
  have : IsScalarTower L L₁ Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_of_forall_mem_range (M := L₁) H)
  exact ⟨n, (IsGalois.card_aut_eq_finrank _ _).symm.trans hn⟩

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

attribute [local instance] traitGenericFieldAlgebra

/-- The compositum `L = Ω(K⟦t⟧)` as an intermediate field of `Ω_K / Frac K⟦t⟧`. -/
noncomputable def traitTensorCompositumOverFractionRing :
    IntermediateField (FractionRing (PowerSeries K)) (traitGenericField K) :=
  (traitTensorCompositum (PowerSeries K) (traitGenericField k')
    (traitGenericField K)).toSubfield.toIntermediateField
      algebraMap_fractionRing_mem_traitTensorCompositum

/-- `F_K·Ω ⊆ L`. -/
lemma traitGenericCompositum_le_traitTensorCompositumOverFractionRing :
    traitGenericCompositum k' K ≤ traitTensorCompositumOverFractionRing (k' := k') (K := K) :=
  adjoin_le_iff.2 <| by
    rintro _ ⟨y, rfl⟩
    exact IntermediateField.algebraMap_mem
      (traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K)) y

/-- The `Frac K⟦t⟧`-algebra structure on the compositum `L = Ω(K⟦t⟧)`. -/
noncomputable abbrev traitTensorCompositumFractionRingAlgebra :
    Algebra (FractionRing (PowerSeries K))
      (traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K)) :=
  ((algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)).codRestrict
    (traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K))
    algebraMap_fractionRing_mem_traitTensorCompositum).toAlgebra

variable [IsAlgClosed K]

/-- **The compositum `L = Ω(K⟦t⟧)` contains the tame elements**: every element of `Ω_K` separable
over `Frac K⟦t⟧` of degree prime to `p` lies in `L`, for a prime `p` such that every natural
number vanishing in `k'` is divisible by `p`. -/
theorem mem_range_traitTensorCompositum_of_isSeparable {p : ℕ}
    (hpk : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (γ : traitGenericField K)
    (hγ : IsSeparable (FractionRing (PowerSeries K)) γ)
    (hdeg : ¬ p ∣ (minpoly (FractionRing (PowerSeries K)) γ).natDegree) :
    γ ∈ (algebraMap (traitTensorCompositum (PowerSeries K) (traitGenericField k')
      (traitGenericField K)) (traitGenericField K)).range := by
  have hd : ((minpoly (FractionRing (PowerSeries K)) γ).natDegree : k') ≠ 0 :=
    fun h ↦ hdeg (hpk _ h)
  have hdK : ((minpoly (FractionRing (PowerSeries K)) γ).natDegree : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k' K)]
    exact (_root_.map_ne_zero _).2 hd
  obtain ⟨ρ, hρ, hγρ⟩ := PowerSeries.exists_pow_eq_X_and_mem_adjoin hγ hdK
  have hmem : γ ∈ traitTensorCompositumOverFractionRing (k' := k') (K := K) :=
    traitGenericCompositum_le_traitTensorCompositumOverFractionRing
      (traitGenericSepCompositum_le
        (adjoin_simple_le_iff.2 (mem_traitGenericSepCompositum_of_pow_eq hd hρ) hγρ))
  exact ⟨⟨γ, hmem⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the instances `Module L L₁` for the concrete composita are found slowly
/-- **Finite Galois subextensions of `L^sep / L` have `p`-power degree**, for a prime `p` such
that every natural number vanishing in `k'` is divisible by `p`. -/
theorem exists_finrank_traitTensorCompositum_eq_pow {p : ℕ} (hp : p.Prime)
    (hpk : ∀ n : ℕ, (n : k') = 0 → p ∣ n)
    (L₁ : FiniteGaloisIntermediateField
      (traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K))
      (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))) :
    ∃ n : ℕ, finrank (traitTensorCompositum (PowerSeries K) (traitGenericField k')
      (traitGenericField K)) L₁ = p ^ n := by
  have := Fact.mk hp
  let := traitTensorCompositumFractionRingAlgebra (k' := k') (K := K)
  have : IsScalarTower (FractionRing (PowerSeries K))
      (traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K))
      (traitGenericField K) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact exists_finrank_eq_pow_of_forall_mem_range (F := FractionRing (PowerSeries K))
    (mem_range_traitTensorCompositum_of_isSeparable hpk) L₁

-- the instances `Module L L₁` for the concrete composita are found slowly
/-- The degrees of the finite Galois subextensions of `L^sep / L` are invertible in every ring in
which `p` is invertible. -/
theorem isUnit_finrank_traitTensorCompositum {p : ℕ} (hp : p.Prime)
    (hpk : ∀ n : ℕ, (n : k') = 0 → p ∣ n) {T₀ : Type*} [CommRing T₀] (hpT : IsUnit (p : T₀))
    (L₁ : FiniteGaloisIntermediateField
      (traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K))
      (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))) :
    IsUnit ((finrank (traitTensorCompositum (PowerSeries K) (traitGenericField k')
      (traitGenericField K)) L₁ : ℕ) : T₀) := by
  obtain ⟨n, hn⟩ := exists_finrank_traitTensorCompositum_eq_pow hp hpk L₁
  rw [hn, Nat.cast_pow]
  exact hpT.pow n

end AlgebraicGeometry
