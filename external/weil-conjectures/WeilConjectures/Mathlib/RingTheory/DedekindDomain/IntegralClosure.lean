/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.MvPolynomial.Expand
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Noether's finiteness theorem

Mathlib's `IsIntegralClosure.finite` says that the integral closure of an integrally closed
Noetherian domain in a finite *separable* extension of its fraction field is finite. Here we prove
E. Noether's finiteness theorem, which has no separability hypothesis: the integral closure of a
finitely generated domain over a field in a finite extension of its fraction field is finite
(Stacks `0335`, `032L`).

The proof reduces, by Noether normalization, to a polynomial ring `P = k[X₁, …, Xₙ]`. For a finite
extension `L` of `K = Frac P` choose `q = p ^ e` such that the `q`-th powers of a `K`-basis of `L`
are separable over `K`. Adjoining to `k` the `q`-th roots of finitely many coefficients gives a
finite extension `k'` such that, over `K' = Frac k'[X₁, …, Xₙ]` with `P → k'[X]` given by
`Xᵢ ↦ Xᵢ ^ q`, the compositum of `L` and `K'` is separable over `K'`. As `k'[X]` is finite over `P`
and integrally closed, the separable case applies.

## Main statements

- `MvPolynomial.finite_integralClosure`: the case of a polynomial ring.
- `Algebra.FiniteType.finite_integralClosure`: Noether's finiteness theorem.
- `Algebra.FiniteType.finite_integralClosure_of_forall_eq_div`: the variant for an algebra map
  `A → L` to a field whose image generates `L` as a field.
- `isIntegrallyClosed_of_isLocalization_away`: if one denominator `b` clears the integral closure
  of `A` in its fraction field, then `A[1/b]` is integrally closed.
-/

@[expose] public section

open Polynomial

namespace MvPolynomial

variable {σ k k' : Type*} [Field k] [Field k'] [Algebra k k']

/-- The substitution `Xᵢ ↦ Xᵢ ^ q` followed by the extension of scalars along `k → k'`. -/
noncomputable abbrev mapExpand (q : ℕ) : MvPolynomial σ k →+* MvPolynomial σ k' :=
  (map (algebraMap k k')).comp (expand q : MvPolynomial σ k →ₐ[k] _).toRingHom

theorem mapExpand_X (q : ℕ) (i : σ) :
    mapExpand (k' := k') q (X i : MvPolynomial σ k) = X i ^ q := by
  simp [mapExpand]

theorem mapExpand_C (q : ℕ) (c : k) :
    mapExpand (σ := σ) (k' := k') q (C c) = C (algebraMap k k' c) := by
  simp [mapExpand]

theorem mapExpand_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (mapExpand (σ := σ) (k := k) (k' := k') q) :=
  (map_injective _ (algebraMap k k').injective).comp (expand_injective hq)

/-- `k'[X]` is finite over `k[X]` along `Xᵢ ↦ Xᵢ ^ q` if `k'` is finite over `k`. -/
theorem mapExpand_finite [Finite σ] [Module.Finite k k'] {q : ℕ} (hq : 0 < q) :
    (mapExpand (σ := σ) (k := k) (k' := k') q).Finite := by
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := (mapExpand q).toAlgebra
  suffices Module.Finite (MvPolynomial σ k) (MvPolynomial σ k') from this
  have : IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ k') :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (mapExpand_C q c).symm
  have : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k') := by
    constructor
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      have : IsIntegral k (C c : MvPolynomial σ k') :=
        (Algebra.IsIntegral.isIntegral (R := k) c).map (IsScalarTower.toAlgHom k k' _)
      exact this.tower_top
    | add f g hf hg => exact hf.add hg
    | mul_X f i hf =>
      refine hf.mul ⟨Polynomial.X ^ q - Polynomial.C (X i), monic_X_pow_sub_C _ hq.ne', ?_⟩
      rw [← Polynomial.aeval_def, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        RingHom.algebraMap_toAlgebra, mapExpand_X, sub_self]
  have : Algebra.FiniteType (MvPolynomial σ k) (MvPolynomial σ k') := by
    have : Algebra.FiniteType k (MvPolynomial σ k') :=
      Algebra.FiniteType.trans (S := k') inferInstance inferInstance
    exact Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial σ k) _
  exact Algebra.IsIntegral.finite

/-- If the coefficients of `u` have `p ^ e`-th roots in `k'`, then the image of `u` under
`Xᵢ ↦ Xᵢ ^ p ^ e` is a `p ^ e`-th power in `k'[X]`. -/
theorem exists_mapExpand_eq_pow (p : ℕ) [ExpChar k' p] (e : ℕ) (u : MvPolynomial σ k)
    (hu : ∀ c ∈ u.coeffs, ∃ d : k', d ^ p ^ e = algebraMap k k' c) :
    ∃ w, mapExpand (k' := k') (p ^ e) u = w ^ p ^ e := by
  have : map (algebraMap k k') u ∈ Set.range (map (iterateFrobenius k' p e)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.mp hc
    rw [mem_support_iff, coeff_map] at hm
    rw [coeff_map]
    obtain ⟨d, hd⟩ := hu _ (coeff_mem_coeffs m fun h ↦ hm (by simp [h]))
    exact ⟨d, by rw [iterateFrobenius_def, hd]⟩
  obtain ⟨v, hv⟩ := this
  refine ⟨v, ?_⟩
  change map (algebraMap k k') (expand (p ^ e) u) = _
  rw [map_expand, ← hv, ← map_expand, map_iterateFrobenius_expand]

end MvPolynomial

/-- If `x ^ p ^ e` is separable over `K` and the coefficients of its minimal polynomial become
`p ^ e`-th powers in `K'`, then `x` is separable over `K'`. -/
theorem IsSeparable.of_pow_of_coeffs {K K' Ω : Type*} [Field K] [Field K'] [Field Ω]
    [Algebra K K'] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω] (p : ℕ) [ExpChar K' p]
    (e : ℕ) {x : Ω} (hsep : IsSeparable K (x ^ p ^ e))
    (hcoeff : ∀ c ∈ (minpoly K (x ^ p ^ e)).coeffs, ∃ d : K', d ^ p ^ e = algebraMap K K' c) :
    IsSeparable K' x := by
  set g' := (minpoly K (x ^ p ^ e)).map (algebraMap K K')
  have hlift : g' ∈ lifts (iterateFrobenius K' p e) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    rw [coeff_map]
    by_cases hj : (minpoly K (x ^ p ^ e)).coeff j = 0
    · exact ⟨0, by simp [hj]⟩
    obtain ⟨d, hd⟩ := hcoeff _ (coeff_mem_coeffs hj)
    exact ⟨d, by rw [iterateFrobenius_def, hd]⟩
  obtain ⟨h, hh⟩ := (mem_lifts _).mp hlift
  have hhsep : h.Separable :=
    (separable_map (iterateFrobenius K' p e)).mp (hh ▸ Polynomial.Separable.map hsep)
  have hroot : aeval x h = 0 := by
    have h1 : aeval (x ^ p ^ e) g' = 0 := by
      rw [aeval_map_algebraMap, minpoly.aeval]
    rw [← expand_aeval, ← hh, ← map_expand, map_iterateFrobenius_expand, map_pow] at h1
    exact pow_eq_zero_iff (pow_ne_zero _ (expChar_pos K' p).ne') |>.mp h1
  exact hhsep.of_dvd (minpoly.dvd K' x hroot)

universe u in
/-- Finitely many elements of a field acquire `q`-th roots in a finite extension. -/
theorem Field.exists_finiteDimensional_pow_eq (k : Type u) [Field k] (S : Finset k) {q : ℕ}
    (hq : 0 < q) : ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      ∀ c ∈ S, ∃ d : k', d ^ q = algebraMap k k' c := by
  classical
  let Ω := AlgebraicClosure k
  have hroot (c : k) : ∃ d : Ω, d ^ q = algebraMap k Ω c := IsAlgClosed.exists_pow_nat_eq _ hq
  choose rt hrt using hroot
  let k' := IntermediateField.adjoin k ((S.image rt : Finset Ω) : Set Ω)
  refine ⟨k', inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ ?_, fun c hc ↦
      ⟨⟨rt c, IntermediateField.subset_adjoin _ _
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem rt hc))⟩, Subtype.ext (by simpa using hrt c)⟩⟩
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨X ^ q - C c, monic_X_pow_sub_C _ hq.ne', by simp [hrt]⟩

/-- Let `P → P'` be finite with `P'` an integrally closed Noetherian domain, and `L` finite over
`K = Frac P`. If `L` embeds into an extension `Ω` of `K' = Frac P'` such that the images of a
spanning family of `L` are separable over `K'`, then the integral closure of `P` in `L` is finite
over `P`. -/
theorem integralClosure.finite_of_isSeparable {P P' K K' L Ω : Type*} [CommRing P] [IsDomain P]
    [IsNoetherianRing P] [CommRing P'] [IsDomain P'] [IsIntegrallyClosed P'] [IsNoetherianRing P']
    [Algebra P P'] [Module.Finite P P'] [Field K] [Algebra P K] [IsFractionRing P K]
    [Field K'] [Algebra P' K'] [IsFractionRing P' K'] [Algebra P K'] [IsScalarTower P P' K']
    [Algebra K K'] [IsScalarTower P K K'] [Field L] [Algebra K L] [Algebra P L]
    [IsScalarTower P K L] [FiniteDimensional K L] [Field Ω] [Algebra K' Ω] [Algebra K Ω]
    [Algebra P Ω] [Algebra P' Ω] [IsScalarTower K K' Ω] [IsScalarTower P K Ω]
    [IsScalarTower P' K' Ω] [IsScalarTower P P' Ω] [IsScalarTower P K' Ω] (τ : L →ₐ[K] Ω)
    {ι : Type*} [Finite ι] (b : ι → L) (hb : Submodule.span K (Set.range b) = ⊤)
    (hsep : ∀ i, IsSeparable K' (τ (b i))) :
    Module.Finite P (integralClosure P L) := by
  let F : IntermediateField K' Ω := IntermediateField.adjoin K' (Set.range fun i ↦ τ (b i))
  have : FiniteDimensional K' F := IntermediateField.finiteDimensional_adjoin <| by
    rintro _ ⟨i, rfl⟩; exact (hsep i).isIntegral
  have : Algebra.IsSeparable K' F :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K' Ω).mpr <| by
      rintro _ ⟨i, rfl⟩; exact hsep i
  have hF (y : L) : τ y ∈ F := by
    have hy : y ∈ Submodule.span K (Set.range b) := hb ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, ← algebraMap_smul K' a]
      exact F.smul_mem hx
  let C := integralClosure P' F
  have : Module.Finite P' C := IsIntegralClosure.finite P' K' F C
  have : IsScalarTower P P' F := IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <| by
    change algebraMap P Ω x = algebraMap P' Ω (algebraMap P P' x)
    exact IsScalarTower.algebraMap_apply P P' Ω x
  have : Module.Finite P C := Module.Finite.trans P' C
  let φ : integralClosure P L →ₗ[P] C :=
    { toFun y := ⟨⟨τ y, hF y⟩, by
        have h1 : IsIntegral P (τ y) := y.2.map (τ.restrictScalars P)
        have h2 : IsIntegral P' (τ y) := h1.tower_top
        exact (isIntegral_algHom_iff (F.val.restrictScalars P') Subtype.val_injective).mp h2⟩
      map_add' x y := by ext; simp
      map_smul' a x := by ext; exact map_smul (τ.restrictScalars P) a x.1 }
  refine Module.Finite.of_injective φ fun x y h ↦ ?_
  exact Subtype.ext (τ.injective congr($h.1.1))

/-- Variant of `integralClosure.finite_of_isSeparable`: it suffices that the `p ^ e`-th powers of
a spanning family of `L` are separable over `K` and that the coefficients of their minimal
polynomials are quotients of elements of `P` which become `p ^ e`-th powers in `P'`. -/
theorem integralClosure.finite_of_pow {P P' K L : Type*} [CommRing P] [IsDomain P]
    [IsNoetherianRing P] [CommRing P'] [IsDomain P'] [IsIntegrallyClosed P'] [IsNoetherianRing P']
    [Algebra P P'] [Module.Finite P P'] [FaithfulSMul P P'] [Field K] [Algebra P K]
    [IsFractionRing P K] [Field L] [Algebra K L] [Algebra P L] [IsScalarTower P K L]
    [FiniteDimensional K L] (p : ℕ) [ExpChar P' p] (e : ℕ) {ι : Type*} [Finite ι] (b : ι → L)
    (hb : Submodule.span K (Set.range b) = ⊤) (hsep : ∀ i, IsSeparable K (b i ^ p ^ e))
    (hpow : ∀ i, ∀ c ∈ (minpoly K (b i ^ p ^ e)).coeffs, ∃ u v : P,
      algebraMap P K u / algebraMap P K v = c ∧ (∃ w : P', algebraMap P P' u = w ^ p ^ e) ∧
        ∃ w : P', algebraMap P P' v = w ^ p ^ e) :
    Module.Finite P (integralClosure P L) := by
  let K' := FractionRing P'
  have : ExpChar K' p := expChar_of_injective_algebraMap (IsFractionRing.injective P' K') p
  have hPK' : Function.Injective (algebraMap P K') := by
    rw [IsScalarTower.algebraMap_eq P P' K']
    exact (IsFractionRing.injective P' K').comp (FaithfulSMul.algebraMap_injective P P')
  let : Algebra K K' := (IsFractionRing.lift hPK').toAlgebra
  have : IsScalarTower P K K' := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
  let Ω := AlgebraicClosure K'
  have : IsScalarTower P K Ω := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply P K' Ω, IsScalarTower.algebraMap_apply P K K',
      ← IsScalarTower.algebraMap_apply K K' Ω]
  let τ : L →ₐ[K] Ω := IsAlgClosed.lift
  refine integralClosure.finite_of_isSeparable (P := P) (P' := P') (K' := K') (Ω := Ω) τ b hb
    fun i ↦ ?_
  refine IsSeparable.of_pow_of_coeffs (K := K) p e ?_ ?_
  · rw [← map_pow]
    exact (hsep i).map τ τ.injective
  · intro c hc
    rw [← map_pow, minpoly.algHom_eq τ τ.injective] at hc
    obtain ⟨u, v, rfl, ⟨w, hw⟩, ⟨w', hw'⟩⟩ := hpow i c hc
    refine ⟨algebraMap P' K' w / algebraMap P' K' w', ?_⟩
    rw [div_pow, ← map_pow, ← map_pow, ← hw, ← hw', map_div₀,
      ← IsScalarTower.algebraMap_apply P K K', ← IsScalarTower.algebraMap_apply P K K',
      ← IsScalarTower.algebraMap_apply P P' K', ← IsScalarTower.algebraMap_apply P P' K']

universe u v in
/-- **Noether's finiteness theorem** for polynomial rings: the integral closure of
`k[X₁, …, Xₙ]` in a finite extension of its fraction field is finite. -/
theorem MvPolynomial.finite_integralClosure {k : Type u} {σ : Type v} [Field k] [Finite σ]
    (K L : Type*) [Field K] [Field L] [Algebra (MvPolynomial σ k) K]
    [IsFractionRing (MvPolynomial σ k) K] [Algebra K L] [Algebra (MvPolynomial σ k) L]
    [IsScalarTower (MvPolynomial σ k) K L] [FiniteDimensional K L] :
    Module.Finite (MvPolynomial σ k) (integralClosure (MvPolynomial σ k) L) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, ExpChar k p := ⟨ringExpChar k, inferInstance⟩
  have : ExpChar K p := expChar_of_injective_ringHom
    (f := (algebraMap (MvPolynomial σ k) K).comp MvPolynomial.C)
    ((IsFractionRing.injective (MvPolynomial σ k) K).comp (MvPolynomial.C_injective σ k)) p
  -- some power `q = p ^ E` of the basis vectors is separable
  let b := Module.finBasis K L
  have hsep1 (i) : ∃ e, IsSeparable K (b i ^ p ^ e) := by
    have : ExpChar (separableClosure K L) p :=
      expChar_of_injective_algebraMap (algebraMap K _).injective p
    obtain ⟨e, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K L) p (b i)
    exact ⟨e, mem_separableClosure_iff.mp (hy ▸ y.2)⟩
  choose e he using hsep1
  set E := Finset.univ.sup e
  have hq : 0 < p ^ E := pow_pos (expChar_pos k p) _
  have hsep (i) : IsSeparable K (b i ^ p ^ E) := by
    have h : b i ^ p ^ E = (b i ^ p ^ e i) ^ p ^ (E - e i) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ i))]
    rw [h]
    exact mem_separableClosure_iff.mp
      (pow_mem (mem_separableClosure_iff.mpr (he i)) _)
  -- the coefficients of the minimal polynomials of the `b i ^ q`
  choose num den hden hnd using fun z : K ↦ IsFractionRing.div_surjective (A := MvPolynomial σ k) z
  let T : Finset K := Finset.univ.biUnion fun i ↦ (minpoly K (b i ^ p ^ E)).coeffs
  let S : Finset k := T.biUnion fun c ↦ (num c).coeffs ∪ (den c).coeffs
  -- adjoin `q`-th roots of the elements of `S` to `k`
  obtain ⟨k', _, _, _, hk'⟩ := Field.exists_finiteDimensional_pow_eq k S hq
  have : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective p
  -- the finite extension `k'[X]` of `k[X]` along `Xᵢ ↦ Xᵢ ^ q`
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') :=
    (MvPolynomial.mapExpand (p ^ E)).toAlgebra
  have : Module.Finite (MvPolynomial σ k) (MvPolynomial σ k') := MvPolynomial.mapExpand_finite hq
  have : FaithfulSMul (MvPolynomial σ k) (MvPolynomial σ k') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.mapExpand_injective hq)
  have : IsIntegrallyClosed (MvPolynomial σ k') := UniqueFactorizationMonoid.instIsIntegrallyClosed
  have : ExpChar (MvPolynomial σ k') p :=
    expChar_of_injective_algebraMap (MvPolynomial.C_injective σ k') p
  refine integralClosure.finite_of_pow (P' := MvPolynomial σ k') p E b b.span_eq hsep
    fun i c hc ↦ ⟨num c, den c, hnd c, ?_, ?_⟩
  all_goals
    refine MvPolynomial.exists_mapExpand_eq_pow p E _ fun a ha ↦ hk' a ?_
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩, by simp [ha]⟩

open scoped nonZeroDivisors in
/-- **Noether's finiteness theorem**: the integral closure of a finitely generated domain over a
field in a finite extension of its fraction field is a finite module (Stacks `0335`). -/
@[stacks 0335]
theorem Algebra.FiniteType.finite_integralClosure (k : Type*) {A : Type*} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let : Algebra (MvPolynomial (Fin s) k) K :=
    ((algebraMap A K).comp g.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin s) k) A K := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (MvPolynomial (Fin s) k) L :=
    ((algebraMap A L).comp g.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin s) k) A L := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (MvPolynomial (Fin s) k) K L :=
    .of_algebraMap_eq fun x ↦ IsScalarTower.algebraMap_apply A K L (g x)
  have : FaithfulSMul (MvPolynomial (Fin s) k) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ((IsFractionRing.injective A K).comp hinj)
  let : Algebra (FractionRing (MvPolynomial (Fin s) k)) K := FractionRing.liftAlgebra _ K
  have : IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) K :=
    FractionRing.isScalarTower_liftAlgebra _ K
  let : Algebra (FractionRing (MvPolynomial (Fin s) k)) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing (MvPolynomial (Fin s) k)) K)).toAlgebra
  have : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) K L := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) K L,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k)
          (FractionRing (MvPolynomial (Fin s) k)) K]
      rfl
  have : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) K := by
    obtain ⟨_, t, ht⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin s) k) (M := A)
    exact Module.finite_def.mpr <| (span_eq_top_localization_localization
      (FractionRing (MvPolynomial (Fin s) k)) (MvPolynomial (Fin s) k)⁰ K ht) ▸
        Submodule.fg_span (Set.toFinite _)
  have : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L := Module.Finite.trans K L
  have := MvPolynomial.finite_integralClosure (k := k) (σ := Fin s)
    (FractionRing (MvPolynomial (Fin s) k)) L
  have : Module.Finite (MvPolynomial (Fin s) k) (integralClosure A L) := by
    let φ : integralClosure A L →ₗ[MvPolynomial (Fin s) k]
        integralClosure (MvPolynomial (Fin s) k) L :=
      { toFun x := ⟨x.1, isIntegral_trans _ x.2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    exact Module.Finite.of_injective φ fun x y h ↦ Subtype.ext congr($h.1)
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A _

open scoped nonZeroDivisors in
/-- **Noether's finiteness theorem**, variant: if `A` is a finitely generated algebra over a field
and every element of the field `L` is a quotient of elements of the image of `A → L`, then the
integral closure of `A` in `L` is a finite `A`-module. -/
theorem Algebra.FiniteType.finite_integralClosure_of_forall_eq_div (k : Type*) {A L : Type*}
    [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field L] [Algebra A L]
    (h : ∀ z : L, ∃ x y : A, z = algebraMap A L x / algebraMap A L y) :
    Module.Finite A (integralClosure A L) := by
  let A' := A ⧸ RingHom.ker (algebraMap A L)
  let : Algebra A' L := (RingHom.kerLift (algebraMap A L)).toAlgebra
  have : IsScalarTower A A' L := .of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap A' L) := RingHom.kerLift_injective _
  have : FaithfulSMul A' L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsDomain A' := hinj.isDomain _
  have : IsFractionRing A' L := .of_field A' L fun z ↦ by
    obtain ⟨x, y, rfl⟩ := h z
    exact ⟨Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y, rfl⟩
  have := Algebra.FiniteType.finite_integralClosure k (A := A') L L
  have : Module.Finite A (integralClosure A' L) := Module.Finite.trans A' _
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let φ : integralClosure A L →ₗ[A] integralClosure A' L :=
    { toFun x := ⟨x.1, x.2.tower_top⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Finite.of_injective φ fun x y h ↦ Subtype.ext congr($h.1)

open scoped nonZeroDivisors

/-- If the integral closure of a domain `A` in its fraction field `K` is a finite `A`-module, then
a single nonzero denominator `b` clears all its elements. -/
theorem exists_isInteger_smul_of_finite_integralClosure {A K : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ b ∈ A⁰, ∀ x : K, IsIntegral A x → IsLocalization.IsInteger A (b • x) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset A⁰
    (s.image fun c : integralClosure A K ↦ (c : K))
  refine ⟨b, hb, fun x hx ↦ ?_⟩
  have hmem : (⟨x, hx⟩ : integralClosure A K) ∈ Submodule.span A (s : Set _) := hs ▸ trivial
  have key : ∀ c ∈ Submodule.span A (s : Set (integralClosure A K)),
      IsLocalization.IsInteger A (b • (c : K)) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc => exact hbs _ (Finset.mem_image_of_mem _ hc)
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨u, hu⟩ := hc; obtain ⟨v, hv⟩ := hd
      exact ⟨u + v, by simp [hu, hv, smul_add]⟩
    | smul a c _ hc =>
      obtain ⟨u, hu⟩ := hc
      refine ⟨a * u, ?_⟩
      rw [map_mul, hu, Subalgebra.coe_smul, smul_comm, Algebra.smul_def a]
  exact key _ hmem

/-- If `b ≠ 0` clears the denominators of all elements of `K = Frac A` integral over `A`, then
the localization `A[1/b]` is integrally closed. -/
theorem isIntegrallyClosed_of_isLocalization_away {A K R : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [CommRing R] [Algebra A R] [Algebra R K]
    [IsScalarTower A R K] [IsFractionRing R K] {b : A} (hb : b ≠ 0) [IsLocalization.Away b R]
    (h : ∀ x : K, IsIntegral A x → IsLocalization.IsInteger A (b • x)) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers b) x hx
  obtain ⟨a, ha⟩ := h _ hm
  have hb' : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb
  refine ⟨IsLocalization.mk' R a (⟨b ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers b), ?_⟩
  have hspec := congr(algebraMap R K $(IsLocalization.mk'_spec R a
    (⟨b ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers b)))
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at hspec
  rw [ha] at hspec
  simp only [Submonoid.smul_def, Algebra.smul_def, map_pow] at hspec
  apply mul_right_cancel₀ (pow_ne_zero (n + 1) hb')
  rw [hspec]
  ring
