/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHCupPerfect
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicCupNondegenerate
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite
public import WeilConjectures.WeilSheaf.CohomologyAdicConstant
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice
public import WeilConjectures.WeilSheaf.CohomologyNonneg
public import WeilConjectures.ZetaLinearAlgebra.TraceCup

/-!
# The trace–cup structure on `H^*(X ⊗ k̄, ℚ̄_ℓ)`

Let `X₀` be a smooth proper geometrically connected scheme of pure dimension `d` over a finite field
`k₀ = 𝔽_q`, and `H^• = H^•(X₀ ⊗ k̄, ℚ̄_ℓ)` the cohomology of the constant Weil sheaf with its
geometric Frobenius `F`. Through the identification of `Hʳ` with the pro-étale cohomology
`Hʳ(X̄_proét, ℚ̄_ℓ)` of the geometric fibre `X̄`, on which `F` is the pullback along the geometric
Galois Frobenius
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback`),
the cup product of `ℚ̄_ℓ`-cohomology (`AlgebraicGeometry.ProEtale.adicConstantHCup`, the
extension of the étale cup products of the finite levels `ℤ/ℓᵐ`) is a Frobenius-compatible
graded-commutative cup product on `H^•`. Given a trace `tr : H^{2d} ≅ ℚ̄_ℓ` on which `F` acts by
`q^d`, the resulting
trace–cup structure is perfect
(`AlgebraicGeometry.WeilSheaf.exists_traceCup_isPerfect_of_linearEquiv`): the pairings
`⟨x, y⟩ = tr(x ⌣ y)` are perfect, by finite-level Poincaré duality for the cup product
(`AlgebraicGeometry.ProEtale.finiteAdicHCup_nondegenerate`) transported to `ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.isPerfPair_adicConstantHCup`).

This is the coefficient stage `ℚ̄_ℓ` of blueprint `corollary-cup-product-pairing--1`,
`corollary-degreewise-duality-over-fields` and `theorem-poincare-duality--9` for the trace–cup
pairing of `corollary-cup-product-pairing--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- A pairing between subsingleton finite-dimensional spaces is perfect. -/
private lemma isPerfPair_of_subsingleton {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [Subsingleton V] [Subsingleton W]
    (P : V →ₗ[K] W →ₗ[K] K) : P.IsPerfPair :=
  .of_injective (fun _ _ _ ↦ Subsingleton.elim _ _) fun _ _ _ ↦ Subsingleton.elim _ _

/-- **The trace–cup structure of `H^•(X ⊗ k̄, ℚ̄_ℓ)` is perfect** (the coefficient stage `ℚ̄_ℓ`
of blueprint `corollary-cup-product-pairing--1` and `corollary-degreewise-duality-over-fields`). For
`X₀` smooth proper geometrically connected of pure dimension `d` over `k₀` and a trace
`tr : H^{2d} ≅ ℚ̄_ℓ` on which the geometric Frobenius acts by `q^d`, the cup product of
`ℚ̄_ℓ`-cohomology and `tr` form a trace–cup structure whose pairings are perfect. -/
theorem exists_traceCup_isPerfect_of_linearEquiv
    (tr : ((adicConstant k₀ l X).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l)
    (htr : ∀ z, tr (((adicConstant k₀ l X).cohomology (2 * d)).frobenius z) =
      (Nat.card k₀ : PadicAlgCl l) ^ d * tr z) :
    ∃ T : FrobeniusModule.TraceCup.{u + 1} (adicConstant k₀ l X).cohomology (2 * d)
      ((Nat.card k₀ : PadicAlgCl l) ^ d), T.IsPerfect := by
  classical
  let f := X ↘ Spec (CommRingCat.of k₀)
  let a := f.geometricFiberToAlgebraicClosure
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f)
      (Scheme.specAlgebraicClosure k₀).hom f.geometricFiberProj a (IsPullback.of_hasPullback _ _)
  have : IsProper a :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) ‹_›
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d a :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_hasPullback _ _) ‹_›
  have hl : ((l : ℕ) : AlgebraicClosure k₀) ≠ 0 := by
    intro h0
    have h1 : ((l : ℕ) : k₀) = 0 := by
      exact (algebraMap k₀ (AlgebraicClosure k₀)).injective (by simpa using h0)
    exact (Fact.out : ringChar k₀ ≠ l)
      ((Nat.Prime.eq_one_or_self_of_dvd (Fact.out : l.Prime) _
        (ringChar.dvd h1)).resolve_left (CharP.ringChar_ne_one))
  have hfin : ∀ m k, Finite (ProEtale.FiniteAdicH f.geometricFiber l m k) :=
    fun m k ↦ ProEtale.finite_finiteAdicH l a hl m k
  -- the pro-étale models of the cohomology groups, in the nonnegative degrees
  have hΘ : ∀ i : ℤ, 0 ≤ i → ∃ Θ : ProEtale.AdicConstantH l f.geometricFiber i.toNat ≃ₗ[
      PadicAlgCl l] ((adicConstant k₀ l X).cohomology i).carrier,
      ∀ x, Θ (ProEtale.adicConstantHPullback l f.geometricGaloisFrobenius.asIso i.toNat x) =
        ((adicConstant k₀ l X).cohomology i).frobenius (Θ x) := by
    intro i hi
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    simpa using exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback
      (k₀ := k₀) (l := l) (Y := X) n
  choose Θ hΘ using hΘ
  have hΘ' (i : ℤ) (hi : 0 ≤ i) (x) : (Θ i hi).symm (((adicConstant k₀ l X).cohomology i).frobenius
      x) = ProEtale.adicConstantHPullback l f.geometricGaloisFrobenius.asIso i.toNat
        ((Θ i hi).symm x) := by
    rw [LinearEquiv.symm_apply_eq, hΘ, LinearEquiv.apply_symm_apply]
  let H := (adicConstant k₀ l X).cohomology
  let cupNN (i j k : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) (hk : 0 ≤ k) (h : i + j = k) :
      (H i).carrier →ₗ[PadicAlgCl l] (H j).carrier →ₗ[PadicAlgCl l] (H k).carrier :=
    ((ProEtale.adicConstantHCup l f.geometricFiber hfin (i := i.toNat) (j := j.toNat)
      (k := k.toNat) (by omega)).compl₁₂ (Θ i hi).symm.toLinearMap
        (Θ j hj).symm.toLinearMap).compr₂ (Θ k hk).toLinearMap
  let cup (i j k : ℤ) (h : i + j = k) :
      (H i).carrier →ₗ[PadicAlgCl l] (H j).carrier →ₗ[PadicAlgCl l] (H k).carrier :=
    if hij : 0 ≤ i ∧ 0 ≤ j then cupNN i j k hij.1 hij.2 (by omega) h else 0
  have hcup (i j k : ℤ) (h : i + j = k) (hij : 0 ≤ i ∧ 0 ≤ j) (x : (H i).carrier)
      (y : (H j).carrier) : cup i j k h x y = Θ k (by omega)
        (ProEtale.adicConstantHCup l f.geometricFiber hfin (i := i.toNat) (j := j.toNat)
          (k := k.toNat) (by omega) ((Θ i hij.1).symm x) ((Θ j hij.2).symm y)) := by
    simp only [cup, dite_eq_left hij]
    rfl
  have hcup0 (i j k : ℤ) (h : i + j = k) (hij : ¬ (0 ≤ i ∧ 0 ≤ j)) : cup i j k h = 0 := by
    simp only [cup, dite_eq_right hij]
  refine ⟨FrobeniusModule.TraceCup.mk cup ?_ ?_ tr.toLinearMap htr,
    ⟨tr.bijective, fun i j h ↦ ?_⟩⟩
  · intro i j k h x y
    by_cases hij : 0 ≤ i ∧ 0 ≤ j
    · rw [hcup i j k h hij, hcup i j k h hij, hΘ', hΘ', ← hΘ]
      exact congrArg _ (ProEtale.adicConstantHPullback_adicConstantHCup l f.geometricFiber hfin
        f.geometricGaloisFrobenius.asIso _ _ _).symm
    · rw [hcup0 i j k h hij]
      exact (map_zero ((adicConstant k₀ l X).cohomology k).frobenius).symm
  · intro i j k h x y
    by_cases hij : 0 ≤ i ∧ 0 ≤ j
    · have hji : 0 ≤ j ∧ 0 ≤ i := ⟨hij.2, hij.1⟩
      have hs : ((i.toNat : ℤ) * j.toNat).negOnePow = (i * j).negOnePow := by
        rw [Int.toNat_of_nonneg hij.1, Int.toNat_of_nonneg hij.2]
      rw [hcup j i k (by omega) hji, hcup i j k h hij,
        ProEtale.adicConstantHCup_comm l f.geometricFiber hfin (i := i.toNat) (j := j.toNat)
          (k := k.toNat) (by omega), hs, Units.smul_def, Units.smul_def, map_zsmul]
    · have hji : ¬ (0 ≤ j ∧ 0 ≤ i) := fun h' ↦ hij ⟨h'.2, h'.1⟩
      rw [hcup0 j i k (by omega) hji, hcup0 i j k h hij, LinearMap.zero_apply, LinearMap.zero_apply,
        LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]
  · -- perfectness of `⟨x, y⟩ = tr (x ⌣ y)`
    change ((cup i j (2 * d) h).compr₂ tr.toLinearMap).IsPerfPair
    by_cases hij : 0 ≤ i ∧ 0 ≤ j
    · have hk : (0 : ℤ) ≤ 2 * d := by positivity
      have hn : i.toNat + j.toNat = (2 * (d : ℤ)).toNat := by omega
      have hnd (m : ℕ) := ProEtale.finiteAdicHCup_nondegenerate l a hl m hn (d := d) (by omega)
      have hP := ProEtale.isPerfPair_adicConstantHCup l f.geometricFiber hfin hn
        (fun m ↦ (hnd m).1) (fun m ↦ (hnd m).2) ((Θ (2 * d) hk).trans tr)
      have heq : (cup i j (2 * d) h).compr₂ tr.toLinearMap =
          ((ProEtale.adicConstantHCup l f.geometricFiber hfin hn).compr₂
            ((Θ (2 * d) hk).trans tr).toLinearMap).compl₁₂ (Θ i hij.1).symm.toLinearMap
              (Θ j hij.2).symm.toLinearMap := by
        ext x y
        rw [LinearMap.compr₂_apply, hcup i j (2 * d) h hij]
        rfl
      rw [heq]
      infer_instance
    · have hsub (r : ℤ) (hr : r < 0 ∨ 2 * (d : ℤ) < r) : Subsingleton (H r).carrier :=
        subsingleton_cohomology_adicConstant_of_two_mul_lt k₀ l X d
          (topologicalKrullDim_geometricFiber_le_of_smoothOfRelativeDimension f d) hr
      have : Subsingleton (H i).carrier := hsub i (by omega)
      have : Subsingleton (H j).carrier := hsub j (by omega)
      exact isPerfPair_of_subsingleton _

end AlgebraicGeometry.WeilSheaf
