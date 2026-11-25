/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar

/-!
# Finiteness for the constant `ℓ`-adic sheaf from lisse-ness on a stratification

The constant case of the finiteness theorem
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` for `F = ℚ̄_ℓ,T`):

- `AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf.of_schemeStratification`: an `ℓ`-adic
  sheaf whose pullbacks to the strata of a stratification
  (`AlgebraicGeometry.Scheme.Stratification`) are lisse is stratified lisse;
- `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_unit_of_stratification`: for
  `g : T ⟶ Y` quasi-compact and quasi-separated between schemes of finite type over a field,
  `Rg_* ℚ̄_ℓ,T` is bounded with constructible cohomology sheaves as soon as there is a
  stratification of `Y` on whose strata all the `Rⁱg_* ℚ̄_ℓ,T` are lisse. Boundedness is
  `AlgebraicGeometry.ProEtale.bounded_rightDerivedFunctor_adicLowerStar_unit`.

The stratification is the uniform stratification of the torsion direct images
(`AlgebraicGeometry.Etale.exists_stratification_isSetFLC_upperStar_higherDirectImageQuotPowTower`);
the lisse-ness of the pullbacks of `Rⁱg_* ℚ̄_ℓ,T` to its strata is the remaining input.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- An `ℓ`-adic sheaf whose pullbacks to the strata of a stratification are lisse is stratified
lisse. -/
lemma IsAdicStratifiedLisseSheaf.of_schemeStratification {X : Scheme.{u}} {F : AdicSheaf l X}
    (R : Scheme.Stratification X) (h : ∀ k, IsAdicLisseSheaf ((R.immersion k)^*ᵃ[l].obj F)) :
    IsAdicStratifiedLisseSheaf F := by
  refine ⟨Fin R.n, inferInstance, R.domain, R.immersion, fun _ ↦ inferInstance, fun k ↦ ?_,
    fun x ↦ ?_, h⟩
  · rw [show Set.range (R.immersion k).base = R.stratum k from R.range_immersion k]
    exact R.isConstructible_stratum k
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (R.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    refine ⟨k, show x ∈ Set.range (R.immersion k) by rw [R.range_immersion k]; exact hk,
      fun k' hk' ↦ ?_⟩
    replace hk' : x ∈ Set.range (R.immersion k') := hk'
    rw [R.range_immersion k'] at hk'
    by_contra hne
    exact Set.disjoint_left.1 (R.pairwise_disjoint_stratum hne) hk' hk

variable {k : Type u} [Field k] {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
  [QuasiSeparated g] (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aT]
  [QuasiCompact aT] [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) (d : ℕ)
  (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (l)

include aT aY hg hd in
/-- **Finiteness for the constant `ℓ`-adic sheaf from a stratification.** Let `g : T ⟶ Y` be
quasi-compact and quasi-separated between schemes of finite type over a field, with
`dim T ≤ d`. If there is a stratification of `Y` on whose strata all the higher direct images
`Rⁱg_* ℚ̄_ℓ,T` are lisse, then `Rg_* ℚ̄_ℓ,T` is bounded with constructible cohomology sheaves. -/
theorem finiteLowerStar_singleFunctor_unit_of_stratification (R : Scheme.Stratification Y)
    (hL : ∀ (i : ℕ) k, IsAdicLisseSheaf
      ((R.immersion k)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i))) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l T)) := by
  refine ⟨bounded_rightDerivedFunctor_adicLowerStar_unit g aT aY hg d hd l, fun n ↦ ?_⟩
  rw [adicConstructibleSheaf_iff]
  rcases lt_or_ge n 0 with hn | hn
  · have := (g)_*ᵃ[l].isGE_rightDerivedFunctor_obj_singleFunctor (AdicSheaf.unit l T)
    exact (IsAdicLisseSheaf.of_isZero
      (DerivedCategory.isZero_of_isGE _ 0 n hn)).isAdicConstructibleSheaf
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (IsAdicStratifiedLisseSheaf.of_schemeStratification R
      (hL i)).isAdicConstructibleSheaf

end AlgebraicGeometry.ProEtale
