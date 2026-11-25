/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowTowerLocallyConstant
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-!
# A common stratification for the higher direct images of `Λ ⧸ I`

- `AlgebraicGeometry.Scheme.exists_stratification_isFiniteLocallyConstantSheaf_upperStar`:
  finitely many constructible sheaves are finite locally constant on the strata of a single
  stratification (iterated common refinements, `AlgebraicGeometry.Scheme.Stratification.inter`);
- `AlgebraicGeometry.Scheme.exists_stratification_isFiniteLocallyConstantSheaf_upperStar_homology`:
  for a bounded constructible complex `K`, a single stratification works for all the homology
  sheaves `Hⁿ(K)`, only finitely many of them being nonzero;
- `AlgebraicGeometry.Etale.exists_stratification_flcProperty_rightDerived_constantQuotSheaf`:
  by the finiteness theorem for torsion coefficients
  (`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`),
  for `g : T ⟶ Y` quasi-compact between schemes locally of finite type over a field, `Y`
  quasi-compact, and `Λ ⧸ I` finite with exponent invertible on `T`, there is a stratification
  of `Y` on whose strata all the `Rᵏg_* (Λ ⧸ I)_T` are finite locally constant. Combined with
  `AlgebraicGeometry.Etale.isSetFLC_upperStar_higherDirectImageQuotPowTower_obj_of_flcProperty_one`
  this is the uniform stratification of the tower `n ↦ Hᵏ(Rg_* (Λ ⧸ Iⁿ))`
  (`exists_stratification_isSetFLC_upperStar_higherDirectImageQuotPowTower`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {X : Scheme.{u}}

/-- **A common stratification for finitely many constructible sheaves**: there is a single
stratification of `X` on whose strata all the given constructible sheaves are finite locally
constant. -/
theorem exists_stratification_isFiniteLocallyConstantSheaf_upperStar {ι : Type*} (s : Finset ι)
    (F : ι → Sheaf X.smallEtaleTopology A) (hF : ∀ i ∈ s, IsConstructibleSheaf (F i)) :
    ∃ R : Stratification X, ∀ i ∈ s, ∀ l,
      IsFiniteLocallyConstantSheaf ((Etale.upperStar A (R.immersion l)).obj (F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Stratification.trivial X, by simp⟩
  | insert a s ha ih =>
    obtain ⟨R, hR⟩ := ih fun i hi ↦ hF i (Finset.mem_insert_of_mem hi)
    obtain ⟨S, hS⟩ := hF a (Finset.mem_insert_self a s)
    refine ⟨R.inter S, fun i hi l ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (R.inter_refines_right S).isFiniteLocallyConstantSheaf_upperStar _ hS l
    · exact (R.inter_refines_left S).isFiniteLocallyConstantSheaf_upperStar _ (hR i hi) l

/-- **A common stratification for the homology of a bounded constructible complex**: all the
homology sheaves `Hⁿ(K)` are finite locally constant on the strata of a single stratification,
only finitely many of them being nonzero. -/
theorem exists_stratification_isFiniteLocallyConstantSheaf_upperStar_homology
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : Etale.DerivedCategory.boundedConstructible A X K) :
    ∃ R : Stratification X, ∀ (n : ℤ) l, IsFiniteLocallyConstantSheaf
      ((Etale.upperStar A (R.immersion l)).obj
        ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  obtain ⟨R, hR⟩ := exists_stratification_isFiniteLocallyConstantSheaf_upperStar
    (Finset.Icc a b) (fun n ↦ (DerivedCategory.homologyFunctor _ n).obj K) fun n _ ↦ hc n
  refine ⟨R, fun n l ↦ ?_⟩
  by_cases hn : n ∈ Finset.Icc a b
  · exact hR n hn l
  · refine IsFiniteLocallyConstantSheaf.of_isZero (Functor.map_isZero _ ?_)
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · exact DerivedCategory.isZero_of_isGE K a n h
    · exact DerivedCategory.isZero_of_isLE K b n h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) {T Y : Scheme.{u}} (g : T ⟶ Y)
  {𝕜 : Type u} [Field 𝕜]

/-- **A stratification for the higher direct images of `Λ ⧸ I`.** Let `g : T ⟶ Y` be a
quasi-compact morphism of schemes locally of finite type over a field, `Y` quasi-compact, and
`Λ ⧸ I` finite with exponent invertible on `T`. Then there is a stratification of `Y` over
whose strata all the higher direct images `Rᵏg_* (Λ ⧸ I)_T` are finite locally constant: they
are the homology sheaves of the bounded constructible complex `Rg_* (Λ ⧸ I)_T`
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`). -/
theorem exists_stratification_flcProperty_rightDerived_constantQuotSheaf [Finite (Λ ⧸ I)]
    [HasInvertibleExponent (Λ ⧸ I) T] [QuasiCompact g] (aT : T ⟶ Spec (.of 𝕜))
    (aY : Y ⟶ Spec (.of 𝕜)) [LocallyOfFiniteType aT] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hg : g ≫ aY = aT) :
    ∃ R : Stratification Y, ∀ (k : ℕ) l, flcProperty (R.domain l)
      ((R.immersion l)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj
        (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived k).obj (constantQuotSheaf Λ I T))) := by
  have : IsConstructibleSheaf (constantQuotSheaf Λ I T) :=
    IsFiniteLocallyConstantSheaf.isConstructibleSheaf inferInstance
  obtain ⟨R, hR⟩ := exists_stratification_isFiniteLocallyConstantSheaf_upperStar_homology _
    (boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (Λ ⧸ I) g aT aY hg _
      (DerivedCategory.boundedConstructible_singleFunctor_obj (constantQuotSheaf Λ I T) 0))
  refine ⟨R, fun k l ↦ ?_⟩
  have := hR k l
  exact IsFiniteLocallyConstantSheaf.of_iso ((R.immersion l)^*[ModuleCat.{u + 1} (Λ ⧸ I)].mapIso
    (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)]).homologyRightDerivedFunctorObjSingleFunctorIso _ k))

variable {I} {ϖ : Λ}

/-- **The uniform stratification of the tower `n ↦ Hᵏ(Rg_* (Λ ⧸ Iⁿ))`.** In the situation of
`AlgebraicGeometry.Etale.exists_stratification_flcProperty_rightDerived_constantQuotSheaf`, with
moreover `Λ` noetherian, `I = (ϖ)` for a nonzerodivisor `ϖ` and all `Λ ⧸ Iⁿ` finite, there is a
stratification of `Y` over whose strata all the levels of all the towers
`n ↦ Hᵏ(Rg_* (Λ ⧸ Iⁿ))`, `k : ℤ`, are `IsSetFLC`. -/
theorem exists_stratification_isSetFLC_upperStar_higherDirectImageQuotPowTower
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) [IsNoetherianRing Λ]
    [∀ n, Finite (Λ ⧸ I ^ n)] [Finite (Λ ⧸ I)] [HasInvertibleExponent (Λ ⧸ I) T] [QuasiCompact g]
    (aT : T ⟶ Spec (.of 𝕜)) (aY : Y ⟶ Spec (.of 𝕜)) [LocallyOfFiniteType aT]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) :
    ∃ R : Stratification Y, ∀ l (n : ℕ) (k : ℤ), IsSetFLC
      ((R.immersion l)^*[ModuleCat.{u + 1} Λ].obj
        ((higherDirectImageQuotPowTower I g k).obj (op n))) := by
  obtain ⟨R, hR⟩ := exists_stratification_flcProperty_rightDerived_constantQuotSheaf I g aT aY hg
  exact ⟨R, fun l n k ↦ isSetFLC_upperStar_higherDirectImageQuotPowTower_obj_of_flcProperty_one
    g (R.immersion l) hϖ hI (fun k ↦ hR k l) n k⟩

end AlgebraicGeometry.Etale
