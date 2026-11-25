/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfBoundedBelow
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit

/-!
# The derived direct image of `ℓ`-adic sheaves commutes with bounded below coproducts

For a quasi-compact quasi-separated morphism `f : Y ⟶ X`, the derived direct image
`Rf_* : D(AdicSheaf l Y) ⥤ D(AdicSheaf l X)` commutes with coproducts of uniformly bounded below
families (`AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar`,
blueprint `corollary-continuity-cohomology--2`; SGA 4 VI 5.1).

The proof has three steps:

* the higher direct images `Rᵠf_*` of `ℓ`-adic sheaves commute with direct sums
  (`AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerived_adicLowerStar`): taking
  underlying abelian sheaves preserves direct sums, reflects isomorphisms and commutes with
  `Rᵠf_*` (`AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarToAbIso`), and the statement for
  abelian sheaves is
  `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`;
* hence `Rf_*` commutes with direct sums of sheaves placed in degree `0`, by comparing
  cohomology sheaves, and then with direct sums of uniformly bounded families, by dévissage
  (`DerivedCategory.isIso_sigmaComparison_of_isGE_of_isLE_of_homologyProperty`);
* finally the way-out argument `DerivedCategory.isIso_sigmaComparison_of_isGE`, `Rf_*` being
  left t-exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-- In the Grothendieck abelian category of `ℓ`-adic sheaves, direct sums are exact. -/
lemma hasExactColimitsOfShape_discrete_adicSheaf (X : Scheme.{u}) (B : Type) :
    HasExactColimitsOfShape (Discrete B) (AdicSheaf l X) :=
  IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1, 0} _ B

attribute [local instance] hasExactColimitsOfShape_discrete_adicSheaf

/-- Taking underlying abelian sheaves of `ℓ`-adic sheaves commutes with direct sums. -/
instance preservesColimitsOfShape_discrete_adicSheafToAb (X : Scheme.{u}) (B : Type) :
    PreservesColimitsOfShape (Discrete B) (AdicSheaf.toAb l X) := by
  have : PreservesColimitsOfShape (Discrete B) (AdicSheaf.forget (l := l) X) :=
    preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts _
  have : PreservesColimitsOfShape (Discrete B) (weilCoefficientsForgetAb l X) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{u + 1}) _
  infer_instance

section

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]

/-- **Higher direct images of `ℓ`-adic sheaves commute with direct sums**, for a quasi-compact
quasi-separated morphism: this holds on underlying abelian sheaves. -/
lemma isIso_sigmaComparison_rightDerived_adicLowerStar {B : Type} (q : ℕ)
    (N : B → AdicSheaf l Y) :
    IsIso (sigmaComparison (((f)_*ᵃ[l]).rightDerived q) N) := by
  have := preservesColimitsOfShape_discrete_rightDerived_lowerStar f B q
  have : IsIso (sigmaComparison (AdicSheaf.toAb l Y ⋙ ((f)_*[Ab.{u + 1}]).rightDerived q) N) := by
    rw [sigmaComparison_comp]
    infer_instance
  have h := isIso_sigmaComparison_of_natIso (rightDerivedAdicLowerStarToAbIso l f q).symm N
  rw [sigmaComparison_comp] at h
  have := IsIso.of_isIso_comp_left (sigmaComparison (AdicSheaf.toAb l X) _)
    ((AdicSheaf.toAb l X).map (sigmaComparison (((f)_*ᵃ[l]).rightDerived q) N))
  exact isIso_of_reflects_iso _ (AdicSheaf.toAb l X)

/-- The derived direct image of `ℓ`-adic sheaves commutes with direct sums of sheaves placed in
degree `0`, for a quasi-compact quasi-separated morphism. -/
lemma isIso_sigmaComparison_rightDerivedFunctor_adicLowerStar_singleFunctor {B : Type}
    (N : B → AdicSheaf l Y) :
    IsIso (sigmaComparison ((f)_*ᵃ[l]).rightDerivedFunctor
      fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j)) := by
  suffices IsIso (sigmaComparison
      (DerivedCategory.singleFunctor _ 0 ⋙ ((f)_*ᵃ[l]).rightDerivedFunctor) N) by
    rw [sigmaComparison_comp] at this
    exact IsIso.of_isIso_comp_right _ (((f)_*ᵃ[l]).rightDerivedFunctor.map
      (sigmaComparison (DerivedCategory.singleFunctor _ 0) N))
  rw [DerivedCategory.isIso_sigmaComparison_iff]
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have := isIso_sigmaComparison_rightDerived_adicLowerStar f q N
    exact isIso_sigmaComparison_of_natIso
      (((f)_*ᵃ[l]).singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso q).symm N
  · refine isIso_sigmaComparison_of_isZero _ _ fun F ↦ ?_
    have := ((f)_*ᵃ[l]).isGE_rightDerivedFunctor_obj_singleFunctor F
    exact DerivedCategory.isZero_of_isGE (((f)_*ᵃ[l]).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) 0 n (by lia)

end

/-- **The derived direct image commutes with bounded below coproducts** (SGA 4 VI 5.1;
Bhatt–Scholze, *The pro-étale topology for schemes*, the pro-étale topos of a qcqs scheme being
coherent): for a quasi-compact quasi-separated morphism `f : Y ⟶ X`, the derived direct image
`Rf_*` of `ℓ`-adic pro-étale sheaves preserves the coproduct of a `ℤ`-indexed family of
complexes which are uniformly bounded below. -/
theorem preservesColimit_discrete_rightDerivedFunctor_adicLowerStar {Y X : Scheme.{u}}
    (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (K : ℤ → DerivedCategory (ProEtale.AdicSheaf l Y))
    (a : ℤ) (hK : ∀ n, (K n).IsGE a) :
    PreservesColimit (Discrete.functor K) (ProEtale.adicLowerStar l f).rightDerivedFunctor := by
  have := DerivedCategory.isIso_sigmaComparison_of_isGE _
    (fun M b hM ↦
      have := hM
      (ProEtale.adicLowerStar l f).isGE_rightDerivedFunctor_obj M b)
    (fun N b c hN ↦ DerivedCategory.isIso_sigmaComparison_of_isGE_of_isLE_of_homologyProperty _ ⊤
      (fun N _ ↦ isIso_sigmaComparison_rightDerivedFunctor_adicLowerStar_singleFunctor f N)
      N b c fun j ↦ ⟨fun _ ↦ trivial, hN j⟩) K a hK
  exact PreservesCoproduct.of_iso_comparison _ _

end ProEtale

end AlgebraicGeometry
