/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarCoproduct
public import WeilConjectures.SixFunctors.ProEtale.Adic.ProperLowerStarCondensedAdjoint
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The proper direct image of Weil complexes is a left adjoint

For a proper morphism `g : Z ⟶ Y` of `k₀`-schemes, `Y` separated of finite type over `k₀`,
the derived direct image `Rg_*` of Weil complexes has a right adjoint
(`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerStar_of_isProper`). The Weil
structure is lifted along the abstract result
`CategoryTheory.Endofunctor.IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor`
from the adjunction `Rḡ_* ⊣ ḡ^!` on `Dᵇc(-, ℚ̄_ℓ)` over the algebraic closure of `k₀`
(`ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar_of_isProper`)
and the commutation of `Rḡ_*` with bounded below coproducts
(`AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

instance : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ CharP.char_is_prime k₀ (ringChar k₀)⟩

instance : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ Fact.out⟩

section Frobenius

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The Frobenius pullback of a constructible sheaf is constructible. -/
theorem WeilSheaf.isAdicConstructibleSheaf_frobeniusPullback_obj
    {H : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hH : ProEtale.IsAdicConstructibleSheaf H) :
    ProEtale.IsAdicConstructibleSheaf ((WeilSheaf.frobeniusPullback k₀ l X).obj H) :=
  (hH.upperStar _).of_iso ((ProEtale.adicUpperStarIsoLowerStarInv l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).app H)

omit [Fact (ringChar k₀ ≠ l)] in
/-- A sheaf whose Frobenius pullback is constructible is constructible. -/
theorem WeilSheaf.isAdicConstructibleSheaf_of_frobeniusPullback_obj
    {H : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hH : ProEtale.IsAdicConstructibleSheaf ((WeilSheaf.frobeniusPullback k₀ l X).obj H)) :
    ProEtale.IsAdicConstructibleSheaf H :=
  let Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  (hH.upperStar Fr.inv).of_iso ((ProEtale.adicUpperStarIsoLowerStarInv l Fr.symm).app _ ≪≫
    ((ProEtale.adicLowerStarEquivalence l Fr.symm).unitIso.app H).symm)

omit [Fact (ringChar k₀ ≠ l)] in
/-- A complex of `ℓ`-adic sheaves on the geometric fiber is bounded with constructible
cohomology if and only if its Frobenius pullback is: the Frobenius pullback is an exact
autoequivalence preserving and reflecting constructibility. -/
theorem WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
    (K : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    ProEtale.DerivedCategory.boundedConstructibleAdic l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.obj K) ↔
      ProEtale.DerivedCategory.boundedConstructibleAdic l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber K := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ⟨fun hK ↦ ⟨Functor.bounded_of_bounded_mapDerivedCategory_obj _ hK.1, fun n ↦ ?_⟩,
    fun hK ↦ ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦ ?_⟩⟩
  · exact WeilSheaf.isAdicConstructibleSheaf_of_frobeniusPullback_obj
      ((ProEtale.adicConstructibleSheaf l _).prop_of_iso
        (((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategoryHomologyFunctorIso n).symm.app K)
        (hK.2 n))
  · exact (ProEtale.adicConstructibleSheaf l _).prop_of_iso
      (((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategoryHomologyFunctorIso n).app K)
      (WeilSheaf.isAdicConstructibleSheaf_frobeniusPullback_obj (hK.2 n))

end Frobenius

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper g] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The proper direct image of Weil complexes is a left adjoint** (blueprint
`theorem-verdier-biduality`, the constructible adjunction `Rf_! ⊣ Rf^!` for a proper `f`):
for a proper morphism `g : Z ⟶ Y` of `k₀`-schemes, `Y` separated of finite type over `k₀`, the
derived direct image `Rg_*` of Weil complexes has a right adjoint. The adjunction `Rḡ_* ⊣ ḡ^!` on
`Dᵇc(-, ℚ̄_ℓ)` over `k̄₀` lifts to Weil complexes
(`CategoryTheory.Endofunctor.IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor`),
`Rḡ_*` commuting with bounded below coproducts. -/
theorem WeilComplex.isLeftAdjoint_derivedLowerStar_of_isProper :
    (derivedLowerStar (k₀ := k₀) (l := l) g).IsLeftAdjoint := by
  have : IsProper (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) g _ ‹_›
  have hk := ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)
  have : IsSeparated (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  exact IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))
    (ProEtale.DerivedCategory.boundedConstructibleAdic l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (ProEtale.DerivedCategory.boundedConstructibleAdic l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK)
    WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
    (fun K hK ↦
      (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff K).2 hK)
    (fun _ hK ↦ ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure hk _ hK)
    (ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar_of_isProper k₀
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure hk _)
    (ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar _)
    (WeilComplex.objectProperty k₀ l Z) (WeilComplex.objectProperty k₀ l Y)
    (WeilComplex.objectProperty_iff (X := Z)) (WeilComplex.objectProperty_iff (X := Y))
    (WeilComplex.objectProperty_rightDerivedLowerStar g)

end AlgebraicGeometry
