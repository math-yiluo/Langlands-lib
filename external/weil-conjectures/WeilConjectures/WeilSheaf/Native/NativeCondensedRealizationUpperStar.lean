/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MatesHCompIsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunctionMate

/-!
# The condensed realization commutes with pullback and pushforward

Let `g : Z ⟶ Y` be a morphism of `k₀`-schemes and `ḡ : Z̄ ⟶ Ȳ` its base change to the geometric
fibres. The condensed realization `N_X` of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealization`) commutes with pullback: forgetting
the Weil structure commutes strictly with `g^*`, and the condensed model commutes with `ḡ^*`
(`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`). This gives an isomorphism
`N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z` (`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso`),
and on derived categories an isomorphism
`D(N_Y) ⋙ Lḡ^* ≅ D(g^*) ⋙ D(N_Z)`
(`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`).

Its mate under the derived adjunctions `D(g^*) ⊣ Rg_*` and `Lḡ^* ⊣ Rḡ_*` is the base change map
`Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*`, and it is an isomorphism
(`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_mateEquiv_derivedCondensedRealizationUpperStarIso`):
the underived base change map is invertible (forgetting the Weil structure commutes with the
pushforward, and so does the condensed model, being an equivalence), and `N_Z` preserves
K-injective complexes (`CategoryTheory.Adjunction.isIso_mateEquiv_mapDerivedCategorySquareIso`).

On complexes, the derived comparison is the counit of `Lḡ^*` followed by the termwise
comparison
(`AlgebraicGeometry.ProEtaleWeilSheaf.whiskerLeft_Q_derivedCondensedRealizationUpperStarIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The condensed realization preserves K-injective complexes: forgetting the Weil structure is
right adjoint to an exact functor
(`CategoryTheory.Endofunctor.IsoAlgebra.preservesKInjectiveComplexes_forget`)
and the condensed model is an equivalence. -/
instance preservesKInjectiveComplexes_condensedRealization (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    (condensedRealization k₀ l X).PreservesKInjectiveComplexes := by
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have : (adicSheafEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.PreservesKInjectiveComplexes :=
    Equivalence.preservesKInjectiveComplexes_functor _
  infer_instance

/-- The condensed realization commutes with pullback: `N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z`. Forgetting the
Weil structure commutes strictly with `g^*`, and the condensed model commutes with `ḡ^*` by
`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`. -/
noncomputable def condensedRealizationUpperStarIso :
    condensedRealization k₀ l Y ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) ≅
      upperStar k₀ l g ⋙ condensedRealization k₀ l Z :=
  Functor.isoHComp (IsoAlgebra.mapOfNatIsoCompForgetIso _).symm
    (adicUpperStarCompCondensedModIso l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).symm

/-- The underived base change map `g_* ⋙ N_Y ⟶ N_Z ⋙ ḡ_*`, the mate of
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso` under `g^* ⊣ g_*` and
`ḡ^* ⊣ ḡ_*`, is an isomorphism: forgetting the Weil structure commutes with `g_*`, and the
condensed model, an equivalence, commutes with `ḡ_*`. -/
instance isIso_mateEquiv_condensedRealizationUpperStarIso :
    IsIso (mateEquiv (upperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationUpperStarIso k₀ l g).hom) := by
  have h₁ : IsIso (mateEquiv (upperStarLowerStarAdjunction k₀ l g)
      (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (IsoAlgebra.mapOfNatIsoCompForgetIso _).symm.hom) :=
    IsoAlgebra.isIso_mateEquiv_mapOfNatIsoCompForgetIso_inv _ _ _ _
  have h₂ : IsIso (mateEquiv (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g
          (comp_over g (Spec (CommRingCat.of k₀))))).symm.hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Adjunction.isIso_mateEquiv_app_of_isIso _ _ _
      (adicSheafEquivCondensedMod l _).toAdjunction (adicSheafEquivCondensedMod l _).toAdjunction M
  exact isIso_mateEquiv_isoHComp (upperStarLowerStarAdjunction k₀ l g)
    (adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) _ _

/-- The condensed realization commutes with pullback on derived categories:
`D(N_Y) ⋙ Lḡ^* ≅ D(g^*) ⋙ D(N_Z)`. It is the identification `Lḡ^* ≅ D(ḡ^*)` of the derived
pullback of module objects with the levelwise one, followed by the isomorphism induced by
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso`. -/
noncomputable def derivedCondensedRealizationUpperStarIso :
    derivedCondensedRealization k₀ l Y ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor ≅
      (upperStar k₀ l g).mapDerivedCategory ⋙ derivedCondensedRealization k₀ l Z :=
  Functor.leftDerivedFunctorSquareIso (condensedRealizationUpperStarIso k₀ l g)

/-- The derived base change map `Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*`, the mate of
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso` under the derived
adjunctions `D(g^*) ⊣ Rg_*` and `Lḡ^* ⊣ Rḡ_*`, is an isomorphism: the underived base change
map is invertible and `N_Z` preserves K-injective complexes. -/
instance isIso_mateEquiv_derivedCondensedRealizationUpperStarIso :
    IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (derivedCondensedRealizationUpperStarIso k₀ l g).hom) :=
  Adjunction.isIso_mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso
    (upperStarLowerStarAdjunction k₀ l g)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (condensedRealizationUpperStarIso k₀ l g)

/-- **The derived pullback comparison on complexes.** After precomposition with
`Q : CochainComplex _ ℤ ⥤ DerivedCategory _`,
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso` is the counit
`Lḡ^* (Qh (N_Y P)) ⟶ Qh (ḡ^* (N_Y P))` of the derived pullback of module objects followed by the
image under `Q` of the termwise isomorphism
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso`, up to the factorizations
of `D(N_Y)`, `D(g^* ⋙ N_Z)` through `Q` and of `Q` through `Qh`. No K-flatness is needed, the
pullback `ḡ^*` of module objects being exact. This is
`CategoryTheory.Functor.whiskerLeft_Q_leftDerivedFunctorSquareIso_hom`; its components at a
complex `P` are obtained with `CategoryTheory.NatTrans.congr_app`. -/
lemma whiskerLeft_Q_derivedCondensedRealizationUpperStarIso_hom :
    Functor.whiskerLeft DerivedCategory.Q (derivedCondensedRealizationUpperStarIso k₀ l g).hom =
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (condensedRealization k₀ l Y).mapDerivedCategoryFactors.hom
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor ≫
      Functor.whiskerRight (Functor.whiskerLeft
        ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).inv)
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctorCounit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom DerivedCategory.Qh ≫
      Functor.whiskerRight (Functor.whiskerLeft
        ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).mapHomotopyCategoryFactors (.up ℤ)).hom)
        DerivedCategory.Qh ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso _).hom ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
        (condensedRealizationUpperStarIso k₀ l g) (.up ℤ)).hom DerivedCategory.Q ≫
      (upperStar k₀ l g ⋙ condensedRealization k₀ l Z).mapDerivedCategoryFactors.inv ≫
      Functor.whiskerLeft DerivedCategory.Q
        (Functor.mapDerivedCategoryCompIso (upperStar k₀ l g) (condensedRealization k₀ l Z)).inv :=
  Functor.whiskerLeft_Q_leftDerivedFunctorSquareIso_hom _

end AlgebraicGeometry.ProEtaleWeilSheaf
