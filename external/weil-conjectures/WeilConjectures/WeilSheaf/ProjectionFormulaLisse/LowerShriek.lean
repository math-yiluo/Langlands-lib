/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraMapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseTensor
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.ProjectionFormulaLisse.ExtensionByZero
public import WeilConjectures.WeilSheaf.UpperStarComp
public import WeilConjectures.WeilSheaf.UpperStarId

/-!
# The projection formula for `Rf₀!` and lisse Weil sheaves

Blueprint `sec-Weil-complexes` (the projection formula): for a separated quasi-compact morphism
`f : X ⟶ Y` locally of finite type of `k₀`-schemes and a lisse Weil sheaf `G` on `Y`,
`G ⊗ Rf₀! K ≅ Rf₀!(f^* G ⊗ K)` naturally in the Weil complex `K`
(`AlgebraicGeometry.WeilComplex.derivedLowerShriekCompTensorLisseIso`).

The tensor product with `G` is the derived functor of the exact functor `[G^∨, -]`. For the
chosen compactification `X ⟶[j] Z ⟶[g] Y` of `f`, `Rf₀! = Rg_* ∘ j_!`, and the isomorphism is
assembled from

* the projection formula `[A, g_* N] ≅ g_* [g^* A, N]` for the pushforward
  (`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso`), which derives to
  `[A, Rg_* N] ≅ Rg_* [g^* A, N]` since `[A, -]` is exact and `[g^* A, -]` preserves K-injective
  complexes after forgetting the Weil structures
  (`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIso`,
  `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesKInjectiveComplexes_ihom`);
* the compatibility `j_! [j^* B, N] ≅ [B, j_! N]` of extension by zero with internal homs
  (`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompIhomFunctorIso`);
* `(f^* G)^∨ ≅ f^* (G^∨) ≅ j^* g^* (G^∨)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

attribute [local instance] Compactification.over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- **The projection formula for `Rg_*`**: for a pro-étale Weil sheaf `A` on `Y` with lisse
underlying sheaf, `R[A, -] ∘ Rg_* ≅ Rg_* ∘ R[g^* A, -]`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerStarCompIhomFunctorIso {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (A : ProEtaleWeilSheaf k₀ l Y) (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l Z
          ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A)).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor := by
  have hB : ProEtale.IsAdicLisseSheaf ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A).carrier :=
    ProEtale.IsAdicLisseSheaf.upperStar _ hA
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor A hA
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor
    ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A) hB
  have := hB.preservesKInjectiveComplexes_ihom
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have e₁ : (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l g ⋙
        ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctor :=
    Functor.isoWhiskerLeft _
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm
  have e₂ : (ProEtaleWeilSheaf.ihomFunctor k₀ l Z ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A) ⋙
        ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l Z
          ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A)).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor :=
    IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIso
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _)) _
      (ProEtaleWeilSheaf.ihomFunctorCompForgetIso k₀ l Z _)
  exact e₁ ≪≫ Functor.rightDerivedFunctorNatIso
    (ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso g A hA) ≪≫ e₂ ≪≫
    Functor.isoWhiskerRight (ProEtaleWeilSheaf.ihomFunctor k₀ l Z
      ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A)).rightDerivedFunctorIsoMapDerivedCategory.symm _

/-- Extension by zero along a quasi-compact open immersion `j` commutes with the derived internal
hom out of a pro-étale Weil sheaf `B` with lisse underlying sheaf:
`R[B, -] ∘ j_! ≅ j_! ∘ R[j^* B, -]`. -/
noncomputable def ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompIhomFunctorIso
    {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (B : ProEtaleWeilSheaf k₀ l X) (hB : ProEtale.IsAdicLisseSheaf B.carrier) :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.ihomFunctor k₀ l X B).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l U
          ((ProEtaleWeilSheaf.upperStar k₀ l j).obj B)).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory := by
  have hjB : ProEtale.IsAdicLisseSheaf ((ProEtaleWeilSheaf.upperStar k₀ l j).obj B).carrier :=
    ProEtale.IsAdicLisseSheaf.upperStar _ hB
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor B hB
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor
    ((ProEtaleWeilSheaf.upperStar k₀ l j).obj B) hjB
  exact Functor.isoWhiskerLeft _
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X B).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtaleWeilSheaf.extensionByZeroCompIhomFunctorIso j B hB).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight (ProEtaleWeilSheaf.ihomFunctor k₀ l U
      ((ProEtaleWeilSheaf.upperStar k₀ l j).obj B)).rightDerivedFunctorIsoMapDerivedCategory.symm _

/-- **The projection formula for `Rf_!` on derived categories of pro-étale Weil sheaves**: for a
compactification `X ⟶[j] Z ⟶[g] Y` of `f` with `j` quasi-compact, a pro-étale Weil sheaf `A` on
`Y` with lisse underlying sheaf and `A' ≅ j^* g^* A`, `R[A, -] ∘ Rf_! ≅ Rf_! ∘ R[A', -]`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriekCompIhomFunctorIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) [QuasiCompact c.i]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (A : ProEtaleWeilSheaf k₀ l Y) (hA : ProEtale.IsAdicLisseSheaf A.carrier)
    (A' : ProEtaleWeilSheaf k₀ l X)
    (e : A' ≅ (ProEtaleWeilSheaf.upperStar k₀ l c.i).obj
      ((ProEtaleWeilSheaf.upperStar k₀ l c.g).obj A)) :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X A').rightDerivedFunctor ⋙
        ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c := by
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  rw [ProEtaleWeilSheaf.rightDerivedLowerShriek]
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.rightDerivedLowerStarCompIhomFunctorIso c.g A hA) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompIhomFunctorIso
      c.i ((ProEtaleWeilSheaf.upperStar k₀ l c.g).obj A)
      (ProEtale.IsAdicLisseSheaf.upperStar _ hA)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso
      (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft e)) _

/-- Blueprint `sec-Weil-complexes` (the projection formula): for a separated quasi-compact
morphism `f : X ⟶ Y` locally of finite type of `k₀`-schemes of finite type and a lisse Weil sheaf
`G` on `Y`, `G ⊗ Rf₀! K ≅ Rf₀!(f^* G ⊗ K)` naturally in the Weil complex `K`
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriekCompIhomFunctorIso` for the chosen
compactification of `f`, with `(f^* G)^∨ ≅ f^* (G^∨) ≅ j^* g^* (G^∨)`). -/
noncomputable def WeilComplex.derivedLowerShriekCompTensorLisseIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.tensorLisse G hG ≅
      WeilComplex.tensorLisse ((WeilSheaf.upperStar f).obj G)
          (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        WeilComplex.derivedLowerShriek k₀ l f := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  -- `c.Z` is noetherian, being proper over the noetherian `Y`; so the open immersion `c.i` is
  -- quasi-compact.
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : QuasiCompact c.i := inferInstance
  let e : (((WeilSheaf.upperStar f).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj ≅
      (ProEtaleWeilSheaf.upperStar k₀ l c.i).obj
        ((ProEtaleWeilSheaf.upperStar k₀ l c.g).obj (G.dual hG).obj) :=
    (ObjectProperty.ι _).mapIso (WeilSheaf.upperStarDualIso f G hG) ≪≫
      (ProEtaleWeilSheaf.upperStarCongrIso (k₀ := k₀) (l := l) c.comm).app _ ≪≫
      (ProEtaleWeilSheaf.upperStarCompIso (k₀ := k₀) (l := l) c.i c.g).app _
  exact ((WeilComplex.objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso _ hG.dual) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (ProEtaleWeilSheaf.rightDerivedLowerShriekCompIhomFunctorIso f c _ hG.dual _ e) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry
