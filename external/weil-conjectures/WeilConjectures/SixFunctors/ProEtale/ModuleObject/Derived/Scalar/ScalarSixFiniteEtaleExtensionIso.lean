/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientPullbackIso
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-! # Finite scalar realization of the canonical locally closed extension

Source: blueprint scalar-six-ctf (1), comparison of locally closed extensions.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

public noncomputable section

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- The specified finite comparison realization is the functor of the finite-discrete
coefficient equivalence for the canonical internal module encoding. -/
def finiteComparisonRealizationEncodingIso (T : Scheme.{u}) :
    finiteComparisonRealization A T eR ≅
      (finiteDiscreteCoefficientEquivalence A eR
        (CondensedQbarGeometricEvaluation.Ordinary.internalToModule (ULift.{u + 1} A))
        rfl T).functor :=
  realizedEncodingIso A T eR

end AlgebraicGeometry.ProEtale.CondensedRing

end

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- Finite comparison realization commutes with extension by zero along an open
immersion, by pullback compatibility and uniqueness of left adjoints. -/
def finiteComparisonRealizationOpenIso {S T : Scheme.{u}} (j : S ⟶ T)
    [IsOpenImmersion j] :
    finiteComparisonRealization A S eR ⋙
        openImmersionLowerShriek (Profinite.continuousMapRingObj A) j ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j ⋙
        finiteComparisonRealization A T eR := by
  let ES := finiteDiscreteCoefficientEquivalence A eR
    (CondensedQbarGeometricEvaluation.Ordinary.internalToModule (ULift.{u + 1} A)) rfl S
  let ET := finiteDiscreteCoefficientEquivalence A eR
    (CondensedQbarGeometricEvaluation.Ordinary.internalToModule (ULift.{u + 1} A)) rfl T
  let i := finiteDiscreteCoefficientProEtalePullbackIso A eR
    (CondensedQbarGeometricEvaluation.Ordinary.internalToModule (ULift.{u + 1} A)) rfl j
  let k := Iso.isoCompInverse (H := ES) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let adj₁ := ES.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.continuousMapRingObj A) j)
  let adj₂ := (ProEtale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).comp ET.toAdjunction
  exact Functor.isoWhiskerRight (finiteComparisonRealizationEncodingIso A eR S) _ ≪≫
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight kr) ≪≫
    Functor.isoWhiskerLeft _ (finiteComparisonRealizationEncodingIso A eR T).symm

/-- Finite comparison realization commutes with direct image, by restriction
compatibility of the finite-discrete coefficient equivalence. -/
def finiteComparisonRealizationLowerStarIso {S T : Scheme.{u}} (f : S ⟶ T) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        finiteComparisonRealization A T eR ≅
      finiteComparisonRealization A S eR ⋙ lowerStar (Profinite.continuousMapRingObj A) f :=
  Functor.isoWhiskerLeft _ (finiteComparisonRealizationEncodingIso A eR T) ≪≫
    (finiteDiscreteCoefficientRestrictionIso A eR
      (CondensedQbarGeometricEvaluation.Ordinary.internalToModule (ULift.{u + 1} A))
      rfl f).symm ≪≫
    Functor.isoWhiskerRight (finiteComparisonRealizationEncodingIso A eR S).symm _

/-- The heart-level finite scalar realization: étale-to-pro-étale comparison, finite
comparison realization, and coefficient restriction along `e`. -/
abbrev finiteScalarRealizationHeart (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⥤
      ModuleRingedComparison.internalModules Λ.X T :=
  comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T ⋙
    finiteComparisonRealization A T eR ⋙
      Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (coefficientMap e.hom.hom T)

/-- On a sheaf in degree zero, finite scalar realization is the degree-zero complex of
the heart-level realization. -/
def finiteScalarRealizationSingleIso (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (finiteScalarRealization A e eR T).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((finiteScalarRealizationHeart A e eR T).obj M) := by
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let H := finiteComparisonRealization A T eR
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.hom.hom T)
  exact U.mapDerivedCategory.mapIso
      (H.mapDerivedCategory.mapIso ((N.mapDerivedCategorySingleFunctor 0).app M) ≪≫
        (H.mapDerivedCategorySingleFunctor 0).app (N.obj M)) ≪≫
    (U.mapDerivedCategorySingleFunctor 0).app (H.obj (N.obj M))

/-- The étale/pro-étale comparison identifies the étale locally closed extension with
the pro-étale extension through the scheme-theoretic image. -/
def comparisonUpperStarExtensionIso {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj
        ((flatModelEtaleExtension _ a ha).obj L) ≅
      (by
        let : IsImmersion a := ha
        let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
        exact (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) a.imageι).obj
          ((ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) a.toImage).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).obj L))) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let := ProEtale.isIso_lowerStarComparisonUpperStarBaseChange a.imageι B
  exact (asIso (lowerStarComparisonUpperStarBaseChange a.imageι B)).app
      ((Etale.openImmersionLowerShriek B a.toImage).obj L) ≪≫
    (ProEtale.lowerStar B a.imageι).mapIso
      ((openImmersionLowerShriekComparisonUpperStarIso B a.toImage).app L)

/-- Finite comparison realization commutes with an open extension followed by a direct
image. -/
def finiteComparisonRealizationExtensionIso {S T X : Scheme.{u}}
    (j : S ⟶ T) [IsOpenImmersion j] (i : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (finiteComparisonRealization A X eR).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj
          ((ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj M)) ≅
      (lowerStar (Profinite.continuousMapRingObj A) i).obj
        ((openImmersionLowerShriek (Profinite.continuousMapRingObj A) j).obj
          ((finiteComparisonRealization A S eR).obj M)) :=
  (finiteComparisonRealizationLowerStarIso A eR i).app _ ≪≫
    (lowerStar (Profinite.continuousMapRingObj A) i).mapIso
      ((finiteComparisonRealizationOpenIso A eR j).symm.app M)

/-- Coefficient restriction commutes with an open extension followed by a direct
image. -/
def comapExtensionIso
    {R R' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj R'] [IsCommMonObj R']
    (c : R ⟶ R') [IsMonHom c] {S T X : Scheme.{u}}
    (j : S ⟶ T) [IsOpenImmersion j] (i : T ⟶ X)
    (M : ModuleRingedComparison.internalModules R' S) :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap c X)).obj
      ((lowerStar R' i).obj ((openImmersionLowerShriek R' j).obj M)) ≅
      (lowerStar R i).obj ((openImmersionLowerShriek R j).obj
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (coefficientMap c S)).obj M)) :=
  (comapLowerStarIso c i).app _ ≪≫
    (lowerStar R i).mapIso ((comapOpenImmersionLowerShriekIso c j).app M)

/-- The heart-level finite scalar realization commutes with the locally closed
extension through the scheme-theoretic image. -/
def finiteScalarRealizationHeartExtensionIso {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (finiteScalarRealizationHeart A e eR X).obj ((flatModelEtaleExtension _ a ha).obj L) ≅
      (by
        let : IsImmersion a := ha
        let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
        exact (lowerStar Λ.X a.imageι).obj
          ((openImmersionLowerShriek Λ.X a.toImage).obj
            ((finiteScalarRealizationHeart A e eR S).obj L))) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.hom.hom X)
  exact U.mapIso ((finiteComparisonRealization A X eR).mapIso
      (comparisonUpperStarExtensionIso A a ha L) ≪≫
      finiteComparisonRealizationExtensionIso A eR a.toImage a.imageι (N.obj L)) ≪≫
    comapExtensionIso (R := Λ.X) (R' := Profinite.continuousMapRingObj A) e.hom.hom
      a.toImage a.imageι ((finiteComparisonRealization A S eR).obj (N.obj L))

/-- Direct image along the closed image inclusion of an immersion into a Noetherian
scheme preserves finite colimits of internal modules. -/
theorem preservesFiniteColimits_lowerStar_imageι {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    PreservesFiniteColimits (lowerStar Λ.X a.imageι) := by
  obtain ⟨_, _, _, _, h, _⟩ :=
    ((coefficientHeart_locallyClosedExtension Λ.X X).2 S a ha).2.2.2.2.2
  exact h

/-- On a sheaf in degree zero, finite scalar realization commutes with the canonical
locally closed extension through the scheme-theoretic image.

Source: blueprint scalar-six-ctf (1), ordinary/internal compactification comparison and
coefficient-isomorphism transport.

Construction: Factor a through its scheme-theoretic image as an open immersion followed
by its closed image inclusion. The sheaf-level étale/pro-étale direct-image comparison
and open-extension comparison identify the two ordinary extensions. The specified
finite coefficient realization is isomorphic to the canonical module encoding;
restriction compatibility gives its closed-pushforward comparison, while pullback
compatibility and uniqueness of left adjoints give its open-extension comparison.
The two coefficient-restriction isomorphisms transport this identification along e.
Thus the heart realization commutes with the specified extension. Each of its three
exact functors commutes with the degree-zero single functor. Finally the closed
internal pushforward is exact by coefficientHeart_locallyClosedExtension, so its
right derived functor also agrees with the single functor on this input. Composing
these isomorphisms gives the result. Zero rings and empty strata need no exclusions. -/
def finiteScalarRealizationExtensionIso
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsNoetherian X.left]
    (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (finiteScalarRealization A e eR X.left).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension (ULift.{u + 1} A) a ha).obj L)) ≅
      (sfbLocallyClosedDerivedExtension Λ a ha).obj
        ((finiteScalarRealization A e eR S).obj
          ((DerivedCategory.singleFunctor _ 0).obj L)) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let J := openImmersionLowerShriek Λ.X a.toImage
  let P := lowerStar Λ.X a.imageι
  have : PreservesFiniteColimits P := preservesFiniteColimits_lowerStar_imageι a ha
  let F := sfbLocallyClosedDerivedExtension Λ a ha
  exact finiteScalarRealizationSingleIso A e eR X.left _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (finiteScalarRealizationHeartExtensionIso A e eR a ha L) ≪≫
    (F.mapIso (finiteScalarRealizationSingleIso A e eR S L) ≪≫
      P.rightDerivedFunctor.mapIso ((J.mapDerivedCategorySingleFunctor 0).app _) ≪≫
      P.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (P.mapDerivedCategorySingleFunctor 0).app _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
