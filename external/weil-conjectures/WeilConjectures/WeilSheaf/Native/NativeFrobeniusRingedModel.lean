/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.WeilSheaf.Category
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusComparison
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality

/-! # An ordinary coefficient model intertwining geometric Frobenius

Source: the underived coefficient comparison in the internal-Hom paragraph of
prose-10-20; Stacks 00YV and 03D6.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwistedActionRingedSite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Ordinary module sheaves with their Frobenius comparison. This is data about
ordinary sheaves, before forming any category of fixed pairs.
Source: native ringed presentation, step 1
(blueprint: lem-sf-native-frobenius-ringed-model). -/
structure NativeFrobeniusRingedModel
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] where
  /-- The small ordinary pro-etale model. -/
  C : Type (u + 1)
  /-- The category structure includes morphisms in the same universe. -/
  [category : SmallCategory C]
  /-- Pullbacks are needed for the twisted action-site construction. -/
  [pullbacks : HasPullbacks C]
  /-- The ordinary topology. -/
  J : GrothendieckTopology C
  /-- Inverse geometric Frobenius on the site. -/
  s : C ≌ C
  /-- Translation preserves sheaves. -/
  [continuous : s.functor.IsContinuous J J]
  /-- Inverse translation preserves sheaves. -/
  [inverseContinuous : s.inverse.IsContinuous J J]
  /-- The continuous, locally finite-subextension coefficient ring. -/
  R : Sheaf J CommRingCat.{u + 1}
  /-- The coefficient identification preserves values of functions. -/
  a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj R ≅ R
  /-- Ordinary sectionwise modules realize the actual native adic modules. -/
  E : Modules R ≌ ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  /-- Sums of module maps are unchanged. -/
  additive : E.functor.Additive
  /-- The ordinary realization intertwines the two actual pullbacks. -/
  comparison : E.functor ⋙ WeilSheaf.frobeniusPullback k₀ l X ≅
    sigma J s R a ⋙ E.functor

  /-- The ordinary internal Hom comparison, before imposing a Weil structure. -/
  hom (M N : Modules R) :
    E.functor.obj (SheafOfModules.homObj (R := R) M N) ≅
      (ProEtale.AdicSheaf.ihom (E.functor.obj M)).obj (E.functor.obj N)
  /-- Ordinary local maps act by precomposition and postcomposition. -/
  hom_naturality {M M' N N' : Modules R} (f : M' ⟶ M) (g : N ⟶ N') :
    E.functor.map (SheafOfModules.homObjMap (R := R) f g) ≫ (hom M' N').hom =
      (hom M N).hom ≫ (Mod.ihomMap (E.functor.map f)).app _ ≫
        (ProEtale.AdicSheaf.ihom (E.functor.obj M')).map (E.functor.map g)
  /-- The ordinary Hom comparison commutes with translation. Only ordinary modules
  occur here: there are no structure maps theta and no fixed-pair categories.
  The presentation's sigmaHom is normalized uniquely by evaluation. -/
  hom_frobenius (P : Presentation J s R a) (M N : Modules R) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (hom M N).hom ≫
        (ProEtale.adicLowerStarCompIhomIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
          (E.functor.obj M)).inv.app (E.functor.obj N) ≫
        (Mod.ihomMap (comparison.app M).inv).app _ ≫
          (ProEtale.AdicSheaf.ihom (E.functor.obj ((sigma J s R a).obj M))).map
            (comparison.app N).hom =
      comparison.hom.app (SheafOfModules.homObj (R := R) M N) ≫
        E.functor.map (P.sigmaHom M N).hom ≫ (hom _ _).hom

attribute [instance] NativeFrobeniusRingedModel.category NativeFrobeniusRingedModel.pullbacks
  NativeFrobeniusRingedModel.continuous NativeFrobeniusRingedModel.inverseContinuous

/-- Ordinary native adic sheaves have a small sectionwise coefficient realization
intertwining their Frobenius pullback.

Source: prose-10-20, internal-Hom paragraph; native ringed
presentation step 1; Stacks 00YV and 03D6
(blueprint: lem-sf-native-frobenius-ringed-model).

Proof: take the bounded pro-etale site of the geometric fiber and lift its hom
sets to universe u+1 with AsSmall. Transport the pro-etale topology along the
resulting equivalence. Postcomposition by inverse geometric Frobenius is an
orbit-stable autoequivalence and preserves covers, because domains and underlying
arrows of a covering family are unchanged. Pullbacks are transported from the
bounded site. Restrict comparisonRing l to this small site. Its sections are the
native locally finite continuous coefficient functions. The coefficient
identification under translation is the identity on those functions; in
particular it preserves their finite field of definition. Combine the inverse
small-site module restriction equivalence with the inverse of the native
section-module equivalence comparisonModuleFunctor. This gives E, which is
additive since each comparison preserves the actual section maps. For the
comparison of pullbacks, identify postcomposition by Frobenius with base change
by inverse Frobenius using the pullback universal property. On coefficient
sections this identification is the same precomposition of functions as in the
native adicLowerStar construction. The native action on tensor generators is
therefore the sectionwise scalar action after transport. The section-module
fully faithful functor lifts these section identifications to module
isomorphisms. Naturality follows from the unchanged section maps. These give
comparison with the displayed direction. All constructions apply to arbitrary
modules, including zero modules, and to an empty geometric fiber. The ordinary
Hom comparison is the transpose of evaluation through the tensor comparison.
Full faithfulness and both tensor-Hom adjunctions prove it invertible;
composition of local maps proves its two-variable naturality. On translated
slices both sides of hom_frobenius send a local map to the same translated local
map with its source and target relabeled by comparison. Evaluation determines
P.sigmaHom uniquely, by P.sigmaHom_evaluation; thus this square holds for every
presentation P. No fixed-pair category or equivariant Hom assertion is used. -/
theorem native_frobenius_ringed_model
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Nonempty (NativeFrobeniusRingedModel k₀ l X) := by
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let g := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).1
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).2
  obtain ⟨H⟩ := ProEtale.adicModuleHomComparisonCore l Y
  obtain ⟨c, hc⟩ := ProEtale.NativeFrobenius.nativeFrobeniusComparison Y l g H
  refine ⟨{
    C := WeilConjectures.WeilFrobeniusAction.Site Y
    category := inferInstance
    pullbacks := ?_
    J := WeilConjectures.WeilFrobeniusAction.topology Y
    s := WeilConjectures.WeilFrobeniusAction.translation g
    R := ProEtale.NativeFrobenius.ring Y l
    a := ProEtale.NativeFrobenius.ringIso Y l g
    E := ProEtale.NativeFrobenius.equivalence Y l
    additive := inferInstance
    comparison := c
    hom := ProEtale.NativeFrobenius.homComparison Y l H
    hom_naturality := ?_
    hom_frobenius := hc }⟩
  · exact Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.equiv.{u, u + 1, u + 1} :
        Y.ProEt ≌ WeilConjectures.WeilFrobeniusAction.Site Y).inverse
  · intro M M' N N' f h
    exact ProEtale.NativeFrobenius.homComparison_naturality Y l H f h

end AlgebraicGeometry.ProEtaleWeilSheaf
