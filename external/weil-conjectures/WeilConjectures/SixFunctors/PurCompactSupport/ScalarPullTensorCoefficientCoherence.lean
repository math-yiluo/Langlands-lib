/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullCoefficientTotalTensor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Tensor coherence for a geometric coefficient square

Source: Stacks Project, Tags 07A4, 07A6 and 0E48.
(blueprint: lem-sf-scalar-pull-tensor-coefficient-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction HasDerivedCategory.standard
  Functor.leftAdjoint proEtaleRingModulePullback proEtaleRingDerivedPullbackFactors
namespace WeilConjectures.PurCompactSupport
attribute [local instance 100000] coefficientAbSheafify coefficientAbLocallyBijective
  coefficientRingSheafify
attribute [local irreducible] scalarPull projectionOpenFactor openComparison
  SheafOfModules.monoidalCategory
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
  scalarPullComplex scalarPullModule scalarTensorTotal proEtaleTensorPullbackTotalIso
  pbcComplexCounit pbcExtensionCounit
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

private def scalarCounit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedExtend a ⟶
      (pbcExtend a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := pbcComplexCounit a P
  naturality := by
    intro P Q f
    have h := (AlgebraicGeometry.Scheme.complexCounitNat (pbcExtend a)
      (pbcDerivedExtend a) (pbcExtensionCounit a)).naturality f
    simpa only [AlgebraicGeometry.Scheme.complexCounitNat_app, pbcComplexCounit,
      reductionComplexCounit] using h

private theorem tensor_composite_normalize
    {B C : Type*} [Category B] [Category C]
    (H : B ⥤ C) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (mu : TB ⋙ H ⟶ (H.prod H) ⋙ TC)
    {X Y X' Y' Z W T : B} {X'' Y'' T' T'' : C}
    (t : Z ⟶ TB.obj (X, Y)) (u : X ⟶ X') (v : Y ⟶ Y')
    (p : H.obj X' ⟶ X'') (q : H.obj Y' ⟶ Y'')
    (z : Z ⟶ W) (d : W ⟶ T) (r : T ⟶ TB.obj (X', Y'))
    (c : H.obj T ⟶ T') (d' : T' ⟶ T'') (r' : T'' ⟶ TC.obj (X'', Y''))
    (hf : t ≫ TB.map (Prod.mkHom u v) = z ≫ d ≫ r)
    (hh : H.map r ≫ mu.app (X', Y') ≫ TC.map (Prod.mkHom p q) = c ≫ d' ≫ r') :
    H.map t ≫ mu.app (X, Y) ≫
      TC.map (Prod.mkHom (H.map u ≫ p) (H.map v ≫ q)) =
      H.map z ≫ H.map d ≫ c ≫ d' ≫ r' := by
  have hm := mu.naturality (Prod.mkHom u v)
  change H.map (TB.map (Prod.mkHom u v)) ≫ mu.app (X', Y') =
    mu.app (X, Y) ≫ TC.map (Prod.mkHom (H.map u) (H.map v)) at hm
  rw [show Prod.mkHom (H.map u ≫ p) (H.map v ≫ q) =
      Prod.mkHom (H.map u) (H.map v) ≫ Prod.mkHom p q from rfl, TC.map_comp]
  rw [← Category.assoc (mu.app (X, Y)), ← hm]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hf]
  simp only [H.map_comp, Category.assoc]
  rw [hh]

private theorem tensor_square_of_normalizations
    {A D : Type*} [Category A] [Category D]
    (L R : A ⥤ D) (TA : A × A ⥤ A) (TD : D × D ⥤ D)
    (muL : TA ⋙ L ⟶ L.prod L ⋙ TD) (muR : TA ⋙ R ⟶ R.prod R ⋙ TD)
    (theta : R ⟶ L) (X Y T : A) (e : T ⟶ TA.obj (X, Y)) [IsIso e]
    {XL YL XR YR TL TR DL DR : D}
    (lX : L.obj X ⟶ XL) (lY : L.obj Y ⟶ YL) [IsIso lX] [IsIso lY]
    (rX : R.obj X ⟶ XR) (rY : R.obj Y ⟶ YR)
    (gammaX : XR ⟶ XL) (gammaY : YR ⟶ YL)
    (lT : L.obj T ⟶ TL) (rT : R.obj T ⟶ TR) (gammaT : TR ⟶ TL)
    (ld : TL ⟶ DL) (rd : TR ⟶ DR) (dgamma : DR ⟶ DL)
    (repL : DL ⟶ TD.obj (XL, YL)) (repR : DR ⟶ TD.obj (XR, YR))
    (hL : L.map e ≫ muL.app (X, Y) ≫ TD.map (Prod.mkHom lX lY) = lT ≫ ld ≫ repL)
    (hR : R.map e ≫ muR.app (X, Y) ≫ TD.map (Prod.mkHom rX rY) = rT ≫ rd ≫ repR)
    (hX : theta.app X ≫ lX = rX ≫ gammaX)
    (hY : theta.app Y ≫ lY = rY ≫ gammaY)
    (hT : theta.app T ≫ lT = rT ≫ gammaT)
    (hd : gammaT ≫ ld = rd ≫ dgamma)
    (hr : dgamma ≫ repL = repR ≫ TD.map (Prod.mkHom gammaX gammaY)) :
    theta.app (TA.obj (X, Y)) ≫ muL.app (X, Y) =
      muR.app (X, Y) ≫ TD.map (Prod.mkHom (theta.app X) (theta.app Y)) := by
  have : IsIso (Prod.mkHom lX lY) :=
    (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (R.map e)).1
  apply (cancel_mono (TD.map (Prod.mkHom lX lY))).1
  simp only [Category.assoc]
  rw [reassoc_of% theta.naturality e, hL, reassoc_of% hT]
  have hp : Prod.mkHom (theta.app X) (theta.app Y) ≫ Prod.mkHom lX lY =
      Prod.mkHom rX rY ≫ Prod.mkHom gammaX gammaY := by
    change Prod.mkHom (_ ≫ _) (_ ≫ _) = Prod.mkHom (_ ≫ _) (_ ≫ _)
    rw [hX, hY]
  conv_rhs => rw [← TD.map_comp, hp, TD.map_comp]
  rw [reassoc_of% hR, ← hr, ← reassoc_of% hd]

private theorem scalarPull_tensor_representative
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (aU : ProEtaleTensorModel U (R.ring U))
    (aV : ProEtaleTensorModel V (R.ring V))
    (bU : ProEtaleTensorModel U (S.ring U))
    (bV : ProEtaleTensorModel V (S.ring V))
    (P Q : CochainComplex (pbcModules V (R.ring V)) ℤ)
    (hp : proEtaleFlatRepresentatives V (R.ring V) P)
    (hq : proEtaleFlatRepresentatives V (R.ring V) Q) :
    (scalarPull a g).inv.app
        (aV.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (pbcDerivedExtend (a.map U)).map
        ((proEtaleCanonicalTensorComparison g (R.ring V) (R.ring U)
          (R.pull g) aV aU).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (scalarTensor (a.map U) aU bU).hom.app
        ((pull R g).obj (DerivedCategory.Q.obj P),
          (pull R g).obj (DerivedCategory.Q.obj Q)) =
    (pull S g).map ((scalarTensor (a.map V) aV bV).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (proEtaleCanonicalTensorComparison g (S.ring V) (S.ring U)
        (S.pull g) bV bU).hom.app
          ((pbcDerivedExtend (a.map V)).obj (DerivedCategory.Q.obj P),
            (pbcDerivedExtend (a.map V)).obj (DerivedCategory.Q.obj Q)) ≫
      bU.tensor.map (Prod.mkHom ((scalarPull a g).inv.app (DerivedCategory.Q.obj P))
        ((scalarPull a g).inv.app (DerivedCategory.Q.obj Q))) := by
  let F := pull R g
  let H := pbcDerivedExtend (a.map U)
  let G := pbcDerivedExtend (a.map V)
  let K := pull S g
  let Fc := (proEtaleRingModulePullback g (R.ring V) (R.ring U)
    (R.pull g)).mapHomologicalComplex (.up ℤ)
  let Hc := (pbcExtend (a.map U)).mapHomologicalComplex (.up ℤ)
  let Gc := (pbcExtend (a.map V)).mapHomologicalComplex (.up ℤ)
  let Kc := (proEtaleRingModulePullback g (S.ring V) (S.ring U)
    (S.pull g)).mapHomologicalComplex (.up ℤ)
  let cF := proEtaleRingDerivedPullbackFactors g (R.ring V) (R.ring U) (R.pull g)
  let cH := scalarCounit (a.map U)
  let cG := scalarCounit (a.map V)
  let cK := proEtaleRingDerivedPullbackFactors g (S.ring V) (S.ring U) (S.pull g)
  let tF := proEtaleCanonicalTensorComparison g (R.ring V) (R.ring U) (R.pull g) aV aU
  let tH := scalarTensor (a.map U) aU bU
  let tG := scalarTensor (a.map V) aV bV
  let tK := proEtaleCanonicalTensorComparison g (S.ring V) (S.ring U) (S.pull g) bV bU
  let theta := (scalarPull a g).inv
  let gamma := scalarPullComplex a g
  let T := (proEtaleResolutionTotal V (R.ring V)).obj (P, Q)
  let dF := (proEtaleTensorPullbackTotalIso g (R.ring V) (R.ring U) (R.pull g) P Q).inv
  let dG := @inv _ _ _ _ (scalarTensorTotal (a.map V) P Q)
    (scalarTensorTotal_isIso (a.map V) P Q)
  let dH := @inv _ _ _ _ (scalarTensorTotal (a.map U) (Fc.obj P) (Fc.obj Q))
    (scalarTensorTotal_isIso (a.map U) _ _)
  let dK := (proEtaleTensorPullbackTotalIso g (S.ring V) (S.ring U) (S.pull g)
    (Gc.obj P) (Gc.obj Q)).inv
  obtain ⟨hpF, hqF, hF⟩ :=
    (proEtaleCanonicalTensorPullback g (R.ring V) (R.ring U) (R.pull g)
      aV aU).2.exists.choose_spec P Q hp hq
  obtain ⟨hpH, hqH, hH⟩ :=
    (scalarTensor_existsUnique (a.map U) aU bU).exists.choose_spec
      (Fc.obj P) (Fc.obj Q) hpF hqF
  obtain ⟨hpG, hqG, hG⟩ :=
    (scalarTensor_existsUnique (a.map V) aV bV).exists.choose_spec P Q hp hq
  obtain ⟨hpK, hqK, hK⟩ :=
    (proEtaleCanonicalTensorPullback g (S.ring V) (S.ring U) (S.pull g)
      bV bU).2.exists.choose_spec (Gc.obj P) (Gc.obj Q) hpG hqG
  let rA := aV.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)
  let rB := aU.representative.hom.app (⟨Fc.obj P, hpF⟩, ⟨Fc.obj Q, hqF⟩)
  let rC := bV.representative.hom.app (⟨Gc.obj P, hpG⟩, ⟨Gc.obj Q, hqG⟩)
  let rD := bU.representative.hom.app
    (⟨Hc.obj (Fc.obj P), hpH⟩, ⟨Hc.obj (Fc.obj Q), hqH⟩)
  let rD' := bU.representative.hom.app
    (⟨Kc.obj (Gc.obj P), hpK⟩, ⟨Kc.obj (Gc.obj Q), hqK⟩)
  change F.map rA ≫ tF.hom.app _ ≫
    aU.tensor.map (Prod.mkHom (cF.hom.app P) (cF.hom.app Q)) =
      cF.hom.app T ≫ DerivedCategory.Q.map dF ≫ rB at hF
  change H.map rB ≫ tH.hom.app _ ≫
    bU.tensor.map (Prod.mkHom (cH.app (Fc.obj P)) (cH.app (Fc.obj Q))) =
      cH.app _ ≫ DerivedCategory.Q.map dH ≫ rD at hH
  change G.map rA ≫ tG.hom.app _ ≫
    bV.tensor.map (Prod.mkHom (cG.app P) (cG.app Q)) =
      cG.app T ≫ DerivedCategory.Q.map dG ≫ rC at hG
  change K.map rC ≫ tK.hom.app _ ≫
    bU.tensor.map (Prod.mkHom (cK.hom.app (Gc.obj P)) (cK.hom.app (Gc.obj Q))) =
      cK.hom.app _ ≫ DerivedCategory.Q.map dK ≫ rD' at hK
  have hL := tensor_composite_normalize H aU.tensor bU.tensor tH.hom
    (F.map rA ≫ tF.hom.app _) (cF.hom.app P) (cF.hom.app Q)
    (cH.app (Fc.obj P)) (cH.app (Fc.obj Q))
    (cF.hom.app T) (DerivedCategory.Q.map dF) rB
    (cH.app _) (DerivedCategory.Q.map dH) rD (by simpa only [Category.assoc] using hF) hH
  have hR := tensor_composite_normalize K bV.tensor bU.tensor tK.hom
    (G.map rA ≫ tG.hom.app _) (cG.app P) (cG.app Q)
    (cK.hom.app (Gc.obj P)) (cK.hom.app (Gc.obj Q))
    (cG.app T) (DerivedCategory.Q.map dG) rC
    (cK.hom.app _) (DerivedCategory.Q.map dK) rD' (by simpa only [Category.assoc] using hG) hK
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hL hR
  have hnL := cH.naturality dF
  have hnR := cK.hom.naturality dG
  dsimp only [Functor.comp_map] at hnL hnR
  rw [reassoc_of% hnL] at hL
  rw [reassoc_of% hnR] at hR
  let l (A : CochainComplex (pbcModules V (R.ring V)) ℤ) :=
    H.map (cF.hom.app A) ≫ cH.app (Fc.obj A)
  let r (A : CochainComplex (pbcModules V (R.ring V)) ℤ) :=
    K.map (cG.app A) ≫ cK.hom.app (Gc.obj A)
  have norm (A : CochainComplex (pbcModules V (R.ring V)) ℤ) :
      theta.app (DerivedCategory.Q.obj A) ≫ l A =
        r A ≫ DerivedCategory.Q.map (gamma.hom.app A) :=
    by
      simpa only [l, r, theta, gamma, cF, cH, cG, cK, F, H, G, K, Fc, Gc,
        scalarCounit, Category.assoc] using scalarPull_complex_normalization a g A
  have hpost (A : CochainComplex (pbcModules V (R.ring V)) ℤ)
      (hA : proEtaleFlatRepresentatives U (R.ring U) (Fc.obj A)) : IsIso (l A) := by
    have := pbcExtensionCounit_isIso (a.map U) (Fc.obj A) hA.1
    dsimp only [l, cH, scalarCounit]
    unfold pbcComplexCounit
    infer_instance
  have := hpost P hpF
  have := hpost Q hqF
  have : IsIso rA := by dsimp only [rA]; infer_instance
  have hrD := bU.representative.hom.naturality
    (Prod.mkHom
      (ObjectProperty.homMk (gamma.hom.app P) :
        (⟨Kc.obj (Gc.obj P), hpK⟩ :
          (proEtaleFlatRepresentatives U (S.ring U)).FullSubcategory) ⟶ ⟨_, hpH⟩)
      (ObjectProperty.homMk (gamma.hom.app Q) :
        (⟨Kc.obj (Gc.obj Q), hqK⟩ :
          (proEtaleFlatRepresentatives U (S.ring U)).FullSubcategory) ⟶ ⟨_, hqH⟩))
  let totalD := proEtaleResolutionTotal U (S.ring U)
  change DerivedCategory.Q.map
      (totalD.map (Prod.mkHom (gamma.hom.app P) (gamma.hom.app Q))) ≫ rD =
    rD' ≫ bU.tensor.map (Prod.mkHom (DerivedCategory.Q.map (gamma.hom.app P))
      (DerivedCategory.Q.map (gamma.hom.app Q))) at hrD
  have ho := congrArg DerivedCategory.Q.map (scalarPull_coefficient_total_tensor a g P Q)
  change DerivedCategory.Q.map (Kc.map dG ≫ dK ≫
      totalD.map (Prod.mkHom (gamma.hom.app P) (gamma.hom.app Q))) =
    DerivedCategory.Q.map (gamma.hom.app T ≫ Hc.map dF ≫ dH) at ho
  simp only [Functor.map_comp] at ho
  let muL : aV.tensor ⋙ F ⋙ H ⟶ (F ⋙ H).prod (F ⋙ H) ⋙ bU.tensor :=
    Functor.whiskerRight tF.hom H ≫ Functor.whiskerLeft (F.prod F) tH.hom
  let muR : aV.tensor ⋙ G ⋙ K ⟶ (G ⋙ K).prod (G ⋙ K) ⋙ bU.tensor :=
    Functor.whiskerRight tG.hom K ≫ Functor.whiskerLeft (G.prod G) tK.hom
  have hL' : (F ⋙ H).map rA ≫ muL.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        bU.tensor.map (Prod.mkHom (l P) (l Q)) =
      l T ≫ DerivedCategory.Q.map (Hc.map dF ≫ dH) ≫ rD := by
    dsimp only [l, muL, Functor.comp_map, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Functor.prod_obj, T,
      Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex] at hL ⊢
    simpa only [Functor.map_comp, Category.assoc] using hL
  have hR' : (G ⋙ K).map rA ≫ muR.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        bU.tensor.map (Prod.mkHom (r P) (r Q)) =
      r T ≫ DerivedCategory.Q.map (Kc.map dG ≫ dK) ≫ rD' := by
    dsimp only [r, muR, Functor.comp_map, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Functor.prod_obj, T,
      Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex] at hR ⊢
    simpa only [Functor.map_comp, Category.assoc] using hR
  simpa only [muL, muR, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.prod_obj, Functor.comp_obj, Category.assoc] using
    tensor_square_of_normalizations (F ⋙ H) (G ⋙ K) aV.tensor bU.tensor
    muL muR theta (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj T) rA (l P) (l Q) (r P) (r Q)
    (DerivedCategory.Q.map (gamma.hom.app P)) (DerivedCategory.Q.map (gamma.hom.app Q))
    (l T) (r T) (DerivedCategory.Q.map (gamma.hom.app T))
    (DerivedCategory.Q.map (Hc.map dF ≫ dH))
    (DerivedCategory.Q.map (Kc.map dG ≫ dK))
    (DerivedCategory.Q.map (totalD.map (Prod.mkHom (gamma.hom.app P) (gamma.hom.app Q))))
    rD rD' hL' hR' (norm P) (norm Q) (norm T)
    (by simpa only [Functor.map_comp, Category.assoc] using ho.symm) hrD

/-- The normalized scalar/pullback comparison respects the four tensor comparisons.
This concerns only left adjoints and contains no projection or direct-image mate.

Source: Stacks Project, Tags 07A4, 07A6 and 0E48, the tensor calculation before
transposing the coefficient square
(blueprint: lem-sf-scalar-pull-tensor-coefficient-coherence).

Proof: choose flat-term K-flat resolutions of P and Q. Geometric pullback and
scalar extension preserve these representatives. The two composite left adjoints
are identified by the balanced coefficient square: their right adjoints have the
specified sectionwise restriction/direct-image comparison. On representatives
this identifies scalarPull inverse with the map sending each iterated unit tensor
to the corresponding iterated unit tensor. To check this normalization, transpose
under the composite scalar/geometric adjunctions; both transposes are exactly the
restriction comparison defining scalarPull, and uniqueness of left adjoints gives
equality. Expand the representative equations for the two geometric tensorators
and the two scalar tensorators. On homogeneous pure tensors both routes distribute
the two sections to the same factors and multiply the same coefficient sections;
the balancing relations identify the resulting maps. Both preserve the pair of
degrees, so there is no additional sign on signed total complexes. Sheafification
and localization preserve the equality. Cancel the representative isomorphisms,
and use the fully faithful restriction of derived bifunctors to flat K-flat pairs
to obtain the equation on arbitrary P and Q. This includes identity coefficient
maps, zero inputs and nonflat quotient maps. -/
theorem scalarPull_tensor_coefficient_coherence
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (aU : ProEtaleTensorModel U (R.ring U))
    (aV : ProEtaleTensorModel V (R.ring V))
    (bU : ProEtaleTensorModel U (S.ring U))
    (bV : ProEtaleTensorModel V (S.ring V))
    (P Q : DerivedCategory (pbcModules V (R.ring V))) :
    (scalarPull a g).inv.app (aV.tensor.obj (P, Q)) ≫
      (pbcDerivedExtend (a.map U)).map
        ((proEtaleCanonicalTensorComparison g (R.ring V) (R.ring U)
          (R.pull g) aV aU).hom.app (P, Q)) ≫
      (scalarTensor (a.map U) aU bU).hom.app
        ((pull R g).obj P, (pull R g).obj Q) =
    (pull S g).map ((scalarTensor (a.map V) aV bV).hom.app (P, Q)) ≫
      (proEtaleCanonicalTensorComparison g (S.ring V) (S.ring U)
        (S.pull g) bV bU).hom.app
          ((pbcDerivedExtend (a.map V)).obj P, (pbcDerivedExtend (a.map V)).obj Q) ≫
      bU.tensor.map (Prod.mkHom ((scalarPull a g).inv.app P)
        ((scalarPull a g).inv.app Q)) := by
  classical
  let F := pull R g
  let H := pbcDerivedExtend (a.map U)
  let G := pbcDerivedExtend (a.map V)
  let K := pull S g
  let theta := (scalarPull a g).inv
  let tF := proEtaleCanonicalTensorComparison g (R.ring V) (R.ring U) (R.pull g) aV aU
  let tH := scalarTensor (a.map U) aU bU
  let tG := scalarTensor (a.map V) aV bV
  let tK := proEtaleCanonicalTensorComparison g (S.ring V) (S.ring U) (S.pull g) bV bU
  let left : aV.tensor ⋙ G ⋙ K ⟶ ((F ⋙ H).prod (F ⋙ H)) ⋙ bU.tensor :=
    Functor.whiskerLeft aV.tensor theta ≫
      Functor.whiskerRight tF.hom H ≫ Functor.whiskerLeft (F.prod F) tH.hom
  let right : aV.tensor ⋙ G ⋙ K ⟶ ((F ⋙ H).prod (F ⋙ H)) ⋙ bU.tensor :=
    Functor.whiskerRight tG.hom K ≫ Functor.whiskerLeft (G.prod G) tK.hom ≫
      Functor.whiskerRight (NatTrans.prod theta theta) bU.tensor
  have rep (M : DerivedCategory (pbcModules V (R.ring V))) :
      ∃ (C : CochainComplex (pbcModules V (R.ring V)) ℤ)
        (hc : proEtaleFlatRepresentatives V (R.ring V) C),
        Nonempty (DerivedCategory.Q.obj C ≅ M) := by
    let : EssentiallySmall.{u + 1} V.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    let : HasSheafify (ProEt.topology V) AddCommGrpCat.{u + 1} :=
      coefficientAbSheafify V
    let : (ProEt.topology V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      coefficientAbLocallyBijective V
    let C₀ := DerivedCategory.Q.objPreimage M
    obtain ⟨C, f, hc, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (J := ProEt.topology V) (R := R.ring V) C₀
    have : IsIso (DerivedCategory.Q.map f) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
    refine ⟨C, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
      (R := R.ring V) C).1 hc, ?_⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫
      DerivedCategory.Q.objObjPreimageIso M⟩⟩
    intro n
    exact (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} (R.ring V) (C.X n)).symm (hf n)
  obtain ⟨C, hc, ⟨e⟩⟩ := rep P
  obtain ⟨D, hd, ⟨f⟩⟩ := rep Q
  have hrep : left.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj D) =
      right.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj D) :=
    scalarPull_tensor_representative a g aU aV bU bV C D hc hd
  have hleft := left.naturality (Iso.prod e f).hom
  have hright := right.naturality (Iso.prod e f).hom
  apply (cancel_epi ((aV.tensor ⋙ G ⋙ K).map (Iso.prod e f).hom)).1
  exact hleft.trans ((congrArg (fun z ↦ z ≫
    (((F ⋙ H).prod (F ⋙ H)) ⋙ bU.tensor).map (Iso.prod e f).hom) hrep).trans hright.symm)

end WeilConjectures.PurCompactSupport
