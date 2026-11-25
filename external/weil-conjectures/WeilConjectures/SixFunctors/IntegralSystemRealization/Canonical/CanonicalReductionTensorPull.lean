/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.CanonicalReductionTensorPullComplex
import WeilConjectures.SixFunctors.IntegralSystemRealization.CanonicalTensorPullProof.CanonicalReductionTensorPullLeft
import WeilConjectures.SixFunctors.IntegralSystemRealization.CanonicalTensorPullProof.CanonicalReductionTensorPullRight
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Pullback and tensor under ordinary coefficient reduction

Source: blueprint fix-prop-coherence, individual coefficient comparisons; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

open CanonicalTensorPullProof
attribute [local irreducible] pullbackTensorCalculus

private theorem on_representatives
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :
    (leftPath l E o m d f).app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      (rightPath l E o m d f).app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) := by
  apply (cancel_epi (pre l E o m d f P Q)).mp
  apply (cancel_mono (post l E o m d f P Q)).mp
  simp only [Category.assoc]
  rw [left_on_representatives, right_on_representatives]
  have h := congrArg DerivedCategory.Q.map
    (canonicalReductionTensorPullComplex l E m.ordinary f P.obj Q.obj)
  simp only [Functor.map_comp] at h
  simpa only [leftNormal, rightNormal, Functor.map_comp, Category.assoc] using
    congrArg (fun a ↦ (calculus l E U).reduction.map
      ((integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
        ((total l E V).obj (P.obj, Q.obj))) ≫
      (pullbackTensorReductionModel l E U).hom.app
        ⟨((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj
          ((total l E V).obj (P.obj, Q.obj)),
          pull_good l E f ⟨_, total_good l E V P Q⟩⟩ ≫ a ≫
      (pullbackTensorSystemModel l E U _ _
        (pullbackTensorSequenceGood l E f _ (pullbackTensorReductionGood l E V P))
        (pullbackTensorSequenceGood l E f _ (pullbackTensorReductionGood l E V Q))).hom) h

/-- The normalized reduction/pullback comparison preserves the ordinary tensor map.
Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
"tensor reassociation, evaluation, and adjunction units and counits", and
proposition-six-operations-change-coefficients; Stacks 07A4, 07A6 and 0941.
(blueprint: lem-sf-canonical-reduction-tensor-pull).

Proof: resolve K and H by flat-term K-flat complexes. Use the total tensor of these
representatives for their tensor product. The tensorRepresentative field identifies
this representative with the tensor in the coefficient calculus, and the model field
of the realization identifies reductionPull with the ordinary quotient/pullback mate.
At the ordinary level that mate is determined by its adjoint limit comparison:
postcomposing with each limit projection is the specified coefficient projection.
Its inverse-image transpose is thus the usual scalar-association map. In each total
tensor summand both composites in the displayed equation send b tensor (x tensor y)
to (b tensor x) tensor (1 tensor y). The defining pure-tensor formulas for the ringed
and system pullback/tensor maps, and the reductionTensor normalization, identify the
four sides with these maps. Pure tensors generate the module tensor product; tensor
sheafification and inverse image preserve this identity. The formula respects the
signed total differential and every adjacent quotient transition, so it is an equality
of whole strict system complexes. Localize it. The representative normalizations
cancel the K-flat factorization isomorphisms and give the equation on the chosen
resolutions. Naturality transports it along their resolving isomorphisms to K and H.
Zero inputs and identity scheme maps use exactly the same summand calculation. -/
theorem canonicalReductionTensorPull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (K H : Integral l E V) :
    let μ (W : Scheme.{u}) :
        (d.tensor W).ordinary.tensor ⋙ (calculus l E W).reduction ⟶
          (calculus l E W).reduction.prod (calculus l E W).reduction ⋙
            (calculus l E W).systemClosed.tensor :=
      Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom (calculus l E W).reduction ≫
        (calculus l E W).reductionTensor.hom
    (m.reductionPull f).hom.app ((d.tensor V).ordinary.tensor.obj (K, H)) ≫
        (pull l E f).map ((μ V).app (K, H)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((calculus l E V).reduction.obj K, (calculus l E V).reduction.obj H) =
      (calculus l E U).reduction.map ((ringedTensorPull l E d f).hom.app (K, H)) ≫
        (μ U).app ((ringedPull l E f).obj K, (ringedPull l E f).obj H) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom ((m.reductionPull f).hom.app K) ((m.reductionPull f).hom.app H)) := by
  suffices hh : (leftPath l E o m d f).app (K, H) =
      (rightPath l E o m d f).app (K, H) by
    simpa only [leftPath, rightPath, mu, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.prod, Functor.prod_obj, Category.assoc] using hh
  let L := integralOperationsGoodLocalization l E V
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E V) (.up ℤ)).inverseImage
    (good l E V).ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E V
  let : L.EssSurj := Localization.essSurj L W
  let e := Iso.prod (L.objObjPreimageIso K) (L.objObjPreimageIso H)
  have h := on_representatives l E o m d f (L.objPreimage K) (L.objPreimage H)
  have hn := (leftPath l E o m d f).naturality e.hom
  have hn' := (rightPath l E o m d f).naturality e.hom
  erw [h] at hn
  exact (cancel_epi _).mp (hn.trans hn'.symm)

end WeilConjectures.IntegralSystemRealization
