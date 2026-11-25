/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Frobenius tensor comparison and the actual completion unit

Source: blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, penultimate sentence, via original step 3 of
lem-wf-tensor-completion-frobenius
(blueprint: def-wf-tensor-unit-square-data).

The strict statement uses the published constant-quotient presentation of the completed
ring, conjugating the coefficient isomorphism by the finite-quotient ring comparison.
It fixes every product projection and both mapping-fiber coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.WfTensorUnitSquare
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A) (e : Aut X) (p : A)

/-- The existing completed quotient-ring presentation.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev ring := adicDatumRing X (intrinsicPresentationDatum d)

/-- The given coefficient isomorphism, conjugated by its finite-quotient presentation.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def coefficientIso :
    (proEtaleSheafInverseImage e.asIso.hom CommRingCat.{u + 1}).obj (ring X d) ≅ ring X d :=
  (proEtaleSheafInverseImage e.asIso.hom CommRingCat.{u + 1}).mapIso
      (pbcCompletedComparison X d) ≪≫
    asIso (completedCoefficientMap e.asIso.hom d) ≪≫ (pbcCompletedComparison X d).symm

/-- Exact module transport with this coefficient identification.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev transport := proEtaleRingModulePullback e.asIso.hom (ring X d) (ring X d)
  (coefficientIso X d e)

/-- The termwise transport functor.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev complexes := (transport X d e).mapHomologicalComplex (.up ℤ)

/-- The existing signed total tensor.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def tensor (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact CochainComplex.mapBifunctor.{u+1,u+2,u+1,u+2,u+1,u+2} U V
    (proEtaleOrdinaryTensor X (ring X d))

/-- The specified ordinary total comparison H(Tot(U tensor V)) to Tot(HU tensor HV).
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def alpha (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    (complexes X d e).obj (tensor X d U V) ≅
      tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V) :=
  (proEtaleTensorPullbackTotalIso e.asIso.hom (ring X d) (ring X d)
    (coefficientIso X d e) U V).symm

attribute [local irreducible] tensor alpha

/-- The already constructed completed constant-module functor.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev constants := completedKoszulConstant X (intrinsicPresentationDatum d)

/-- The canonical constant section of an extended constant module.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def generator (M : ModuleCat.{u + 1} A) (U : X.ProEtᵒᵖ) (x : M) :=
  adicDatumTensorSection X (adicDatumScalar X (intrinsicPresentationDatum d))
    ((adicLisseConstantModules X A).obj M) U 1 (completedConstantGenerator X A M U x)

/-- The original rank-one Koszul complex; index m means the positive power m+1.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev koszul (m : ℕ) := completedKoszulPowerSheaf X (intrinsicPresentationDatum d)
  1 (fun _ ↦ p) m

/-- The existing strict Koszul tensor tower.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev tower (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :=
  completedKoszulTensor X (intrinsicPresentationDatum d) 1 (fun _ ↦ p) C

/-- Its original product.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev product (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :=
  completedKoszulProduct X (intrinsicPresentationDatum d) 1 (fun _ ↦ p) C

/-- Negative of one minus shift, as in the published mapping cocone.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev differential
    (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :=
  -completedKoszulOneSubShift X (intrinsicPresentationDatum d) 1 (fun _ ↦ p) C

/-- The original signed fiber complex.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev fiber (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :=
  completedKoszulFiber X (intrinsicPresentationDatum d) 1 (fun _ ↦ p) C

/-- Its actual (u,0) chain-map unit.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev unit (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :=
  completedKoszulUnitComplex X (intrinsicPresentationDatum d) 1 (fun _ ↦ p) C

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The stipulated level comparison, with alpha and HQ_m to Q_m on the two factors.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def beta (k : constants X d ⋙ transport X d e ≅ constants X d)
    (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) (m : ℕ) :
    (complexes X d e).obj (tower X d p (tensor X d U V) m) ⟶
      tower X d p (tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V)) m := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let q : (complexes X d e).obj (koszul X d p m) ⟶ koszul X d p m :=
    (NatIso.mapHomologicalComplex k (.up ℤ)).hom.app
      (completedKoszulPower (A := A) 1 (fun _ ↦ p) m)
  let a : (complexes X d e).obj (tensor X d U V) ⟶
      tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V) :=
    (alpha X d e U V).hom
  exact (proEtaleTensorPullbackTotalIso e.asIso.hom (ring X d) (ring X d)
      (coefficientIso X d e) (tensor X d U V) (koszul X d p m)).inv ≫
    HomologicalComplex.mapBifunctorMap a q (proEtaleOrdinaryTensor X (ring X d)) (.up ℤ)

/-- The ordinary derived comparison of the recorded tensor model.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
abbrev ordinary (M N : PbcBoundedConstructibleComplete X d) :=
  (proEtaleCanonicalTensorComparison e.asIso.hom (pbcAdicCompletion X d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.asIso.hom d))
    (wfTensorModel X d) (wfTensorModel X d)).app (M.obj, N.obj)

/-- Its specified completed comparison before restricting to the complete subcategory.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def completed (hp : Ideal.span (Set.range (fun _ : Fin 1 ↦ p)) = d.ideal)
    (M N : PbcBoundedConstructibleComplete X d) :=
  wfPullbackCompletion X d 1 (fun _ ↦ p) hp e
      ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj)) ≪≫
    (ObjectProperty.ι (WfIsComplete X d 1 (fun _ ↦ p) hp)).mapIso
      ((wfCompletion X d 1 (fun _ ↦ p) hp).mapIso (ordinary X d e M N))

/-- The node's derived equation with its actual units and specified comparisons.
Source: projection-formula equivariance
(blueprint: def-wf-tensor-unit-square-data). -/
def DerivedSquare (hp : Ideal.span (Set.range (fun _ : Fin 1 ↦ p)) = d.ideal)
    (M N : PbcBoundedConstructibleComplete X d) : Prop :=
  (pbcIsoAmbientPullback e.asIso.hom d).map
      (wfCompletionUnit X d 1 (fun _ ↦ p) hp
        ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj))) ≫
      (completed X d e p hp M N).hom =
    (ordinary X d e M N).hom ≫ wfCompletionUnit X d 1 (fun _ ↦ p) hp
      ((wfOrdinaryDerivedTensor X d).obj
        ((pbcIsoAmbientPullback e.asIso.hom d).obj M.obj,
          (pbcIsoAmbientPullback e.asIso.hom d).obj N.obj))

end WeilConjectures.WfTensorUnitSquare
