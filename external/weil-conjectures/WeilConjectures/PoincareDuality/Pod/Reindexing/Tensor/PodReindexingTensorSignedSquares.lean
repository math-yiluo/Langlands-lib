/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftStrictTowerSquares
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftRoosPathNormalization
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Tensor-factor signed-shift squares under reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem goodRepresentative (W : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E W)) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ M) := by
  let L := integralOperationsGoodLocalization l E W
  let V := (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let : L.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  have : L.EssSurj := Localization.essSurj L V
  exact ⟨L.objPreimage M, ⟨L.objObjPreimageIso M⟩⟩

set_option linter.unusedVariables false in
/-- The two tensor-factor shift squares for generator/model normalized signed shifts.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-signed-shift-squares-r3).

The generator and representative-model laws are necessary: the underlying shift
structure alone permits independent sign changes of its derived isomorphisms.

Proof: choose good representatives for M and N using the existing localization.
Present M' and N' by their shifted representatives, using a and b. The separate
Roos normalizations compute each derived path from its strict tower map with a
common prefix and suffix. The strict tower squares identify these maps, since
reindexing preserves degrees and the second-slot Koszul sign. Substitute these
equalities and cancel the reindexed tensor presentation isomorphism. -/
theorem podReindexingTensorSignedShifts_tensorSquares
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (hSY : SY.Generators l E) (hSX : SX.Generators l E)
    (mSY : SY.Model l E D.shiftSource) (mSX : SX.Model l E D.shiftTarget) :
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.left M N M' r a).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M' N).hom ≫
          (SX.left ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible M'⟩ r
            ((podOrdinaryReindex l E g).mapIso a ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app M.obj)).hom)) ∧
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.right M N N' r b).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M N').hom ≫
          (SX.right ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible N'⟩ r
            ((podOrdinaryReindex l E g).mapIso b ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app N.obj)).hom)) := by
  simp only [← forall_and]
  intro M N M' N' r a b
  obtain ⟨P, ⟨eP⟩⟩ := goodRepresentative l E Y M.obj
  obtain ⟨Q, ⟨eQ⟩⟩ := goodRepresentative l E Y N.obj
  let eP' := (DerivedCategory.Q.commShiftIso r).app P.obj ≪≫
    (shiftFunctor _ r).mapIso eP ≪≫ a.symm
  let eQ' := (DerivedCategory.Q.commShiftIso r).app Q.obj ≪≫
    (shiftFunctor _ r).mapIso eQ ≪≫ b.symm
  have ha : eP'.hom ≫ a.hom =
      (DerivedCategory.Q.commShiftIso r).hom.app P.obj ≫ eP.hom⟦r⟧' := by
    simp [eP']
  have hb : eQ'.hom ≫ b.hom =
      (DerivedCategory.Q.commShiftIso r).hom.app Q.obj ≫ eQ.hom⟦r⟧' := by
    simp [eQ']
  have hn := podTensorShift_roosPathNormalization l E g D _hD T _hT SY SX mSY mSX
    P Q M N M' N' r a b eP eQ eP' eQ' ha hb
  have ht := podTensorShift_strictTowerSquares l E g D _hD T _hT SY SX hSY hSX P Q r
  constructor
  · let e := (podOrdinaryReindex l E g).mapIso
      ((integralCompletedTensor l E Y).mapIso (eP'.prod eQ))
    apply (cancel_epi e.hom).mp
    simp only [e, Functor.mapIso_hom, Iso.prod_hom]
    refine hn.1.trans (Eq.trans ?_ hn.2.1.symm)
    exact congrArg (fun k => _ ≫ DerivedCategory.Q.map (integralOperationsRoosMap k) ≫ _) ht.1
  · let e := (podOrdinaryReindex l E g).mapIso
      ((integralCompletedTensor l E Y).mapIso (eP.prod eQ'))
    apply (cancel_epi e.hom).mp
    simp only [e, Functor.mapIso_hom, Iso.prod_hom]
    refine hn.2.2.1.trans (Eq.trans ?_ hn.2.2.2.symm)
    exact congrArg (fun k => _ ≫ DerivedCategory.Q.map (integralOperationsRoosMap k) ≫ _) ht.2

end WeilConjectures
