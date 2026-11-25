/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateBoundedBelow
import WeilConjectures.SmoothPurity.Sf.SfIntegralStandardTruncations
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # Integral scalar-mate steps for native compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_scalar_mate_isIso
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (PurCompactSupport.openComparison a j) := by
  have := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  let d := asIso (proEtaleRingRestrictionPullbackInv
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j))
  have : IsIso ((mateEquiv
      (PurCompactSupport.openAdjunction S j) (PurCompactSupport.openAdjunction R j)).symm
      (TwoSquare.mk _ _ _ _ d.symm.hom)) := by
    change IsIso (PurCompactSupport.openRestrictionMap a j)
    infer_instance
  have hm := (exact_localization_inverse_mate
    (PurCompactSupport.openAdjunction S j) (PurCompactSupport.openAdjunction R j)
    d.symm).2.1
  change ((mateEquiv
    (PurCompactSupport.openDerivedAdjunction S j)
    (PurCompactSupport.openDerivedAdjunction R j)).symm
    (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback
      j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)).hom)) =
    (PurCompactSupport.openRestriction a j).hom at hm
  let δ := TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)).hom
  have hm' : ((mateEquiv (PurCompactSupport.openDerivedAdjunction S j)
      (PurCompactSupport.openDerivedAdjunction R j)).symm δ) =
      TwoSquare.mk _ _ _ _ (PurCompactSupport.openRestriction a j).hom := by
    ext M
    exact congr_app hm M
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (pbcDerivedScalarAdjunction (a.map U)) (pbcDerivedScalarAdjunction (a.map V))
    (PurCompactSupport.openDerivedAdjunction R j)
    (PurCompactSupport.openDerivedAdjunction S j) δ
  erw [hm'] at h
  have hh := h
  change PurCompactSupport.openComparison a j =
    (conjugateEquiv
      ((pbcDerivedScalarAdjunction (a.map U)).comp
        (PurCompactSupport.openDerivedAdjunction S j))
      ((PurCompactSupport.openDerivedAdjunction R j).comp
        (pbcDerivedScalarAdjunction (a.map V)))).symm δ at hh
  rw [hh]
  infer_instance

variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

include D hl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
/-- Invertibility of the single completed-to-native compact-support scalar mate.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 5.3(1);
Stacks Tag 0GL1; steps 3 and 5--7 of the native finite comparison plan.
(blueprint: lem-sf-native-compact-support-scalar-mate-invertible).

Proof: the intrinsic standard-truncation theorem makes the underlying integral
constructible object bounded. Exact open extension preserves its lower bound. Apply
the bounded-below native proper scalar-mate theorem to this open extension.
For the open factor, the ordinary inverse restriction/pullback square has invertible
open-adjunction mate. Exact localization identifies its derived mate with the
specified open restriction isomorphism. The iterated-mate/conjugation identity then
identifies the scalar mate with the conjugate of an isomorphism between right
adjoints, so it is invertible on every input. Finally the proved proper/open
factorization identifies the compact-support comparison with the proper component
followed by the direct image of this open component. Both factors are invertible.
No completeness or Tor assertion about the open extension is needed. -/
theorem native_compact_support_scalar_mate_invertible [G : NativeGeometry.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    IsIso ((PurCompactSupport.comparison a c).app K.obj) := by
  obtain ⟨⟨n, hn⟩, _⟩ :=
    (sfIntegralStandardTruncations l (Coefficient.{u} l (PadicAlgCl l) E) X D hl
      ⟨K.obj, K.property.1⟩).1
  let := hn
  let J : scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) E) X ⥤
      scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) E) c.Z :=
    PurCompactSupport.openExtension
      (PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)) c.i
  have hJ : DerivedCategory.TStructure.t.plus (J.mapDerivedCategory.obj K.obj) :=
    ⟨n, J.isGE_mapDerivedCategory_obj K.obj n⟩
  have := native_proper_scalar_mate_bounded_below l E a ha c.g
    (J.mapDerivedCategory.obj K.obj) hJ
  have := open_scalar_mate_isIso a c.i
  erw [PurCompactSupport.comparison_factorization]
  infer_instance

end WeilConjectures.LocallyFiniteAdicCompactSupport
