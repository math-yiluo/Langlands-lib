/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
public import WeilConjectures.SixFunctors.AdicFiniteRealization.LocallyFiniteAdicFiniteCondensedRealization
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteCompletedCoefficientMap
import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantSheafLeg

/-! # The finite condensed coefficient leg into native coefficients

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-condensed-native-coefficient-leg)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization
open AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [IsCommMonObj (abRing l X)]

private theorem finiteComparison_eq_chart (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) :
    (CondensedQbarCoefficientRealization.fieldDiagramIso l T).hom.app E =
      chartComparison T E := by
  unfold CondensedQbarCoefficientRealization.fieldDiagramIso
  change (CondensedQbarCoefficientRealization.finiteFieldComparisonIso E l T).hom.hom = _
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ _ = adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply]
  ext S f
  exact CondensedQbarCoefficientRealization.finiteFieldComparison_test E l T S.unop f.down

private lemma finiteLeg_native (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : T.ProEtᵒᵖ)
    (s : ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf T E)).obj.obj V) (x : V.unop.left) :
    (((((padicAlgClSheafCocone T ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) =
        (s.down x : PadicAlgCl ℓ) := by
  have h := padicSubfieldSheafToPadicAlgClSheaf_comp_iso_hom_app T ℓ E V s
  exact congrArg (fun f : C(V.unop.left, PadicAlgCl ℓ) ↦ f x) h

set_option backward.isDefEq.respectTransparency false in
/-- The finite closure leg followed by the native coefficient comparison is the
specified actual field inclusion on continuous functions.
Source: BS 6.8.2; finite chart normalization and the fixed coefficient cocone.
(blueprint: lem-sf-finite-condensed-native-coefficient-leg). -/
theorem finiteCondensedNativeLeg (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l))
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E)) :
    C.rationalInclusion = A.closure.leg E ≫
      ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X) := by
  let c : rationalCoefficientSheaf l X (pbcFiniteField.{u} l (PadicAlgCl l) E) ⟶
      ringSheaf l X := C.rationalInclusion
  change c = _
  apply (cancel_epi (A.closure.finiteIso E).hom).mp
  erw [← Category.assoc, A.closure.leg_normalization]
  have hfac : padicSubfieldRingObjToPadicAlgCl X l E ≫ condensedNativeMap l X =
      chartComparison X E.val ≫ (padicAlgClSheafCocone X l).ι.app E ≫
        padicAlgClSheafToAdicConstantSheaf X l := by
    change (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
      ((CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf X l) = _
    erw [← Category.assoc, CondensedQbarCoefficientRealization.globalCoefficientIso_fac,
      finiteComparison_eq_chart, Category.assoc]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (C.rationalInclusion.hom.app U ((A.closure.finiteIso E).hom.hom.app U s)).down.1 x =
    (((padicSubfieldRingObjToPadicAlgCl X l E ≫ condensedNativeMap l X).hom.app U s).down.1 x)
  have hr := C.rationalInclusion_normalized U
    ((A.closure.finiteIso E).hom.hom.app U s) x
  have hc := congrArg (fun f : ProEtale.padicSubfieldRingObj X l E ⟶ abRing l X ↦
    ((f.hom.app U s).down.1 x)) hfac
  have hv := finiteLeg_native l X E U ((chartComparison X E.val).hom.app U s) x
  exact hr.trans ((congrArg (fun y : E.val ↦ (y : PadicAlgCl l))
    (A.closure.finite_normalization E U s x)).trans (hv.symm.trans hc.symm))

end WeilConjectures.LocallyFiniteAdicRealization
