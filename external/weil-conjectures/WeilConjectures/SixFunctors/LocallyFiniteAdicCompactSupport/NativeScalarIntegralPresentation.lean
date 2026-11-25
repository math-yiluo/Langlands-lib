/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientPresentations
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic

/-! # The normalized integral chart of completed coefficients

Source: Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-sf-native-scalar-integral-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale

private theorem coefficientModel_norm (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (x : Coefficient.{u} l (PadicAlgCl l) E) :
    Padic.coefficientExtensionAbsoluteValue l (Coefficient.{u} l (PadicAlgCl l) E) x =
      ‖embedding l E x‖ := by
  let f := embedding l E
  let av := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp f.injective
  have ha (y : ℚ_[l]) : av (algebraMap ℚ_[l] _ y) = ‖y‖ := by
    change ‖f (algebraMap ℚ_[l] _ y)‖ = ‖y‖
    rw [f.commutes]
    exact PadicAlgCl.norm_extends l y
  exact (spectralNorm_unique_field_norm_ext ha x).symm

private theorem coefficientModel_mem (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (x : Coefficient.{u} l (PadicAlgCl l) E) :
    x ∈ Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E) ↔
      Shrink.algEquiv ℚ_[l] E.1 x ∈ PadicAlgCl.integers l E.1 := by
  have h :=
    (Padic.coefficientExtensionIntegers_dvr l (Coefficient.{u} l (PadicAlgCl l) E)).choose_spec.1 x
  rw [coefficientModel_norm l E] at h
  exact h.trans (by
    rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
    rfl)

private def coefficientIntegerEquiv (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) :
    Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E) ≃+*
      PadicAlgCl.integers l E.1 :=
  RingEquiv.restrict (Shrink.algEquiv ℚ_[l] E.1).toRingEquiv _ _
    (coefficientModel_mem l E)

private def integralContinuousIso (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    letI := PadicAlgCl.normedFieldOfAlgebra l E.1
    (adicLisseForget T).obj
        (AlgebraicGeometry.Scheme.integralCoefficientSheaf l T
          (Coefficient.{u} l (PadicAlgCl l) E)) ≅
      continuousMapRingSheaf T (PadicAlgCl.integers l E.1) := by
  letI nf := coefficientExtensionNormedField l (Coefficient.{u} l (PadicAlgCl l) E)
  letI : TopologicalSpace (Coefficient.{u} l (PadicAlgCl l) E) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := PadicAlgCl.normedFieldOfAlgebra l E.1
  let e := coefficientIntegerEquiv l E
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    exact (coefficientModel_norm l E x).symm
  have hei : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let forward (W : T.ProEtᵒᵖ) :
      C(W.unop.left, ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E))) →+*
      ULift.{u + 1} C(W.unop.left, PadicAlgCl.integers l E.1) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.comp ULift.ringEquiv.toRingHom).compLeftContinuous W.unop.left
        (he.continuous.comp continuous_uliftDown))
  let backward (W : T.ProEtᵒᵖ) :
      ULift.{u + 1} C(W.unop.left, PadicAlgCl.integers l E.1) →+*
      C(W.unop.left, ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E))) :=
    ((ULift.ringEquiv.symm.toRingHom.comp e.symm.toRingHom).compLeftContinuous
      W.unop.left (continuous_uliftUp.comp hei.continuous)).comp ULift.ringEquiv.toRingHom
  refine
    { hom := ⟨{ app := fun W ↦ RingCat.ofHom (forward W)
                naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{ app := fun W ↦ RingCat.ofHom (backward W)
                naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext W : 3
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro x
    change C(W.unop.left, ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E))) at s
    exact congrArg ULift.up (e.symm_apply_apply (s x).down)
  · ext W : 3
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (s.down x)

private def integralChartRingIso (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    letI := PadicAlgCl.normedFieldOfAlgebra l E.1
    InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T ≅
      continuousMapRingSheaf T (PadicAlgCl.integers l E.1) := by
  letI := PadicAlgCl.normedFieldOfAlgebra l E.1
  letI := PadicAlgCl.isUltrametricDist_ofAlgebra l E.1
  let c := asIso (chartComparison T (PadicAlgCl.integers l E.1))
  letI hc : IsMonHom c.hom := chartComparison_isMonHom T _
  letI hci : IsMonHom c.inv := inferInstance
  let R := continuousMapRingSheaf T (PadicAlgCl.integers l E.1)
  let F := sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  refine
    { hom := F.map (@CondensedRing.sectionRingMap _ _ _ _ _ _ _ c.hom hc) ≫
        (CondensedRing.reconstructedRingIso T R).hom
      inv := (CondensedRing.reconstructedRingIso T R).inv ≫
        F.map (@CondensedRing.sectionRingMap _ _ _ _ _ _ _ c.inv hci)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext W s
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f :
        condensedRingObj (Profinite.padicIntegersRingObj l E.1) T ⟶
        condensedRingObj (Profinite.padicIntegersRingObj l E.1) T ↦ f.hom)
        c.hom_inv_id) W) s
  · ext W s
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f :
        (sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R ⟶
        (sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R ↦ f.hom)
        c.inv_hom_id) W) s

private def integralPresentationIso (l : ℕ) [Fact l.Prime] [NativeRings.{u} l]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
    (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E)) :
    (adicLisseForget T).obj ((PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)).ring T) ≅
      InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T :=
  (adicLisseForget T).mapIso C.integral.symm ≪≫
    integralContinuousIso l E T ≪≫ (integralChartRingIso l E T).symm

private theorem integralPresentationIso_value (l : ℕ) [Fact l.Prime] [NativeRings.{u} l]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
    (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E))
    (W : T.ProEtᵒᵖ)
    (s : ((PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)).ring T).obj.obj W) (x : W.unop.left) :
    let := PadicAlgCl.normedFieldOfAlgebra l E.1
    ((C.integralMap l T).hom.app W s).down.1 x =
      (((chartComparison T (PadicAlgCl.integers l E.1)).hom.app W
        ((integralPresentationIso l E T C).hom.hom.app W s)).down x : E.1) := by
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  have h := C.rationalInclusion_normalized W
    (C.integralInclusion.hom.app W (C.integral.inv.hom.app W s)) x
  have hi := C.integralInclusion_normalized W.unop (C.integral.inv.hom.app W s) x
  change ((C.integralMap l T).hom.app W s).down.1 x =
    embedding l E (rationalCoefficientValue l _ T W
      (C.integralInclusion.hom.app W (C.integral.inv.hom.app W s)) x) at h
  rw [hi] at h
  refine h.trans ?_
  have hc := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : continuousMapRingSheaf T (PadicAlgCl.integers l E.1) ⟶
      continuousMapRingSheaf T (PadicAlgCl.integers l E.1) ↦ f.hom)
      (integralChartRingIso l E T).inv_hom_id) W)
      ((integralContinuousIso l E T).hom.hom.app W (C.integral.inv.hom.app W s))
  have hc' := (congrArg (fun t : ULift.{u + 1}
    C(W.unop.left, PadicAlgCl.integers l E.1) ↦ (t.down x : PadicAlgCl l)) hc).symm
  change (embedding l E)
      (integralCoefficientValue l (Coefficient.{u} l (PadicAlgCl l) E) T W
        (C.integral.inv.hom.app W s) x) =
    (((integralChartRingIso l E T).hom.hom.app W
      ((integralChartRingIso l E T).inv.hom.app W
        ((integralContinuousIso l E T).hom.hom.app W
          (C.integral.inv.hom.app W s)))).down x : PadicAlgCl l)
  change (((integralContinuousIso l E T).hom.hom.app W
    (C.integral.inv.hom.app W s)).down x : PadicAlgCl l) = _
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    RingCat.comp_apply, RingCat.id_apply] using hc'

private theorem continuousChart_precomp (O : Type) [TopologicalSpace O]
    [Ring O] [IsTopologicalRing O]
    [IsCommMonObj (Profinite.continuousMapRingObj O)] {U V : Scheme.{u}} (g : U ⟶ V)
    (W : V.ProEtᵒᵖ)
    (s : (InternalModuleOperations.ring (Profinite.continuousMapRingObj O) V).obj.obj W)
    (x : ((proEtaleBaseChange g).obj W.unop).left) :
    ((chartComparison U O).hom.app
      ((proEtaleBaseChange g).op.obj W)
      ((InternalModuleOperations.coefficientMap
        (Profinite.continuousMapRingObj O) g).hom.app W s)).down x =
      ((chartComparison V O).hom.app W s).down
        ((pullback.fst W.unop.hom g).base x) := by
  have hn := CondensedRing.continuousChart_scheme_naturality g
    O
  have h := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f :
      condensedRingObj (Profinite.continuousMapRingObj O) V ⟶
      (lowerStar Ab.{u + 1} g).obj
        ((sheafCompose (ProEt.topology U) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (continuousMapRingSheaf U O)) ↦ f.hom) hn) W) s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app'] at h
  have hc := (InternalModuleOperations.coefficientMap_existsUnique
    (Profinite.continuousMapRingObj O) g).exists.choose_spec W s
  change (InternalModuleOperations.coefficientMap
    (Profinite.continuousMapRingObj O) g).hom.app W s = _ at hc
  have h' := congrArg (fun t : ULift.{u + 1}
    C(((proEtaleBaseChange g).obj W.unop).left, O) ↦
      t.down x) h
  change ((chartComparison U O).hom.app
    ((proEtaleBaseChange g).op.obj W)
      ((condensedPushforwardHom (Profinite.continuousMapRingObj O) g).hom.app W s)).down x =
    ((CondensedRing.continuousFunctionPushforward g O).hom.app
      (Opposite.op W.unop)
      ((chartComparison V O).hom.app W s)).down x at h'
  have hp := CondensedRing.continuousFunctionPushforward_app g
    O W.unop
    ((chartComparison V O).hom.app W s)
  have hp' := congrArg (fun t : ULift.{u + 1}
    C(((proEtaleBaseChange g).obj W.unop).left, O) ↦ t.down x) hp
  exact (congrArg (fun t ↦ ((chartComparison U
    O).hom.app ((proEtaleBaseChange g).op.obj W) t).down x)
      hc).trans (h'.trans hp')

private theorem integralPresentation_natural (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (I : ∀ T : Scheme.{u}, (adicLisseForget T).obj ((PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)).ring T) ≅
      InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T)
    (hI : ∀ (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
      (s : ((PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)).ring T).obj.obj W) (x : W.unop.left),
      let := PadicAlgCl.normedFieldOfAlgebra l E.1
      ((a.map T).hom.app W s).down.1 x =
        (((chartComparison T (PadicAlgCl.integers l E.1)).hom.app W
          ((I T).hom.hom.app W s)).down x : E.1))
    {U V : Scheme.{u}} (g : U ⟶ V) (W : V.ProEtᵒᵖ)
    (s : ((PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)).ring V).obj.obj W) :
    (I U).hom.hom.app ((proEtaleBaseChange g).op.obj W)
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
        ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).pull g).hom).hom.app W s) =
      (InternalModuleOperations.coefficientMap
        (Profinite.padicIntegersRingObj l E.1) g).hom.app W ((I V).hom.hom.app W s) := by
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  let := PadicAlgCl.isUltrametricDist_ofAlgebra l E.1
  have hn := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv_naturality_left_square
    (a.map V) (N.pull g).hom
    ((PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).pull g).hom
    (a.map U) (a.square g).symm
  have h := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f :
      (PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).ring V ⟶
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj (ringSheaf l U) ↦ f.hom) hn) W) s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h
  apply (ConcreteCategory.bijective_of_isIso
    ((chartComparison U (PadicAlgCl.integers l E.1)).hom.app
      ((proEtaleBaseChange g).op.obj W))).1
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  have h' := congrArg (fun t : (ringSheaf l U).obj.obj
    ((proEtaleBaseChange g).op.obj W) ↦ t.down.1 x) h
  have hleft := hI U ((proEtaleBaseChange g).op.obj W)
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      ((PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)).pull g).hom).hom.app W s) x
  have hright := hI V W s ((pullback.fst W.unop.hom g).base x)
  have hp := N.pull_normalized g W ((a.map V).hom.app W s) x
  have hc := @continuousChart_precomp (PadicAlgCl.integers l E.1)
    inferInstance inferInstance inferInstance inferInstance U V g W ((I V).hom.hom.app W s) x
  exact hleft.symm.trans (h'.symm.trans (hp.trans (hright.trans
    (congrArg (fun z : PadicAlgCl.integers l E.1 ↦ (z : PadicAlgCl l)) hc).symm)))

/-- Completed integral coefficients have the normalized continuous integral chart.

Source: Bhatt--Scholze, Lemma 6.8.2, the integral comparison and its finite quotient
normalizations; the integral component of lem-sf-native-scalar-ring-model, steps 1 and 3.
(blueprint: lem-sf-native-scalar-integral-presentation).

Proof in words: take the integral isomorphism of a normalized CoefficientPresentation.
Transport its continuous functions along Shrink.algEquiv. Uniqueness of the extension
of the p-adic absolute value shows that this algebra equivalence identifies the integer
subrings and is an isometry. The inverse of the canonical condensed continuous chart,
followed by section-ring reconstruction, gives the displayed ring isomorphism. The
finite constant and residue equations show that the integral comparison is independent
of the chosen presentation. Its integral and rational inclusions evaluate to the given
embedding, proving the pointwise equation with a.map by ha. Both completed pullback and
continuous precomposition have the same finite-quotient projections. Their equality at
every projection gives the last naturality clause. This works also on empty schemes. -/
theorem exists_nativeScalarIntegralPresentation
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T) :
    ∃ I : ∀ T : Scheme.{u}, (adicLisseForget T).obj ((PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)).ring T) ≅
      InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T,
      (∀ (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
        (s : ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).ring T).obj.obj W) (x : W.unop.left),
        letI := PadicAlgCl.normedFieldOfAlgebra l E.1
        ((a.map T).hom.app W s).down.1 x =
          (((chartComparison T (PadicAlgCl.integers l E.1)).hom.app W
            ((I T).hom.hom.app W s)).down x : E.1)) ∧
      (∀ {U V : Scheme.{u}} (g : U ⟶ V) (W : V.ProEtᵒᵖ)
        (s : ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).ring V).obj.obj W),
        (I U).hom.hom.app ((proEtaleBaseChange g).op.obj W)
          (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
            ((PurCompactSupport.completed l
              (Coefficient.{u} l (PadicAlgCl l) E)).pull g).hom).hom.app W s) =
          (InternalModuleOperations.coefficientMap
            (Profinite.padicIntegersRingObj l E.1) g).hom.app W ((I V).hom.hom.app W s)) := by
  choose C hC using fun T : Scheme.{u} ↦ coefficientPresentations_exists l T
  let I := fun T : Scheme.{u} ↦ integralPresentationIso l E T (C T E)
  have hI (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
      (s : ((PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)).ring T).obj.obj W) (x : W.unop.left) :
      letI := PadicAlgCl.normedFieldOfAlgebra l E.1
      ((a.map T).hom.app W s).down.1 x =
        (((chartComparison T (PadicAlgCl.integers l E.1)).hom.app W
          ((I T).hom.hom.app W s)).down x : E.1) := by
    rw [ha T (C T E)]
    exact integralPresentationIso_value l E T (C T E) W s x
  exact ⟨I, hI, fun g W s ↦ integralPresentation_natural l E a I hI g W s⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
