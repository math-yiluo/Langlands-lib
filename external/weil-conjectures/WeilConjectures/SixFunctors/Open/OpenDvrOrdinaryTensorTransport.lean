/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import WeilConjectures.SixFunctors.Open.OpenDvrScalarUnitFormula
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
import all WeilConjectures.Algebra.Homology.QuotientIsoTransport.RingIsoQuotientSystemTransport
import all WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Ordinary tensor transport for the DVR coefficient comparison

Source: Stacks Tag 03EK; the ordinary tensor transport step of
`lem-sf-open-dvr-strict-reduction-comparison`.
(blueprint: lem-sf-open-dvr-ordinary-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open MonoidalCategory
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance (priority := 20000) preciseAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} := openDvrAbSheafify T

local instance (priority := 20000) preciseAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  openDvrAbLocallyBijective T

attribute [local irreducible] HasDerivedCategory.standard scalarReductionExistence
  scalarReductionExtension coefficientSequenceRestriction
  coefficientSequenceEvaluation coefficientSequenceTransition coefficientOrdinaryQuotient
  unrestrictedIntegralTransition constantSheaf operationOrdinaryAdjunction
  Adjunction.leftAdjointUniq

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  SheafOfModules.restrictScalars integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose completedAdicCommRing completedAdicCommPresheaf
  SheafOfModules.QuotientIsoTransport.transport completedAdicFiniteModule
  completedAdicFiniteCommRing completedAdicFiniteCommPresheaf completedAdicCommProjection
  completedAdicOrdinaryTower completedAdicModules_monoidal SheafOfModules.monoidalCategory

private theorem scalarAugmentation_component (T : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E T)
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) (i : ℤ) (n : ℕ) :
    ((openScalarComplexAugmentation l E T M Q).f i).app (op n) =
      M.adjunction.unit.app (Q.X i) ≫
        limit.π ((coefficientSequenceRestriction l E T).obj (M.tensor.obj (Q.X i)))
          (op n) := by
  dsimp only [openScalarComplexAugmentation, Adjunction.homEquiv_counit,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    Adjunction.mapHomologicalComplex_unit_app_f]
  change (M.adjunction.unit.app (Q.X i) ≫ 𝟙 _) ≫ limit.π _ (op n) = _
  rw [Category.comp_id]

private theorem scalarTowerComparison (T : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E T)
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) :
    ∃ κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
        ((CompletionUnit.tower l E T).obj ((M.quotient l E T).obj Q)) ≅
          unrestrictedIntegralComplexTower.{u, u} l E T Q,
      ∀ n : ℕ, HEq
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (openScalarComplexAugmentation l E T M Q)).app (op n) ≫ κ.hom.app (op n))
        (unrestrictedTowerUnit.{u, u} l E T Q n) := by
  classical
  let D := effectivityTestDatum (if l = 2 then 3 else 2)
    (by split <;> decide)
  have hl : l ≠ D.p := by
    dsimp only [D, effectivityTestDatum]
    split <;> omega
  let I := (M.quotient l E T).obj Q
  let b (n : ℕ) := ordinaryFiniteComparison l E T n I Q
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app Q)
  have hb (n : ℕ) :
      ((CompletionUnit.tower l E T).obj I).asFunctor.map
          (homOfLE (Nat.le_succ n)).op ≫ (b n).hom =
        (b (n + 1)).hom ≫
          (unrestrictedIntegralComplexTower l E T Q).map (homOfLE (Nat.le_succ n)).op := by
    change _ = (b (n + 1)).hom ≫
      (Functor.ofOpSequence (X := fun n ↦ unrestrictedTowerComplex l E T n Q)
        (fun n ↦ unrestrictedTowerTransition l E T Q n)).map
        (homOfLE (Nat.le_succ n)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    apply ordinaryChainSquare l E T D hl (n + 1) n (Nat.le_succ n) I Q
    · apply HomologicalComplex.hom_ext
      intro i
      change (coefficientSequenceTransition l E T (Nat.le_succ n)).app
          (M.tensor.obj (Q.X i)) ≫ (normalizedDVRModuleRes l E T (Nat.le_succ n)).map
            ((M.evaluation n).hom.app (Q.X i)) =
        (M.evaluation (n + 1)).hom.app (Q.X i) ≫
          (coefficientOrdinaryQuotient l E T (Nat.le_succ n)).app (Q.X i)
      have h := M.transition (Q.X i) (m := n + 1) (n := n) (Nat.le_succ n)
      exact h
    · exact fun i ↦ unitStepDegree l E T n D hl Q i
  obtain ⟨κ, hκ⟩ := assembleObjectTowerIso ((CompletionUnit.tower l E T).obj I)
    (unrestrictedIntegralComplexTower l E T Q) b hb
  refine ⟨κ, ?_⟩
  intro n
  apply heq_of_eq
  rw [hκ]
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, ordinaryFiniteComparison_f]
  change ((openScalarComplexAugmentation l E T M Q).f i).app (op n) ≫
    ((operationEvaluationAt l E T n (M.tensor.obj (Q.X i))).hom ≫
      (scalarReductionRestriction l E T n).map ((M.evaluation n).hom.app (Q.X i))) = _
  rw [scalarAugmentation_component]
  ext V x
  exact (M.unit_tensor (Q.X i) n V x).trans
    ((unrestrictedTowerUnit_condition l E T Q) n i V x).symm

private def finiteCommIso
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) (n : ℕ) :
    integralCoefficientCommRingSheaf.{u, u} l E T n ≅ completedAdicFiniteCommRing T d n :=
  (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimageIso (C.finite n)

private theorem finiteCommSquare
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) (n : ℕ) :
    C.completed.inv ≫ completedAdicCommProjection T d n =
      completedIntegralCommRingProjectionUnrestricted l E T n ≫ (finiteCommIso l E C n).hom := by
  apply (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  simp only [Functor.map_comp, finiteCommIso, Functor.preimageIso_hom, Functor.map_preimage]
  have hp : (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedAdicCommProjection T d n) = completedAdicProjection T d n := by
    ext U x
    rfl
  have hq : (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted l E T n) =
          limit.π (integralCoefficientSheafSystem l E T) (op n) := by
    ext U x
    rfl
  rw [hp, hq, ← C.completed_projection]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

section ScalarTensor
universe a b r
variable {X : Type a} [Category.{b} X] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology X}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

private def tensorModelIso (φ : R ⟶ S) (A : SheafOfModules.SystemScalarModel φ) :
    tensorRight (SheafOfModules.restrictedTensorCoefficient φ) ≅
      A.model.E ⋙ SheafOfModules.restrictedTensorScalars φ :=
  (SheafOfModules.siteSheafTensorRightIso R _).symm ≪≫
    (SheafOfModules.ordinarySwapIso A.model).symm

private theorem tensorModelIso_one (φ : R ⟶ S) (A : SheafOfModules.SystemScalarModel φ)
    (F : SheafOfModules.QuotientIsoTransport.Modules R) (U : Xᵒᵖ) (x : F.val.obj U) :
    ((tensorModelIso φ A).hom.app F).val.app U
      (CategoryTheory.CochainPullback.moduleTmul F
        (SheafOfModules.restrictedTensorCoefficient φ) U x (1 : S.obj.obj U)) =
      (A.ordinaryAdj.unit.app F).val.app U x := by
  rw [A.unit_normalized]
  change (((SheafOfModules.restrictedTensorScalars φ).map
      (eqToHom (A.model.obj_eq F).symm)).val.app U)
      ((SheafOfModules.moduleTensorScalarIso φ F).hom.val.app U
        (CategoryTheory.CochainPullback.moduleTmul F
          (SheafOfModules.restrictedTensorCoefficient φ) U x (1 : S.obj.obj U))) = _
  rw [SheafOfModules.moduleTensorScalarIso_pure]
  simp only [SheafOfModules.systemModelTmul, one_smul]
  rfl
end ScalarTensor

attribute [local irreducible] tensorModelIso
  SheafOfModules.QuotientIsoTransport.ordinaryScalarSquare
  SheafOfModules.QuotientIsoTransport.scalarRestrictionSquare

private def coefficientTransport
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) :
    scalarReductionSource.{u, u} l E T ⥤ CompletedAdicModules T d :=
  SheafOfModules.QuotientIsoTransport.transport.{u + 1, u, u + 1}
    (J := ProEt.topology T) C.completed.symm

attribute [local implicit_reducible] coefficientTransport

private def adicScalarModel (T : Scheme.{u})
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)) (n : ℕ) :
    SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (J := ProEt.topology T) (completedAdicCommProjection T d n) :=
  (SheafOfModules.nonempty_systemScalarModel.{u + 1, u, u + 1}
    (J := ProEt.topology T) (completedAdicCommProjection T d n)).some

private def integralScalarModel (T : Scheme.{u}) (n : ℕ) :
    SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (J := ProEt.topology T) (completedIntegralCommRingProjectionUnrestricted.{u, u} l E T n) :=
  (SheafOfModules.nonempty_systemScalarModel.{u + 1, u, u + 1}
    (J := ProEt.topology T)
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E T n)).some

attribute [local irreducible] adicScalarModel integralScalarModel

private theorem tensorQuotientUnit_model (T : Scheme.{u})
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)) (n : ℕ)
    (F : CompletedAdicModules T d) :
    (ρ_ F).inv ≫ (F ◁ reconstructionQuotientUnit T d n) ≫
      (tensorModelIso.{u + 1, u, u + 1} (J := ProEt.topology T)
      (completedAdicCommProjection T d n)
        (adicScalarModel l E T d n)).hom.app F =
      (adicScalarModel l E T d n).ordinaryAdj.unit.app F := by
  ext U x
  change ((tensorModelIso.{u + 1, u, u + 1} (J := ProEt.topology T)
      (completedAdicCommProjection T d n)
    (adicScalarModel l E T d n)).hom.app F).val.app U
    ((F ◁ reconstructionQuotientUnit T d n).val.app U ((ρ_ F).inv.val.app U x)) = _
  erw [SheafOfModules.unitor_inv_pure.{u + 1, u, 0}
    (completedAdicCommRing T d) F U x]
  erw [← id_tensorHom F (reconstructionQuotientUnit T d n),
    CategoryTheory.CochainPullback.moduleTmul_map (R := completedAdicCommRing T d)
      (𝟙 F) (reconstructionQuotientUnit T d n) U x
        (1 : (completedAdicRing T d).obj.obj U)]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  erw [reconstructionQuotientUnit,
    (reconstructionQuotientUnit_exists T d n).exists.choose_spec U]
  exact tensorModelIso_one.{u + 1, u, u + 1} (J := ProEt.topology T)
    (completedAdicCommProjection T d n) (adicScalarModel l E T d n) F U x

private def finiteTensorIso
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) (n : ℕ) :
    coefficientTransport l E C ⋙
        tensorRight (completedAdicFiniteModule T d n) ≅
      scalarReductionExtension l E T n ⋙ scalarReductionRestriction l E T n ⋙
        coefficientTransport l E C := by
  let A := integralScalarModel l E T n
  let B := adicScalarModel l E T d n
  let φ := completedIntegralCommRingProjectionUnrestricted l E T n
  let ψ := completedAdicCommProjection T d n
  let H := coefficientTransport l E C
  let j := A.ordinaryAdj.leftAdjointUniq (operationOrdinaryAdjunction l E T n)
  let q := SheafOfModules.QuotientIsoTransport.ordinaryScalarSquare φ ψ
    C.completed.symm (finiteCommIso l E C n) (finiteCommSquare l E C n) A B
  let r := SheafOfModules.QuotientIsoTransport.scalarRestrictionSquare φ ψ
    C.completed.symm (finiteCommIso l E C n) (finiteCommSquare l E C n)
  exact Functor.isoWhiskerLeft H (tensorModelIso.{u + 1, u, u + 1} (J := ProEt.topology T) ψ B) ≪≫
    Functor.isoWhiskerRight q.symm
      (SheafOfModules.restrictedTensorScalars.{u + 1, u, u + 1}
        (J := ProEt.topology T) ψ) ≪≫
    Functor.isoWhiskerLeft A.model.E r.symm ≪≫
    Functor.isoWhiskerRight j (scalarReductionRestriction l E T n ⋙ H)

private theorem composeNormalizedUnit
    {Y : Type*} [Category Y] {A B C D E F G : Y}
    (a : A ⟶ B) (b : B ⟶ C) (t : C ⟶ D) (c : A ⟶ D)
    (f : D ⟶ E) (d : A ⟶ F) (r : F ≅ E) (g : F ⟶ G)
    (ht : a ≫ b ≫ t = c) (hu : c ≫ f = d ≫ r.hom) :
    a ≫ b ≫ t ≫ f ≫ r.inv ≫ g = d ≫ g := by
  simp only [← Category.assoc] at ht ⊢
  rw [ht, hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem isoComparisonFromUnit
    {Y : Type*} [Category Y] {A B C D : Y}
    (a : A ⟶ B) (e : B ≅ D) (t : C ≅ D) (b : A ⟶ C)
    (h : a ≫ e.hom = b ≫ t.hom) : a ≫ (e ≪≫ t.symm).hom = b := by
  apply (cancel_mono t.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using h

private theorem finiteTensorIso_unit
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) (n : ℕ)
    (F : scalarReductionSource.{u, u} l E T) :
    let H := coefficientTransport l E C
    (ρ_ (H.obj F)).inv ≫ (H.obj F ◁ reconstructionQuotientUnit T d n) ≫
      (finiteTensorIso l E C n).hom.app F =
      H.map ((operationOrdinaryAdjunction l E T n).unit.app F) := by
  let A := integralScalarModel l E T n
  let B := adicScalarModel l E T d n
  let φ := completedIntegralCommRingProjectionUnrestricted l E T n
  let ψ := completedAdicCommProjection T d n
  let H := coefficientTransport l E C
  let j := A.ordinaryAdj.leftAdjointUniq (operationOrdinaryAdjunction l E T n)
  let q := SheafOfModules.QuotientIsoTransport.ordinaryScalarSquare φ ψ
    C.completed.symm (finiteCommIso l E C n) (finiteCommSquare l E C n) A B
  let r := SheafOfModules.QuotientIsoTransport.scalarRestrictionSquare φ ψ
    C.completed.symm (finiteCommIso l E C n) (finiteCommSquare l E C n)
  have hu : B.ordinaryAdj.unit.app (H.obj F) ≫
      (SheafOfModules.restrictedTensorScalars ψ).map (q.inv.app F) =
      H.map (A.ordinaryAdj.unit.app F) ≫ r.hom.app (A.model.E.obj F) := by
    have h := SheafOfModules.QuotientIsoTransport.ordinaryScalarSquare_unit φ ψ
      C.completed.symm (finiteCommIso l E C n) (finiteCommSquare l E C n) A B F
    exact h
  dsimp only [finiteTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_map]
  exact (composeNormalizedUnit (ρ_ (H.obj F)).inv
    (H.obj F ◁ reconstructionQuotientUnit T d n)
    ((tensorModelIso.{u + 1, u, u + 1} (J := ProEt.topology T) ψ B).hom.app (H.obj F))
    (B.ordinaryAdj.unit.app (H.obj F))
    ((SheafOfModules.restrictedTensorScalars ψ).map (q.inv.app F))
    (H.map (A.ordinaryAdj.unit.app F)) (r.app (A.model.E.obj F))
    (H.map ((scalarReductionRestriction l E T n).map (j.hom.app F)))
    (tensorQuotientUnit_model l E T d n (H.obj F)) hu).trans
      ((H.map_comp _ _).symm.trans (congrArg H.map
        (Adjunction.unit_leftAdjointUniq_hom_app A.ordinaryAdj
          (operationOrdinaryAdjunction l E T n) F)))

private theorem quotientUnit_epi
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) (n : ℕ) :
    Epi (reconstructionQuotientUnit T d n) := by
  let J := ProEt.topology T
  let a := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    C.completed.hom
  let b := limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op n)
  let c := (C.finite n).hom
  have ha : Presheaf.IsLocallySurjective J a.hom := inferInstance
  have hb : Presheaf.IsLocallySurjective J b.hom :=
    completedProjection_locallySurjective l E T n
  have hc : Presheaf.IsLocallySurjective J c.hom := inferInstance
  have hp : Presheaf.IsLocallySurjective J (completedAdicProjection T d n).hom := by
    rw [← C.completed_projection]
    change Presheaf.IsLocallySurjective J (a.hom ≫ b.hom ≫ c.hom)
    infer_instance
  have he : ((SheafOfModules.toSheaf.{u + 1} (completedAdicRing T d)).map
      (reconstructionQuotientUnit T d n)).hom =
      Functor.whiskerRight (completedAdicProjection T d n).hom
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
    ext U x
    change (reconstructionQuotientUnit T d n).val.app U x =
      (completedAdicProjection T d n).hom.app U x
    change (completedAdicRing T d).obj.obj U at x
    have h := ((reconstructionQuotientUnit T d n).val.app U).hom.map_smul
      x (1 : (completedAdicRing T d).obj.obj U)
    change (reconstructionQuotientUnit T d n).val.app U
        (x * (1 : (completedAdicRing T d).obj.obj U)) =
      (completedAdicProjection T d n).hom.app U x *
        (show (completedAdicFiniteRing T d n).obj.obj U from
          (reconstructionQuotientUnit T d n).val.app U
            (1 : (completedAdicRing T d).obj.obj U)) at h
    rw [mul_one, reconstructionQuotientUnit,
      (reconstructionQuotientUnit_exists T d n).exists.choose_spec U, mul_one] at h
    exact h
  have hu : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf.{u + 1} (completedAdicRing T d)).map
        (reconstructionQuotientUnit T d n)) := by
    change Presheaf.IsLocallySurjective J _
    rw [he, Presheaf.isLocallySurjective_iff_whisker_forget]
    exact (Presheaf.isLocallySurjective_iff_whisker_forget J
      (completedAdicProjection T d n).hom).mp hp
  have : Epi ((SheafOfModules.toSheaf.{u + 1} (completedAdicRing T d)).map
      (reconstructionQuotientUnit T d n)) :=
    Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf.{u + 1} (completedAdicRing T d)).epi_of_epi_map inferInstance

private theorem tensorQuotientUnit_epi
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)}
    {T : Scheme.{u}} (C : OpenDvrCoefficientModel l E d T) (n : ℕ)
    (F : CompletedAdicModules T d) :
    Epi ((reconstructionOrdinaryUnit T d).app F ≫
      limit.π ((completedAdicOrdinaryTower T d).obj F) (op n)) := by
  rw [show (reconstructionOrdinaryUnit T d).app F ≫
      limit.π ((completedAdicOrdinaryTower T d).obj F) (op n) =
        (ρ_ F).inv ≫ (F ◁ reconstructionQuotientUnit T d n) from
    (reconstructionOrdinaryUnit_exists T d).exists.choose_spec F n]
  have : Epi (reconstructionQuotientUnit T d n) := quotientUnit_epi l E C n
  have : PreservesColimits (tensorLeft F) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients
      (completedAdicCommRing T d) F
  have : Epi (F ◁ reconstructionQuotientUnit T d n) :=
    (tensorLeft F).map_epi _
  infer_instance

private theorem towerIsoFromUnits
    {X Y : Type*} [Category X] [Category Y]
    (H : X ⥤ Y) (A B : X ⥤ (ℕᵒᵖ ⥤ Y))
    (α : ∀ (n : ℕ) (F : X), H.obj F ⟶ (A.obj F).obj (op n))
    (β : ∀ F : X, (Functor.const ℕᵒᵖ).obj (H.obj F) ⟶ B.obj F)
    (en : ∀ n : ℕ,
      A ⋙ (evaluation ℕᵒᵖ Y).obj (op n) ≅ B ⋙ (evaluation ℕᵒᵖ Y).obj (op n))
    (hepi : ∀ n F, Epi (α n F))
    (hstep : ∀ F n, α (n + 1) F ≫ (A.obj F).map (homOfLE n.le_succ).op = α n F)
    (hnorm : ∀ n F, α n F ≫ (en n).hom.app F = (β F).app (op n)) :
    ∃ e : A ≅ B, ∀ F n, α n F ≫ (e.hom.app F).app (op n) = (β F).app (op n) := by
  have ht (F : X) (n : ℕ) :
      (A.obj F).map (homOfLE n.le_succ).op ≫ (en n).hom.app F =
        (en (n + 1)).hom.app F ≫ (B.obj F).map (homOfLE n.le_succ).op := by
    have := hepi (n + 1) F
    apply (cancel_epi (α (n + 1) F)).mp
    rw [← Category.assoc, hstep, hnorm, ← Category.assoc, hnorm]
    exact (Category.id_comp _).symm.trans
      ((β F).naturality (homOfLE n.le_succ).op)
  let e : A ≅ B := NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents (fun n ↦ (en n.unop).app F)
      (fun f ↦ (NatTrans.ofOpSequence (fun n ↦ (en n).hom.app F) (ht F)).naturality f))
    (by
      intro F G f
      apply NatTrans.ext
      funext n
      exact (en n.unop).hom.naturality f)
  exact ⟨e, fun F n ↦ hnorm n F⟩

private def evaluationTensorIso (T : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E T) (n : ℕ) :
    M.tensor ⋙ coefficientSequenceRestriction l E T ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E T)).obj (op n) ≅
      scalarReductionExtension l E T n ⋙ scalarReductionRestriction l E T n :=
  Functor.isoWhiskerLeft M.tensor (eqToIso (coefficientSequenceRestriction_evaluation l E T n)) ≪≫
    Functor.isoWhiskerRight (M.evaluation n) (scalarReductionRestriction l E T n)

private theorem ordinaryFiniteUnit (T : Scheme.{u}) (n : ℕ)
    (F : scalarReductionSource.{u, u} l E T) (U : T.ProEtᵒᵖ) (x : F.val.obj U) :
    ((operationOrdinaryAdjunction l E T n).unit.app F).val.app U x =
      unrestrictedIntegralTensorSection l E T n F U 1 x := by
  unfold operationOrdinaryAdjunction
  rw [(scalarReductionExtension_adjunction l E T n).choose_spec]
  rfl

/-- The ordinary, representative-level tensor comparison under the coefficient isomorphism.
Source: Stacks Tag 03EK, strict tensor transport in the proof of
`lem-sf-open-dvr-strict-reduction-comparison`
(blueprint: lem-sf-open-dvr-ordinary-tensor-transport).

Proof: use C.completed_projection to identify each completed coefficient projection
with its scalar coefficient projection followed by C.finite. On sheafified tensor
sections send x tensor b to the scalar tensor with the same x and the inverse finite
coefficient image of b. Balancing follows from the projection square. The inverse
uses C.finite; extend both maps by the tensor universal property and sheafification,
so they are inverse isomorphisms. They commute with adjacent quotient transitions
by C.finite_transition; induction gives every tower arrow and hence the natural
isomorphism nu of ordinary tower functors.
At b = 1 the comparison sends the quotient unit to M.adjunction.unit, by M.unit_tensor;
this is the displayed ordinary unit equation. The evaluation isomorphisms of M,
after exact scalar restriction and transposition of the complex indices, give kappa.
M.transition identifies its arrows with the recorded unrestrictedIntegralTransition,
whose uniqueness is fixed on pure tensors. M.unit_tensor identifies its augmentation
with unrestrictedTowerUnit, also by its sectionwise uniqueness. All arguments allow
zero modules and empty site objects;
no quotient flatness is used. -/
theorem openDvrOrdinaryTensorTransport
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (M : CompletionUnit.OrdinaryModel l E T) :
    ∃ ν : C.modules.functor ⋙ completedAdicOrdinaryTower T d ≅
        M.tensor ⋙ coefficientSequenceRestriction.{u, u} l E T ⋙ C.ordinaryTowers,
      (∀ (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
        (i : ℤ) (n : ℕ),
        (reconstructionOrdinaryUnit T d).app (C.modules.functor.obj (Q.X i)) ≫
            limit.π ((completedAdicOrdinaryTower T d).obj
              (C.modules.functor.obj (Q.X i))) (op n) ≫ (ν.hom.app (Q.X i)).app (op n) =
          C.modules.functor.map
            (((openScalarComplexAugmentation l E T M Q).f i).app (op n))) ∧
      (∀ Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ,
        ∃ κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
            ((CompletionUnit.tower l E T).obj ((M.quotient l E T).obj Q)) ≅
              unrestrictedIntegralComplexTower.{u, u} l E T Q,
          ∀ n : ℕ, HEq
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
                (openScalarComplexAugmentation l E T M Q)).app (op n) ≫ κ.hom.app (op n))
            (unrestrictedTowerUnit.{u, u} l E T Q n)) := by
  classical
  dsimp only [OpenDvrCoefficientModel.ordinaryTowers]
  rw [C.modules_functor]
  let H := coefficientTransport l E C
  let A := H ⋙ completedAdicOrdinaryTower T d
  let B := M.tensor ⋙ coefficientSequenceRestriction l E T ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj H
  let α (n : ℕ) (F : scalarReductionSource l E T) :=
    (reconstructionOrdinaryUnit T d).app (H.obj F) ≫
      limit.π ((completedAdicOrdinaryTower T d).obj (H.obj F)) (op n)
  let β (F : scalarReductionSource l E T) :
      (Functor.const ℕᵒᵖ).obj (H.obj F) ⟶ B.obj F :=
    Functor.whiskerRight
      ((Functor.const ℕᵒᵖ).map (M.adjunction.unit.app F) ≫
        (limit.cone ((coefficientSequenceRestriction l E T).obj (M.tensor.obj F))).π) H
  let t (n : ℕ) := Functor.isoWhiskerRight (evaluationTensorIso l E T M n) H
  let en (n : ℕ) :
      A ⋙ (evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj (op n) ≅
        B ⋙ (evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj (op n) :=
    finiteTensorIso l E C n ≪≫ (t n).symm
  have hn (n : ℕ) (F : scalarReductionSource l E T) :
      α n F ≫ (en n).hom.app F = (β F).app (op n) := by
    have hn' : α n F ≫ (finiteTensorIso l E C n).hom.app F =
        H.map ((operationOrdinaryAdjunction l E T n).unit.app F) := by
      have ha : α n F = (ρ_ (H.obj F)).inv ≫
          (H.obj F ◁ reconstructionQuotientUnit T d n) :=
        (reconstructionOrdinaryUnit_exists T d).exists.choose_spec (H.obj F) n
      exact (congrArg (fun f ↦ f ≫ (finiteTensorIso l E C n).hom.app F) ha).trans
        ((Category.assoc _ _ _).trans (finiteTensorIso_unit l E C n F))
    have hunit : H.map ((operationOrdinaryAdjunction l E T n).unit.app F) =
        (β F).app (op n) ≫ (t n).hom.app F := by
      change H.map ((operationOrdinaryAdjunction l E T n).unit.app F) =
        H.map (M.adjunction.unit.app F ≫ limit.π _ (op n)) ≫
          H.map ((operationEvaluationAt l E T n (M.tensor.obj F)).hom ≫
            (scalarReductionRestriction l E T n).map ((M.evaluation n).hom.app F))
      rw [← H.map_comp]
      congr 1
      ext U x
      exact (ordinaryFiniteUnit l E T n F U x).trans (M.unit_tensor F n U x).symm
    exact isoComparisonFromUnit (α n F) ((finiteTensorIso l E C n).app F)
      ((t n).app F) ((β F).app (op n)) (hn'.trans hunit)
  obtain ⟨ν, hν⟩ := towerIsoFromUnits H A B α β en
    (fun n F ↦ tensorQuotientUnit_epi l E C n (H.obj F))
    (by
      intro F n
      dsimp only [α, A, Functor.comp_obj]
      rw [Category.assoc, limit.w]) hn
  refine ⟨ν, ?_, fun Q ↦ scalarTowerComparison l E T M Q⟩
  intro Q i n
  rw [scalarAugmentation_component]
  exact hν (Q.X i) n

end WeilConjectures
