/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientImageComparisons
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientStrictImage
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientTowerLimitAcyclic
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Normalized direct image on completed-coefficient diagrams

Source: Stacks Tags 0D6E, 0A07 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance moduleGrothendieck (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    IsGrothendieckAbelian.{max u (t + 1)} (Mod W B) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := integralCoefficientAbSheafify.{t, u} W
  let := integralCoefficientAbLocallyBijective.{t, u} W
  exact CategoryTheory.moduleSheaves_grothendieck (ProEt.topology W) B

private instance towersGrothendieck (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ Mod W B) :=
  CategoryTheory.tower_grothendieck _

private instance pushLimits {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) :
    PreservesLimitsOfShape ℕᵒᵖ (push f c) := by
  let V := SheafOfModules.forget.{max u (t + 1)} (R l E Y) ⋙
    PresheafOfModules.toPresheaf (R l E Y).obj
  have : PreservesLimitsOfShape ℕᵒᵖ (push f c ⋙ V) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      ((SheafOfModules.forget.{max u (t + 1)} (R l E X) ⋙
        PresheafOfModules.toPresheaf (R l E X).obj) ⋙
        (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ
          AddCommGrpCat.{max u (t + 1)}).obj (proEtaleBaseChange f).op)
    infer_instance
  have : ReflectsLimitsOfShape ℕᵒᵖ V := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ V

private theorem towerSquares {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f)
    (T : RightImage ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap)))
    (n : ℕ) :
    ∃ S : Square ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap))
        (push f C.structureMap)
        ((evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n))
        ((evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n))
        T C.completedImage (C.source.evaluation n) (C.target.evaluation n),
      IsSectionwiseIdentity Y (R l E Y) S.ordinary.hom := by
  let := C.completedAdditive
  let c : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap)) ⋙
      (evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n) ≅
        (evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n) ⋙ push f C.structureMap :=
    Iso.refl _
  obtain ⟨e, he, -⟩ := CategoryTheory.derivedCoefficientComparison
    _ _ _ _ (C.source.evaluation n).functor (C.target.evaluation n).functor
    (C.source.evaluation n).factors (C.target.evaluation n).factors
    T.functor C.completedImage.functor T.unit C.completedImage.unit T.computes
    (fun I hI ↦ by
      have := hI
      exact C.completedImage.computes _ (tower_evaluation_isKInjective _ I (op n))) c
  refine ⟨⟨c, e, ?_⟩, fun _ _ _ ↦ HEq.rfl⟩
  intro K
  have h := congrArg
    (fun a ↦ (C.target.evaluation n).factors.hom.app
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          (push f C.structureMap)).mapHomologicalComplex (.up ℤ)).obj K) ≫
      a ≫ C.completedImage.functor.map ((C.source.evaluation n).factors.hom.app K))
    (he K)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at h
  erw [C.completedImage.functor.map_id, Category.comp_id] at h
  exact h

/-- Extend any normalized site-side models to the coherent direct-image comparison.
The supplied structural map is fixed by all its finite projections.
The conclusion concerns strict derived diagrams and their actual limit projections;
it makes no completeness or reconstruction assertion.

Source: Stacks sites-cohomology.tex, Tags 0D6E and 0A07; Zheng, Construction 4.1
(blueprint: lem-pur-completed-coefficient-direct-image-diagrams).
Proof:
1. Obtain the coefficient comparisons, preserving the supplied site models and
structural map. Their quotient identity, composition and projection equations are
retained in CoefficientComparisonData.
2. Derive the additive levelwise pushforward on the Grothendieck category of towers.
Evaluation preserves K-injective complexes, so the generic normalized derived square
constructs every tower evaluation comparison. Its ordinary map is identity.
3. Obtain the strict-system direct image and its diagram square for the fixed
coefficient comparisons and tower image. This keeps all semilinear transitions.
4. Detect preservation of ordinary limits after forgetting to abelian presheaves.
The resulting ordinary comparison is limit.post. Acyclicity for the target inverse
limit gives the normalized derived comparison by derived composition.
5. Use uniqueness after the unit of the composite derived functor to prove the
projection equation. Cancel the source exact evaluation factor; use the comparison
normalization, target projection naturality, evaluation-square normalization, and
both projection normalizations. The remaining equation is limit.post followed by
a limit projection equals pushforward of the source projection. Assemble the record.
All identifications retain the supplied exact factors and universal units. -/
theorem directImageDiagrams_exists {X Y : Scheme.{t}} (f : X ⟶ Y)
    (source : SiteData l E X) (target : SiteData l E Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    (hconstant : integralConstantToCompletionOfUniverses l E Y ≫ c =
      constantStructure l E f ≫
        (ringPush.{t, u} f).map (integralConstantToCompletionOfUniverses l E X)) :
    ∃ D : DiagramComparisonData l E f,
      D.source = source ∧ D.target = target ∧ D.structureMap = c := by
  classical
  obtain ⟨C, hsource, htarget, hcmap⟩ :=
    coefficientComparisons_exists l E f source target c hc hconstant
  let := C.completedAdditive
  obtain ⟨Rt, ηt, ht, hIt, -⟩ := CategoryTheory.totalDerivedData
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap))
  let T : RightImage ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap)) :=
    ⟨Rt, ηt, ht, hIt⟩
  obtain ⟨S⟩ := strictImage_exists l E f C T
  choose ev hev using towerSquares l E f C T
  let ordinary : ordinaryTowerLimit l E X ⋙ push f C.structureMap ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap) ⋙
        ordinaryTowerLimit l E Y := preservesLimitNatIso (push f C.structureMap)
  let := C.source.limitAdditive
  let := C.target.limitAdditive
  obtain ⟨a, ha⟩ := CategoryTheory.towerComparison_existsLimitIso
    (push f C.structureMap) C.completedImage.functor T.functor
    C.source.limit.functor C.target.limit.functor
    C.completedImage.unit T.unit C.source.limit.unit C.target.limit.unit
    C.completedImage.computes T.computes C.source.limit.computes
    (towerLimit_push_acyclic l E f C.structureMap C.target.toSiteLimitData) ordinary
  have hprojection : ∀ (M : DerivedCategory (ℕᵒᵖ ⥤ Mod X (R l E X))) n,
      a.hom.app M ≫ (C.target.limitProjection n).app (T.functor.obj M) ≫
          (ev n).comparison.hom.app M =
        C.completedImage.functor.map ((C.source.limitProjection n).app M) := by
    intro M n
    have := CategoryTheory.towerComparison_limPreservesKInjective
      (A := Mod X (R l E X))
    obtain ⟨α, hα, hαapp⟩ := CategoryTheory.towerComparison_existsComposite
      (ordinaryTowerLimit l E X) (push f C.structureMap)
      C.source.limit.functor C.completedImage.functor
      C.source.limit.unit C.completedImage.unit C.source.limit.computes (fun I hI ↦ by
        have := hI
        exact C.completedImage.computes _ inferInstance)
    have := hα
    let γ₁ : C.source.limit.functor ⋙ C.completedImage.functor ⟶
        (C.source.evaluation n).functor ⋙ C.completedImage.functor :=
      a.hom ≫ Functor.whiskerLeft T.functor (C.target.limitProjection n) ≫
        (ev n).comparison.hom
    let γ₂ : C.source.limit.functor ⋙ C.completedImage.functor ⟶
        (C.source.evaluation n).functor ⋙ C.completedImage.functor :=
      Functor.whiskerRight (C.source.limitProjection n) C.completedImage.functor
    have hγ : γ₁ = γ₂ := by
      apply Functor.rightDerived_ext _ α
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod X (R l E X)) (.up ℤ))
      apply NatTrans.ext
      funext K
      change α.app K ≫ (a.hom.app (DerivedCategory.Q.obj K) ≫
          (C.target.limitProjection n).app (T.functor.obj (DerivedCategory.Q.obj K)) ≫
          (ev n).comparison.hom.app (DerivedCategory.Q.obj K)) =
        α.app K ≫ C.completedImage.functor.map
          ((C.source.limitProjection n).app (DerivedCategory.Q.obj K))
      rw [hαapp]
      apply (cancel_mono
        (C.completedImage.functor.map ((C.source.evaluation n).factors.hom.app K))).mp
      let Ftc := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (push f C.structureMap)).mapHomologicalComplex (.up ℤ)
      have hn := (C.target.limitProjection n).naturality (T.unit.app K)
      have hevid (H : ℕᵒᵖ ⥤ Mod X (R l E X)) :
          (ev n).ordinary.hom.app H = 𝟙 _ := by
        ext U x
        exact eq_of_heq (hev n H U x)
      have hchain :
          (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app K ≫
            (NatTrans.mapHomologicalComplex
              (lim.π (op n) : ordinaryTowerLimit l E Y ⟶
                (evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n)) (.up ℤ)).app
                  (Ftc.obj K) ≫
            (NatTrans.mapHomologicalComplex (ev n).ordinary.hom (.up ℤ)).app K =
          ((push f C.structureMap).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (lim.π (op n) : ordinaryTowerLimit l E X ⟶
                (evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n)) (.up ℤ)).app K) := by
        apply HomologicalComplex.hom_ext
        intro i
        change limit.post (K.X i) (push f C.structureMap) ≫
            limit.π _ (op n) ≫ (ev n).ordinary.hom.app (K.X i) = _
        rw [hevid]
        erw [Category.comp_id]
        exact preservesLimitIso_hom_π (push f C.structureMap) (K.X i) (op n)
      have hfπ := C.completedImage.unit.naturality
        ((NatTrans.mapHomologicalComplex
          (lim.π (op n) : ordinaryTowerLimit l E X ⟶
            (evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n)) (.up ℤ)).app K)
      simp only [Category.assoc]
      have ha' := congrArg (fun k ↦ k ≫
        (C.target.limitProjection n).app (T.functor.obj (DerivedCategory.Q.obj K)) ≫
        (ev n).comparison.hom.app (DerivedCategory.Q.obj K) ≫
        C.completedImage.functor.map ((C.source.evaluation n).factors.hom.app K)) (ha K)
      simp only [Category.assoc] at ha'
      rw [ha']
      erw [← Category.assoc (C.target.limit.functor.map (T.unit.app K)), hn]
      simp only [Category.assoc]
      erw [(ev n).normalization K]
      have hs' := congrArg (fun k ↦ k ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ev n).ordinary.hom (.up ℤ)).app K) ≫
        C.completedImage.unit.app
          ((((evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n)).mapHomologicalComplex
            (.up ℤ)).obj K)) (C.target.limitProjection_normalization (Ftc.obj K) n)
      simp only [Category.assoc] at hs'
      erw [hs']
      erw [← Category.assoc, ← DerivedCategory.Q.map_comp,
        ← Category.assoc, ← DerivedCategory.Q.map_comp, hchain, hfπ]
      simp only [← C.completedImage.functor.map_comp]
      erw [C.source.limitProjection_normalization K n]
      rfl
    exact NatTrans.congr_app hγ M
  refine ⟨{ toCoefficientComparisonData := C
            systemPush := S.systemPush
            systemPushAdditive := S.systemPushAdditive
            systemPushEvaluation := S.systemPushEvaluation
            systemPushEvaluation_identity := S.systemPushEvaluation_identity
            systemImage := S.systemImage
            towerImage := T
            diagramSquare := S.diagramSquare
            diagramOrdinary_identity := S.diagramOrdinary_identity
            towerEvaluation := ev
            towerEvaluation_identity := hev
            ordinaryLimit := ordinary
            ordinaryLimit_projections := fun _ ↦ rfl
            limitComparison := a
            limitNormalization := ha
            limitProjection := hprojection }, hsource, htarget, hcmap⟩

end WeilConjectures.CompletedCoefficientPushforward
