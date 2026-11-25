/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # The normalized integral pullback tower

Source: Stacks Project, sites-modules.tex, Tags 03D7 and 03EL;
sites-cohomology.tex, Tag 06YY
(blueprint: lem-pur-normalized-integral-pullback-tower).

The projection square identifies the right adjoints of pullback followed by reduction
and reduction followed by finite pullback. Uniqueness of left adjoints gives the
comparison, and the composite units determine it on generators. Restriction along
the quotient epimorphism is fully faithful; this proves transition compatibility
and uniqueness of the whole strict tower comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.IntegralAmbient
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
attribute [local instance 2000] integralOperationsFiniteHasMap

attribute [local irreducible] constantSheaf

universe a₁ b₁ c₁ d₁
private theorem adjunctionSquare
    {C : Type a₁} [Category.{b₁} C] {D : Type c₁} [Category.{d₁} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A B : C} {P Q : D} (a : A ⟶ B) (b : P ⟶ Q)
    (f : L.obj A ⟶ P) (g : L.obj B ⟶ Q) :
    f ≫ b = L.map a ≫ g ↔
      adj.homEquiv A P f ≫ R.map b = a ≫ adj.homEquiv B Q g := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  exact (adj.homEquiv A Q).injective.eq_iff.symm

/-- The completed-ring structure map is determined by all finite projections.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-normalized-integral-pullback-tower).
Proof: the constant-section maps commute with every quotient reduction. Compose them
with the completed-ring projections to obtain a cone after direct image. Direct image
preserves limits, so its universal property gives the map, and the projections give
uniqueness. Taking the adjoint gives the map f⁻¹R_Y → R_X without interchanging f⁻¹
and inverse limit. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! c : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).obj (completedIntegralCommRingSheafUnrestricted l E X),
      ∀ n : ℕ, c ≫ ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
            (Scheme.ProEt.topology X)).map
              (completedIntegralCommRingProjectionUnrestricted l E X n) =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          Scheme.coefficientProEtaleDirectRingMap.{t, u} f
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let e := (completedRingAdj.{t, u} f).homEquiv
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
  let c := completedRingMap l E f
  have hc := (completedRingMap_existsUnique l E f).exists.choose_spec
  have hm (n : ℕ) : e c ≫
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        Scheme.coefficientProEtaleDirectRingMap.{t, u} f
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
    have hh := (adjunctionSquare (completedRingAdj.{t, u} f)
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
      (completedIntegralCommRingProjectionUnrestricted l E X n) c
      (completedRingConstantMap f
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).mp
      (hc n)
    simpa only [completedRingConstantMap, integralCoefficientCommRingSheaf, e,
      Equiv.apply_symm_apply] using hh
  refine ⟨e c, hm, ?_⟩
  intro d hd
  have h : e.symm d = c := by
    apply (completedRingMap_existsUnique l E f).unique ?_ hc
    intro n
    apply (adjunctionSquare (completedRingAdj.{t, u} f)
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
      (completedIntegralCommRingProjectionUnrestricted l E X n) (e.symm d)
      (completedRingConstantMap f
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).mpr
    simpa only [completedRingConstantMap, integralCoefficientCommRingSheaf, e,
      Equiv.apply_symm_apply] using hd n
  exact (e.apply_symm_apply d).symm.trans (congrArg e h)

/-- The unique projection-induced ring map, in its adjoint presentation.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def coefficientMap {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (coefficientMap_existsUnique l E f).exists.choose

attribute [local irreducible] HasDerivedCategory.standard

/-- Ordinary module direct image with the projection-induced scalar action.
Source: Stacks 03D2 (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def push {X Y : Scheme.{t}} (f : X ⟶ Y) :
    integralTowerModules l E X ⥤ integralTowerModules l E Y :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (S := SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (R := SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))
    ⟨Functor.whiskerRight (coefficientMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The ordinary module pullback exists in the independent coefficient universe.
Source: Stacks 03D2, 03D7 (blueprint: lem-pur-normalized-integral-pullback-tower).
Proof: transport to the coefficient-sized small site model. Presheaf module Kan
extension followed by module sheafification is left adjoint to this pushforward.
Transport back. Its tensor presentation is R_X ⊗_(f⁻¹R_Y) f⁻¹(-). -/
@[instance]
theorem push_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (push l E f).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes
    ⟨Functor.whiskerRight (coefficientMap l E f).hom (forget₂ CommRingCat RingCat)⟩

/-- Ordinary ambient module pullback along the specified coefficient map.
Source: Stacks 03D2 (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def pull {X Y : Scheme.{t}} (f : X ⟶ Y) := (push l E f).leftAdjoint

/-- The canonical module adjunction, fixing scalar insertion on generators.
Source: Stacks 03D7 (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def adjunction {X Y : Scheme.{t}} (f : X ⟶ Y) : pull l E f ⊣ push l E f :=
  Adjunction.ofIsRightAdjoint _

/-- Direct image is additive since it precomposes the sectionwise linear maps.
Source: Stacks 03D2 (blueprint: lem-pur-normalized-integral-pullback-tower).
Proof: addition of maps is sectionwise; coefficient restriction changes only the action. -/
@[instance]
theorem push_additive {X Y : Scheme.{t}} (f : X ⟶ Y) : (push l E f).Additive := by
  exact Functor.additive_of_preserves_binary_products (push l E f)

/-- The module pullback is additive.
Source: Stacks 03D2 (blueprint: lem-pur-normalized-integral-pullback-tower). -/
instance pull_additive {X Y : Scheme.{t}} (f : X ⟶ Y) : (pull l E f).Additive :=
  (adjunction l E f).left_adjoint_additive

/-- Termwise ordinary pullback, with no boundedness restriction.
Source: Stacks 06YY (blueprint: lem-pur-normalized-integral-pullback-tower). -/
abbrev pullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
  (pull l E f).mapHomologicalComplex (.up ℤ)

/-- The generalized inverse-image generator, normalized by the adjunction unit.
Source: Stacks 03D7 (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def pullSection {X Y : Scheme.{t}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (V : Y.ProEt) (x : M.val.obj (op V)) :=
  ((adjunction l E f).unit.app M).val.app (op V) x

/-- Scalar insertion into the finite-operation pullback, in the existing presentation.
Source: Stacks 03EL (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def finitePullSection {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)) :
    ((integralOperationsLevelPullback l E f n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange f).obj V)) :=
  @SMul.smul
    ((integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange f).obj V)))
    (((integralOperationsLevelPullback l E f n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange f).obj V))) inferInstance a
    (integralOperationsPullbackGenerator l E f n _ V
    (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) :
      ((integralOperationsLevelPullback l E f n).obj
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
          (op ((Scheme.proEtaleBaseChange f).obj V)))

/-- The source strict tower is completion of ordinary pullback.
Source: Stacks 06YY, 0941 (blueprint: lem-pur-normalized-integral-pullback-tower). -/
def pullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ) :=
  pullComplex l E f ⋙ IntegralOnSlice.tower l E X none

@[irreducible] private def pullGenerator {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pull l E f).obj M).val.obj (op ((proEtaleBaseChange f).obj V)) :=
  pullSection l E f M V x

@[irreducible] private def finiteGenerator {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((integralOperationsLevelPullback l E f n).obj M).val.obj
      (op ((proEtaleBaseChange f).obj V)) :=
  integralOperationsPullbackGenerator l E f n M V x

private theorem reductionAdjunction (W : Scheme.{t}) (n : ℕ) :
    ∃ a : unrestrictedIntegralReductionFunctor l E W n ⊣
        SheafOfModules.restrictScalars.{max u (t + 1)}
          ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat RingCat)).map
            (completedIntegralCommRingProjectionUnrestricted l E W n)),
      ∀ (M : integralTowerModules l E W) (V : W.ProEtᵒᵖ) (x : M.val.obj V),
        (a.unit.app M).val.app V x =
          unrestrictedIntegralTensorSection l E W n M V 1 x := by
  obtain ⟨a, ha⟩ := scalarReductionExtension_adjunction l E W n
  refine ⟨a, ?_⟩
  intro M V x
  exact ha M V x

@[irreducible] private def reductionAdj (W : Scheme.{t}) (n : ℕ) :=
  (reductionAdjunction l E W n).choose

private theorem reductionAdj_unit (W : Scheme.{t}) (n : ℕ)
    (M : integralTowerModules l E W) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((reductionAdj l E W n).unit.app M).val.app V x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  unfold reductionAdj
  exact (reductionAdjunction l E W n).choose_spec M V x

private def ambientDirectRingMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    completedIntegralCoefficientSheafUnrestricted l E Y ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (completedIntegralCoefficientSheafUnrestricted l E X) :=
  ⟨Functor.whiskerRight (coefficientMap l E f).hom (forget₂ CommRingCat RingCat)⟩

private theorem projectionSquare {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n)) ≫
        integralOperationsDirectRingMap l E f n =
      (ambientDirectRingMap l E f) ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat
          (ProEt.topology Y) (ProEt.topology X)).map
            ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
              (completedIntegralCommRingProjectionUnrestricted l E X n)) := by
  have h := (coefficientMap_existsUnique l E f).exists.choose_spec n
  exact congrArg
    (fun k ↦ (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map k)
    h.symm

@[irreducible] private def finitePullComparison {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    pull l E f ⋙ unrestrictedIntegralReductionFunctor l E X n ≅
      unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E f n := by
  let e := SheafOfModules.IntegralPullbackProof.pushRestrictionIso
    (proEtaleBaseChange f)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n))
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))
    (ambientDirectRingMap l E f)
    (integralOperationsDirectRingMap l E f n) (projectionSquare l E f n)
  exact ((adjunction l E f).comp (reductionAdj l E X n)).leftAdjointUniq
    (((reductionAdj l E Y n).comp (integralOperationsPullbackAdjunction l E f n)).ofNatIsoRight
      e.symm)

private theorem finitePullComparison_unit {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((finitePullComparison l E f n).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (unrestrictedIntegralTensorSection l E X n ((pull l E f).obj M)
        (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f M V x)) =
      finiteGenerator l E f n
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
          (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((adjunction l E f).comp (reductionAdj l E X n))
    (((reductionAdj l E Y n).comp (integralOperationsPullbackAdjunction l E f n)).ofNatIsoRight
        (SheafOfModules.IntegralPullbackProof.pushRestrictionIso
          (proEtaleBaseChange f)
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
            (completedIntegralCommRingProjectionUnrestricted l E X n))
          ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n))
          (ambientDirectRingMap l E f)
          (integralOperationsDirectRingMap l E f n) (projectionSquare l E f n)).symm) M
  have hh := congrArg (fun k ↦ k.val.app (op V) x) h
  simp only [Adjunction.comp_unit_app] at hh
  with_unfolding_all change (((finitePullComparison l E f n).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj V))
      (((reductionAdj l E X n).unit.app ((pull l E f).obj M)).val.app
        (op ((proEtaleBaseChange f).obj V)) (pullGenerator l E f M V x)) =
    (((integralOperationsPullbackAdjunction l E f n).unit.app
      ((unrestrictedIntegralReductionFunctor l E Y n).obj M)).val.app (op V))
        (((reductionAdj l E Y n).unit.app M).val.app (op V) x)) at hh
  simp only [reductionAdj_unit, finiteGenerator, integralOperationsPullbackGenerator,
    integralOperationsPullbackAdjunction] at hh
  with_unfolding_all exact hh

universe r₀
-- Work over abstract rings here: unfolding the completed ring limits at every
-- sectionwise equality would make kernel checking unnecessarily expensive.
private theorem adjointReduction_hom_ext
    {C : Type a₁} [Category.{b₁} C] {D : Type c₁} [Category.{d₁} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R Rm Rn : Sheaf K RingCat.{r₀}} {S : Sheaf J RingCat.{r₀}}
    (πm : R ⟶ Rm) (πn : R ⟶ Rn) (q : Rm ⟶ Rn) (hq : πm ≫ q = πn)
    [Presheaf.IsLocallySurjective K πm.hom]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r₀} J K).obj R)
    {L : SheafOfModules.{r₀} S ⥤ SheafOfModules.{r₀} R}
    {A : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} Rm}
    (adj : L ⊣ SheafOfModules.pushforward φ)
    (red : A ⊣ SheafOfModules.restrictScalars πm)
    (M : SheafOfModules.{r₀} S) (N : SheafOfModules.{r₀} Rn)
    (a b : (SheafOfModules.restrictScalars πm).obj (A.obj (L.obj M)) ⟶
      (SheafOfModules.restrictScalars πn).obj N)
    (h : ∀ (V : Cᵒᵖ) (x : M.val.obj V),
      a.val.app (F.op.obj V)
        ((red.unit.app (L.obj M)).val.app (F.op.obj V)
          ((adj.unit.app M).val.app V x)) =
      b.val.app (F.op.obj V)
        ((red.unit.app (L.obj M)).val.app (F.op.obj V)
          ((adj.unit.app M).val.app V x))) : a = b := by
  let lift := SheafOfModules.IntegralScalarProof.liftMap πm πn q hq (A.obj (L.obj M)) N
  have he : lift a = lift b := by
    apply ((adj.comp red).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
    ext V x
    change (lift a).val.app (F.op.obj V)
        ((red.unit.app (L.obj M)).val.app (F.op.obj V) ((adj.unit.app M).val.app V x)) =
      (lift b).val.app (F.op.obj V)
        ((red.unit.app (L.obj M)).val.app (F.op.obj V) ((adj.unit.app M).val.app V x))
    rw [SheafOfModules.IntegralScalarProof.liftMap_apply,
      SheafOfModules.IntegralScalarProof.liftMap_apply]
    exact h V x
  ext V x
  calc
    a.val.app V x = (lift a).val.app V x :=
      (SheafOfModules.IntegralScalarProof.liftMap_apply _ _ _ _ _ _ a V x).symm
    _ = (lift b).val.app V x := congrArg (fun k ↦ k.val.app V x) he
    _ = b.val.app V x :=
      SheafOfModules.IntegralScalarProof.liftMap_apply _ _ _ _ _ _ b V x

private theorem pullReduction_hom_ext {X Y : Scheme.{t}} (f : X ⟶ Y)
    (m n : ℕ) (q : integralCoefficientSheaf l E X m ⟶ integralCoefficientSheaf l E X n)
    (hq : integralCompletedProjection l E X m ≫ q = integralCompletedProjection l E X n)
    (M : integralTowerModules l E Y) (N : integralOperationsFiniteModules l E X n)
    (a b : (integralCompletedRestrict l E X m).obj
        ((unrestrictedIntegralReductionFunctor l E X m).obj ((pull l E f).obj M)) ⟶
      (integralCompletedRestrict l E X n).obj N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      a.val.app (op ((proEtaleBaseChange f).obj V))
        (unrestrictedIntegralTensorSection l E X m ((pull l E f).obj M)
          (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f M V x)) =
      b.val.app (op ((proEtaleBaseChange f).obj V))
        (unrestrictedIntegralTensorSection l E X m ((pull l E f).obj M)
          (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f M V x))) : a = b := by
  haveI : Presheaf.IsLocallySurjective (ProEt.topology X)
      (integralCompletedProjection l E X m).hom := by
    with_unfolding_all exact completedProjection_locallySurjective l E X m
  apply adjointReduction_hom_ext (proEtaleBaseChange f)
    (integralCompletedProjection l E X m) (integralCompletedProjection l E X n) q hq
    (ambientDirectRingMap l E f) (adjunction l E f) (reductionAdj l E X m) M N a b
  intro V x
  have hx := reductionAdj_unit l E X m ((pull l E f).obj M)
    ((proEtaleBaseChange f).op.obj V) (((adjunction l E f).unit.app M).val.app V x)
  have ha := congrArg (a.val.app ((proEtaleBaseChange f).op.obj V)) hx
  have hb := congrArg (b.val.app ((proEtaleBaseChange f).op.obj V)) hx
  with_unfolding_all exact ha.trans ((h V.unop x).trans hb.symm)

private theorem finitePullComparison_generator {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((proEtaleBaseChange f).obj V))) (x : M.val.obj (op V)) :
    ((finitePullComparison l E f n).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (unrestrictedIntegralTensorSection l E X n ((pull l E f).obj M)
        (op ((proEtaleBaseChange f).obj V)) a (pullGenerator l E f M V x)) =
      a • (show ((integralOperationsLevelPullback l E f n).obj
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M)).val.obj
          (op ((proEtaleBaseChange f).obj V)) from
        finiteGenerator l E f n
          ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
            (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)) := by
  have hs := identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (unrestrictedIntegralReductionFunctor l E X n) (unrestrictedReduction_obj l E X n)
    ((pull l E f).obj M) (op ((proEtaleBaseChange f).obj V)) a
    (pullGenerator l E f M V x)
  change unrestrictedIntegralTensorSection l E X n ((pull l E f).obj M)
      (op ((proEtaleBaseChange f).obj V)) a (pullGenerator l E f M V x) =
    a • unrestrictedIntegralTensorSection l E X n ((pull l E f).obj M)
      (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f M V x) at hs
  rw [hs, map_smul, finitePullComparison_unit]

@[irreducible] private def pullLevelComparison {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    pullComplex l E f ⋙ unrestrictedIntegralComplexFunctor l E X n ≅
      integralOperationsPullbackLevel l E f n := by
  letI := integralOperationsLevelPullback_additive l E f n
  exact Functor.isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (finitePullComparison l E f n) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (unrestrictedIntegralReductionFunctor l E Y n ⋙
          integralOperationsLevelPullback l E f n)) (.up ℤ)).symm)
    (integralOperationsRestrict l E X n)

private theorem pullLevelComparison_unit {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)) :
    (((pullLevelComparison l E f n).hom.app P).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
      (unrestrictedIntegralTensorSection l E X n ((pull l E f).obj (P.X i))
        (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f (P.X i) V x)) =
      finiteGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  unfold pullLevelComparison
  with_unfolding_all exact finitePullComparison_unit l E f n (P.X i) V x

private theorem pullLevelComparison_transition {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    Functor.whiskerLeft (pullComplex l E f) (unrestrictedIntegralTransition l E X n) ≫
        (pullLevelComparison l E f n).hom =
      (pullLevelComparison l E f (n + 1)).hom ≫
        integralOperationsPullbackTransition l E f n := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply pullReduction_hom_ext l E f (n + 1) n
    (integralCoefficientSheafTransition l E X n) (integralProjection_step l E X n)
    (P.X i) ((integralOperationsLevelPullback l E f n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj (P.X i)))
  intro V x
  change (((pullLevelComparison l E f n).hom.app P).f i).val.app _
      ((((unrestrictedIntegralTransition l E X n).app ((pullComplex l E f).obj P)).f i).val.app _
        (unrestrictedIntegralTensorSection l E X (n + 1) ((pull l E f).obj (P.X i))
          (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f (P.X i) V x))) =
    (((integralOperationsPullbackTransition l E f n).app P).f i).val.app _
      ((((pullLevelComparison l E f (n + 1)).hom.app P).f i).val.app _
        (unrestrictedIntegralTensorSection l E X (n + 1) ((pull l E f).obj (P.X i))
          (op ((proEtaleBaseChange f).obj V)) 1 (pullGenerator l E f (P.X i) V x)))
  have hx := (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec
    ((pullComplex l E f).obj P) i (op ((proEtaleBaseChange f).obj V)) 1
      (pullGenerator l E f (P.X i) V x)
  have hy := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
    P i (op V) 1 x
  simp only [map_one] at hx hy
  have ht := (integralOperationsPullbackTransition_existsUnique l E f n).exists.choose_spec
    P i V (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) 1 x)
  have hl := congrArg
    ((((pullLevelComparison l E f n).hom.app P).f i).val.app
      (op ((proEtaleBaseChange f).obj V))) hx
  have hr := congrArg
    ((((integralOperationsPullbackTransition l E f n).app P).f i).val.app
      (op ((proEtaleBaseChange f).obj V)))
    (pullLevelComparison_unit l E f (n + 1) P i V x)
  have hy' := congrArg (fun z ↦ finiteGenerator l E f n
    (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V z) hy
  with_unfolding_all exact ((hl.trans (pullLevelComparison_unit l E f n P i V x)).trans
    ((hr.trans ht).trans hy').symm)

/-- The normalized scalar-association isomorphism of whole strict pullback towers.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-normalized-integral-pullback-tower).
Proof: the coefficient square commutes by coefficientMap's projections. In degree i
send (r tensor x) tensor a to pi_n(r)a tensor (x tensor 1); the inverse sends
 a tensor (x tensor b) to (1 tensor x) tensor a c_n(b). Balancing proves both
composites are identities. The maps commute with differentials and chain maps.
Reduction of a gives the same formula on both paths of every quotient transition.
This determines the unique natural strict tower isomorphism. -/
theorem pullTowerModel {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! b : pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((Scheme.proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)),
        (((b.hom.app P).app (op n)).f i).val.app
            (op ((Scheme.proEtaleBaseChange f).obj V))
          (IntegralOnSlice.generator l E X none n ((pull l E f).obj (P.X i))
            (op ((Scheme.proEtaleBaseChange f).obj V)) a (pullSection l E f (P.X i) V x)) =
          finitePullSection l E f n P i V a x := by
  classical
  let α (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      ((pullComplex l E f ⋙
        (Functor.ofOpSequence (unrestrictedIntegralTransition l E X)).flip).obj P) ⟶
          (integralOperationsPullbackTowerFunctor l E f).obj P :=
    NatTrans.ofOpSequence (fun n ↦ (pullLevelComparison l E f n).hom.app P) (by
      intro n
      have h := congrArg (fun a ↦ a.app P) (pullLevelComparison_transition l E f n)
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
        Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ,
        integralOperationsPullbackTowerFunctor] using h)
  have hα (P) : IsIso (α P) := by
    have hn (n : ℕᵒᵖ) : IsIso ((α P).app n) := by
      change IsIso ((pullLevelComparison l E f n.unop).hom.app P)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let d₀ : pullComplex l E f ⋙
      (Functor.ofOpSequence (unrestrictedIntegralTransition l E X)).flip ≅
        integralOperationsPullbackTowerFunctor l E f :=
    NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (α P) (hα P)) (by
      intro P Q g
      apply NatTrans.ext
      funext n
      exact (pullLevelComparison l E f n.unop).hom.naturality g)
  let d : pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f :=
    Functor.isoWhiskerLeft (pullComplex l E f)
      (eqToIso (IntegralOnSlice.globalTower_eq l E X)) ≪≫ d₀
  have hd (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
      (V : Y.ProEt) (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
        (op ((proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)) :
      (((d.hom.app P).app (op n)).f i).val.app
          (op ((proEtaleBaseChange f).obj V))
        (IntegralOnSlice.generator l E X none n ((pull l E f).obj (P.X i))
          (op ((proEtaleBaseChange f).obj V)) a (pullSection l E f (P.X i) V x)) =
        finitePullSection l E f n P i V a x := by
    change (((pullLevelComparison l E f n).hom.app P).f i).val.app _
      (unrestrictedIntegralTensorSection l E X n ((pull l E f).obj (P.X i))
        (op ((proEtaleBaseChange f).obj V)) a (pullSection l E f (P.X i) V x)) = _
    unfold pullLevelComparison
    with_unfolding_all exact finitePullComparison_generator l E f n (P.X i) V a x
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  apply pullReduction_hom_ext l E f n.unop n.unop (𝟙 _) (Category.comp_id _)
    (P.X i) ((integralOperationsLevelPullback l E f n.unop).obj
      ((unrestrictedIntegralReductionFunctor l E Y n.unop).obj (P.X i)))
  intro V x
  with_unfolding_all exact (hd' P n.unop i V 1 x).trans (hd P n.unop i V 1 x).symm

end WeilConjectures.IntegralAmbient
