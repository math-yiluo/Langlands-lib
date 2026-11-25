/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceSectionsLimit
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.SixFunctors.CoefficientSectionsCoreComparison.NormalizedSectionsLimitComparison

/-! Transported data for the normalized coefficient-sections core.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941.
(blueprint: lem-coef-derived-sections-core-data)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

/-- A section of a restricted module is the same as a section over the quotient ring:
`f` is sent to the morphism `b ↦ b • f 1`. -/
private noncomputable def ordinaryScalarSectionsEquiv (n : ℕ)
    (M : scalarReductionTarget l E W n) :
    (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat RingCat)).obj (completedIntegralCommRingSheafUnrestricted l E W)) ⟶
      (scalarReductionRestriction l E W n).obj M) ≃+
    (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat RingCat)).obj (integralCoefficientCommRingSheaf l E W n)) ⟶ M) where
  toEquiv := ((scalarReductionRestriction l E W n).obj M).unitHomEquiv.trans M.unitHomEquiv.symm
  map_add' f g := by
    ext V
    let o : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj V := 1
    let i : (integralCoefficientSheaf l E W n).obj.obj V := 1
    change i • (@id (M.val.obj V) ((f + g).val.app V o)) =
      i • (@id (M.val.obj V) (f.val.app V o)) + i • (@id (M.val.obj V) (g.val.app V o))
    simp only [i, one_smul]
    rfl

/-- Ordinary global sections commute with restriction of scalars to the quotient ring.
Source: Stacks 03CZ, 08JA. -/
private noncomputable def ordinaryScalarSectionsIso (n : ℕ) :
    scalarReductionRestriction l E W n ⋙
      coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) :=
  NatIso.ofComponents (fun M ↦ (ordinaryScalarSectionsEquiv l E W n M).toAddCommGrpIso) (by
    intro M N p
    ext f
    change N.unitHomEquiv.symm (((scalarReductionRestriction l E W n).obj N).unitHomEquiv
        (f ≫ (scalarReductionRestriction l E W n).map p)) =
      M.unitHomEquiv.symm (((scalarReductionRestriction l E W n).obj M).unitHomEquiv f) ≫ p
    rw [SheafOfModules.unitHomEquiv_symm_comp]
    rfl)

/-- Evaluation of a global section at the unit, as a cone over the underlying abelian
presheaf of a completed-coefficient module. -/
private noncomputable def sectionsCone (M : scalarReductionSource l E W) :
    Cone ((sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t+1)}).obj
      ((SheafOfModules.toSheaf _).obj M)) where
  pt := (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj M
  π :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ (M.unitHomEquiv f).val V
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun V V' g ↦ by
        ext f
        exact ((M.unitHomEquiv f).property g).symm }

/-- Global sections of a module are the limit of its underlying abelian presheaf. -/
private theorem sectionsCone_isIso (M : scalarReductionSource l E W) :
    IsIso (limit.lift _ (sectionsCone l E W M)) := by
  let P := (sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t+1)}).obj
    ((SheafOfModules.toSheaf _).obj M)
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro f g h
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro V
    have := congrArg (limit.π P V) h
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] at this
    exact this
  · intro x
    refine ⟨M.unitHomEquiv.symm (M.val.sectionsMk (fun V ↦ limit.π P V x) ?_), ?_⟩
    · intro V V' g
      exact (limit.w_apply P g x)
    · apply Concrete.limit_ext
      intro V
      rw [← ConcreteCategory.comp_apply, limit.lift_π]
      change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val V = _
      rw [Equiv.apply_symm_apply]
      rfl

/-- Global sections agree naturally with the limit of the underlying abelian presheaf. -/
private noncomputable def sectionsLimIso :
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
      SheafOfModules.toSheaf _ ⋙
        sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t+1)} ⋙ lim :=
  NatIso.ofComponents (fun M ↦
    have := sectionsCone_isIso l E W M
    asIso (limit.lift _ (sectionsCone l E W M))) (by
    intro M N p
    apply limit.hom_ext
    intro V
    ext f
    simp only [asIso_hom, Category.assoc, limit.lift_π, Functor.comp_map, lim_map,
      limMap_π, limit.lift_π_assoc]
    rfl)

open SheafOfModules in
/-- Restricted K-injective complexes compute derived global sections over the completed ring.
Source: Stacks 0D6E, through `coefficientRestrictionSections_quasiIso`. -/
private theorem restrictedSectionsUnit_isIso (n : ℕ)
    (I : CochainComplex (scalarReductionTarget l E W n) ℤ) (hI : I.IsKInjective) :
    letI : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
      (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
        (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
    IsIso ((coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).rightDerivedFunctorUnitQ
      (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I)) := by
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : EssentiallySmall.{max u (t+1)} W.ProEt := essentiallySmallSelf _
  let Γ := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  obtain ⟨K, hK, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I)
  have hq := SheafOfModules.coefficientRestrictionSections_quasiIso
    (completedIntegralCommRingProjectionUnrestricted l E W n) I K j
  have : (SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat RingCat)).obj (completedIntegralCommRingSheafUnrestricted l E W)) ⋙
      sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t+1)} ⋙
        lim).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hq' : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map j) :=
    SheafOfModules.quasiIso_map_iso _ Γ (sectionsLimIso l E W).symm j
  have hK' : IsIso (Γ.rightDerivedFunctorUnitQ K) := by
    rw [Γ.rightDerivedFunctorUnitQ_eq K]
    infer_instance
  have h := Γ.rightDerivedFunctorUnitQ_naturality j
  have : IsIso (Γ.rightDerivedFunctorUnitQ
      (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj I) ≫
        Γ.rightDerivedFunctor.map (DerivedCategory.Q.map j)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Γ.rightDerivedFunctor.map (DerivedCategory.Q.map j))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Derived global sections commute with restriction of scalars to a quotient level,
compatibly with the ordinary comparison on all complexes.
Source: Stacks 079P, 08JA, 0D6E. Both composites are right derived functors of
ordinary sections, the first since restricted K-injectives are sections-acyclic;
right-derived uniqueness gives the comparison with its unit equation. -/
private theorem scalarSectionsDerived (n : ℕ) :
    ∃ σ : coefficientFiniteDerivedRestriction l E W n ⋙ coefficientIntegralSections l E W ≅
        coefficientFiniteSections l E W n,
      ∀ I : CochainComplex (scalarReductionTarget l E W n) ℤ,
        let G : scalarReductionTarget l E W n ⥤ AddCommGrpCat.{max u (t+1)} :=
          coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)
        let : G.PreservesZeroMorphisms := by
          let : G.Additive := CategoryTheory.additive_coyonedaObj' _
          exact Functor.preservesZeroMorphisms_of_additive G
        CoefficientComparisonEquation
          (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)
            (((scalarReductionRestriction l E W n).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))
          ((coefficientIntegralSections l E W).map
            ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I))
          (σ.hom.app (DerivedCategory.Q.obj I))
          (DerivedCategory.Q.map
            (coefficientComplexCompositeSourceTransformation
              (scalarReductionRestriction l E W n)
              (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
                (completedIntegralCommRingSheafUnrestricted l E W))
              (H := G) (ordinaryScalarSectionsIso l E W n).hom I))
          (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n) I) := by
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionTarget l E W n) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)).1
  let Γc := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let Γn : scalarReductionTarget l E W n ⥤ AddCommGrpCat.{max u (t+1)} :=
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
  have : Γn.Additive := CategoryTheory.additive_coyonedaObj' _
  let T := scalarReductionRestriction l E W n
  let P := CoefficientSectionsCoreComparison.standardPair Γc
  let A := SheafOfModules.sectionsExactComposite T Γc P
    (fun I hI ↦ restrictedSectionsUnit_isIso l E W n I hI)
  let B := CoefficientSectionsCoreComparison.standardPair Γn
  have := A.universal
  have := B.universal
  let τ₀ : T ⋙ Γc ≅ Γn := ordinaryScalarSectionsIso l E W n
  let τ := Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex τ₀ (.up ℤ)) DerivedCategory.Q
  let κ := Functor.rightDerivedNatIso _ _ A.unit B.unit
    (HomologicalComplex.quasiIso (scalarReductionTarget l E W n) (.up ℤ)) τ
  refine ⟨κ, fun I ↦ ?_⟩
  have h := Functor.rightDerivedNatTrans_app _ _ A.unit B.unit
    (HomologicalComplex.quasiIso (scalarReductionTarget l E W n) (.up ℤ)) τ.hom I
  unfold CoefficientComparisonEquation
  exact (Category.assoc _ _ _).symm.trans h

open SheafOfModules in
private theorem scalarSectionsCoherenceExists :
    Nonempty (CoefficientDerivedSystemScalarCoherence l E W) := by
  choose s hs using scalarSectionsDerived l E W
  let D : CoefficientDerivedSystemScalarData l E W :=
    { scalarSections := s
      ordinaryScalarSections := ordinaryScalarSectionsIso l E W }
  refine ⟨{ toCoefficientDerivedSystemScalarData := D
            ordinaryScalarSections_formula := ?_
            scalarSections_model := ?_ }⟩
  · unfold CoefficientOrdinaryScalarSectionsFormula
    intro n M f V b
    rfl
  · unfold CoefficientScalarSectionsModel
    intro n I
    exact hs n I

open SheafOfModules in
private theorem totalSectionsLimitExists :
    Nonempty (coefficientConstantTowerLimit l E W ⋙ coefficientIntegralSections l E W ≅
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t+1)}) := by
  let A := scalarReductionSource l E W
  let F := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let : IsGrothendieckAbelian.{max u (t+1)} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : PreservesLimits F := CategoryTheory.preservesLimits_preadditiveCoyoneda_obj _
  let : PreservesLimitsOfSize.{0, 0} F := preservesLimitsOfSize_shrink F
  exact ⟨(CoefficientSectionsCoreComparison.comparison_exists F).choose⟩

/-- The scalar, finite-evaluation and total-limit data before their two equations.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941; transport through the coefficient
sequence equivalence.
Proof: choose normalized derived sections for the completed coefficient ring and its
quotient tower, transport their scalar and evaluation comparisons through the exact
sequence-site restriction, and transport the ordinary and derived limit comparisons
through the same equivalence. The resulting three fields have exactly the displayed
endpoints.
(blueprint: lem-coef-derived-sections-core-data) -/
structure CoefficientDerivedSectionsCoreData
    (R : CoefficientDerivedSystemReduction l E W) where
  scalar : CoefficientDerivedSystemScalarCoherence l E W
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t + 1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteSections l E W n
  globalLimit : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t + 1)}

open SheafOfModules in
/-- The transported scalar/evaluation/limit data exist under finite tensor normalization.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941; extracted construction step of the
normalized coefficient-sections package.
(blueprint: lem-coef-derived-sections-core-data) -/
theorem coefficientDerivedSectionsCoreData
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    Nonempty (CoefficientDerivedSectionsCoreData l E W R) := by
  have _ := hF
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  obtain ⟨D⟩ := scalarSectionsCoherenceExists l E W
  let F := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let P := CoefficientSectionsCoreComparison.standardPair F
  let T := CoefficientSectionsCoreComparison.standardPair (coefficientTowerSections l E W)
  have enough (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (a : K ⟶ I),
        I.IsKInjective ∧ QuasiIso a := by
    obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, ha⟩
  obtain ⟨β, _⟩ := SheafOfModules.coefficientTowerComparison F P T enough
  obtain ⟨κ⟩ := totalSectionsLimitExists l E W
  refine ⟨{ scalar := D
            systemSectionsEvaluation := fun n ↦ ?_
            globalLimit := Functor.isoWhiskerLeft
              (coefficientSequenceDerivedRestriction l E W) κ }⟩
  exact Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E W) (β (op n)) ≪≫
    Functor.isoWhiskerRight (coefficientRestrictedEvaluationIso l E W n)
      (coefficientIntegralSections l E W) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E W n) (D.scalarSections n)

end WeilConjectures
