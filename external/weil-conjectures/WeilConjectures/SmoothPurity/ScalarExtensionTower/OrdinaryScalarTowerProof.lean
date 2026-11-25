/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import all WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationTensorCoordinates

/-! # Ordinary quotient scalar tower helpers

Section casts, finite comparisons, the assembled scalar tower comparison, its
normalization and fixed scalar models for the ordinary quotient scalar
extension. These private helpers are used, via `import all`, by the ordinary
scalar/pullback calculations.

Source: Stacks 03EK, 03D7, 06YY and 0941, balanced tensor association.
-/

-- All declarations here are private helpers, used by importers via `import all`.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

section OrdinaryQuotientScalarSectionCasts

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem evaluation_section_heq {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    HEq (coefficientEvaluationSection l E X N n U x) x := by rfl

private theorem evaluation_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E X n).map g).val.app U)
      (coefficientEvaluationSection l E X N n U x) =
    coefficientEvaluationSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := rfl

private theorem eqToHom_section {C : Type v} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {N N' : SheafOfModules.{u} R} (h : N = N') (U : Cᵒᵖ) (x : N.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst N'
  rfl

private theorem restrictionEvaluation_section {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app N).hom.val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
        coefficientEvaluationSection l E X N n U x := by
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app]
  apply eq_of_heq
  have h := eqToHom_section
    (congrArg (fun F ↦ F.obj N) (coefficientSequenceRestriction_evaluation l E X n))
    U (integralComparisonRestrictedSection l E X N n U x)
  have hc : HEq (integralComparisonRestrictedSection l E X N n U x) x :=
    cast_heq (integralComparisonRestrictedSectionType l E X N n U).symm x
  exact (h.trans hc).trans (evaluation_section_heq l E N n U x).symm

private theorem cast_map {A A' B B' : Type v} (hA : A = A') (hB : B = B')
    (f : A → B) (g : A' → B') (h : HEq f g) (x : A') :
    f (cast hA.symm x) = cast hB.symm (g x) := by
  cases hA
  cases hB
  exact congrFun (eq_of_heq h) x

private theorem restriction_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
    integralComparisonRestrictedSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := by
  have h : HEq (fun y ↦
      ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U) y)
      (fun y : N.val.obj (op (n, U.unop)) ↦ g.val.app (op (n, U.unop)) y) := by
    unfold coefficientSequenceRestriction
    exact (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 g n U
  exact cast_map (integralComparisonRestrictedSectionType l E X N n U)
    (integralComparisonRestrictedSectionType l E X N' n U) _ _ h x

private theorem eqToHom_ab_heq {A B : AddCommGrpCat.{v}} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst B
  rfl

private theorem sequenceSection_heq (N : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq (integralComparisonSequenceSection l E W N n U x) x :=
  eqToHom_ab_heq (coefficientSequenceEvaluationAb_eq l E W N n U) x


end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarSectionCasts

section OrdinaryQuotientScalarSections

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem finiteUnit_eq (K : scalarReductionSource l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    CoefficientExtensionAssociation.finiteUnitSection l E W K n U x =
      unrestrictedIntegralTensorSection l E W n K U 1 x := by
  unfold CoefficientExtensionAssociation.finiteUnitSection
    CoefficientExtensionAssociation.normalizedUnitSection
    CoefficientExtensionAssociation.quotientAdjunction
  exact (scalarReductionExtension_adjunction l E W n).choose_spec K U x

/-- The presentation inverse takes the kappa-inverse unit section to M's quotient unit.
Source: Stacks 03D7, naturality and normalization of the ordinary quotient unit.
(blueprint: lem-trf-ordinary-quotient-scalar-presentation-unit).
Proof: invert the presentation comparison equation, evaluate at degree i and
apply it to 1 tensor x. Evaluation commutes with the presentation inverse, and
its section casts are HEq to identity. The normalized quotient-adjunction unit
identifies the finite unit section with 1 tensor x, giving the stated formula. -/
private theorem presentationUnit
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj P ≅ C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (hκ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    (a.inv.f i).val.app (op (n, U.unop))
      (integralComparisonSequenceSection l E W (C.X i) n U
        (((κ n).inv.f i).val.app U
          (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))) =
      CoefficientExtensionAssociation.quotientUnitSection l E W M (P.X i) n U x := by
  let z := unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x
  let w := integralComparisonSequenceSection l E W (C.X i) n U
    (((κ n).inv.f i).val.app U z)
  have hi := congrArg (fun b ↦ b.inv.f i) (hκ n)
  simp only [Iso.trans_inv, HomologicalComplex.comp_f, Functor.mapIso_inv,
    Functor.mapHomologicalComplex_map_f] at hi
  have hx := congrArg (fun b ↦ b.val.app U z) hi
  have hw : coefficientEvaluationSection l E W (C.X i) n U w =
      ((κ n).inv.f i).val.app U z :=
    eq_of_heq ((evaluation_section_heq l E (C.X i) n U w).trans
      (sequenceSection_heq l E W (C.X i) n U _))
  have hm := evaluation_map_section l E (a.inv.f i) n U w
  rw [hw] at hm
  change ((coefficientSequenceEvaluation l E W n).map (a.inv.f i)).val.app U
      (((κ n).inv.f i).val.app U z) =
    ((M.evaluation n).inv.app (P.X i)).val.app U z at hx
  rw [hx] at hm
  have he := evaluation_section_heq l E (M.tensor.obj (P.X i)) n U
    ((a.inv.f i).val.app (op (n, U.unop)) w)
  unfold CoefficientExtensionAssociation.quotientUnitSection
  rw [finiteUnit_eq l E W]
  exact eq_of_heq (he.symm.trans (heq_of_eq hm.symm))

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarSections

section OrdinaryQuotientScalarTowerLevels

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

private def finiteComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (n : ℕ) :
    M.tensor ⋙ A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n :=
  Functor.isoWhiskerLeft M.tensor (ρ n) ≪≫
    Functor.isoWhiskerRight (C := scalarReductionSource l E W)
      (D := normalizedDVRModules l E W n) (E := normalizedDVRModules l L W n)
      (M.evaluation n) (A.levels n).model.E ≪≫ association n

private def direct (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W) :
    CochainComplex (scalarReductionSource l E W) ℤ ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ :=
  M.quotient l E W ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)

private def directEvaluation
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (n : ℕ) :
    direct l E L ι W A M ⋙
      (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        integralScalarFiniteComplex l E L ι W n :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (finiteComparison l E L ι W A M ρ association n).app (P.X i)) (by
      intro i j hij
      exact ((finiteComparison l E L ι W A M ρ association n).hom.naturality
        (P.d i j)).symm)) (by
    intro P Q f
    apply HomologicalComplex.hom_ext
    intro i
    exact (finiteComparison l E L ι W A M ρ association n).hom.naturality (f.f i))

private theorem directEvaluation_hom_f
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ) :
    ((directEvaluation l E L ι W A M ρ association n).hom.app P).f i =
      (finiteComparison l E L ι W A M ρ association n).hom.app (P.X i) := rfl

private theorem directTransition
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj
      (((direct l E L ι W A M).obj P).X i)).val.obj U) :
    HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
      (((direct l E L ι W A M).obj P).X i)).val.app U x)
      ((((directEvaluation l E L ι W A M ρ association n).inv.app P).f i).val.app U
        ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
          ((((directEvaluation l E L ι W A M ρ association (n + 1)).hom.app P).f i).val.app U
            x))) := by
  exact coefficientExtensionAssociation_successor l E L ι W A M ρ hρ
    association hassociation P n i U x

attribute [local irreducible] SemilinearSections.systemMap
  CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

private theorem coefficientEvaluation_smul
    (N : coefficientSequenceModules l L W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U)
    (x : N.val.obj (op (n, U.unop))) :
    s • (show ((coefficientSequenceEvaluation l L W n).obj N).val.obj U from x) =
      (s • x : N.val.obj (op (n, U.unop))) := by
  change ((eqToHom (coefficientSequenceEvaluationRing_eq l L W n).symm).hom.app U).hom s • x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private theorem evaluatedUnit_raw_eq
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ N n U x =
      (show ((coefficientSequenceEvaluation l L W n).obj
        (A.scalar.model.E.obj N)).val.obj U from
          (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x) := by
  exact eq_of_heq (CoefficientExtensionAssociation.evaluatedUnitSection_raw
    l E L ι W A ρ hρ N n U x)

private theorem evaluatedUnit_smul_raw
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq
      (s • (show (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) from
        (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x))
      (s • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ N n U x) := by
  have hr' := evaluatedUnit_raw_eq l E L ι W A ρ hρ N n U x
  have hs := coefficientEvaluation_smul l L W (A.scalar.model.E.obj N) n U s
    (show (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) from
      (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x)
  have hm := congrArg (fun z :
    ((coefficientSequenceEvaluation l L W n).obj (A.scalar.model.E.obj N)).val.obj U ↦
      s • z) hr'.symm
  have hh := hs.symm.trans hm
  exact heq_of_eq hh

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarTowerLevels

section OrdinaryQuotientScalarTowerConstruction

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

attribute [local irreducible] direct directEvaluation finiteComparison

/-- Assemble the explicit finite balanced comparisons into an all-complex tower.
Source: Stacks 03D7, 03EK, and successor compatibility on the sequence site.
(blueprint: lem-trf-ordinary-quotient-scalar-tower-construction).
Proof: restriction-evaluation followed by the finite comparison defines each level.
The given successor identity proves their naturality along adjacent arrows; the
opposite-sequence construction extends this to all arrows. Pointwise inverses
and naturality in the complex give the natural isomorphism and component formula. -/
private theorem comparison_exists
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    :
    let direct := direct l E L ι W A M
    let directEvaluation := directEvaluation l E L ι W A M ρ association
    ∃ e : direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ),
        (e.hom.app P).app (op n) =
          (coefficientRestrictedComplexEvaluation l L W n).hom.app (direct.obj P) ≫
            ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
              ((directEvaluation n).hom.app P) := by
  classical
  let direct := direct l E L ι W A M
  let directEvaluation := directEvaluation l E L ι W A M ρ association
  have htransition := directTransition l E L ι W A M ρ hρ association hassociation
  let H := direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)
  let a (n : ℕ) : H ⋙
      ((evaluation ℕᵒᵖ (scalarReductionSource l L W)).obj (op n)).mapHomologicalComplex
        (.up ℤ) ≅ integralScalarLevel l E L ι W n :=
    Functor.isoWhiskerLeft direct (coefficientRestrictedComplexEvaluation l L W n) ≪≫
      Functor.isoWhiskerRight (directEvaluation n)
        ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ))
  have ha (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
      (H.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ (a n).hom.app P =
        (a (n + 1)).hom.app P ≫ (integralScalarTransition l E L ι W n).app P := by
    apply (cancel_mono ((a n).inv.app P)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    have hobj (k : ℕ) := congrArg (fun F ↦ F.obj ((direct.obj P).X i))
      (coefficientSequenceRestriction_evaluation l L W k)
    have hs (k : ℕ) :
        ((scalarReductionRestriction l L W k).obj
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i))).val.presheaf.obj V =
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i)).val.presheaf.obj V :=
      restrictScalars_presheaf_obj _ _ _
    let y : ((coefficientSequenceEvaluation l L W (n + 1)).obj
        ((direct.obj P).X i)).val.obj V :=
      cast (congrArg (fun G : AddCommGrpCat ↦ ↥G)
        ((congrArg (fun M : scalarReductionSource l L W ↦ M.val.presheaf.obj V)
          (hobj (n + 1))).trans (hs (n + 1)))) x
    have hy : HEq y x := by
      exact cast_heq _ x
    have hh := restriction_transition_apply_heq l L W ((direct.obj P).X i)
      (Nat.le_succ n) V x y hy.symm
    have ht := htransition P n i V y
    simp only [a, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Functor.mapHomologicalComplex_map_f,
      restrictedEvaluation_hom_f, restrictedEvaluation_inv_f]
    erw [Category.comp_id]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    apply eq_of_heq
    refine (hh.trans ht).trans ?_
    have hc0 := module_eqToHom_apply_heq l L W (hobj (n + 1)) V x
    have hc1 := restrictionMap_apply_heq l L W (n + 1)
      (((directEvaluation (n + 1)).hom.app P).f i) V _ y (hc0.trans hy.symm)
    have hc2 := hcongr_apply rfl
      (HEq.rfl (a := fun x ↦
        ((((integralScalarTransition l E L ι W n).app P).f i).val.app V) x)) hc1
    have hc3 := restrictionMap_apply_heq l L W n
      (((directEvaluation n).inv.app P).f i) V _ _ hc2
    have hc4 := module_eqToHom_apply_heq l L W (hobj n).symm V
      (((((scalarReductionRestriction l L W n).map
        (((directEvaluation n).inv.app P).f i)).val.app V))
          (((((integralScalarTransition l E L ι W n).app P).f i).val.app V)
            (((((scalarReductionRestriction l L W (n + 1)).map
              (((directEvaluation (n + 1)).hom.app P).f i)).val.app V))
                (((eqToHom (hobj (n + 1))).val.app V) x))))
    exact (hc4.trans hc3).symm
  let T := integralScalarTowerFunctor l E L ι W
  obtain ⟨e, he⟩ := assembleTowerIso H T a (fun P n ↦ by
    dsimp only [T, Functor.comp_obj, integralScalarTowerFunctor]
    erw [Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
    exact ha P n)
  refine ⟨e, ?_⟩
  intro P n
  rw [he]
  simp only [a, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rfl

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarTowerConstruction

section OrdinaryQuotientScalarNormalization

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
  SemilinearSections.systemMap CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] direct integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- The finite balanced comparison takes scalar multiples of quotient units to tensors.
Source: Stacks 03D7 and 03EK, the normalized balanced associator.
(blueprint: lem-trf-ordinary-quotient-scalar-tensor-normalization).
Proof: apply the forward comparison to its proved inverse-coordinate tensor
formula and cancel the inverse isomorphism. This calculation holds for every
completed module, scalar and section, with no flatness condition. -/
private theorem finiteComparison_unit
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
    coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : K.val.obj U) :
    ((finiteComparison l E L ι W A M ρ association n).hom.app K).val.app U
      (s • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ
        (M.tensor.obj K) n U
          (CoefficientExtensionAssociation.quotientUnitSection l E W M K n U x)) =
      integralScalarTensorSection l E L ι W n K U s x := by
  have h := CoefficientExtensionAssociation.association_inverse_tensor l E L ι W A M ρ
    association hassociation K n U s x
  exact (congrArg
    (fun y ↦ ((finiteComparison l E L ι W A M ρ association n).hom.app K).val.app U y)
    h.symm).trans
      (congrArg (fun f ↦ f.val.app U (integralScalarTensorSection l E L ι W n K U s x))
        ((finiteComparison l E L ι W A M ρ association n).app K).inv_hom_id)

private theorem comparison_section
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (e : ((direct l E L ι W A M) ⋙
        (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex).obj P ≅
      (integralScalarTowerFunctor l E L ι W).obj P)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (he : e.hom.app (op n) =
      (coefficientRestrictedComplexEvaluation l L W n).hom.app
        ((direct l E L ι W A M).obj P) ≫
      ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
        ((directEvaluation l E L ι W A M ρ association n).hom.app P))
    (y : (A.scalar.model.E.obj (M.tensor.obj (P.X i))).val.obj (op (n, U.unop)))
    (z : ((coefficientSequenceEvaluation l L W n).obj
      (A.scalar.model.E.obj (M.tensor.obj (P.X i)))).val.obj U)
    (hy : HEq y z) :
    ((e.hom.app (op n)).f i).val.app U
      (integralComparisonRestrictedSection l L W
        (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y) =
      ((finiteComparison l E L ι W A M ρ association n).hom.app (P.X i)).val.app U z := by
  rw [he]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    restrictedEvaluation_hom_f, directEvaluation_hom_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have ht : HEq
      ((((eqToIso (coefficientSequenceRestriction_evaluation l L W n)).app
        (A.scalar.model.E.obj (M.tensor.obj (P.X i))))).hom.val.app U
          (integralComparisonRestrictedSection l L W
            (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y)) z :=
    (heq_of_eq (restrictionEvaluation_section l L
      (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y)).trans
        ((evaluation_section_heq l L
          (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y).trans hy)
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app] at ht
  exact eq_of_heq (restrictionMap_apply_heq l L W n
    ((finiteComparison l E L ι W A M ρ association n).hom.app (P.X i)) U _ z ht)

private theorem normalizedComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (F : coefficientSequenceModules l E W ⥤ coefficientSequenceModules l L W)
    [F.Additive] (hF : A.scalar.model.E = F) :
    let T := F.mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E W ⋙ T ≅ integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
        (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (a : (M.quotient l E W).obj P ≅ C)
        (κ : ∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
            (unrestrictedIntegralFiniteComplex l E W n).obj P),
        (∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
            κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
        ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
          (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
          (x : (P.X i).val.obj U)
          (y : (F.obj (C.X i)).val.obj (op (n, U.unop))),
          HEq y (s • (show (A.scalar.model.E.obj (C.X i)).val.obj (op (n, U.unop)) from
            (A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop))
              (integralComparisonSequenceSection l E W (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))) →
          (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l L W (F.obj (C.X i)) n U y) =
            integralScalarTensorSection l E L ι W n (P.X i) U s x := by
  subst F
  dsimp only
  obtain ⟨θ, hθ⟩ := comparison_exists l E L ι W A M ρ hρ association hassociation
  refine ⟨θ, ?_⟩
  intro P C a κ hκ n i U s x y hy
  let w := integralComparisonSequenceSection l E W (C.X i) n U
    (((κ n).inv.f i).val.app U
      (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))
  have hp := presentationUnit l E W M P C a κ hκ n i U x
  have hn := congrArg (fun f ↦ f.val.app (op (n, U.unop)) w)
    (A.scalar.ordinaryAdjunction.unit.naturality (a.inv.f i))
  have hy' := eq_of_heq hy
  subst y
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapIso_hom,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [restriction_map_section l L
    (A.scalar.model.E.map (a.inv.f i)) n U]
  change (A.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (P.X i))).val.app
      (op (n, U.unop)) ((a.inv.f i).val.app (op (n, U.unop)) w) =
    (A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop))
      ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop)) w) at hn
  rw [hp] at hn
  dsimp only [w] at hn
  erw [map_smul, ← hn]
  have hu := evaluatedUnit_smul_raw l E L ι W A ρ hρ (M.tensor.obj (P.X i)) n U s
    (CoefficientExtensionAssociation.quotientUnitSection l E W M (P.X i) n U x)
  exact (comparison_section l E L ι W A M ρ association P (θ.app P) n i U
    (hθ P n) _ _ hu).trans
      (finiteComparison_unit l E L ι W A M ρ association hassociation (P.X i) n U s x)

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarNormalization

section OrdinaryQuotientScalarModels

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof

private theorem fixedScalarData
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} φ) :
    ∃ A : SemilinearSections.ScalarData.{c, v, max c v r} φ, A.model = D := by
  obtain ⟨A, hA⟩ := SequenceScalarConstruction.scalarPackageExists φ D
  refine ⟨{ model := A.model
            ordinaryAdjunction := A.ordinaryAdj
            unit_section := ?_
            adjunction := A.adjunction
            transpose_model := ?_ }, hA⟩
  · intro M U x
    rw [A.unit_normalized]
    dsimp only [SheafOfModules.systemModelTmul]
    rw [one_smul]
    have hh : eqToHom (A.model.obj_eq M).symm ≫ eqToHom (A.model.obj_eq M) =
        𝟙 _ := by simp
    exact congrArg (fun f ↦ f.val.app U
      (SemilinearSections.extensionUnit.{c, v, max c v r} φ M U x)) hh
  · intro P Q _ f
    rw [A.transpose]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _

private theorem transportModel_E
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
    {φ ψ : R ⟶ S} (h : φ = ψ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} φ) :
    (h ▸ D).E = D.E := by
  subst ψ
  rfl

private theorem transportModel_heq
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
    {φ ψ : R ⟶ S} (h : φ = ψ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} φ) :
    HEq (h ▸ D) D := by
  subst ψ
  rfl

private theorem modelTensor_unit
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
    {φ ψ : R ⟶ S} (hφ : φ = ψ)
    (A : SemilinearSections.ScalarData.{c, v, max c v r} φ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} ψ)
    (hD : HEq A.model D)
    (N : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : N.val.obj U) :
    HEq (SheafOfModules.systemModelTmul D N U s x)
      (s • (show (A.model.E.obj N).val.obj U from
        (A.ordinaryAdjunction.unit.app N).val.app U x)) := by
  subst ψ
  have hh : A.model = D := eq_of_heq hD
  subst D
  apply heq_of_eq
  change s • SemilinearSections.scalarExtensionSection.{c, v, r} φ A N U x = _
  rw [scalarSection_eq_unit.{c, v, r}]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  integralComparisonSequenceScalarModel

private theorem scalarMap_eq :
    SemilinearSections.systemMap.{t + 1, t, max (t + 1) u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W) =
    integralComparisonSequenceScalarMap l E L ι W := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact (SemilinearSections.systemMap_existsUnique.{t + 1, t, max (t + 1) u}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)).exists.choose_spec
      U.unop.1 (op U.unop.2)

/-- Scalar systems whose sequence model is the prescribed actual cochain model.
Source: Stacks 03D7 and 03EK.
(blueprint: lem-trf-ordinary-quotient-fixed-scalar-systems).
Proof: identify the two sequence ring maps on components, transport the fixed
model, and use its normalized scalar package. Choose the finite scalar packages
and apply scalar evaluation transpose. The prescribed model equality and the
normalized ordinary unit compute the tensor section, including its section casts. -/
private theorem fixedSystems_exists :
    ∃ A : CoefficientExtensionSystems l E L ι W,
      A.scalar.model.E = (integralComparisonSequenceScalarModel l E L ι W).E ∧
      ∀ (N : coefficientSequenceModules l E W) (U : (ℕ × W.ProEt)ᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L W).obj.obj U) (x : N.val.obj U),
        HEq (integralComparisonSequenceTensorSection l E L ι W N U s x)
          (s • (show (A.scalar.model.E.obj N).val.obj U from
            (A.scalar.ordinaryAdjunction.unit.app N).val.app U x)) := by
  classical
  let J := Scheme.ProEt.topology W
  let B := integralCoefficientCommRingSheaf l E W
  let τ := coefficientSequenceCommRingTransition l E W
  let F := integralCoefficientCommRingSheaf l L W
  let σ := coefficientSequenceCommRingTransition l L W
  let α := integralScalarQuotientSheafMap l E L ι W
  let hα := coefficientExtensionQuotient_naturality l E L ι W
  let φ := SemilinearSections.systemMap.{t + 1, t, max (t + 1) u} J B τ F σ α hα
  let D := integralComparisonSequenceScalarModel l E L ι W
  have hφ : φ = integralComparisonSequenceScalarMap l E L ι W := scalarMap_eq l E L ι W
  let := SemilinearSections.hasDerived.{t + 1, t, max (t + 1) u}
    (coefficientSequenceTopology J) (SemilinearSections.systemRing.{t + 1, t, max (t + 1) u} J B τ)
  let := SemilinearSections.hasDerived.{t + 1, t, max (t + 1) u}
    (coefficientSequenceTopology J) (SemilinearSections.systemRing.{t + 1, t, max (t + 1) u} J F σ)
  let D' : SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max (t + 1) u,
      max (t + 2) (u + 1), max (t + 2) (u + 1)} φ := hφ.symm ▸ D
  obtain ⟨S, hS⟩ := fixedScalarData.{t + 1, t, u} (coefficientSequenceTopology J) φ D'
  obtain ⟨_, hL⟩ := SemilinearSections.semilinearScalarData.{t + 1, t, u} J B τ F σ α hα
  let levels := fun n ↦ (hL n).some
  obtain ⟨ev⟩ := SemilinearSections.semilinearScalarEvaluationTranspose.{t + 1, t, u}
    J B τ F σ α hα S levels
  refine ⟨{ scalar := S
            levels := levels
            evaluation := ev.evaluation
            transpose_evaluation := ev.transpose_evaluation }, ?_⟩
  constructor
  · change S.model.E = D.E
    rw [hS]
    exact transportModel_E.{t + 1, t, u} (coefficientSequenceTopology J) hφ.symm D
  · intro N U s x
    have hD : HEq S.model D := (heq_of_eq hS).trans
      (transportModel_heq.{t + 1, t, u} (coefficientSequenceTopology J) hφ.symm D)
    exact (heq_of_eq (sequenceTensorSection_eq l E L ι W N U s x)).trans
      (modelTensor_unit.{t + 1, t, u} (coefficientSequenceTopology J) hφ S D hD N U s x)

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarModels

end
