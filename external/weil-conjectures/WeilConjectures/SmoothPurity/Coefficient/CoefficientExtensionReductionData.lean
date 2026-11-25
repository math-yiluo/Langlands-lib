/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-! # Interfaces for coherent finite reduction of coefficient extension

Source: the integral-operations clause of the main-20261015 blueprint.
The model records and their predicates are shared by the construction lemmas and
the public reduction theorem. Existing declarations are moved here verbatim.
(blueprint: stage3-pur-extension-reduction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
/-- A comparison with ordinary and derived normalizations, abstracted over its types.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientScalarComparisonData (Ordinary Derived : Type*)
    (sectionFormula : Ordinary → Prop) (modelFormula : Ordinary → Derived → Prop) where
  ordinary : Ordinary
  section_formula : sectionFormula ordinary
  derived : Derived
  model : modelFormula ordinary derived

/-- An ordinary association with its balanced formula, abstracted over its type.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientAssociationData (Association : Type*)
    (sectionFormula : Association → Prop) where
  association : Association
  association_section : sectionFormula association

/-- A strict model with its evaluation and transition specifications.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientStrictModelData (Association Direct : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop)
    extends CoefficientAssociationData Association sectionFormula where
  direct : Direct
  directEvaluation : Evaluation direct
  direct_transition : transitionFormula direct directEvaluation

/-- A representative model, normalized completion and its invertible counit.
The parameters cache the concrete functor types before structure generation.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientReductionModelData (Association Direct Completion : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop) (Model : Direct → Type*)
    (modelFormula : Association → ∀ direct, Evaluation direct → Model direct → Prop)
    (Normalized : Prop)
    (completionFormula : ∀ direct, Evaluation direct → Model direct → Completion → Prop)
    (comparisonFormula : Completion → Prop)
    extends CoefficientStrictModelData Association Direct sectionFormula Evaluation
      transitionFormula where
  model : Model direct
  model_evaluation : modelFormula association direct directEvaluation model
  normalized : Normalized
  completion : Completion
  completion_projection : completionFormula direct directEvaluation model completion
  comparison_isIso : comparisonFormula completion

section ScalarZero
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{r} C] {R S : Sheaf J CommRingCat.{r}} {f : R ⟶ S}
/-- Zero preservation from the actual additive structure, with the coefficient
universe explicitly retained. Source: Stacks 06YY
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientScalarModelZero (A : SemilinearSections.ScalarData.{c, v, r} f) :
    A.model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ A.model.E A.model.additive
end ScalarZero

section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

/-- Canonical scalar association, normalized on local tensors and on K-flat complexes.
It applies in particular on the actual coefficient sequence site.
Source: integral operations, node proof steps 2 and 7
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
abbrev CoefficientScalarAssociation :=
  CoefficientScalarComparisonData (A.model.E ⋙ B.model.E ≅ D.model.E) (A.T ⋙ B.T ≅ D.T)
    (fun ordinary ↦ ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
      (s : S.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (t • SemilinearSections.scalarExtensionSection.{c, v, r} g B (A.model.E.obj M) U
          (s • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x)) =
        (((g.hom.app U) s * t) •
          SemilinearSections.scalarExtensionSection.{c, v, r} h D M U x))
    (fun ordinary derived ↦ ∀
      (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
      derived.hom.app (DerivedCategory.Q.obj P) ≫ D.model.ε.app P =
        B.T.map (A.model.ε.app P) ≫
          B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- The `ULift`-transported finite quotient ring maps commute with transitions.

Source: the quotient-transition calculation in
`IntegralScalarExtensionWellDefined.integralScalarQuotientMap_transition`.
The two composites are equal after applying `RingHom.ext`; each sends a quotient
class represented by `x` to the class represented by the image of `x` under
`ι`, and the source transition and quotient lift are defined by quotient
induction.
(blueprint: lem-pur-coefficient-extension-reduction-model) -/
private theorem quotientRing_transition (n : ℕ) :
    CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarQuotientMap l E L ι (n + 1)).comp ULift.ringEquiv.toRingHom)) ≫
      CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l L (n + 1)).comp
            ULift.ringEquiv.toRingHom)) =
    CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            ULift.ringEquiv.toRingHom)) ≫
      CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarQuotientMap l E L ι n).comp ULift.ringEquiv.toRingHom)) := by
  ext x
  change (Padic.coefficientExtensionTransition l L (n + 1))
      ((integralScalarQuotientMap l E L ι (n + 1)) x.down) =
    (integralScalarQuotientMap l E L ι n)
      ((Padic.coefficientExtensionTransition l E (n + 1)) x.down)
  exact RingHom.congr_fun (integralScalarQuotientMap_transition l E L ι n) x.down

/-- The actual finite quotient inclusions commute with quotient transitions.
Source: the integral operations clause and integralScalarQuotientMap_transition
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: both ring maps send the residue of x to the residue of ι(x). Apply quotient
induction, then functorial constant sheafification. This includes ramified inclusions. -/
theorem coefficientExtensionQuotient_naturality (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι W (n + 1) ≫
        coefficientSequenceCommRingTransition l L W n =
      coefficientSequenceCommRingTransition l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n := by
  let forgetComm := sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat RingCat)
  unfold coefficientSequenceCommRingTransition integralScalarQuotientSheafMap
  apply forgetComm.map_injective
  change forgetComm.map _ ≫ forgetComm.map _ =
    forgetComm.map _ ≫ forgetComm.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← forgetComm.map_comp]
  apply congrArg (fun z ↦ forgetComm.map z)
  rw [quotientRing_transition l E L ι n]
  exact Functor.map_comp _ _ _

/-- The dependency's canonical semilinear scalar-extension data for the actual
quotient inclusions; no replacement functor or arbitrary coefficient map is used.
Source: integral operations and lem-coef-semilinear-derived-sections
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
abbrev CoefficientExtensionSystems :=
  SemilinearSections.ScalarSystems.{t + 1, t, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)

variable (SE : CoefficientDerivedSystemCalculus l E W)
  (SL : CoefficientDerivedSystemCalculus l L W)
  (A : CoefficientExtensionSystems l E L ι W)

/-- The coherent system C(K), formed by actual derived extension of the reduction
system; its evaluation is K_m tensor over A_m with B_m by A.evaluation.
Source: integral operations, simultaneous coefficient extension
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionSystem :
    DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l L W :=
  SE.reduction ⋙ A.scalar.T

/-- The actual comparison: inverse of the completed-limit identification, followed
by the coherent counit. Associativity and unitors only display its functorial type.
Source: node proof step 4, φ=a⁻¹e, expressed with C already associated
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom

/-- Finite scalar extension preserves zero maps via its own additive structure.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionFiniteZero (n : ℕ) :
    (A.levels n).model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (A.levels n).model.additive

/-- Zero preservation from the published additive finite reduction.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionReductionZero (n : ℕ) :
    (scalarReductionExtension l E W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (coefficientFiniteExtensionAdditive l E W n)

/-- Zero preservation from the published additive direct scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionDirectZero (n : ℕ) :
    (integralScalarReduction l E L ι W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (integralScalarReduction_additive l E L ι W n)

/-- Zero preservation for the same ordinary association source functor.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionCompositeZero (n : ℕ) :
    (scalarReductionExtension l E W n ⋙ (A.levels n).model.E).PreservesZeroMorphisms :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  Functor.preservesZeroMorphisms_comp _ _

/-- Apply ordinary scalar association degree by degree. The explicit zero-map
instances expose the existing additive witnesses without changing any functor.
Source: integral operations, node proof step 2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionAssociationChain (n : ℕ)
    (a : scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (((scalarReductionExtension l E W n ⋙ (A.levels n).model.E).mapHomologicalComplex
      (.up ℤ)).obj P) ⟶
      (((integralScalarReduction l E L ι W n).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI := coefficientExtensionDirectZero l E L ι W n
  letI := coefficientExtensionCompositeZero l E L ι W A n
  (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P

/-- The existing shifted Roos cone's actual nth projection, with its tower explicit.
Source: integral operations and completed scalar extension, node proof step 4
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n

/-- The balanced scalar-association formula on every local tensor section.
Source: integral operations, node proof step 2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def IsCoefficientExtensionAssociation
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n) : Prop :=
  ∀ (n : ℕ) (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U),
    ((association n).hom.app M).val.app U
      (b • SemilinearSections.scalarExtensionSection.{t + 1, t, u}
        (integralScalarQuotientSheafMap l E L ι W n) (A.levels n)
        ((scalarReductionExtension l E W n).obj M) U
        (a • @id (((scalarReductionExtension l E W n).obj M).val.obj U)
          (((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app U x))) =
      integralScalarTensorSection l E L ι W n M U
        (((integralScalarQuotientSheafMap l E L ι W n).hom.app U) a * b) x

/-- Simultaneous ordinary scalar association on the actual finite quotient models.
The section formula fixes the balanced association on arbitrary tensor coefficients.
Source: integral operations, node proof steps 1--2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
abbrev CoefficientExtensionAssociationData :=
  CoefficientAssociationData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (IsCoefficientExtensionAssociation l E L ι W A)

/-- The direct quotient model has exactly the published quotient transitions.
Source: integral operations, node proof steps 2--3
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def IsCoefficientExtensionStrictTransition
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceEvaluation l L W (n + 1)).obj
      ((direct.obj P).X i)).val.obj U)),
    HEq ((((coefficientSequenceTransition l L W (Nat.le_succ n)).app
        ((direct.obj P).X i)).val.app U).hom x)
      (((((directEvaluation n).inv.app P).f i).val.app U).hom
        ((((integralScalarTransition l E L ι W n).app P.obj).f i).val.app U
          ((((directEvaluation (n + 1)).hom.app P).f i).val.app U x)))

/-- The finite evaluation equation of the coherent representative model.
Caching this proposition prevents expansion when projecting the model record.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def IsCoefficientExtensionModelEvaluation
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
        (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
          (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P) =
      (A.evaluation n).hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map ((SE.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom ≫
        (A.levels n).model.ε.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map
          (coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj)

/-- The completion identification preserves the specified Roos projections.
Caching this proposition prevents expansion when projecting the model record.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def IsCoefficientExtensionCompletionProjection
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (completion : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    completion.inv.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceProjection l L W n).app
          ((coefficientExtensionSystem l E L ι W SE A).obj (DerivedCategory.Q.obj P.obj)) ≫
        (coefficientFiniteDerivedRestriction l L W n).map
          ((coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
            (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
              (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) ≫
        (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
          ((integralScalarFiniteComplex l E L ι W n).obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        DerivedCategory.Q.map
          (coefficientExtensionRoosProjection l E L ι W P.obj n)

/-- The representative-normalized coherent counit comparison, with its completion.
Source: integral operations, node proof steps 4--6
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
abbrev CoefficientExtensionReductionData :=
  CoefficientReductionModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)
    (fun direct ↦ integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (IsCoefficientExtensionModelEvaluation l E L ι W SE A)
    (∀ K : DerivedCategory (scalarReductionSource l E W),
    IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj K))
    (IsCoefficientExtensionCompletionProjection l E L ι W SE A)
    (fun completion ↦ IsIso (coefficientExtensionCounit l E L ι W SE SL A completion))

/-- The natural isomorphism of coherent quotient systems, with its specified counit.
Source: integral operations, node proof step 4
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso

/-- The coherent reduction data before the final counit isomorphism.
Source: integral operations and normalized DVR effectivity
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def CoefficientExtensionReductionSkeleton :=
  CoefficientReductionModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)
    (fun direct ↦ integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (IsCoefficientExtensionModelEvaluation l E L ι W SE A)
    (∀ K : DerivedCategory (scalarReductionSource l E W),
      IsNormalizedCoefficientSequence l L W
        ((coefficientExtensionSystem l E L ι W SE A).obj K))
    (IsCoefficientExtensionCompletionProjection l E L ι W SE A)
    (fun _ ↦ True)

end WeilConjectures
