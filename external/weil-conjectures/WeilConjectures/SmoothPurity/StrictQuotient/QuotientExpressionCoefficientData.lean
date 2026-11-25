/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import all WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientCompletedHorizontal

/-! # Prescribed strict quotient-expression towers

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E (lemma-pullback-K-flat)
and 07A2 (lemma-tensor-product-K-flat), and the extracted finite-expression argument
of lem-pur-quotient-expression-kflat-normalization
(blueprint: def-sf-strict-quotient-coefficient-comparisons).

The syntax retains distinct trees. Its interpretation uses the recorded ordinary
sequence-site operations. Natural-number level n denotes positive exponent n+1.
The completed-coefficient tower is localized before evaluation. No normalization
of transition adjoints is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

/-- The finite constructor trees, with no quotient by tensor or pullback identities.
This refines the recorded Generated predicate by retaining its constructor history.
Source: finite syntactic expressions in the node, Stacks 07A2 and 0G7E
(blueprint: def-pur-strict-quotient-expression-data). -/
inductive Expression {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y) (r : ℕ) :
    (W : Scheme.{t}) → Type (t + 1) where
  | input (i : Fin r) : Expression h f r Y
  | unitY : Expression h f r Y
  | unitX : Expression h f r X
  | unitZ : Expression h f r Z
  | tensor {W : Scheme.{t}} : Expression h f r W → Expression h f r W → Expression h f r W
  | pullF : Expression h f r Y → Expression h f r X
  | pullH : Expression h f r X → Expression h f r Z
  | pullHF : Expression h f r Y → Expression h f r Z

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Interpretation uses exactly the recorded sequence complexes, their direct-sum total
and termwise module inverse image. It chooses no replacement resolution.
Source: Stacks 07A2, 0G7E; def-pur-strict-quotient-expressions
(blueprint: def-pur-strict-quotient-expression-data). -/
def Expression.interpret {Z X Y : Scheme.{t}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ}
    (N : Fin r → Complex l E Y) : {W : Scheme.{t}} → Expression h f r W → Complex l E W
  | _, .input i => N i
  | _, .unitY => 𝟙_ (Complex l E Y)
  | _, .unitX => 𝟙_ (Complex l E X)
  | _, .unitZ => 𝟙_ (Complex l E Z)
  | _, .tensor A B => total l E (A.interpret N) (B.interpret N)
  | _, .pullF A => pull l E f (A.interpret N)
  | _, .pullH A => pull l E h (A.interpret N)
  | _, .pullHF A => pull l E (h ≫ f) (A.interpret N)

/-- The specified ring inverse image, on the original small sites and with coefficients
in the universe containing both the scheme and E. It is Kan extension and sheafification.
Source: Stacks 00VC and 03D2; def-weil-proetale-inverse-image
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
abbrev coefficientInverseImage {V W : Scheme.{t}} (g : V ⟶ W) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Scheme.coefficientProEtaleModelBaseChange.{t, u} g) CommRingCat.{max u (t + 1)}
    (Scheme.coefficientProEtaleModelTopology.{t, u} W)
    (Scheme.coefficientProEtaleModelTopology.{t, u} V)

/-- Transport of the coefficient rings to the equivalent small model; all original
objects and section maps are retained.
Source: Stacks 09A5; def-weil-proetale-inverse-image
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
abbrev coefficientToModel (W : Scheme.{t}) :=
  (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{t, u} W ⥤ W.ProEt)
    |>.sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
      (Scheme.coefficientProEtaleModelTopology.{t, u} W) (Scheme.ProEt.topology W)

/-- The actual constant-ring comparison is the adjunct of the constant-section map.
Source: Stacks 0H7J and 03D2; def-weil-proetale-inverse-image
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
def constantCoefficientMap {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ) :
    (coefficientInverseImage.{t, u} g).obj
        ((coefficientToModel.{t, u} W).obj (integralCoefficientCommRingSheaf l E W n)) ⟶
      (coefficientToModel.{t, u} V).obj (integralCoefficientCommRingSheaf l E V n) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{t, u} g) CommRingCat.{max u (t + 1)}
    (Scheme.coefficientProEtaleModelTopology.{t, u} W)
    (Scheme.coefficientProEtaleModelTopology.{t, u} V)).homEquiv _ _).symm
    ⟨Functor.whiskerLeft AsSmall.down.op
      (Scheme.coefficientProEtaleDirectRingMap.{t, u} g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom⟩

/-- The actual complex of completed-coefficient towers: restrict the prescribed
section groups and horizontal maps by the limit projections in each degree.
Source: Stacks 0941 and the coherent datum in def-coef-normalized-dvr-tower
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
abbrev completedTower {W : Scheme.{t}} (K : Complex l E W) :=
  ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj K

/-- The coefficient section of the actual degree-zero unit complex.
Source: Stacks 07A2 and 0941; the unit constructor of def-pur-strict-quotient-expressions
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
def unitSection (W : Scheme.{t}) (n : ℕ) (U : W.ProEt)
    (b : (integralCoefficientCommRingSheaf l E W n).obj.obj (op U)) :
    ((𝟙_ (Complex l E W)).X 0).val.obj (op (n, U)) :=
  ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (𝟙_ (coefficientSequenceModules l E W))).inv).val.app (op (n, U)) b

/-- The transition of the derived completed-coefficient tower, descended from its
actual ordinary arrows by localization, not supplied as independent derived data.
Source: Stacks 05RU and 0941; def-coef-normalized-dvr-tower, tower_tau
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
def completedTowerDerivedTransition (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m) :
    coefficientConstantTowerEvaluation l E W m ⟶ coefficientConstantTowerEvaluation l E W n :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ))
      (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m)).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q) (coefficientConstantTowerEvaluation l E W m) :=
    ⟨coefficientConstantTowerEvaluationFactors l E W m⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ))
      (((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q) (coefficientConstantTowerEvaluation l E W n) :=
    ⟨coefficientConstantTowerEvaluationFactors l E W n⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ)) _ _
    (coefficientConstantTowerEvaluation l E W m) (coefficientConstantTowerEvaluation l E W n)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE hmn).op) (.up ℤ))
      DerivedCategory.Q)

/-- Canonical evaluation of the localized actual completed tower. Its target is
exactly Res_n QK_n, using the exact-localization comparisons at both steps.
Source: Stacks 0941; def-coef-normalized-dvr-tower, evaluationIso
(blueprint: def-sf-strict-quotient-coefficient-comparisons). -/
def completedTowerLevelIso {W : Scheme.{t}} (K : Complex l E W) (n : ℕ) :
    (coefficientConstantTowerEvaluation l E W n).obj
        (DerivedCategory.Q.obj (completedTower l E K)) ≅
      (coefficientFiniteDerivedRestriction l E W n).obj
        (DerivedCategory.Q.obj (level l E K n)) :=
  ((coefficientConstantTowerEvaluation l E W n).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app K)).symm ≪≫
    (coefficientRestrictedEvaluationIso l E W n).app (DerivedCategory.Q.obj K) ≪≫
    (coefficientFiniteDerivedRestriction l E W n).mapIso
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app K)

/-- Flat terms and K-flatness on the vertical sequence site itself, not after
restriction to completed coefficients.
Source: Stacks 03ER, 06YN and 0941
(blueprint: def-pur-strict-quotient-expression-data). -/
def SystemGood {W : Scheme.{t}} (K : Complex l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) K ∧
    ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) (K.X k)

private theorem quotient_sequence_map (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m) :
    (coefficientSequenceCommRingSystem l E W).map (homOfLE hmn).op =
      coefficientFiniteQuotient l E W hmn := by
  let F := sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let ε : coefficientSequenceCommRingSystem l E W ⋙ F ⟶
      integralCoefficientSheafSystem l E W :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro k
      dsimp only [coefficientSequenceCommRingSystem, integralCoefficientSheafSystem,
        Functor.comp_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      simp only [Category.comp_id, Category.id_comp]
      rfl)
  have he := ε.naturality (homOfLE hmn).op
  change F.map ((coefficientSequenceCommRingSystem l E W).map (homOfLE hmn).op) ≫
    𝟙 _ = 𝟙 _ ≫ (integralCoefficientSheafSystem l E W).map (homOfLE hmn).op at he
  simp only [Category.comp_id, Category.id_comp] at he
  apply F.map_injective
  exact he

private theorem quotient_horizontal (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m)
    (U : W.ProEt) :
    (coefficientSequenceCommRingPresheaf l E W).map
        (Prod.mkHom (homOfLE hmn) (𝟙 U)).op =
      (coefficientFiniteQuotient l E W hmn).hom.app (op U) := by
  exact (WeilConjectures.horizontal_map
    (coefficientSequenceCommRingSystem l E W ⋙
      sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)})
        hmn (op U)).trans
    (congrArg (fun z ↦ z.hom.app (op U)) (quotient_sequence_map l E W hmn))

/-- The coefficient-map part of the strict quotient tower argument.
Source: Stacks 0G7E and 07A2; the constant-section comparison and its quotient square.
(blueprint: lem-pur-quotient-expression-strict-kflat-towers-constant-maps).
-/
theorem quotientExpressionStrictKFlatTowers_constantMaps
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (_hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (_hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
      (∀ n : ℕ, IsIso (constantCoefficientMap l E g n) ∧
        PreservesFiniteLimits (integralOperationsLevelPullback l E g n) ∧
        PreservesFiniteColimits (integralOperationsLevelPullback l E g n)) ∧
      (∀ {m n : ℕ} (hmn : n ≤ m),
        (coefficientInverseImage.{t, u} g).map
            ((coefficientToModel.{t, u} W).map (coefficientFiniteQuotient l E W hmn)) ≫
            constantCoefficientMap l E g n =
          constantCoefficientMap l E g m ≫
            (coefficientToModel.{t, u} V).map (coefficientFiniteQuotient l E V hmn))) := by
  have _ := hP
  intro V W g _hg
  constructor
  · intro n
    refine ⟨?_, Scheme.coefficientProEtaleModulePullback_exact.{t, u} g _⟩
    exact Scheme.modelCommRingMapAdjunct_isIso.{t, u} g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  · intro m n hmn
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.coefficientProEtaleModelBaseChange.{t, u} g) CommRingCat.{max u (t + 1)}
      (Scheme.coefficientProEtaleModelTopology.{t, u} W)
      (Scheme.coefficientProEtaleModelTopology.{t, u} V)
    apply (adj.homEquiv _ _).injective
    dsimp only [constantCoefficientMap]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hh := integralComparisonSequenceRing_naturality l E g
      (Prod.mkHom (homOfLE hmn) (𝟙 (AsSmall.down.obj U.unop))).op
    have hi : (integralComparisonSequenceBaseChange g).map
        (Prod.mkHom (homOfLE hmn) (𝟙 (AsSmall.down.obj U.unop))) =
        Prod.mkHom (homOfLE hmn)
          (𝟙 ((Scheme.proEtaleBaseChange g).obj (AsSmall.down.obj U.unop))) := by
      ext <;> simp [integralComparisonSequenceBaseChange]
    simp only [Functor.op_map, Quiver.Hom.unop_op, hi] at hh
    rw [quotient_horizontal l E, quotient_horizontal l E] at hh
    exact hh

/-- The unit-transition part of the strict quotient tower argument.
Source: Stacks 0941; the degree-zero coefficient unit and quotient transition.
(blueprint: lem-pur-quotient-expression-strict-kflat-towers-unit-transitions).
-/
theorem quotientExpressionStrictKFlatTowers_unitTransitions
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (_hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (_hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    (∀ (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m) (U : W.ProEt)
      (b : (integralCoefficientCommRingSheaf l E W m).obj.obj (op U)),
      horizontal l E ((𝟙_ (Complex l E W)).X 0) hmn U (unitSection l E W m U b) =
        unitSection l E W n U ((coefficientFiniteQuotient l E W hmn).hom.app (op U) b)) := by
  have _ := h
  have _ := f
  have _ := hP
  intro W m n hmn U b
  calc
    _ = unitSection l E W n U
        ((coefficientSequenceCommRingPresheaf l E W).map
          (Prod.mkHom (homOfLE hmn) (𝟙 U)).op b) :=
      (ConcreteCategory.congr_hom
        (((PresheafOfModules.toPresheaf _).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ (coefficientSequenceModules l E W))).inv.val).naturality
              (Prod.mkHom (homOfLE hmn) (𝟙 U)).op) b).symm
    _ = _ := congrArg (unitSection l E W n U)
      (ConcreteCategory.congr_hom (quotient_horizontal l E W hmn U) b)

end WeilConjectures.StrictQuotient
