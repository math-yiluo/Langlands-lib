/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction
public import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionStrictKFlatTowers
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceTower
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons

import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Simultaneous quotient realization of completed comparisons

The construction data are owned by
(blueprint: def-pur-completed-comparison-quotient-realization-data).

Source: the integral reduction compatibility in the Weil blueprint,
`prose-03-02`, and its representative refinement
(blueprint: lem-pur-completed-comparison-quotient-realization).

Natural level n means positive quotient exponent n+1. All maps below are maps
of entire coefficient systems before evaluation or total derived limit.
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
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual ordinary reduction diagram of a representative, not a new resolution.
Source: Stacks 0941, quotient construction
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
abbrev quotient {Y : Scheme.{u}}
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :=
  ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P

/-- Evaluate the existing finite constructor trees using the specified completed
operations. The unit is the total limit of the actual coefficient unit system.
Source: integral finite-expression clause
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def value {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ} :
    {W : Scheme.{u}} → StrictQuotient.Expression h f r W →
      ((Fin r → DerivedCategory (scalarReductionSource l E Y)) ⥤
        DerivedCategory (scalarReductionSource l E W))
  | _, .input i => Pi.eval _ i
  | _, .unitY => (Functor.const _).obj
      ((coefficientSequenceLimit l E Y).obj
        (DerivedCategory.Q.obj
          (HomologicalComplex.tensorUnit (coefficientSequenceModules l E Y) (.up ℤ))))
  | _, .unitX => (Functor.const _).obj
      ((coefficientSequenceLimit l E X).obj
        (DerivedCategory.Q.obj
          (HomologicalComplex.tensorUnit (coefficientSequenceModules l E X) (.up ℤ))))
  | _, .unitZ => (Functor.const _).obj
      ((coefficientSequenceLimit l E Z).obj
        (DerivedCategory.Q.obj
          (HomologicalComplex.tensorUnit (coefficientSequenceModules l E Z) (.up ℤ))))
  | W, .tensor A B => (value A).prod' (value B) ⋙ integralCompletedTensor l E W
  | _, .pullF A => value A ⋙ integralDerivedPullback l E f
  | _, .pullH A => value A ⋙ integralDerivedPullback l E h
  | _, .pullHF A => value A ⋙ integralDerivedPullback l E (h ≫ f)

/-- Translate the already recorded finite syntax to the shared structural-map
syntax. This retains each constructor and its actual scheme morphism.
Source: finite-expression and coherence clauses
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def expression {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ} :
    {W : Scheme.{u}} → StrictQuotient.Expression h f r W →
      CompletedOperations.Expression (fun V : Scheme.{u} ↦ V) (fun _ : Fin r ↦ Y) W
  | _, .input i => .input i
  | _, .unitY => .unit Y
  | _, .unitX => .unit X
  | _, .unitZ => .unit Z
  | _, .tensor A B => .tensor (expression A) (expression B)
  | _, .pullF A => .pullback f (expression A)
  | _, .pullH A => .pullback h (expression A)
  | _, .pullHF A => .pullback (h ≫ f) (expression A)

/-- Interpret that same syntax by the existing strict-system interpretation.
Source: finite-expression and coherence clauses
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
abbrev strictValue {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ}
    (N : Fin r → StrictQuotient.Complex l E Y) {W : Scheme.{u}}
    (A : StrictQuotient.Expression h f r W) :=
  IntegralCoherence.value l E (W := fun V : Scheme.{u} ↦ V) N (expression A)

/-- The specified coherent reduction of a substitution map, followed by the actual
counit. This formula does not assume that the substitution is invertible.
Source: whole-system equation, proof step 4
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def reduction {W : Scheme.{u}}
    {K : DerivedCategory (scalarReductionSource l E W)}
    {A : coefficientSequenceDerived l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj A) :
    (pullbackTensorCalculus l E W).reduction.obj K ⟶ A :=
  (pullbackTensorCalculus l E W).reduction.map β ≫
    (pullbackTensorCalculus l E W).adjunction.counit.app A

/-- Tensor substitution is its actual Roos-normalized realization followed by the
image of the two coherent reduction maps, then the fixed K-flat tensor model.
Source: proof steps 1 and 4; Stacks 07A4, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def tensorSubstitution {W : Scheme.{u}}
    {K H : DerivedCategory (scalarReductionSource l E W)}
    (A B : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (βA : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (βB : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B)) :
    (integralCompletedTensor l E W).obj (K,H) ⟶
      (coefficientSequenceLimit l E W).obj
        (DerivedCategory.Q.obj (StrictQuotient.total l E A B)) :=
  (pullbackTensorIntegralTensorModel l E W).hom.app (K,H) ≫
    (coefficientSequenceLimit l E W).map
      ((pullbackTensorCalculus l E W).systemClosed.tensor.map
        (Prod.mkHom (reduction l E βA) (reduction l E βB))) ≫
    (coefficientSequenceLimit l E W).map
      (pullbackTensorSystemModel l E W A B hA.1 hB.1).inv

attribute [local irreducible] tensorSubstitution

/-- The two recorded sequence interfaces use the same constant-section ring map
and the same sectionwise right adjoint, hence the same chosen left adjoint.
Source: Stacks 03D2, 0941; actual finite pullbacks in the node
(blueprint: lem-pur-completed-comparison-quotient-realization).
Proof: uniqueness in pullbackTensorSequenceRing_existsUnique identifies its ring
map with integralComparisonSequenceRingMap. Unfold the two direct images; they
are the same pushforward. Their IsRightAdjoint proofs agree by proof irrelevance.
Applying Functor.leftAdjoint to that equality gives the asserted equality. -/
theorem sequencePullback_eq {V W : Scheme.{u}} (g : V ⟶ W) :
    pullbackTensorSequenceInverse l E g = integralComparisonSequencePullback l E g := by
  have hr : pullbackTensorSequenceRing l E g = integralComparisonSequenceRingMap l E g := by
    apply (pullbackTensorSequenceRing_existsUnique l E g).unique
    · intro n U
      unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
      rfl
    · intro n U
      rfl
  have hd : pullbackTensorSequenceDirect l E g =
      integralComparisonSequenceDirectImage l E g := by
    unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
    rw [hr]
  have chosen (R R' : coefficientSequenceModules l E V ⥤ coefficientSequenceModules l E W)
      [R.IsRightAdjoint] [R'.IsRightAdjoint] (e : R = R') :
      R.leftAdjoint = R'.leftAdjoint := by
    subst R'
    rfl
  exact chosen _ _ hd

/-- Transport between the two names of the same actual strict inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def pullBridge {V W : Scheme.{u}} (g : V ⟶ W) :=
  NatIso.mapHomologicalComplex (eqToIso (sequencePullback_eq l E g)) (.up ℤ)

/-- The specified strict comparison on quotient systems, transported only across
the recorded equality of inverse-image interfaces. Its hom and inverse retain
all horizontal maps because this is an isomorphism of sequence complexes.
Source: Stacks 07A4; the displayed c and inverse in the node
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def comparison {V W : Scheme.{u}} (g : V ⟶ W)
    (P Q : StrictQuotient.Complex l E W) :
    StrictQuotient.pull l E g (StrictQuotient.total l E P Q) ≅
      StrictQuotient.total l E (StrictQuotient.pull l E g P) (StrictQuotient.pull l E g Q) :=
  ((pullBridge l E g).app (StrictQuotient.total l E P Q)).symm ≪≫
    (pullbackTensorSequenceCochain l E g).app (P,Q) ≪≫
    (coefficientTotalTensor.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology V))
      (coefficientSequenceCommRingSheaf l E V)).mapIso
        (Iso.prod ((pullBridge l E g).app P) ((pullBridge l E g).app Q))

attribute [local irreducible] comparison pullBridge

/-- Pullback substitution uses the actual primitive realization, its counit, and
exact localization of this very strict inverse image.
Source: proof steps 1 and 4; Stacks 099N, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def pullSubstitution {V W : Scheme.{u}} (g : V ⟶ W)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W)
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A)) :
    (integralDerivedPullback l E g).obj K ⟶
      (coefficientSequenceLimit l E V).obj
        (DerivedCategory.Q.obj (StrictQuotient.pull l E g A)) :=
  (pullbackTensorIntegralPullbackModel l E g).hom.app K ≫
    (coefficientSequenceLimit l E V).map
      ((pullbackTensorSequenceDerived l E g).map (reduction l E β)) ≫
    (coefficientSequenceLimit l E V).map
      (((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.hom.app A) ≫
        DerivedCategory.Q.map ((pullBridge l E g).hom.app A))

attribute [local irreducible] pullSubstitution

/-- Recursive substitution from specified leaf comparisons. Tensor and pullback
vertices use the actual primitive counit formulas, retaining every parenthesis.
Source: proof step 1 and the displayed beta comparisons
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def substituteInputs {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ}
    (N : Fin r → StrictQuotient.Complex l E Y)
    (M : Fin r → DerivedCategory (scalarReductionSource l E Y))
    (β : ∀ i : Fin r, M i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N i)))
    (good : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f r W),
      StrictQuotient.SystemGood l E (strictValue l E N A)) :
    {W : Scheme.{u}} → (A : StrictQuotient.Expression h f r W) →
      (value l E A).obj M ⟶ (coefficientSequenceLimit l E W).obj
        (DerivedCategory.Q.obj (strictValue l E N A))
  | _, .input i => β i
  | _, .unitY => 𝟙 _
  | _, .unitX => 𝟙 _
  | _, .unitZ => 𝟙 _
  | _, .tensor A B => tensorSubstitution l E _ _ (good A) (good B)
      (substituteInputs N M β good A) (substituteInputs N M β good B)
  | _, .pullF A => pullSubstitution l E f _ (substituteInputs N M β good A)
  | _, .pullH A => pullSubstitution l E h _ (substituteInputs N M β good A)
  | _, .pullHF A => pullSubstitution l E (h ≫ f) _ (substituteInputs N M β good A)

attribute [local irreducible] substituteInputs

/-- Substitute simultaneous representatives using the actual reconstruction unit at leaves.
Source: proof step 1 and the displayed beta comparisons
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def substitution {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ}
    (P : Fin r → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M : Fin r → DerivedCategory (scalarReductionSource l E Y))
    (φ : ∀ i : Fin r, DerivedCategory.Q.obj (P i).obj ≅ M i)
    (good : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f r W),
      StrictQuotient.SystemGood l E (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) :
    {W : Scheme.{u}} → (A : StrictQuotient.Expression h f r W) →
      (value l E A).obj M ⟶ (coefficientSequenceLimit l E W).obj
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) :=
  fun A ↦ substituteInputs l E (fun i ↦ quotient l E (P i).obj) M
    (fun i ↦ (pullbackTensorCalculus l E Y).adjunction.unit.app (M i) ≫
      (coefficientSequenceLimit l E Y).map
        ((pullbackTensorCalculus l E Y).reduction.map (φ i).inv ≫
          (pullbackTensorReductionModel l E Y).hom.app (P i))) good A

attribute [local irreducible] substitution

/-- Whole-system K-flatness needed to evaluate the normalized tensor models.
Source: finite-expression clause, proof step 1
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
abbrev GoodExpressions {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) {r : ℕ}
    (P : Fin r → (integralOperationsGoodComplex l E Y).FullSubcategory) : Prop :=
  ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f r W),
    StrictQuotient.SystemGood l E (strictValue l E (fun i ↦ quotient l E (P i).obj) A)

/-- The canonical completed image of a strict arrow, with both vertices fixed
by recursive substitution. This also defines the completed structural maps by
their representative normalization; there is no independent isomorphism choice.
Source: comparison, coherence and counit clauses, proof steps 2--5
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def transport {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ}
    (P : Fin r → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M : Fin r → DerivedCategory (scalarReductionSource l E Y))
    (φ : ∀ i : Fin r, DerivedCategory.Q.obj (P i).obj ≅ M i)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f r W),
      IsIso (substitution l E P M φ good A))
    {W : Scheme.{u}} (A B : StrictQuotient.Expression h f r W)
    (v : strictValue l E (fun i ↦ quotient l E (P i).obj) A ⟶
      strictValue l E (fun i ↦ quotient l E (P i).obj) B) :
    (value l E A).obj M ⟶ (value l E B).obj M :=
  substitution l E P M φ good A ≫
    (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map v) ≫
      (@asIso _ _ _ _ (substitution l E P M φ good B) (invertible B)).inv

attribute [local irreducible] transport

/-- The two expressions defining K_s and K_t, with the first two inputs at Y.
Source: displayed K_s,K_t equation
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def sourceExpression {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) :
    StrictQuotient.Expression h f 3 X := .pullF (.tensor (.input 0) (.input 1))

/-- The tensor of the two completed pullbacks, with the displayed parentheses.
Source: displayed K_s,K_t equation
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def targetExpression {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) :
    StrictQuotient.Expression h f 3 X := .tensor (.pullF (.input 0)) (.pullF (.input 1))

/-- Naturality of the fixed completed comparison under all derived morphisms;
the input full subcategory imposes no restriction on its Hom sets.
Source: derived naturality clause, proof step 3
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def NaturalComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N M' N' : sfIntegralConstructibleCategory l E Y)
    (a : M.obj ⟶ M'.obj) (b : N.obj ⟶ N'.obj),
    (integralDerivedPullback l E f).map
        ((integralCompletedTensor l E Y).map (Prod.mkHom a b)) ≫
        (canonicalIntegralPullbackTensor l E f M' N').hom.hom =
      (canonicalIntegralPullbackTensor l E f M N).hom.hom ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((integralDerivedPullback l E f).map a)
            ((integralDerivedPullback l E f).map b))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The two coefficient rows of the actual strict scalar-expression calculus.
Source: scalar quotient paragraph
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def ScalarComplex (d : Bool) (W : Scheme.{u}) :=
  if d then StrictQuotient.Complex l L W else StrictQuotient.Complex l E W

/-- The least family of finite expressions using the given three inputs, units,
tensor, the displayed pullbacks, and the actual coefficient extension. It records
both orders of scalar change and pullback; no closure property is assumed.
Source: scalar quotient and finite-expression paragraphs
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
inductive ScalarGenerated {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (N : Fin 3 → StrictQuotient.Complex l E Y) :
    (d : Bool) → (W : Scheme.{u}) → ScalarComplex l E L d W → Prop where
  | input (i : Fin 3) : ScalarGenerated h f N false Y (N i)
  | unitE (W : Scheme.{u}) : W = Z ∨ W = X ∨ W = Y →
      ScalarGenerated h f N false W
        (HomologicalComplex.tensorUnit (coefficientSequenceModules l E W) (.up ℤ))
  | unitL (W : Scheme.{u}) : W = Z ∨ W = X ∨ W = Y →
      ScalarGenerated h f N true W
        (HomologicalComplex.tensorUnit (coefficientSequenceModules l L W) (.up ℤ))
  | tensorE {W : Scheme.{u}} {A B : StrictQuotient.Complex l E W} :
      ScalarGenerated h f N false W A → ScalarGenerated h f N false W B →
        ScalarGenerated h f N false W (StrictQuotient.total l E A B)
  | tensorL {W : Scheme.{u}} {A B : StrictQuotient.Complex l L W} :
      ScalarGenerated h f N true W A → ScalarGenerated h f N true W B →
        ScalarGenerated h f N true W (StrictQuotient.total l L A B)
  | pullE {V W : Scheme.{u}} (g : V ⟶ W) : StrictQuotient.AllowedArrow h f g →
      ∀ {A : StrictQuotient.Complex l E W}, ScalarGenerated h f N false W A →
        ScalarGenerated h f N false V (StrictQuotient.pull l E g A)
  | pullL {V W : Scheme.{u}} (g : V ⟶ W) : StrictQuotient.AllowedArrow h f g →
      ∀ {A : StrictQuotient.Complex l L W}, ScalarGenerated h f N true W A →
        ScalarGenerated h f N true V (StrictQuotient.pull l L g A)
  | scalar {W : Scheme.{u}} {A : StrictQuotient.Complex l E W} :
      ScalarGenerated h f N false W A → ScalarGenerated h f N true W
        ((ScalarExtensionTower.scalar l E L ι W).obj A)

/-- Flat-term K-flatness and normalization in either coefficient row.
Source: scalar normalization clause; Stacks 06YS, 0G7E, 07A2
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def ScalarGood (d : Bool) (W : Scheme.{u}) : ScalarComplex l E L d W → Prop :=
  match d with
  | false => fun A ↦ StrictQuotient.SystemGood l E A ∧
      (∀ n : ℕ, StrictQuotient.Good l E A n) ∧
      IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A)
  | true => fun A ↦ StrictQuotient.SystemGood l L A ∧
      (∀ n : ℕ, StrictQuotient.Good l L A n) ∧
      IsNormalizedCoefficientSequence l L W (DerivedCategory.Q.obj A)

/-- The induced map of strict expressions, using the same ordinary constructor
functors as their objects. No localization or resolution is chosen here.
Source: natural substitution paragraph, proof steps 1 and 3
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def strictMap {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y} {r : ℕ}
    {N N' : Fin r → StrictQuotient.Complex l E Y} (a : ∀ i : Fin r, N i ⟶ N' i) :
    {W : Scheme.{u}} → (A : StrictQuotient.Expression h f r W) →
      strictValue l E N A ⟶ strictValue l E N' A
  | _, .input i => a i
  | _, .unitY => 𝟙 _
  | _, .unitX => 𝟙 _
  | _, .unitZ => 𝟙 _
  | W, .tensor A B =>
      @MonoidalCategory.tensorHom (StrictQuotient.Complex l E W) _ _
        (strictValue l E N A) (strictValue l E N' A)
        (strictValue l E N B) (strictValue l E N' B)
        (strictMap a A) (strictMap a B)
  | _, .pullF A => (IntegralCoherence.pull l E f).map (strictMap a A)
  | _, .pullH A => (IntegralCoherence.pull l E h).map (strictMap a A)
  | _, .pullHF A => (IntegralCoherence.pull l E (h ≫ f)).map (strictMap a A)

attribute [local irreducible] strictMap

/-- Naturality of every canonical substitution in representative maps and their
arbitrary derived input maps. The fixed comparison itself has the all-derived
naturality statement NaturalComparison, so representative roofs are not excluded.
Source: naturality and representative-independence paragraphs, proof step 3
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def NaturalSubstitution {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P) : Prop :=
  ∀ (M' : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P' : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ' : ∀ i : Fin 3, DerivedCategory.Q.obj (P' i).obj ≅ (M' i).obj)
    (good' : GoodExpressions l E h f P')
    (a : ∀ i : Fin 3, (P i).obj ⟶ (P' i).obj)
    (v : ∀ i : Fin 3, (M i).obj ⟶ (M' i).obj)
    (_comm : ∀ i : Fin 3, DerivedCategory.Q.map (a i) ≫ (φ' i).hom = (φ i).hom ≫ v i)
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
    (value l E A).map v ≫ substitution l E P' (fun i ↦ (M' i).obj) φ' good' A =
      substitution l E P (fun i ↦ (M i).obj) φ good A ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map
          (strictMap l E
            (fun i ↦ ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex
              (.up ℤ)).map (a i)) A))

/-- The strict associativity, signed symmetry, action units and composition laws,
for the very comparison defined above, rather than unrelated monoidal data.
Source: comparison coherence paragraph; Stacks 07A4, 0D6D
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def StrictCoherence {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) : Prop :=
  ∃ (cf : IntegralCoherence.PullbackComparison l E f)
    (ch : IntegralCoherence.PullbackComparison l E h)
    (chf : IntegralCoherence.PullbackComparison l E (h ≫ f)),
    IntegralCoherence.Coherent l E f cf ∧ IntegralCoherence.Coherent l E h ch ∧
    IntegralCoherence.Coherent l E (h ≫ f) chf ∧
    IntegralCoherence.CompositionLaw l E h f cf ch chf ∧
    (∀ A B : StrictQuotient.Complex l E Y, cf.tensor l E A B = comparison l E f A B) ∧
    (∀ A B : StrictQuotient.Complex l E X, ch.tensor l E A B = comparison l E h A B) ∧
    (∀ A B : StrictQuotient.Complex l E Y,
      chf.tensor l E A B = comparison l E (h ≫ f) A B)

/-- Scalar change of a specified substitution, using the normalized scalar realization,
the derived scalar image of its coherent counit, and the actual K-flat counit.
Source: scalar paragraph, proof steps 6--7; Stacks 06YY, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def scalarSubstitution {W : Scheme.{u}}
    {ρ : IntegralComparisonRoosModel l L W}
    (S : IntegralComparisonScalarModel l E L ι W
      (pullbackTensorCalculus l E W) ρ)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W)
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A)) :
    (integralScalarExtension l E L ι W).obj K ⟶
      (coefficientSequenceLimit l L W).obj
        (DerivedCategory.Q.obj ((ScalarExtensionTower.scalar l E L ι W).obj A)) :=
  S.realization.hom.app K ≫ (coefficientSequenceLimit l L W).map
    ((integralComparisonDerivedSequenceScalar l E L ι W).map (reduction l E β) ≫
      (integralComparisonSequenceScalarModel l E L ι W).ε.app A)

/-- The actual scalar quotient list, without choosing new resolutions over L.
Source: balanced quotient association in proof step 6
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def scalarQuotients {Y : Scheme.{u}}
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory) :
    Fin 3 → StrictQuotient.Complex l L Y :=
  fun i ↦ (ScalarExtensionTower.scalar l E L ι Y).obj (quotient l E (P i).obj)

/-- Apply this item's same recursive substitution at L, with the scalar-realized
E quotient leaves. This pins the L vertices used by the strict scalar square.
Source: scalar paragraph, proof steps 6--7
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def scalarBeta {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    {ρY : IntegralComparisonRoosModel l L Y}
    (SY : IntegralComparisonScalarModel l E L ι Y
      (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A)) :
    {W : Scheme.{u}} → (A : StrictQuotient.Expression h f 3 W) →
      (value l L A).obj (fun i ↦ (integralScalarExtension l E L ι Y).obj (M i).obj) ⟶
      (coefficientSequenceLimit l L W).obj
        (DerivedCategory.Q.obj (strictValue l L (scalarQuotients l E L ι P) A)) :=
  fun A ↦ substituteInputs l L (scalarQuotients l E L ι P)
    (fun i ↦ (integralScalarExtension l E L ι Y).obj (M i).obj)
    (fun i ↦ scalarSubstitution l E L ι SY (quotient l E (P i).obj)
      (substitution l E P (fun j ↦ (M j).obj) φ good (.input i))) goodL A

/-- Transport at L by the scalar-realized leaves and this item's recursive substitution.
Source: the limit-image clause of the scalar paragraph
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def scalarTransport {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    {ρY : IntegralComparisonRoosModel l L Y}
    (SY : IntegralComparisonScalarModel l E L ι Y
      (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A))
    (invertibleL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (scalarBeta l E L ι M P φ good SY goodL A))
    {W : Scheme.{u}} (A B : StrictQuotient.Expression h f 3 W)
    (v : strictValue l L (scalarQuotients l E L ι P) A ⟶
      strictValue l L (scalarQuotients l E L ι P) B) :
    (value l L A).obj (fun i ↦ (integralScalarExtension l E L ι Y).obj (M i).obj) ⟶
      (value l L B).obj (fun i ↦ (integralScalarExtension l E L ι Y).obj (M i).obj) :=
  scalarBeta l E L ι M P φ good SY goodL A ≫
    (coefficientSequenceLimit l L W).map (DerivedCategory.Q.map v) ≫
    (@asIso _ _ _ _ (scalarBeta l E L ι M P φ good SY goodL B) (invertibleL B)).inv

/-- The strict scalar square's first route, using this item's comparison c_L.
Source: displayed scalar square, proof step 7; Stacks 03EL, 07A4
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def scalarLeft {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : StrictQuotient.Complex l E Y) :
    (ScalarExtensionTower.scalar l E L ι X).obj
      (StrictQuotient.pull l E f (StrictQuotient.total l E P Q)) ≅
    StrictQuotient.total l L
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj P))
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj Q)) :=
  Iso.trans
    (X := (ScalarExtensionTower.scalar l E L ι X).obj
      (StrictQuotient.pull l E f (StrictQuotient.total l E P Q)))
    (Y := StrictQuotient.pull l L f
      ((ScalarExtensionTower.scalar l E L ι Y).obj (StrictQuotient.total l E P Q)))
    (Z := StrictQuotient.total l L
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj P))
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj Q)))
    ((ScalarExtensionTower.kappa l E L ι f).app (StrictQuotient.total l E P Q))
    (Iso.trans
      (Y := StrictQuotient.pull l L f (StrictQuotient.total l L
        ((ScalarExtensionTower.scalar l E L ι Y).obj P)
        ((ScalarExtensionTower.scalar l E L ι Y).obj Q)))
      ((ScalarExtensionTower.pull l L f).mapIso
        (((ScalarExtensionTower.comparisons l).sigma E L ι Y).app (P,Q)))
      (comparison l L f ((ScalarExtensionTower.scalar l E L ι Y).obj P)
        ((ScalarExtensionTower.scalar l E L ι Y).obj Q)))

/-- The strict scalar square's second route, using this item's comparison c_E.
Source: displayed scalar square, proof step 7; Stacks 03EL, 07A4
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def scalarRight {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : StrictQuotient.Complex l E Y) :
    (ScalarExtensionTower.scalar l E L ι X).obj
      (StrictQuotient.pull l E f (StrictQuotient.total l E P Q)) ≅
    StrictQuotient.total l L
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj P))
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj Q)) :=
  (ScalarExtensionTower.scalar l E L ι X).mapIso (comparison l E f P Q) ≪≫
    ((ScalarExtensionTower.comparisons l).sigma E L ι X).app
      (StrictQuotient.pull l E f P, StrictQuotient.pull l E f Q) ≪≫
    (ScalarExtensionTower.tensor l L X).mapIso
      (Iso.prod ((ScalarExtensionTower.kappa l E L ι f).app P)
        ((ScalarExtensionTower.kappa l E L ι f).app Q))

attribute [local irreducible] scalarSubstitution scalarBeta scalarTransport scalarLeft scalarRight

/-- The actual link from strict scalar routes to completed gamma and alpha composites.
The L substitutions use the same recursion as the E substitutions and the normalized
scalar realization at their leaves. All equalities are before finite evaluation.
Source: scalar paragraph's limit-image assertion, proof steps 6--7
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def ScalarLimitImage {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)) : Prop :=
  ∃ (ρX : IntegralComparisonRoosModel l L X) (ρY : IntegralComparisonRoosModel l L Y)
    (SX : IntegralComparisonScalarModel l E L ι X (pullbackTensorCalculus l E X) ρX)
    (SY : IntegralComparisonScalarModel l E L ι Y
      (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A))
    (invertibleL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (scalarBeta l E L ι M P φ good SY goodL A)),
  (scalarLeft l E L ι f (quotient l E (P 0).obj) (quotient l E (P 1).obj) =
    scalarRight l E L ι f (quotient l E (P 0).obj) (quotient l E (P 1).obj)) ∧
  (scalarTransport l E L ι M P φ good SY goodL invertibleL
      (sourceExpression h f) (targetExpression h f)
      (comparison l L f ((scalarQuotients l E L ι P) 0)
        ((scalarQuotients l E L ι P) 1)).hom =
    (canonicalIntegralPullbackTensor l L f
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M 0))
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M 1))).hom.hom) ∧
  (∀ (v : (ScalarExtensionTower.scalar l E L ι X).obj
        (strictValue l E (fun i ↦ quotient l E (P i).obj) (sourceExpression h f)) ⟶
      strictValue l L (scalarQuotients l E L ι P) (targetExpression h f)),
    v = (scalarLeft l E L ι f (quotient l E (P 0).obj)
      (quotient l E (P 1).obj)).hom ∨
    v = (scalarRight l E L ι f (quotient l E (P 0).obj)
      (quotient l E (P 1).obj)).hom →
    scalarSubstitution l E L ι SX
        (strictValue l E (fun i ↦ quotient l E (P i).obj) (sourceExpression h f))
        (substitution l E P (fun i ↦ (M i).obj) φ good (sourceExpression h f)) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map v) ≫
      (@asIso _ _ _ _ (scalarBeta l E L ι M P φ good SY goodL (targetExpression h f))
        (invertibleL (targetExpression h f))).inv =
    (integralPullbackScalarComparison l E L ι f
        ((constructibleIntegralTensor l E Y).obj (M 0, M 1))).hom.hom ≫
      (integralDerivedPullback l L f).map
        (integralTensorScalarComparison l E L ι Y (M 0) (M 1)).hom.hom ≫
      scalarTransport l E L ι M P φ good SY goodL invertibleL
        (sourceExpression h f) (targetExpression h f)
        (comparison l L f ((scalarQuotients l E L ι P) 0)
          ((scalarQuotients l E L ι P) 1)).hom ∧
    scalarSubstitution l E L ι SX
        (strictValue l E (fun i ↦ quotient l E (P i).obj) (sourceExpression h f))
        (substitution l E P (fun i ↦ (M i).obj) φ good (sourceExpression h f)) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map v) ≫
      (@asIso _ _ _ _ (scalarBeta l E L ι M P φ good SY goodL (targetExpression h f))
        (invertibleL (targetExpression h f))).inv =
    (integralScalarExtension l E L ι X).map
      (transport l E P (fun i ↦ (M i).obj) φ good invertible
        (sourceExpression h f) (targetExpression h f)
        (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj)).hom) ≫
      (integralTensorScalarComparison l E L ι X
        ((constructibleIntegralPullback l E f).obj (M 0))
        ((constructibleIntegralPullback l E f).obj (M 1))).hom.hom ≫
      (integralCompletedTensor l L X).map (Prod.mkHom
        (integralPullbackScalarComparison l E L ι f (M 0)).hom.hom
        (integralPullbackScalarComparison l E L ι f (M 1)).hom.hom))

open ScalarExtensionTower in
/-- Identity coefficient extension uses the actual action unitors.
Source: scalar paragraph, proof steps 6--7; Stacks 03EL, 07A4, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def ScalarIdentity {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  type_of% (ScalarExtensionTower.unit l E f)

open ScalarExtensionTower in
/-- Successive extensions use the actual scalar associators.
Source: scalar paragraph, proof steps 6--7; Stacks 03EL, 07A4, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def ScalarComposition (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  type_of% (ScalarExtensionTower.composition l E L ι F j f)

open ScalarExtensionTower in
/-- The actual quotient association, including its balanced section formula.
Source: scalar paragraph, proof steps 6--7; Stacks 03EL, 07A4, 0941
(blueprint: lem-pur-completed-comparison-quotient-realization). -/
def ScalarAssociation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (A : CoefficientExtensionSystems.{u, u} l E L ι Y)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) Y)
    (M N : sfIntegralConstructibleCategory l E Y)
    (P Q : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (_eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (_eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj) : Prop :=
  type_of% (ScalarExtensionTower.quotientModels l E L ι f
    _hX _hY SE SL A A0 M N P Q _eP _eQ)

attribute [local irreducible] ScalarIdentity ScalarComposition ScalarAssociation
  NaturalSubstitution ScalarGood StrictCoherence ScalarLimitImage

attribute [local irreducible] reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end WeilConjectures.CompletedQuotient
