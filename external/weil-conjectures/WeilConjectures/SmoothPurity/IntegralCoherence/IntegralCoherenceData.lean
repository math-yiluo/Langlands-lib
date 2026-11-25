/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
/-! # Integral coherence before and after the derived limit

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0941;
blueprint main-20261015, coefficient twists, simultaneous strict quotient-tower extraction
(blueprint: lem-pur-integral-coherence-tower).

The ringed sequence site encodes strict semilinear quotient towers. Thus every
cochain map below commutes with every quotient transition before localization.
The index n denotes the positive exponent n+1; there is no boundedness condition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Strict quotient systems of unbounded cochains, not towers in a derived category.
Source: Stacks 0941 (blueprint: lem-pur-integral-coherence-tower). -/
abbrev Complex (W : Scheme.{t}) := CochainComplex (coefficientSequenceModules l E W) ℤ

local instance sequenceMonoidal (V : Scheme.{t}) :
    MonoidalCategory (coefficientSequenceModules l E V) :=
  SheafOfModules.cochainModulesMonoidal (coefficientSequenceCommRingSheaf l E V)
local instance sequencePreadditive (V : Scheme.{t}) :
    MonoidalPreadditive (coefficientSequenceModules l E V) :=
  SheafOfModules.cochainModulesPreadditive (coefficientSequenceCommRingSheaf l E V)
local instance sequenceColimits (V : Scheme.{t}) :
    HasColimitsOfSize.{0, 0} (coefficientSequenceModules l E V) := by
  with_unfolding_all infer_instance
local instance sequenceLeftColim (V : Scheme.{t}) (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits (coefficientSequenceCommRingSheaf l E V) M
local instance sequenceRightColim (V : Scheme.{t}) (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits (coefficientSequenceCommRingSheaf l E V) M
local instance sequenceTensor (V : Scheme.{t})
    (X Y : GradedObject ℤ (coefficientSequenceModules l E V)) : X.HasTensor Y := inferInstance
local instance sequenceFour (V : Scheme.{t})
    (X Y Z U : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasTensor₄ObjExt X Y Z U := inferInstance
local instance sequenceLeft (V : Scheme.{t})
    (X Y Z : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
local instance sequenceRight (V : Scheme.{t})
    (X Y Z : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
local instance complexMonoidal (V : Scheme.{t}) :
    MonoidalCategory (Complex l E V) := inferInstance

/-- The actual termwise inverse image on the sequence site.
Source: Stacks 07A4 (blueprint: lem-pur-integral-coherence-tower). -/
abbrev pull {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)

/-- The adjunction-normalized composition map, lifted termwise before localization.
Source: Stacks 0D6D, 07A4 (blueprint: lem-pur-integral-coherence-tower). -/
def compositor {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y) :
    pull l E (h ≫ f) ≅ pull l E f ⋙ pull l E h :=
  (Functor.mapHomologicalComplexCompIso
    (integralComparisonSequenceComposition l E h f).symm (.up ℤ)).symm

/-- The actual adjunction-unit generator, read as a section on the base-changed object.
Source: Stacks 03D2 (blueprint: lem-pur-integral-coherence-tower). -/
def generator {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback l E f).obj M).val.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)) :=
  integralComparisonSequenceGenerator l E f M n U x

/-- The normalized total comparison on strict systems. Its generator equation fixes
c on 1 tensor (x tensor y); linearity gives the stated s tensor formula, and the
inverse contracts the two scalars. Units are fixed by the action equations below.
Source: Stacks 07A4, 03EL (blueprint: lem-pur-integral-coherence-tower). -/
structure PullbackComparison {X Y : Scheme.{t}} (f : X ⟶ Y)
    extends (pull l E f).CoreMonoidal where
  generators : ∀ (P Q : Complex l E Y) (p q k : ℤ) (hpq : p + q = k)
    (n : ℕ) (U : Y.ProEt) (x : (P.X p).val.obj (op (n, U)))
    (y : (Q.X q).val.obj (op (n, U))),
    ((μIso P Q).inv.f k).val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
      (generator l E f ((P ⊗ Q).X k) n U
        (coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) P Q p q k hpq (op (n, U)) x y)) =
      coefficientTensorGenerator.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        ((pull l E f).obj P) ((pull l E f).obj Q) p q k hpq
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (generator l E f (P.X p) n U x)
        (generator l E f (Q.X q) n U y)

/-- The forward cochain comparison; CoreMonoidal records its naturality,
associativity and both action-unit equations in the inverse orientation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-coherence-tower). -/
def PullbackComparison.tensor {X Y : Scheme.{t}} {f : X ⟶ Y}
    (c : PullbackComparison l E f) (P Q : Complex l E Y) := (c.μIso P Q).symm

/-- The action-unit identification, with the coefficient in degree zero.
Source: Stacks 03EL (blueprint: lem-pur-integral-coherence-tower). -/
def PullbackComparison.unit {X Y : Scheme.{t}} {f : X ⟶ Y}
    (c : PullbackComparison l E f) := c.εIso.symm

/-- Signed symmetry for the same CoreMonoidal comparison. Its other fields
are exactly the naturality, associativity and two action-unit equations.
Source: Stacks 07A4 (blueprint: lem-pur-integral-coherence-tower). -/
def Coherent {X Y : Scheme.{t}} (f : X ⟶ Y) (c : PullbackComparison l E f) : Prop :=
  ∀ P Q : Complex l E Y,
    (pull l E f).map (CochainComplex.Monoidal.braiding P Q).hom ≫ (c.tensor l E Q P).hom =
      (c.tensor l E P Q).hom ≫
        (CochainComplex.Monoidal.braiding ((pull l E f).obj P) ((pull l E f).obj Q)).hom

/-- The composition identity with the prescribed adjunction-normalized compositor.
Source: Stacks 07A4, 0D6D (blueprint: lem-pur-integral-coherence-tower). -/
def CompositionLaw {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (cf : PullbackComparison l E f) (ch : PullbackComparison l E h)
    (chf : PullbackComparison l E (h ≫ f)) : Prop :=
  ∀ P Q : Complex l E Y,
    (chf.tensor l E P Q).hom ≫
        ((compositor l E h f).hom.app P ⊗ₘ (compositor l E h f).hom.app Q) =
      (compositor l E h f).hom.app (P ⊗ Q) ≫
        (pull l E h).map (cf.tensor l E P Q).hom ≫
          (ch.tensor l E ((pull l E f).obj P) ((pull l E f).obj Q)).hom

variable {S : Type s} {W : S → Scheme.{t}}

/-- A finite expression evaluated on strict quotient complexes. The syntax is the
recorded completed-operation syntax; only its interpretation changes here.
Source: node first two paragraphs, Stacks 07A4 and 0941
(blueprint: lem-pur-integral-coherence-tower). -/
def value {I : Type i} {location : I → S}
    (N : ∀ k : I, Complex l E (W (location k))) {a : S} :
    CompletedOperations.Expression W location a → Complex l E (W a)
  | .input k => N k
  | .unit _ => 𝟙_ _
  | .tensor P Q => value N P ⊗ value N Q
  | .pullback f P => (pull l E f).obj (value N P)

/-- K-flatness with flat terms in the recorded independent-coefficient interface.
This predicate merely joins the two hypotheses, without defining either again.
Source: Stacks 06YN, 07A4 (blueprint: lem-pur-integral-coherence-tower). -/
def Good (a : S) (P : Complex l E (W a)) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E (W a)) P ∧
    ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
      (R := coefficientSequenceCommRingSheaf l E (W a)) (P.X k)

/-- Interpret the named structural maps on strict cochain systems, including their
inverses and contexts. Symmetry is the existing Koszul-signed cochain braiding.
Source: Stacks 07A4 and 0D6D (blueprint: lem-pur-integral-coherence-tower). -/
def structuralValue {I : Type i} {location : I → S}
    (N : ∀ k : I, Complex l E (W (location k))) {a : S}
    {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q) : value l E N P ≅ value l E N Q :=
  match α with
  | .associator P Q H => α_ (value l E N P) (value l E N Q) (value l E N H)
  | .leftUnitor P => λ_ (value l E N P)
  | .rightUnitor P => ρ_ (value l E N P)
  | .symmetry P Q => CochainComplex.Monoidal.braiding (value l E N P) (value l E N Q)
  | .composition h f P => (compositor l E h f).app (value l E N P)
  | .identity _ => Iso.refl _
  | .inverse α => (structuralValue N α).symm
  | .compose α β => structuralValue N α ≪≫ structuralValue N β
  | .tensor α β => tensorIso (structuralValue N α) (structuralValue N β)
  | .pullback f α => (pull l E f).mapIso (structuralValue N α)

/-- The simultaneous realization of every finite strict expression. The recursive
normalizations fix its vertices and structural arrows; the completed and reduction
isomorphisms are pinned by the coherent counit, including quotient transitions.
Source: node last paragraph, Stacks 07A4 and 0941
(blueprint: lem-pur-integral-coherence-tower). -/
structure Realization (M : CompletedOperations.Models l E W)
    {I : Type i} {location : I → S} (N : ∀ k : I, Complex l E (W (location k))) where
  good : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    Good l E (W := W) a (value l E N P)
  normalized : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    IsNormalizedCoefficientSequence l E (W a) (DerivedCategory.Q.obj (value l E N P))
  system : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    DerivedCategory.Q.obj (value l E N P) ≅
      (CompletedOperations.systemValue l E M P).obj (fun k ↦ DerivedCategory.Q.obj (N k))
  system_input : ∀ k : I, system (.input k) = Iso.refl _
  system_unit : ∀ a : S, system (.unit a) = (by
    exact (show DerivedCategory.Q.obj (value l E N (.unit a)) ≅
      CompletedOperations.unit l E (W := W) a from
      (by with_unfolding_all exact Iso.refl (CompletedOperations.unit l E (W := W) a))))
  system_tensor : ∀ {a : S} (P Q : CompletedOperations.Expression W location a),
    system (.tensor P Q) =
      CoefficientTensorModels.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
        (coefficientSequenceCommRingSheaf l E (W a)) (M.system a).closed (M.system a).models
        (value l E N P) (value l E N Q) (good P).1 (good Q).1 ≪≫
      (CompletedOperations.tensor l E M a).mapIso (Iso.prod (system P) (system Q))
  system_pullback : ∀ {a b : S} (f : W a ⟶ W b)
    (P : CompletedOperations.Expression W location b),
    system (.pullback f P) =
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app
        (value l E N P)).symm ≪≫
        (integralComparisonDerivedSequencePullback l E f).mapIso (system P)
  structural : ∀ {a : S} {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q),
    DerivedCategory.Q.map (structuralValue l E N α).hom ≫ (system Q).hom =
      (system P).hom ≫ (CompletedOperations.structuralValue l E M α
        (fun k ↦ DerivedCategory.Q.obj (N k))).hom
  completed : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    (CompletedOperations.completedValue l E P).obj
        (fun k ↦ (coefficientSequenceLimit l E _).obj (DerivedCategory.Q.obj (N k))) ≅
      (coefficientSequenceLimit l E (W a)).obj (DerivedCategory.Q.obj (value l E N P))
  completed_normalization : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    (completed P).hom ≫ (coefficientSequenceLimit l E (W a)).map (system P).hom =
      CompletedOperations.comparison l E M P (fun k ↦ DerivedCategory.Q.obj (N k))
  reduction : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    (M.calculus a).reduction.obj
        ((CompletedOperations.completedValue l E P).obj
          (fun k ↦ (coefficientSequenceLimit l E _).obj (DerivedCategory.Q.obj (N k)))) ≅
      DerivedCategory.Q.obj (value l E N P)
  reduction_normalization : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    (reduction P).hom = (M.calculus a).reduction.map (completed P).hom ≫
      (M.calculus a).adjunction.counit.app (DerivedCategory.Q.obj (value l E N P))

end WeilConjectures.IntegralCoherence
