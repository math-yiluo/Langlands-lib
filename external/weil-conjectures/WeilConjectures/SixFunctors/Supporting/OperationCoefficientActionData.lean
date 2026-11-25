/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SixFunctors.Integral.IntegralCompactSupportPrescribedReductions
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Field.Shrink
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralHomReduction
public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction

/-! # Basic operations and coefficient reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-pf-reduction/lem-fix-operation-reduction.md
(blueprint: proposition-six-operations-change-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe d t u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The scalar direct-image comparison is the prescribed proper projection mate.
Its components are natural in the input, including zero objects and identity field maps.
Source: blueprint main-20261015, proof step 8 (blueprint:
proposition-six-operations-change-coefficients). -/
def directImageScalarExtensionLaws (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X)),
    sfIntegralConstructible l E X M →
      IsIso ((PurCompactSupport.properComparison
      (PurCompactSupport.completedChange l E L ι) f).app M)

/-- Integral compact-support scalar comparison on its stated constructible domain.
The map is the actual proper/open mate, not a chosen isomorphism.
Source: blueprint proof step 8 (blueprint: proposition-six-operations-change-coefficients). -/
def compactSupportScalarIsomorphisms (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X)),
    sfIntegralConstructible l E X M →
      IsIso ((PurCompactSupport.comparison
        (PurCompactSupport.completedChange l E L ι) c).app M)

/-- Both geometric-adjunction equations for the actual coefficient mate, for finite
reductions and integral scalar extension alike. The inverse scalar-pullback comparison
is the map a of proof step 10. Source: Stacks 07A6
(blueprint: proposition-six-operations-change-coefficients). -/
def coefficientOperationMateEquations : Prop :=
  ∀ {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    let AR := proEtaleRingDerivedAdjunction f (R.ring Y) (R.ring X) (R.pull f)
    let AS := proEtaleRingDerivedAdjunction f (S.ring Y) (S.ring X) (S.pull f)
    (∀ K : DerivedCategory (proEtaleRingModules X (R.ring X)),
      (PurCompactSupport.pull S f).map ((PurCompactSupport.properComparison a f).app K) ≫
          AS.counit.app ((pbcDerivedExtend (a.map X)).obj K) =
        (PurCompactSupport.scalarPull a f).inv.app ((PurCompactSupport.push R f).obj K) ≫
          (pbcDerivedExtend (a.map X)).map (AR.counit.app K)) ∧
    (∀ N : DerivedCategory (proEtaleRingModules Y (R.ring Y)),
      AS.unit.app ((pbcDerivedExtend (a.map Y)).obj N) ≫
          (PurCompactSupport.push S f).map ((PurCompactSupport.scalarPull a f).inv.app N) =
        (pbcDerivedExtend (a.map Y)).map (AR.unit.app N) ≫
          (PurCompactSupport.properComparison a f).app ((PurCompactSupport.pull R f).obj N))

/-- The compact-support scalar-extension laws are the canonical proper/open
comparison composition laws.  They include naturality, identity and tower
compatibility through `comparison_composition` and `comparison_identity`.
Source: Stacks Tags 07A6, 0E8I (blueprint: proposition-six-operations-change-coefficients). -/
def purCompactSupportScalarExtensionLaws : Prop :=
  ∀ {R S T : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) (b : PurCompactSupport.Change S T)
    (d : PurCompactSupport.Change R T)
    (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (proEtaleRingModules X (R.ring X))),
    (pbcDerivedExtend (b.map Y)).map ((PurCompactSupport.comparison a c).app M) ≫
        (PurCompactSupport.comparison b c).app
          ((pbcDerivedExtend (a.map X)).obj M) ≫
        (PurCompactSupport.image T c).map
          ((PurCompactSupport.tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (PurCompactSupport.tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((PurCompactSupport.image R c).obj M) ≫
        (PurCompactSupport.comparison d c).app M

/-- Tower coherence for the actual ordinary direct-image mates, including every
three-field scalar tower. Source: blueprint proof steps 8 and 10
(blueprint: proposition-six-operations-change-coefficients). -/
def directImageScalarTowerLaws : Prop :=
  ∀ {R S T : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) (b : PurCompactSupport.Change S T)
    (d : PurCompactSupport.Change R T)
    (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (proEtaleRingModules X (R.ring X))),
    (pbcDerivedExtend (b.map Y)).map ((PurCompactSupport.properComparison a f).app M) ≫
        (PurCompactSupport.properComparison b f).app
          ((pbcDerivedExtend (a.map X)).obj M) ≫
        (PurCompactSupport.push T f).map
          ((PurCompactSupport.tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (PurCompactSupport.tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((PurCompactSupport.push R f).obj M) ≫
        (PurCompactSupport.properComparison d f).app M

/-- Identity normalization of direct-image and compact-support mates with the
canonical multiplication unitor. Source: blueprint proof steps 8 and 10
(blueprint: proposition-six-operations-change-coefficients). -/
def coefficientOperationIdentityLaws : Prop :=
  ∀ {R : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R R)
    (h : ∀ W : Scheme.{u}, a.map W = 𝟙 (R.ring W))
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    (∀ M : DerivedCategory (proEtaleRingModules X (R.ring X)),
      (PurCompactSupport.properComparison a f).app M ≫
          (PurCompactSupport.push R f).map
            ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h X)) ≪≫
              PurCompactSupport.tensorIdentity (R.ring X)).hom.app M) =
        (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h Y)) ≪≫
          PurCompactSupport.tensorIdentity (R.ring Y)).hom.app
            ((PurCompactSupport.push R f).obj M)) ∧
    ∀ (c : Compactification f)
      (M : DerivedCategory (proEtaleRingModules X (R.ring X))),
      (PurCompactSupport.comparison a c).app M ≫
          (PurCompactSupport.image R c).map
            ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h X)) ≪≫
              PurCompactSupport.tensorIdentity (R.ring X)).hom.app M) =
        (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (h Y)) ≪≫
          PurCompactSupport.tensorIdentity (R.ring Y)).hom.app
            ((PurCompactSupport.image R c).obj M)

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open scoped TensorProduct

/-- The integral stage associator is the published balanced-tensor associator,
transported along the actual composition law of the coefficient inclusions.
Source: blueprint proof step 8 (blueprint: proposition-six-operations-change-coefficients). -/
def operationIntegralStageAssociator
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    integralTransition l Ω W E L h ⋙ integralTransition l Ω W L M k ≅
      integralTransition l Ω W E M (h.trans k) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
  eqToIso (congrArg
    (fun ι ↦ sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω M) ι W)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k))

/-- The integral stage unit is normalized by ordinary multiplication and completion.
Source: blueprint proof step 8 (blueprint: proposition-six-operations-change-coefficients). -/
def operationIntegralStageUnit
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u}) (E : Index l Ω) :
    integralTransition l Ω W E E (le_refl E) ≅
      𝟭 (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :=
  eqToIso (congrArg
    (fun ι ↦ sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω E) ι W)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
    sfIntegralScalarUnit l (Coefficient.{u} l Ω E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- Naturality is built into the natural isomorphisms; these are the identity and
three-field tower equations on those same comparisons, including repeated stages.
Source: blueprint proof steps 8--10 (blueprint: proposition-six-operations-change-coefficients). -/
def operationIntegralCoefficientCoherent
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X Y : Scheme.{u})
    (F : ∀ E : Index l Ω, sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (β : ∀ {E L : Index l Ω} (h : E ≤ L),
      F E ⋙ integralTransition l Ω Y E L h ≅ integralTransition l Ω X E L h ⋙ F L) : Prop :=
  (∀ (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X),
    (β (le_refl E)).hom.app K ≫
        (F E).map ((operationIntegralStageUnit l Ω X E).hom.app K) =
      (operationIntegralStageUnit l Ω Y E).hom.app ((F E).obj K)) ∧
  ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X),
    (integralTransition l Ω Y L M k).map ((β h).hom.app K) ≫
        (β k).hom.app ((integralTransition l Ω X E L h).obj K) ≫
        (F M).map ((operationIntegralStageAssociator l Ω X E L M h k).hom.app K) =
      (operationIntegralStageAssociator l Ω Y E L M h k).hom.app ((F E).obj K) ≫
        (β (h.trans k)).hom.app K

/-- Canonical identification of the two published ordinary scalar models. Its
module map sends every sheafified pure tensor to that same pure tensor. Its derived
map is fixed by the universal derived counit on every cochain representative. Thus
this transport is determined, rather than an arbitrary equivalence of categories.
Source: Stacks 03EK, 06YY; blueprint proof step 8
(blueprint: proposition-six-operations-change-coefficients). -/
structure OperationScalarTransport (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) where
  ordinary : integralOrdinaryScalar l E L ι W ≅ pbcExtend (completedCoefficientMap l E L ι W)
  tensor : ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U (integralOrdinaryTensorSection l E L ι W M U s x) =
      pbcTensorSection (completedCoefficientMap l E L ι W) M U s x
  derived : integralOrdinaryDerivedScalar l E L ι W ≅
    pbcDerivedExtend (completedCoefficientMap l E L ι W)
  counit : letI := pbcExtend_additive (completedCoefficientMap l E L ι W)
    ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        pbcComplexCounit (completedCoefficientMap l E L ι W) P =
      (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)

/-- The specified ordinary model transport, restricted to the intrinsic category.
Source: blueprint proof step 8 (blueprint: proposition-six-operations-change-coefficients). -/
def operationConstructibleScalarTransport (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (T : OperationScalarTransport l E L ι W) :
    sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W ⋙ (sfIntegralConstructible l L W).ι ≅
      (sfIntegralConstructible l E W).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E L ι W) :=
  (sfIntegralOrdinaryComparison l E L ι W).symm ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible l E W).ι T.derived

/-- Ordinary direct image at integral, rational and common finite coefficient stages.
The ambient realization is the actual completed-ring direct image. The integral
coefficient map is fixed by the proper scalar mate and the ordinary-to-completed
normalizations. The rational family is fixed on unchanged objects and pure tensors;
its coefficient maps are the localized integral maps. Its `system.coh` is the tower
law and `system.functor` is the prescribed common-stage conjugation on representatives.
Source: blueprint main-20261015, proof steps 4, 8 and 9
(blueprint: proposition-six-operations-change-coefficients). -/
def OperationDirectImageCoefficientAction
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X Y : Scheme.{u}) (f : X ⟶ Y) : Prop :=
  ∃ (integral : ∀ E : Index l Ω,
    sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (ambient : ∀ E : Index l Ω,
    integral E ⋙ (sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E) X).ι ⋙
        PurCompactSupport.push (PurCompactSupport.completed l (Coefficient.{u} l Ω E)) f)
    (integralBeta : ∀ {E L : Index l Ω} (h : E ≤ L),
    integral E ⋙ integralTransition l Ω Y E L h ≅
      integralTransition l Ω X E L h ⋙ integral L),
    operationIntegralCoefficientCoherent l Ω X Y integral integralBeta ∧
  ∃ scalarTransport : ∀ {E L : Index l Ω} (h : E ≤ L) (W : Scheme.{u}),
    OperationScalarTransport l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) W,
  (∀ {E L : Index l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X),
    HEq ((operationConstructibleScalarTransport l
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y
      (scalarTransport (E := E) (L := L) h Y)).inv.app
        ((integral E).obj K) ≫
      ((sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.map
        ((integralBeta (E := E) (L := L) h).hom.app K)) ≫
        (ambient L).hom.app ((integralTransition l Ω X E L h).obj K) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l (Coefficient.{u} l Ω L)) f).map
          ((operationConstructibleScalarTransport l
            (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) X
            (scalarTransport (E := E) (L := L) h X)).hom.app K))
      ((pbcDerivedExtend (completedCoefficientMap l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) Y)).map
        ((ambient E).hom.app K) ≫
        (PurCompactSupport.properComparison (PurCompactSupport.completedChange l
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h)) f).app
          K.obj)) ∧
  ∃ system : (stageSystem l Ω X).Morphism (stageSystem l Ω Y),
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (system.Φ E).obj K = ⟨(integral E).obj K.obj⟩) ∧
  (∀ (E : Index l Ω)
    (K L : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (a : K ⟶ L)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))),
    HEq ((system.Φ E).map (c ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)] a :
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj K ⟶
        (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj L))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)] (integral E).map a)) ∧
  (∀ {E L : Index l Ω} (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((system.β h).hom.app K)
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
        ((integralBeta h).hom.app K.obj))) ∧
  ∀ (E : Index l Ω) (K : Stage l Ω X E),
    (system.β (le_refl E)).hom.app K ≫
        (system.Φ E).map
          ((operationStageTransitionIso l Ω X E E (le_refl E)).hom.app K ≫
            (unitor l Ω X E).hom.app K) =
      (operationStageTransitionIso l Ω Y E E (le_refl E)).hom.app ((system.Φ E).obj K) ≫
        (unitor l Ω Y E).hom.app ((system.Φ E).obj K)

/-! This proposition records the named canonical arrows themselves. Every
finite reduction arrow is indexed by `m ≤ n`, including equality, and the
finite tensor assertion is made only on the bounded finite-Tor domain supplied
by its hypotheses. -/
end WeilConjectures
