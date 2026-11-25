/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars

/-! # IntegralSystemOperations

Source: Stacks 0941, 03DI, 07A7 and blueprint fix-prop-coherence,
strict-system operations and bounded finite expressions
(blueprint: def-sf-integral-system-operations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded unbounded category of strict semilinear systems.
Source: Stacks 0941 (blueprint: def-sf-integral-system-operations). -/
abbrev System (W : Scheme.{u}) := coefficientSequenceDerived l E W

/-- The recorded completed-coefficient derived category.
Source: Stacks 0941 (blueprint: def-sf-integral-system-operations). -/
abbrev Integral (W : Scheme.{u}) := DerivedCategory (scalarReductionSource l E W)

/-- Exact inverse image on the actual sequence site, with its canonical quotient actions.
Source: Stacks 0941, 03D2
(blueprint: def-sf-integral-system-operations). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := pullbackTensorSequenceDerived l E f

/-- The fixed reconstruction adjunction and its K-flat normalized tensor models.
Source: Stacks 0941, 07A6
(blueprint: def-sf-integral-system-operations). -/
abbrev calculus (W : Scheme.{u}) := pullbackTensorCalculus l E W

/-- Additivity of actual direct image follows from its recorded ordinary adjunction.
Source: Stacks 03D2 (blueprint: def-sf-integral-system-operations). -/
instance sequenceDirectAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceDirect l E f).Additive :=
  (pullbackTensorSequenceAdjunction l E f).right_adjoint_additive

/-- The universal derived image of the actual ordinary sequence-site direct image.
Its transpose equation is the one in the recorded coefficient comparison interface.
Source: Zheng 4.1, 4.10 (blueprint: def-sf-integral-system-operations). -/
structure Direct {X Y : Scheme.{u}} (f : X ⟶ Y) where
  model : SheafOfModules.CoefficientDerivedImage
    (pullbackTensorSequenceInverse l E f) (pullbackTensorSequenceDirect l E f)
    (pullbackTensorSequenceAdjunction l E f)
  inverse : model.inverse ≅ pull l E f
  factors : ∀ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    inverse.hom.app (DerivedCategory.Q.obj P) ≫
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P =
        model.inverseFactors.hom.app P

/-- The actual derived image, retaining its universal right-derived certificate.
Source: Zheng 4.10 (blueprint: def-sf-integral-system-operations). -/
abbrev Direct.direct {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Direct l E f) := d.model.direct

/-- The derived adjunction transported by the exact-inverse-image factorization.
Source: Zheng 4.10 (blueprint: def-sf-integral-system-operations). -/
def Direct.adj {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Direct l E f) :
    pull l E f ⊣ d.direct := d.model.adjunction.ofNatIsoLeft d.inverse

/-- The coefficient-level adjunction obtained from the actual module adjunction.
Source: Zheng 4.10 (blueprint: def-sf-integral-system-operations). -/
def finiteAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteDerivedPullback l E n f ⊣
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  (sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction

/-- Direct-image evaluation, its two adjunction equations, and all adjacent quotient
transitions. The inverse-image comparison is the fixed cochain-normalized one.
Source: Zheng 4.1, 4.10 (blueprint: def-sf-integral-system-operations). -/
structure DirectEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Direct l E f) where
  evaluation : ∀ n : ℕ,
    d.direct ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1))
  unit : ∀ (n : ℕ) (M : System l E Y),
    (coefficientSequenceDerivedEvaluation l E Y n).map (d.adj.unit.app M) ≫
      (evaluation n).hom.app ((pull l E f).obj M) ≫
      (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1))).map
        ((pullbackTensorDerivedEvaluation l E f n).hom.app M) =
    (finiteAdj l E f n).unit.app ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
  counit : ∀ (n : ℕ) (M : System l E X),
    (pullbackTensorDerivedEvaluation l E f n).hom.app (d.direct.obj M) ≫
      (finiteDerivedPullback l E n f).map ((evaluation n).hom.app M) ≫
      (finiteAdj l E f n).counit.app ((coefficientSequenceDerivedEvaluation l E X n).obj M) =
    (coefficientSequenceDerivedEvaluation l E X n).map (d.adj.counit.app M)
  restrictedDirect : ∀ n : ℕ,
    normalizedDVRRes l E X (Nat.le_succ n) ⋙
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
    proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      normalizedDVRRes l E Y (Nat.le_succ n)
  restrictedDirectCanonical : ∀ n : ℕ, HEq (restrictedDirect n)
    (sfDerivedImageRestriction f (Padic.coefficientExtensionTransition l E (n + 1)))
  transition : ∀ (n : ℕ) (M : System l E X),
    (coefficientSequenceDerivedTransition l E Y (Nat.le_succ n)).app (d.direct.obj M) ≫
      (normalizedDVRRes l E Y (Nat.le_succ n)).map ((evaluation n).hom.app M) =
    (evaluation (n + 1)).hom.app M ≫
      (proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 2))).map
          ((coefficientSequenceDerivedTransition l E X (Nat.le_succ n)).app M) ≫
      (restrictedDirect n).hom.app ((coefficientSequenceDerivedEvaluation l E X n).obj M)

/-- Exact termwise extension by zero, specified by its ordinary adjunction to the
actual sequence inverse image. This retains the entire coefficient system.
Source: Stacks 03DI, 0941
(blueprint: def-sf-integral-system-operations). -/
structure Open {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] where
  ordinary : coefficientSequenceModules l E U ⥤ coefficientSequenceModules l E X
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]
  adjunction : ordinary ⊣ pullbackTensorSequenceInverse l E j

attribute [instance] Open.additive Open.limits Open.colimits

/-- Extension by zero descends by the exact-functor factorization.
Source: Stacks 03DI (blueprint: def-sf-integral-system-operations). -/
abbrev Open.derived {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (o : Open l E j) := o.ordinary.mapDerivedCategory

/-- The exact open adjunction is the localization of the ordinary one.
Source: Stacks 03DI (blueprint: def-sf-integral-system-operations). -/
def Open.adj {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (o : Open l E j) : o.derived ⊣ pull l E j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction o.adjunction

/-- The finite open adjunction, localized from its canonical ordinary unit.
Source: Stacks 03DI (blueprint: def-sf-integral-system-operations). -/
def finiteOpenAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⊣
      finiteDerivedPullback l E n j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)

/-- Evaluation of open extension is fixed by the transpose of the canonical inverse
image evaluation map. Source: Stacks 03DI, 0941
(blueprint: def-sf-integral-system-operations). -/
structure OpenEvaluation {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (a : Open l E j) where
  evaluation : ∀ n : ℕ,
    a.derived ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E U n ⋙
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  transpose : ∀ n : ℕ,
    (mateEquiv a.adj (finiteOpenAdj l E j n)).symm
      (pullbackTensorDerivedEvaluation l E j n).hom = (evaluation n).inv

/-- Canonical simultaneous operations on the single ringed sequence site at each scheme.
Functorial right derivation and exact open localization are part of the conclusions,
not extra hypotheses on inputs. Source: Stacks 0941, Zheng Lemma 4.10
(blueprint: def-sf-integral-system-operations). -/
structure Operations where
  direct : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Direct l E f
  evaluation : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), DirectEvaluation l E (direct f)
  extension : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], Open l E j
  openEvaluation : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    OpenEvaluation l E (extension j)

/-- The actual total right derived system image.
Source: Stacks 0941 (blueprint: def-sf-integral-system-operations). -/
abbrev Operations.push (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (o.direct f).direct

/-- The actual exact derived system open extension.
Source: Stacks 03DI, 0941
(blueprint: def-sf-integral-system-operations). -/
abbrev Operations.shriek (o : Operations l E) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] := (o.extension j).derived

/-- Evaluation of the chosen compactification composite, with the actual open and
proper evaluation factors. Source: Stacks 0F7J
(blueprint: def-sf-integral-system-operations). -/
def supportEvaluation (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    (Operations.shriek l E o c.i ⋙ Operations.push l E o c.g) ⋙
      coefficientSequenceDerivedEvaluation l E Y n ≅
    coefficientSequenceDerivedEvaluation l E X n ⋙
      sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((o.evaluation c.g).evaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((o.openEvaluation c.i).evaluation n) _ ≪≫
    Functor.associator _ _ _

/-- Composition is fixed before localization, on sections of the actual sequence site.
The inverse-image comparison is the conjugate of this section map, and the derived
comparison is its class on complexes. These requirements fix the canonical scalar
normalization, rather than merely asserting existence of some natural isomorphism.
Source: Stacks 03D8, 07A7
(blueprint: def-sf-integral-system-operations). -/
structure Compositors (o : Operations l E) where
  ordinaryDirect : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullbackTensorSequenceDirect l E f ⋙ pullbackTensorSequenceDirect l E g ≅
      pullbackTensorSequenceDirect l E (f ≫ g)
  sections : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : coefficientSequenceModules l E X) (n : ℕ) (U : Z.ProEt)
      (x : ((pullbackTensorSequenceDirect l E f ⋙
        pullbackTensorSequenceDirect l E g).obj M).val.obj (op (n, U))),
    ((ordinaryDirect f g).hom.app M).val.app (op (n, U)) x =
      M.val.map (@Quiver.Hom.op (ℕ × X.ProEt) _
        (n, (proEtaleBaseChange (f ≫ g)).obj U)
        (n, (proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U))
        (𝟙 n, (MorphismProperty.Over.pullbackComp f g).hom.app U)) x
  ordinaryPull : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullbackTensorSequenceInverse l E (f ≫ g) ≅
      pullbackTensorSequenceInverse l E g ⋙ pullbackTensorSequenceInverse l E f
  conjugate : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    conjugateIsoEquiv
      ((pullbackTensorSequenceAdjunction l E g).comp
        (pullbackTensorSequenceAdjunction l E f))
      (pullbackTensorSequenceAdjunction l E (f ≫ g)) (ordinaryPull f g) =
        ordinaryDirect f g
  pullComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull l E (f ≫ g) ≅ pull l E g ⋙ pull l E f
  pullComp_model : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (P : CochainComplex (coefficientSequenceModules l E Z) ℤ),
    (pullComp f g).hom.app (DerivedCategory.Q.obj P) ≫
        (pull l E f).map
          ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
        (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
          (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj P) =
      (pullbackTensorSequenceInverse l E (f ≫ g)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryPull f g) (.up ℤ)).hom.app P)

/-- Direct-image compositors are exactly conjugate to the fixed inverse-image ones.
Source: Stacks 07A7 (blueprint: def-sf-integral-system-operations). -/
def Compositors.pushComp {o : Operations l E} (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Operations.push l E o f ⋙ Operations.push l E o g ≅ Operations.push l E o (f ≫ g) :=
  conjugateIsoEquiv ((o.direct g).adj.comp (o.direct f).adj)
    (o.direct (f ≫ g)).adj (c.pullComp f g)

/-- Open compositors are the specified conjugates under the open adjunctions.
Source: Stacks 03DI, 07A7
(blueprint: def-sf-integral-system-operations). -/
def Compositors.openComp {o : Operations l E} (c : Compositors l E o)
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    Operations.shriek l E o j ⋙ Operations.shriek l E o k ≅ Operations.shriek l E o (j ≫ k) :=
  Adjunction.leftAdjointCompIso (o.extension j).adj (o.extension k).adj
    (o.extension (j ≫ k)).adj (c.pullComp j k).symm

/-- The inverse-image comparison around a commutative square.
Source: Stacks 07A7 (blueprint: def-sf-integral-system-operations). -/
def Compositors.square {o : Operations l E} (c : Compositors l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) : pull l E i ⋙ pull l E r ≅ pull l E p ⋙ pull l E k :=
  (c.pullComp r i).symm ≪≫ eqToIso (congrArg (pull l E) h.symm) ≪≫ c.pullComp k p

/-- The left side of the open projection comparison.
Source: Stacks 0E8I (blueprint: def-sf-integral-system-operations). -/
def openTensorLeft (o : Operations l E) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : System l E U × System l E X ⥤ System l E X :=
  (Operations.shriek l E o j).prod (𝟭 _) ⋙ (calculus l E X).systemClosed.tensor

/-- The right side of the open projection comparison, with restriction in its second slot.
Source: Stacks 0E8I (blueprint: def-sf-integral-system-operations). -/
def openTensorRight (o : Operations l E) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : System l E U × System l E X ⥤ System l E X :=
  (𝟭 _).prod (pull l E j) ⋙ (calculus l E U).systemClosed.tensor ⋙
    Operations.shriek l E o j

/-- Open comparisons with precisely their open-unit normalizations. The base-change
comparison is indexed by a cartesian square. Its inverse, and the inverse projection
comparison, are fixed by the displayed adjunction transposes. The clopen comparison
uses the inverse of the open unit under the direct-image adjunction.
Source: Stacks 03DI, 09AE, 0E8I; blueprint fix-prop-coherence
(blueprint: def-sf-integral-system-operations). -/
structure OpenComparisons (o : Operations l E) (c : Compositors l E o) where
  unitIso : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : System l E U), IsIso ((o.extension j).adj.unit.app M)
  beta : ∀ {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (_h : a ≫ j = j' ≫ g) (_sq : IsPullback a j' j g),
    Operations.shriek l E o j ⋙ pull l E g ≅ pull l E a ⋙ Operations.shriek l E o j'
  beta_transpose : ∀ {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) (M : System l E U),
    ((o.extension j').adj.homEquiv _ _) ((beta a j' j g h sq).inv.app M) =
      (pull l E a).map ((o.extension j).adj.unit.app M) ≫
        (c.square l E a j' j g h).inv.app ((Operations.shriek l E o j).obj M)
  projection : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    openTensorLeft l E o j ≅ openTensorRight l E o j
  projection_transpose : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : System l E U) (N : System l E X),
    ((o.extension j).adj.homEquiv _ _) ((projection j).inv.app (M, N)) =
      (calculus l E U).systemClosed.tensor.map
        (Prod.mkHom ((o.extension j).adj.unit.app M) (𝟙 ((pull l E j).obj N))) ≫
      (pullbackTensorSystemComparison l E j).inv.app
        ((Operations.shriek l E o j).obj M, N)
  clopen : ∀ {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j],
    Operations.shriek l E o j ≅ Operations.push l E o j
  clopen_transpose : ∀ {U X : Scheme.{u}} (j : U ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion j] (M : System l E U),
    (clopen j).hom.app M =
      ((o.direct j).adj.homEquiv _ _)
        (@inv _ _ _ _ ((o.extension j).adj.unit.app M) (unitIso j M))

/-- Canonical open-unit isomorphism, assembled from its actual components.
Source: Stacks 03DI (blueprint: def-sf-integral-system-operations). -/
def OpenComparisons.unit (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : 𝟭 (System l E U) ≅
      Operations.shriek l E o j ⋙ pull l E j :=
  NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ ((o.extension j).adj.unit.app M)
    (a.unitIso j M)) (fun f ↦ (o.extension j).adj.unit.naturality f)

/-- Open-extension equality transport is fixed by the inverse-image adjunction.
Source: Stacks 03DI (blueprint: def-sf-integral-system-operations). -/
def openCongr (o : Operations l E) {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    Operations.shriek l E o f ≅ Operations.shriek l E o g :=
  (o.extension f).adj.leftAdjointUniq
    ((o.extension g).adj.ofNatIsoRight (eqToIso (congrArg (pull l E) h.symm)))

/-- Open restriction of direct image is conjugate to the normalized open base change.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-operations). -/
def cartesianConjugate (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion i] :
    Operations.push l E o p ⋙ pull l E i ≅
      pull l E (pullback.fst p i) ⋙ Operations.push l E o (pullback.snd p i) :=
  conjugateIsoEquiv ((o.extension i).adj.comp (o.direct p).adj)
    ((o.direct (pullback.snd p i)).adj.comp (o.extension (pullback.fst p i)).adj)
    (a.beta (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).symm

/-- Restriction of k-extension to the pulled-back open is s-extension. The inverse
open unit fixes this identification, including the empty open.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-operations). -/
def restrictFactor (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Operations.shriek l E o k ⋙ pull l E (pullback.fst p i) ≅
      Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((c.openComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)) ≪≫
      openCongr l E o (pullback.lift_fst k r h)).symm (pull l E (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (Operations.shriek l E o
    (ProEtale.StrictTower.squareLift k r p i h)) (a.unit l E o c (pullback.fst p i)).symm ≪≫
  Functor.rightUnitor _

/-- The prescribed lambda: restrict p, factor k through its clopen lift s, identify
J_s with S_s using the open unit, and compose the direct images.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-operations). -/
def properOpenLambda (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    (Operations.shriek l E o k ⋙ Operations.push l E o p) ⋙ pull l E i ≅
      Operations.push l E o r :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (Operations.shriek l E o k) (cartesianConjugate l E o c a p i) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (restrictFactor l E o c a k r p i h)
    (Operations.push l E o (pullback.snd p i)) ≪≫
  Functor.isoWhiskerRight (a.clopen (ProEtale.StrictTower.squareLift k r p i h))
    (Operations.push l E o (pullback.snd p i)) ≪≫
  c.pushComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i) ≪≫
  eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h))

/-- A finite-type compactified arrow has a quasi-compact open factor, by cancellation
of quasi-compactness against the separated proper factor. Source: Stacks 01K5
(blueprint: def-sf-integral-system-operations). -/
abbrev compactOpenQuasiCompact {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) (h : QuasiCompact f) : QuasiCompact d.i :=
  @QuasiCompact.of_comp X d.Z Y d.i d.g (d.comm ▸ h) inferInstance

end IntegralSystemRealization
end WeilConjectures
