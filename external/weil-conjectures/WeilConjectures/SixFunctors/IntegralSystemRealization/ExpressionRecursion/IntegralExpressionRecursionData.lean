/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralBasicRealization
public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionStatement

/-! # Recursion for integral expression comparisons

Source: blueprint main-20261015, fix-prop-coherence.proof.md, coefficient-comparison
sentence; the expression-tree refinement in the DAG
(blueprint: lem-sf-integral-expression-recursion).

The comparison data below are the given primitive comparisons, restricted to the
published intermediate domains. All coefficient equalities live in the derived
category of strict systems. No structural-generator coherence is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
namespace ExpressionRecursion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A single unary constructor, with precisely the permitted arrow hypotheses.
Source: fix-prop-coherence, expression-tree refinement
(blueprint: lem-sf-integral-expression-recursion). -/
inductive Unary (B : Scheme.{u}) : Over B → Over B → Type (u + 1) where
  | pull {U V : Over B} (f : U ⟶ V) (hs : IsSeparated f.left)
      (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left) : Unary B V U
  | push {U V : Over B} (p : U ⟶ V) (hp : IsProper p.left) : Unary B U V
  | shriek {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hqc : QuasiCompact j.left) : Unary B U V

/-- The actual system functor of a unary constructor.
Source: fix-prop-coherence (blueprint: lem-sf-integral-expression-recursion). -/
def Unary.system (o : Operations l E) {B : Scheme.{u}} {U V : Over B} :
    Unary B U V → System l E U.left ⥤ System l E V.left
  | .pull f _ _ _ => IntegralSystemRealization.pull l E f.left
  | .push p _ => Operations.push l E o p.left
  | .shriek j hj _ =>
    letI := hj
    Operations.shriek l E o j.left

/-- The prescribed completed/integral interpretation of the same constructor.
Source: fix-prop-coherence (blueprint: lem-sf-integral-expression-recursion). -/
def Unary.integral {B : Scheme.{u}} {U V : Over B} :
    Unary B U V → Integral l E U.left ⥤ Integral l E V.left
  | .pull f _ _ _ => integralDerivedPullback l E f.left
  | .push p _ => ringedPush l E p.left
  | .shriek j hj _ =>
    letI := hj
    ringedOpen l E j.left

/-- The prescribed primitive realization map before restricting its domain.
The actual inverse is used on the complete domain; its ambient value is irrelevant.
Source: fix-prop-coherence, primitive comparison refinement
(blueprint: lem-sf-integral-expression-recursion). -/
def Unary.primitiveHom (o : Operations l E) (model : RealizationModel l E o)
    {B : Scheme.{u}} {U V : Over B} (a : Unary B U V) (K : Integral l E U.left) :
    (coefficientSequenceLimit l E V.left).obj
      ((a.system l E o).obj ((calculus l E U.left).reduction.obj K)) ⟶
        (a.integral l E).obj K :=
  match a with
  | .pull f _ _ _ => (pullbackTensorIntegralPullbackModel l E f.left).inv.app K
  | .push p _ =>
    (model.push l E p.left).hom.app ((calculus l E U.left).reduction.obj K) ≫
      (ringedPush l E p.left).map
        (GeneratorReduction.inverseOrZero ((calculus l E U.left).adjunction.unit.app K))
  | .shriek j hj _ =>
    letI := hj
    (coefficientSequenceLimit l E V.left).map ((model.openReduction l E j.left).app K) ≫
      GeneratorReduction.inverseOrZero
        ((calculus l E V.left).adjunction.unit.app ((ringedOpen l E j.left).obj K))

/-- The given natural primitive comparisons d_A and r_A, and their assumed whole-system
transpose identities. The compactification comparison is pinned by the recorded
Roos projections and finite scalar-adjunction mates, as in basic realization.
Source: fix-prop-coherence, hypotheses of the expression-tree refinement
(blueprint: lem-sf-integral-expression-recursion). -/
structure Primitives (D : FiniteFieldDatum.{u}) (o : Operations l E) where
  model : RealizationModel l E o
  unary : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom],
    basicUnarySource l E U.left V.left (a.system l E o) ≅
      basicUnaryTarget l E U.left V.left (a.system l E o) (a.integral l E)
  unary_spec : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (K : (basicUnaryDomain l E U.left V.left (a.system l E o)).FullSubcategory),
    (unary a).hom.app K = a.primitiveHom l E o model K.obj
  unaryReduction : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V),
    a.integral l E ⋙ (calculus l E V.left).reduction ⟶
      (calculus l E U.left).reduction ⋙ a.system l E o
  unaryTranspose : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (K : (basicUnaryDomain l E U.left V.left (a.system l E o)).FullSubcategory),
    (unaryReduction a).app K.obj =
      (calculus l E V.left).reduction.map ((unary a).inv.app K) ≫
        (calculus l E V.left).adjunction.counit.app
          ((a.system l E o).obj ((calculus l E U.left).reduction.obj K.obj))
  tensor : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    (basicTensorDomain l E W.left).ι ⋙
        (calculus l E W.left).reduction.prod (calculus l E W.left).reduction ⋙
          (calculus l E W.left).systemClosed.tensor ⋙ coefficientSequenceLimit l E W.left ≅
      (basicTensorDomain l E W.left).ι ⋙ integralCompletedTensor l E W.left
  tensor_spec : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    tensor W = Functor.isoWhiskerLeft (basicTensorDomain l E W.left).ι
      (pullbackTensorIntegralTensorModel l E W.left).symm
  tensorReduction : ∀ (W : Over (Spec (.of D.k))),
    integralCompletedTensor l E W.left ⋙ (calculus l E W.left).reduction ⟶
      (calculus l E W.left).reduction.prod (calculus l E W.left).reduction ⋙
        (calculus l E W.left).systemClosed.tensor
  tensorTranspose : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (K : (basicTensorDomain l E W.left).FullSubcategory),
    (tensorReduction W).app K.obj =
      (calculus l E W.left).reduction.map ((tensor W).inv.app K) ≫
        (calculus l E W.left).adjunction.counit.app
          ((calculus l E W.left).systemClosed.tensor.obj
            ((calculus l E W.left).reduction.obj K.obj.1,
              (calculus l E W.left).reduction.obj K.obj.2))

/-- Transport d_A across the actual counit, exactly as in the displayed definition of a_A.
Source: fix-prop-coherence, unary counit substitution
(blueprint: lem-sf-integral-expression-recursion). -/
def unaryA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] (M : System l E U.left)
    (h : basicUnaryDomain l E U.left V.left (a.system l E o)
      ((coefficientSequenceLimit l E U.left).obj M)) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E V.left).map
    ((a.system l E o).map ((calculus l E U.left).adjunction.counit.app M))) ≫
      (d.unary a).hom.app ⟨(coefficientSequenceLimit l E U.left).obj M, h⟩

/-- The two-input version, using the tensor of the two actual counits.
Source: fix-prop-coherence, binary counit substitution
(blueprint: lem-sf-integral-expression-recursion). -/
def tensorA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (M N : System l E W.left)
    (h : basicTensorDomain l E W.left
      ((coefficientSequenceLimit l E W.left).obj M,
        (coefficientSequenceLimit l E W.left).obj N)) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E W.left).map
    ((calculus l E W.left).systemClosed.tensor.map
      (Prod.mkHom ((calculus l E W.left).adjunction.counit.app M)
        ((calculus l E W.left).adjunction.counit.app N)))) ≫
    (d.tensor W).hom.app
      ⟨((coefficientSequenceLimit l E W.left).obj M,
        (coefficientSequenceLimit l E W.left).obj N), h⟩

/-- Full input-family natural realization comparisons. The finite expression can
reuse any variable, including in both tensor branches.
Source: fix-prop-coherence (blueprint: lem-sf-integral-expression-recursion). -/
abbrev Comparisons (D : FiniteFieldDatum.{u}) (o : Operations l E) :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (_g : e.geometric),
    e.realizationSource l E o ≅ e.realizationTarget l E o

/-- Coefficient maps are constructed on the finite tree, beginning with identity.
The compact-support abbreviation uses the same open/proper composite.
Source: fix-prop-coherence, displayed recursion for r_V
(blueprint: lem-sf-integral-expression-recursion). -/
def coefficientMap {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : ∀ i, Integral l E (X i).left) :
    (calculus l E W.left).reduction.obj ((e.evaluate (integralInterpretation l E)).obj K) ⟶
      (e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K) :=
  match e, g with
  | .var _, _ => 𝟙 _
  | .pull f e, g =>
    (d.unaryReduction (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)).app
        ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (IntegralSystemRealization.pull l E f.left).map (coefficientMap d e g.2.2.2.2.2 K)
  | .push p hp e, g =>
    (d.unaryReduction (.push p hp)).app ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (Operations.push l E o p.left).map (coefficientMap d e g.2.2 K)
  | .shriek j hj hqc e, g =>
    letI := hj
    (d.unaryReduction (.shriek j hj hqc)).app ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (Operations.shriek l E o j.left).map (coefficientMap d e g.2.2 K)
  | .tensor e t, g =>
    (d.tensorReduction W).app
        ((e.evaluate (integralInterpretation l E)).obj K,
          (t.evaluate (integralInterpretation l E)).obj K) ≫
      (calculus l E W.left).systemClosed.tensor.map
        (Prod.mkHom (coefficientMap d e g.2.2.1 K) (coefficientMap d t g.2.2.2 K))
  | .compactSupport f c e, g =>
    let Z : Over (Spec (.of D.k)) := Over.mk (c.g ≫ W.hom)
    let j : _ ⟶ Z := Over.homMk c.i
      ((Category.assoc c.i c.g W.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ W.hom) c.comm.symm).trans f.w))
    let p : Z ⟶ W := Over.homMk c.g rfl
    (d.unaryReduction (.push p (inferInstance : IsProper c.g))).app
        ((ringedOpen l E c.i).obj ((e.evaluate (integralInterpretation l E)).obj K)) ≫
      (Operations.push l E o c.g).map
        ((d.unaryReduction (.shriek j (inferInstance : IsOpenImmersion c.i)
          (compactOpenQuasiCompact c g.2.2.2.2.1))).app
            ((e.evaluate (integralInterpretation l E)).obj K) ≫
          (Operations.shriek l E o c.i).map (coefficientMap d e g.2.2.2.2.2 K))

/-- Read the root's two geometric hypotheses without imposing a constructor on its tree.
This is just projection from the recorded recursive domain, by cases.
Source: fix-prop-coherence, geometric domain
(blueprint: lem-sf-integral-expression-recursion). -/
abbrev geometricRoot {B : Scheme.{u}} {I : Type u} {X : I → Over B} {W : Over B}
    (e : Expression B I X W) (g : e.geometric) :
    LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom :=
  match e, g with
  | .var _, g => ⟨g.1, g.2.1⟩
  | .pull _ _, g => ⟨g.1, g.2.1⟩
  | .push _ _ _, g => ⟨g.1, g.2.1⟩
  | .shriek _ _ _ _, g => ⟨g.1, g.2.1⟩
  | .tensor _ _, g => ⟨g.1, g.2.1⟩
  | .compactSupport _ _ _, g => ⟨g.1, g.2.1⟩

/-- The displayed leaf, unary and binary equations, recursively at every child.
The existential domain proofs merely license d_A(L M); the maps themselves are
specified by unaryA and tensorA. The compact-support constructor expands to S_p J_j.
Source: fix-prop-coherence, tree induction
(blueprint: lem-sf-integral-expression-recursion). -/
def Equations {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (c : Comparisons l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))} :
    {W : Over (Spec (.of D.k))} → (e : Expression _ I X W) →
    (g : e.geometric) → (K : (e.domain l E o).FullSubcategory) → Prop
  | _, .var i, g, K =>
    (c (.var i) g).hom.app K =
      GeneratorReduction.inverseOrZero ((calculus l E (X i).left).adjunction.unit.app (K.obj i))
  | W, .pull f e, g, K =>
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.2.2.2.2.2).1
    letI := (geometricRoot e g.2.2.2.2.2).2
    ∃ h : basicUnaryDomain l E _ W.left
      ((Unary.system l E o (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)))
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.pull f e) g).hom.app K =
        unaryA l E d (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (Unary.integral l E (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)).map
          ((c e g.2.2.2.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      IsIso (unaryA l E d (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2.2.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .push f hp e, g, K =>
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.2.2).1
    letI := (geometricRoot e g.2.2).2
    ∃ h : basicUnaryDomain l E _ W.left
      ((Unary.system l E o (.push f hp)))
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.push f hp e) g).hom.app K =
        unaryA l E d (.push f hp)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (Unary.integral l E (.push f hp)).map
          ((c e g.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      IsIso (unaryA l E d (.push f hp)
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .shriek f hj hqc e, g, K =>
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.2.2).1
    letI := (geometricRoot e g.2.2).2
    ∃ h : basicUnaryDomain l E _ W.left
      ((Unary.system l E o (.shriek f hj hqc)))
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.shriek f hj hqc e) g).hom.app K =
        unaryA l E d (.shriek f hj hqc)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (Unary.integral l E (.shriek f hj hqc)).map
          ((c e g.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      IsIso (unaryA l E d (.shriek f hj hqc)
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .tensor e t, g, K =>
    letI := g.1
    letI := g.2.1
    ∃ h : basicTensorDomain l E W.left
      ((coefficientSequenceLimit l E W.left).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)),
        (coefficientSequenceLimit l E W.left).obj
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.tensor e t) g).hom.app K =
        tensorA l E d W
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (integralCompletedTensor l E W.left).map
          (Prod.mkHom
            ((c e g.2.2.1).hom.app ⟨K.obj, K.property.1, K.property.2.2.1⟩)
            ((c t g.2.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2.2⟩)) ∧
      IsIso (tensorA l E d W
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
        ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2.1 ⟨K.obj, K.property.1, K.property.2.2.1⟩ ∧
      Equations d c t g.2.2.2 ⟨K.obj, K.property.1, K.property.2.2.2⟩
  | W, .compactSupport f cf e, g, K =>
    let Z : Over (Spec (.of D.k)) := Over.mk (cf.g ≫ W.hom)
    let j : _ ⟶ Z := Over.homMk cf.i
      ((Category.assoc cf.i cf.g W.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ W.hom) cf.comm.symm).trans f.w))
    let p : Z ⟶ W := Over.homMk cf.g rfl
    let aj : Unary _ _ Z := .shriek j (inferInstance : IsOpenImmersion cf.i)
      (compactOpenQuasiCompact cf g.2.2.2.2.1)
    let ap : Unary _ Z W := .push p (inferInstance : IsProper cf.g)
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.2.2.2.2.2).1
    letI := (geometricRoot e g.2.2.2.2.2).2
    letI : LocallyOfFiniteType Z.hom := inferInstanceAs
      (LocallyOfFiniteType (cf.g ≫ W.hom))
    letI : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (cf.g ≫ W.hom))
    ∃ hj : basicUnaryDomain l E _ cf.Z (aj.system l E o)
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
    ∃ hp : basicUnaryDomain l E cf.Z W.left (ap.system l E o)
      ((coefficientSequenceLimit l E cf.Z).obj
        ((Operations.shriek l E o cf.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))),
      (c (.compactSupport f cf e) g).hom.app K =
        unaryA l E d ap
          ((Operations.shriek l E o cf.i).obj
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) hp ≫
        (ringedPush l E cf.g).map
          (unaryA l E d aj
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) hj ≫
          (ringedOpen l E cf.i).map
            ((c e g.2.2.2.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2.1⟩)) ∧
      Equations d c e g.2.2.2.2.2 ⟨K.obj, K.property.1, K.property.2.2.1⟩

/-- The coefficient recursion is natural on the entire input-family category.
Each vertex is the composite of its given natural primitive map with the
functorial image of its children's transformations; no completeness is used.
Source: fix-prop-coherence, finite-tree coefficient recursion
(blueprint: def-sf-integral-expression-recursion-data). -/
def coefficientTransformation {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric) :
    e.evaluate (integralInterpretation l E) ⋙ (calculus l E W.left).reduction ⟶
      inputReduction l E X ⋙ e.evaluate (systemInterpretation l E o) :=
  match e, g with
  | .var _, _ => 𝟙 _
  | .pull f e, g =>
    Functor.whiskerLeft (e.evaluate (integralInterpretation l E))
      (d.unaryReduction (.pull f g.2.2.1 g.2.2.2.1 g.2.2.2.2.1)) ≫
    Functor.whiskerRight (coefficientTransformation d e g.2.2.2.2.2)
      (IntegralSystemRealization.pull l E f.left)
  | .push p hp e, g =>
    Functor.whiskerLeft (e.evaluate (integralInterpretation l E))
      (d.unaryReduction (.push p hp)) ≫
    Functor.whiskerRight (coefficientTransformation d e g.2.2) (Operations.push l E o p.left)
  | .shriek j hj hqc e, g =>
    letI := hj
    Functor.whiskerLeft (e.evaluate (integralInterpretation l E))
      (d.unaryReduction (.shriek j hj hqc)) ≫
    Functor.whiskerRight (coefficientTransformation d e g.2.2)
      (Operations.shriek l E o j.left)
  | .tensor e t, g =>
    Functor.whiskerLeft ((e.evaluate (integralInterpretation l E)).prod'
      (t.evaluate (integralInterpretation l E))) (d.tensorReduction W) ≫
    Functor.whiskerRight
      ((coefficientTransformation d e g.2.2.1).prod'
        (coefficientTransformation d t g.2.2.2))
      (calculus l E W.left).systemClosed.tensor
  | .compactSupport f c e, g =>
    let Z : Over (Spec (.of D.k)) := Over.mk (c.g ≫ W.hom)
    let j : _ ⟶ Z := Over.homMk c.i
      ((Category.assoc c.i c.g W.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ W.hom) c.comm.symm).trans f.w))
    let p : Z ⟶ W := Over.homMk c.g rfl
    Functor.whiskerLeft
      (e.evaluate (integralInterpretation l E) ⋙ ringedOpen l E c.i)
      (d.unaryReduction (.push p (inferInstance : IsProper c.g))) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (e.evaluate (integralInterpretation l E))
        (d.unaryReduction (.shriek j (inferInstance : IsOpenImmersion c.i)
          (compactOpenQuasiCompact c g.2.2.2.2.1))) ≫
       Functor.whiskerRight (coefficientTransformation d e g.2.2.2.2.2)
        (Operations.shriek l E o c.i)) (Operations.push l E o c.g)

attribute [irreducible] coefficientTransformation

/-- Transpose of the coefficient recursion under the actual reduction/limit adjunction.
This is an explicit natural transformation, before any invertibility theorem.
Source: fix-prop-coherence, counit substitution
(blueprint: def-sf-integral-expression-recursion-data). -/
@[irreducible] def transposeComparison {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric) :
    e.realizationTarget l E o ⟶ e.realizationSource l E o :=
  Functor.whiskerLeft (e.realizationTarget l E o) (calculus l E W.left).adjunction.unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (e.domain l E o).ι (coefficientTransformation l E d e g))
      (coefficientSequenceLimit l E W.left)

end ExpressionRecursion
end WeilConjectures.IntegralSystemRealization
