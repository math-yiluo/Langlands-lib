/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
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
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionTensorUnit
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction

/-! # Normalized comparisons on strict quotient models

Source: main-20261015 blueprint, prose-03-02, integral operations;
Stacks Tags 03EL and 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).

## Main definitions

* `Comparisons`: the pure-tensor-normalized comparisons on whole quotient systems.
* `leftRoute`, `rightRoute`: the two strict scalar/pullback/tensor routes.

## Main statements

* `comparisons_existsUnique`: the unique comparisons with their pure-tensor normalization.

This is the self-contained comparison construction formerly in
`WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence`,
which publicly re-exports this module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.monoidalCategory
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.integralComparisonSequenceScalarModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

attribute [local semireducible] coefficientTotalTensor in
/-- The sequence site has the small pro-etale site's original size.
Source: Stacks 0941 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance (priority := 3000) sequenceSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} W

/-- The original small pro-etale site, with object size u+1 and Hom size u.
Source: blueprint size convention (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance (priority := 3000) siteSmall (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The scalar-first route, abstracted over its categories.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-scalar-extension-tower-data). -/
def leftRouteCore {C D A B : Type*}
    [Category C] [Category D] [Category A] [Category B]
    (T : C × C ⥤ C) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (F : C ⥤ D) (G : C ⥤ A) (H : D ⥤ B) (K : A ⥤ B)
    (k : F ⋙ H ≅ G ⋙ K) (s : T ⋙ G ≅ G.prod G ⋙ TA)
    (c : TA ⋙ K ≅ K.prod K ⋙ TB) :
    T ⋙ F ⋙ H ≅ G.prod G ⋙ K.prod K ⋙ TB :=
  Functor.isoWhiskerLeft T k ≪≫ Functor.isoWhiskerRight s K ≪≫
    Functor.isoWhiskerLeft (G.prod G) c

/-- The pullback-first route, abstracted over its categories.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-scalar-extension-tower-data). -/
def rightRouteCore {C D A B : Type*}
    [Category C] [Category D] [Category A] [Category B]
    (T : C × C ⥤ C) (TD : D × D ⥤ D) (TB : B × B ⥤ B)
    (F : C ⥤ D) (G : C ⥤ A) (H : D ⥤ B) (K : A ⥤ B)
    (k : F ⋙ H ≅ G ⋙ K) (s : TD ⋙ H ≅ H.prod H ⋙ TB)
    (c : T ⋙ F ≅ F.prod F ⋙ TD) :
    T ⋙ F ⋙ H ≅ G.prod G ⋙ K.prod K ⋙ TB :=
  Functor.isoWhiskerRight c H ≪≫ Functor.isoWhiskerLeft (F.prod F) s ≪≫
    Functor.isoWhiskerRight (NatIso.prod k k) TB

/-- The unit square for a functor and two specified action unitors.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def UnitSquare {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (U : C ⥤ C) (V : D ⥤ D)
    (k : F ⋙ V ≅ U ⋙ F) (u : U ≅ 𝟭 C) (v : V ≅ 𝟭 D) : Prop :=
  k ≪≫ Functor.isoWhiskerRight u F = Functor.isoWhiskerLeft F v

/-- The tensor comparison commutes with the specified action unitor.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def TensorUnitSquare {C : Type*} [Category C] (T : C × C ⥤ C)
    (U : C ⥤ C) (s : T ⋙ U ≅ U.prod U ⋙ T) (u : U ≅ 𝟭 C) : Prop :=
  s ≪≫ Functor.isoWhiskerRight (NatIso.prod u u) T = Functor.isoWhiskerLeft T u

/-- Two successive coefficient squares under their specified associators.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def CompositionSquare {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (p : A ⥤ B) (q : C ⥤ D) (r : E ⥤ F)
    (s : A ⥤ C) (t : C ⥤ E) (v : A ⥤ E)
    (s' : B ⥤ D) (t' : D ⥤ F) (v' : B ⥤ F)
    (k : p ⋙ s' ≅ s ⋙ q) (h : q ⋙ t' ≅ t ⋙ r)
    (d : p ⋙ v' ≅ v ⋙ r) (a : s ⋙ t ≅ v) (b : s' ⋙ t' ≅ v') : Prop :=
  Functor.isoWhiskerRight k t' ≪≫ Functor.isoWhiskerLeft s h ≪≫
      Functor.isoWhiskerRight a r = Functor.isoWhiskerLeft p b ≪≫ d

/-- Tensor comparison for two successive scalar extensions.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def TensorCompositionSquare {A B C : Type*} [Category A] [Category B] [Category C]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (s : A ⥤ B) (t : B ⥤ C) (v : A ⥤ C)
    (a : s ⋙ t ≅ v) (k : TA ⋙ s ≅ s.prod s ⋙ TB)
    (h : TB ⋙ t ≅ t.prod t ⋙ TC) (d : TA ⋙ v ≅ v.prod v ⋙ TC) : Prop :=
  Functor.isoWhiskerRight k t ≪≫ Functor.isoWhiskerLeft (s.prod s) h ≪≫
      Functor.isoWhiskerRight (NatIso.prod a a) TC = Functor.isoWhiskerLeft TA a ≪≫ d

private theorem map_unit_square {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B]
    (F : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    [F.Additive] [U.Additive] [V.Additive]
    (k : F ⋙ V ≅ U ⋙ F) (u : U ≅ 𝟭 A) (v : V ≅ 𝟭 B)
    (h : UnitSquare F U V k u v) :
    UnitSquare (F.mapHomologicalComplex (.up ℤ))
      (U.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex k (.up ℤ))
      (NatIso.mapHomologicalComplex u (.up ℤ))
      (NatIso.mapHomologicalComplex v (.up ℤ)) := by
  exact congrArg (fun a ↦ NatIso.mapHomologicalComplex a (.up ℤ)) h

/-- Equality of a five-map composite with a specified morphism.
Source: the strict categorical composites in Stacks 03EL, 07A4
(blueprint: def-pur-scalar-extension-tower-data). -/
def FiveStepEquation {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G)
    {α : Type*} (f : α) : Prop := HEq (a ≫ b ≫ c ≫ d ≫ e) f

variable (l : ℕ) [Fact l.Prime]

/-- Cochain quotient systems, with every transition retained in their module structure.
Source: blueprint integral operations; Stacks 0941
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev Complex (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :=
  CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ

/-- Signed direct-sum total tensor on the actual quotient sequence site.
Source: blueprint integral operations; Stacks 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def tensor (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) : Complex l E W × Complex l E W ⥤ Complex l E W :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Additivity of the actual ordinary sequence-site scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance scalarAdditive (W : Scheme.{u}) :
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.Additive :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).additive

/-- Termwise scalar extension through the actual quotient-ring inclusions.
Source: blueprint integral operations; Stacks 06YY
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev scalar (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    Complex l E W ⥤ Complex l L W :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.mapHomologicalComplex (.up ℤ)

/-- Termwise constant-coefficient pro-etale pullback of entire quotient systems.
Source: blueprint integral operations; Stacks 03D2
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : Complex l E Y ⥤ Complex l E X :=
  (integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)

/-- The specified scalar-association isomorphism, lifted termwise.
Source: blueprint integral operations, proof step 3; Stacks 03EL
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def kappa {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull l E f ⋙ scalar l E L ι X ≅ scalar l E L ι Y ⋙ pull l L f :=
  NatIso.mapHomologicalComplex (integralComparisonSequenceScalarPullback.{u, u} l E L ι f) (.up ℤ)

/-- The scalar action unitor on the same strict quotient complexes.
Source: blueprint integral operations, proof step 7
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarUnit (W : Scheme.{u}) : scalar l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit.{u, u} l E W) (.up ℤ)

/-- Successive extension is identified by multiplication of the coefficient factors.
Source: blueprint integral operations, proof step 7
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarComp (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : Scheme.{u}) :
    scalar l E L ι W ⋙ scalar l L F j W ≅ scalar l E F (j.comp ι) W :=
  NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarComposition.{u, u} l E L ι F j W) (.up ℤ)

/-- Tensor generator in the (p,q) summand of the signed direct-sum total.
Source: Stacks 03EK, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev generator (W : Scheme.{u}) (P Q : Complex l E W) (p q : ℤ)
    (U : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((tensor l E W).obj (P, Q)).X (p + q)).val.obj U :=
  coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl U x y

/-- The adjunction-unit generator read as a section on the base-change object.
Source: Stacks 03D2 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback.{u, u} l E f).obj M).val.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)) :=
  integralComparisonSequenceGenerator.{u, u} l E f M n U x

/-- The pure-tensor formula for a scalar comparison on the whole sequence site.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def ScalarFormula (sigma : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W) : Prop :=
  ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    (P Q : Complex l A W) (p q : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l B W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    (((sigma A B i W).hom.app (P, Q)).f (p + q)).val.app U
      (integralComparisonSequenceTensorSection.{u, u} l A B i W
        (((tensor l A W).obj (P, Q)).X (p + q)) U b
        (generator l A W P Q p q U x y)) =
      generator l B W ((scalar l A B i W).obj P) ((scalar l A B i W).obj Q) p q U
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (P.X p) U b x)
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (Q.X q) U 1 y)

/-- The unit formula for a tensor-pullback comparison on the whole sequence site.
Source: Stacks 03D2, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def PullFormula (c : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X) : Prop :=
  ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l A Y) (p q : ℤ) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l A X).obj.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))),
    (((c A f).hom.app (P, Q)).f (p + q)).val.app
      (op (n, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l A f
        (((tensor l A Y).obj (P, Q)).X (p + q)) n U
        (generator l A Y P Q p q (op (n, U)) x y)) =
      generator l A X ((pull l A f).obj P) ((pull l A f).obj Q) p q
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l A f (P.X p) n U x)
        (pullSection l A f (Q.X q) n U y)

/-- Pure-tensor-normalized tensor comparisons on strict quotient systems.
All components, including their inverses, are chain maps of actual sequence-site modules.
Source: blueprint integral operations, proof steps 3--6; Stacks 03EL and 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
structure ComparisonData (Sigma Pullback : Type*)
    (sigmaFormula : Sigma → Prop) (pullFormula : Pullback → Prop) where
  sigma : Sigma
  sigma_formula : sigmaFormula sigma
  c : Pullback
  c_formula : pullFormula c

/-- The original two comparisons and their exact generator formulas.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-scalar-extension-tower-data). -/
abbrev Comparisons :=
  ComparisonData (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W)
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X)
    (ScalarFormula l) (PullFormula l)

private def scalar_adj (W : Scheme.{u}) :
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E ⊣
      SheafOfModules.restrictScalars ((sheafCompose
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralComparisonSequenceScalarMap.{u, u} l E L ι W)) :=
  (sequenceScalarAdjunction.{u, u} l E L ι W).choose

attribute [local irreducible] scalar_adj
  integralComparisonSequenceTensorSection

private theorem scalar_transpose_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W)
    (N : coefficientSequenceModules.{u, u} l L W)
    (a : (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.obj M ⟶ N)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj V) :
    (((scalar_adj l E L ι W).homEquiv M N) a).val.app V x =
      a.val.app V (integralComparisonSequenceTensorSection l E L ι W M V 1 x) := by
  rw [Adjunction.homEquiv_unit]
  change a.val.app V (((scalar_adj l E L ι W).unit.app M).val.app V x) = _
  unfold scalar_adj
  exact congrArg (a.val.app V) (sequenceScalarAdjunction_unit l E L ι W M V x)

private theorem scalar_section_naturality (W : Scheme.{u})
    {M N : coefficientSequenceModules.{u, u} l E W} (a : M ⟶ N)
    (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.map a).val.app V
        (integralComparisonSequenceTensorSection l E L ι W M V b x) =
      integralComparisonSequenceTensorSection l E L ι W N V b (a.val.app V x) := by
  obtain ⟨A, hA⟩ := SequenceScalarProof.scalarPackageExists
    (integralComparisonSequenceScalarMap.{u, u} l E L ι W)
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W)
  rw [sequenceTensorSection_eq, sequenceTensorSection_eq, ← hA]
  exact SheafOfModules.systemScalarModel_map_tmul A a V b x

open CategoryTheory.CochainPullback
open MonoidalCategory

private theorem scalar_section_smul (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : M.val.obj V) :
    integralComparisonSequenceTensorSection l E L ι W M V b x =
      b • integralComparisonSequenceTensorSection l E L ι W M V 1 x := by
  rw [sequenceTensorSection_eq, sequenceTensorSection_eq]
  unfold SheafOfModules.systemModelTmul
  simp only [one_smul]

attribute [local semireducible] coefficientTotalTensor in
private theorem generator_smul (W : Scheme.{u}) (P Q : Complex l E W)
    (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    generator l E W P Q p q V (b • x) y = b • generator l E W P Q p q V x y := by
  unfold generator coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', map_smul]

attribute [local semireducible] integralComparisonSequenceTensorSection

-- The comparison identifies two presentations of the same total complex.

attribute [local semireducible] coefficientTotalTensor in
private theorem scalar_tensor_comparison (W : Scheme.{u}) :
    ∃ e : tensor l E W ⋙ scalar l E L ι W ≅
      (scalar l E L ι W).prod (scalar l E L ι W) ⋙ tensor l L W,
      ∀ (P Q : Complex l E W) (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
        (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        ((e.hom.app (P, Q)).f (p + q)).val.app V
          (integralComparisonSequenceTensorSection l E L ι W
            (((tensor l E W).obj (P, Q)).X (p + q)) V b
            (generator l E W P Q p q V x y)) =
          generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
            (integralComparisonSequenceTensorSection l E L ι W (P.X p) V b x)
            (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := by
  obtain ⟨e, he⟩ := scalarTensorTotal.{u + 1, u, u}
    (integralComparisonSequenceScalarMap.{u, u} l E L ι W)
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).obj_eq
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).map_eq
  refine ⟨e, ?_⟩
  intro P Q p q V b x y
  have h := he P Q p q (p + q) rfl V x y
  change ((e.hom.app (P,Q)).f (p+q)).val.app V
    (integralComparisonSequenceTensorSection l E L ι W _ V 1
      (generator l E W P Q p q V x y)) = _ at h
  rw [scalar_section_smul, map_smul]
  have hh : ((e.hom.app (P,Q)).f (p+q)).val.app V
      (integralComparisonSequenceTensorSection l E L ι W _ V 1
        (generator l E W P Q p q V x y)) =
    generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
      (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
      (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := h
  refine (congrArg (fun z ↦ b • z) hh).trans ?_
  conv_rhs => rw [scalar_section_smul]
  exact (generator_smul l L W ((scalar l E L ι W).obj P)
    ((scalar l E L ι W).obj Q) p q V b
    (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
    (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y)).symm

private def chosen_sigma (W : Scheme.{u}) :
    tensor l E W ⋙ scalar l E L ι W ≅
      (scalar l E L ι W).prod (scalar l E L ι W) ⋙ tensor l L W :=
  (scalar_tensor_comparison l E L ι W).choose

private theorem chosen_sigma_formula (W : Scheme.{u}) (P Q : Complex l E W)
    (p q : ℤ) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((chosen_sigma l E L ι W).hom.app (P, Q)).f (p + q)).val.app V
      (integralComparisonSequenceTensorSection l E L ι W
        (((tensor l E W).obj (P, Q)).X (p + q)) V b
        (generator l E W P Q p q V x y)) =
      generator l L W ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q V
        (integralComparisonSequenceTensorSection l E L ι W (P.X p) V b x)
        (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) :=
  (scalar_tensor_comparison l E L ι W).choose_spec P Q p q V b x y

private theorem pullback_comparison (X Y : Scheme.{u}) (f : X ⟶ Y) :
    ∃ e : tensor l E Y ⋙ pull l E f ≅ (pull l E f).prod (pull l E f) ⋙ tensor l E X,
      ∀ (P Q : Complex l E Y) (p q : ℤ) (m : ℕ) (U : Y.ProEt)
        (x : (P.X p).val.obj (op (m, U))) (y : (Q.X q).val.obj (op (m, U))),
        ((e.hom.app (P, Q)).f (p + q)).val.app
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (pullSection l E f (((tensor l E Y).obj (P, Q)).X (p + q)) m U
              (generator l E Y P Q p q (op (m, U)) x y)) =
          generator l E X ((pull l E f).obj P) ((pull l E f).obj Q) p q
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (pullSection l E f (P.X p) m U x) (pullSection l E f (Q.X q) m U y) := by
  let G (r : coefficientSequenceCommRingSheaf.{u, u} l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf.{u, u} l E X)) :=
    SheafOfModules.pushforward.{u + 1} (F := integralComparisonSequenceBaseChange f)
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E Y))
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E X))
      ⟨Functor.whiskerRight r.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let H (r : coefficientSequenceCommRingSheaf.{u, u} l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf.{u, u} l E X))
      (hG : (G r).IsRightAdjoint) : Prop :=
    letI := hG
    let F := (G r).leftAdjoint.mapHomologicalComplex (.up ℤ)
    ∃ e : tensor l E Y ⋙ F ≅ F.prod F ⋙ tensor l E X,
      ∀ (P Q : Complex l E Y) (p q : ℤ) (m : ℕ) (U : Y.ProEt)
        (x : (P.X p).val.obj (op (m, U))) (y : (Q.X q).val.obj (op (m, U))),
        ((e.hom.app (P, Q)).f (p + q)).val.app
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (((Adjunction.ofIsRightAdjoint (G r)).unit.app
              (((tensor l E Y).obj (P, Q)).X (p + q))).val.app (op (m, U))
              (generator l E Y P Q p q (op (m, U)) x y)) =
          generator l E X (F.obj P) (F.obj Q) p q
            (op (m, (Scheme.proEtaleBaseChange f).obj U))
            (((Adjunction.ofIsRightAdjoint (G r)).unit.app (P.X p)).val.app (op (m, U)) x)
            (((Adjunction.ofIsRightAdjoint (G r)).unit.app (Q.X q)).val.app (op (m, U)) y)
  have h1 : H (pullbackTensorSequenceRing l E f)
      (pullbackTensorSequenceDirect_rightAdjoint l E f) := by
    obtain ⟨e, he⟩ := (pullbackTensorSequenceCochain_existsUnique l E f).exists
    refine ⟨e, ?_⟩
    intro P Q p q m U x y
    exact he P Q p q (p + q) rfl (m, U) x y
  have h2 : ∃ h : (G (integralComparisonSequenceRingMap l E f)).IsRightAdjoint,
      H (integralComparisonSequenceRingMap l E f) h := by
    rw [← WeilConjectures.pullbackTensorSequenceRing_eq]
    exact ⟨_, h1⟩
  exact h2.choose_spec

attribute [local irreducible] integralComparisonSequenceTensorSection
  coefficientTensorGenerator
  integralComparisonSequenceScalarPullback
-- Use adjunction injectivity and the generators of each tensor summand.
private theorem comparisons_unique (c d : Comparisons.{u} l) : c = d := by
  have hs : c.sigma = d.sigma := by
    funext A B _ _ _ _ _ _ i W
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ((scalar_adj l A B i W).homEquiv _ _).injective
    apply WeilConjectures.total_tensor_sections_ext l A W P Q n
    intro p q hpq V x y
    subst n
    have hc := c.sigma_formula A B i W P Q p q V 1 x y
    have hd := d.sigma_formula A B i W P Q p q V 1 x y
    exact (scalar_transpose_section l A B i W _ _ _ V _).trans
      (hc.trans (hd.symm.trans (scalar_transpose_section l A B i W _ _ _ V _).symm))
  have hc : c.c = d.c := by
    funext A _ _ _ X Y f
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage.{u, u} l A f)).homEquiv _ _).injective
    apply WeilConjectures.total_tensor_sections_ext l A Y P Q n
    intro p q hpq V
    rcases V with ⟨m, U⟩
    intro x y
    subst n
    change (((c.c A f).hom.app (P, Q)).f (p + q)).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l A f _ m U (generator l A Y P Q p q (op (m, U)) x y)) =
      (((d.c A f).hom.app (P, Q)).f (p + q)).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l A f _ m U (generator l A Y P Q p q (op (m, U)) x y))
    have h1 := c.c_formula A f P Q p q m U 1 x y
    have h2 := d.c_formula A f P Q p q m U 1 x y
    simp only [one_smul] at h1 h2
    exact h1.trans h2.symm
  cases c
  cases d
  cases hs
  cases hc
  rfl

private def chosen_c {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ≅ (pull l E f).prod (pull l E f) ⋙ tensor l E X :=
  (pullback_comparison l E X Y f).choose

private theorem chosen_c_formula {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l E Y) (p q : ℤ) (m : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l E X).obj.obj
      (op (m, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (m, U))) (y : (Q.X q).val.obj (op (m, U))) :
    (((chosen_c l E f).hom.app (P, Q)).f (p + q)).val.app
      (op (m, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l E f (((tensor l E Y).obj (P, Q)).X (p + q)) m U
        (generator l E Y P Q p q (op (m, U)) x y)) =
      generator l E X ((pull l E f).obj P) ((pull l E f).obj Q) p q
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l E f (P.X p) m U x)
        (pullSection l E f (Q.X q) m U y) := by
  rw [map_smul]
  exact ((congrArg (fun z ↦ b • z)
    ((pullback_comparison l E X Y f).choose_spec P Q p q m U x y)).trans
      (generator_smul l E X _ _ p q _ b _ _).symm)

/-- Existence and uniqueness of the two specified chain comparisons.
Source: blueprint integral operations, proof steps 3--4; Stacks 03EL and 07A4
(blueprint: stage3-pur-normalized-scalar-tower-comparisons).
Proof: apply the ordinary sheaf tensor comparison to the geometric inverse image
and to identity inverse image with the actual coefficient map. Its insertion and
multiplication formulas are inverse by balancing. Totalize over all p+q=n. The
comparison preserves bidegrees, so commutes with both differential terms, including
(-1)^p. These formulas commute with horizontal quotient maps and vertical restrictions,
hence are maps on the sequence site. Pure tensors locally generate the sheaf tensor
and its direct-sum total; this proves uniqueness as well as naturality. -/
theorem comparisons_existsUnique : Nonempty (Unique (Comparisons l)) := by
  let c : Comparisons l :=
    { sigma := fun A B _ _ _ _ _ _ i W ↦ chosen_sigma l A B i W
      sigma_formula := fun A B _ _ _ _ _ _ i W P Q p q V b x y ↦
        chosen_sigma_formula l A B i W P Q p q V b x y
      c := fun A _ _ _ _ _ f ↦ chosen_c l A f
      c_formula := fun A _ _ _ _ _ f P Q p q n U b x y ↦
        chosen_c_formula l A f P Q p q n U b x y }
  exact ⟨⟨⟨c⟩, fun d ↦ comparisons_unique l d c⟩⟩

/-- Canonical comparisons fixed by their pure-tensor characterization.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def comparisons : Comparisons l := (Classical.choice (comparisons_existsUnique l)).default

attribute [local irreducible] comparisons

/-- The left route around the scalar-extension square, as an actual strict chain iso.
Source: node proof steps 3--6 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def leftRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ⋙ scalar l E L ι X ≅
      (scalar l E L ι Y).prod (scalar l E L ι Y) ⋙
        (pull l L f).prod (pull l L f) ⋙ tensor l L X :=
  leftRouteCore (tensor l E Y) (tensor l L Y) (tensor l L X)
    (pull l E f) (scalar l E L ι Y) (scalar l E L ι X) (pull l L f)
    (kappa l E L ι f) ((comparisons l).sigma E L ι Y) ((comparisons l).c L f)

/-- The right route, using the same scalar-association maps on both tensor factors.
Source: node proof steps 3--6 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def rightRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ⋙ scalar l E L ι X ≅
      (scalar l E L ι Y).prod (scalar l E L ι Y) ⋙
        (pull l L f).prod (pull l L f) ⋙ tensor l L X :=
  rightRouteCore (tensor l E Y) (tensor l E X) (tensor l L X)
    (pull l E f) (scalar l E L ι Y) (scalar l E L ι X) (pull l L f)
    (kappa l E L ι f) ((comparisons l).sigma E L ι X) ((comparisons l).c E f)

private theorem pull_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y)
    (N : coefficientSequenceModules.{u, u} l E X)
    {a b : (integralComparisonSequencePullback.{u, u} l E f).obj M ⟶ N}
    (h : ∀ (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))),
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
          (pullSection l E f M n U x) =
        b.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
          (pullSection l E f M n U x)) : a = b := by
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h V.unop.1 V.unop.2 x

private theorem scalar_unit_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).hom.app M).val.app V
      (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V s x) =
        s • x := by
  exact (integralComparisonSequenceScalarUnit_existsUnique.{u, u} l E W).exists.choose_spec
    M V s x

private theorem scalar_unit_inv_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V x =
      integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V 1 x := by
  have h := scalar_unit_section l E W M V 1 x
  have hh := congrArg
    (fun z ↦ ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V z) h
  simpa only [one_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.hom_inv_id_app, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using hh.symm

private theorem pull_section_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : coefficientSequenceModules.{u, u} l E Y} (a : M ⟶ N)
    (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback.{u, u} l E f).map a).val.app
        (op (n, (Scheme.proEtaleBaseChange f).obj U)) (pullSection l E f M n U x) =
      pullSection l E f N n U (a.val.app (op (n, U)) x) := by
  have h := (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).unit.naturality a
  exact (congrArg (fun k ↦ (k.val.app (op (n, U))) x) h).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_pull_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y) (m : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (m, U))) :
    ((integralComparisonSequenceScalarPullback.{u, u} l E L ι f).hom.app M).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback.{u, u} l E f).obj M)
          (op (m, (Scheme.proEtaleBaseChange f).obj U)) 1
          (pullSection l E f M m U x)) =
      pullSection l L f ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj M)
        m U (integralComparisonSequenceTensorSection l E L ι Y M (op (m, U)) 1 x) := by
  simpa only [integralComparisonSequenceScalarPullback, pullSection] using
    (integralComparisonSequenceScalarPullback_existsUnique.{u, u}
      l E L ι f).exists.choose_spec M m U x

private theorem scalar_pull_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonSequenceScalarPullback.{u, u} l E E (AlgHom.id ℚ_[l] E) f ≪≫
        Functor.isoWhiskerRight (integralComparisonSequenceScalarUnit.{u, u} l E Y)
          (integralComparisonSequencePullback.{u, u} l E f) =
      Functor.isoWhiskerLeft (integralComparisonSequencePullback.{u, u} l E f)
        (integralComparisonSequenceScalarUnit.{u, u} l E X) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi ((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
    ((integralComparisonSequencePullback.{u, u} l E f).obj M))).1
  apply pull_hom_ext l E f M
  intro n U x
  change
    ((integralComparisonSequencePullback.{u, u} l E f).map
      ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app M)).val.app _
      (((integralComparisonSequenceScalarPullback.{u, u} l E E
        (AlgHom.id ℚ_[l] E) f).hom.app M).val.app _
        (((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj M)).val.app _
            (pullSection l E f M n U x))) =
    ((integralComparisonSequenceScalarUnit.{u, u} l E X).hom.app
      ((integralComparisonSequencePullback.{u, u} l E f).obj M)).val.app _
        (((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj M)).val.app _
            (pullSection l E f M n U x))
  erw [scalar_unit_inv_section l E X
    ((integralComparisonSequencePullback.{u, u} l E f).obj M)
    (op (n, (Scheme.proEtaleBaseChange f).obj U)) (pullSection l E f M n U x)]
  have hk := scalar_pull_section l E E (AlgHom.id ℚ_[l] E) f M n U x
  change ((integralComparisonSequencePullback.{u, u} l E f).map
      ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app M)).val.app _
      (((integralComparisonSequenceScalarPullback.{u, u} l E E
        (AlgHom.id ℚ_[l] E) f).hom.app M).val.app _ _) = _
  erw [hk, pull_section_naturality, scalar_unit_section, one_smul]
  symm
  simpa only [Functor.id_obj, one_smul] using scalar_unit_section l E X
    ((integralComparisonSequencePullback.{u, u} l E f).obj M)
    (op (n, (Scheme.proEtaleBaseChange f).obj U)) 1 (pullSection l E f M n U x)

attribute [local irreducible] integralComparisonSequenceScalarUnit

private theorem pull_tensor_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l E Y) (p q : ℤ) (n : ℕ) (U : Y.ProEt)
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))) :
    ((((comparisons l).c E f).hom.app (P, Q)).f (p + q)).val.app
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f (((tensor l E Y).obj (P, Q)).X (p + q)) n U
          (generator l E Y P Q p q (op (n, U)) x y)) =
      generator l E X ((pull l E f).obj P) ((pull l E f).obj Q) p q
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f (P.X p) n U x) (pullSection l E f (Q.X q) n U y) := by
  simpa only [one_smul] using (comparisons l).c_formula E f P Q p q n U 1 x y

end WeilConjectures.ScalarExtensionTower
