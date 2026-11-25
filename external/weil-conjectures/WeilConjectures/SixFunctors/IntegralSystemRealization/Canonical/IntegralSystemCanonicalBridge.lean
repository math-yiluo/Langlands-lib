/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

/-! # Canonical constant-ring presentation of the strict coefficient system

Source: Stacks 0941 and 0F7B; blueprint fix-prop-coherence, strict-system realization
(blueprint: def-sf-integral-system-canonical-bridge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uC vC r s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Positive coefficient rings in the published constant-ring universe.
Source: Stacks 0941 (blueprint: def-sf-integral-system-canonical-bridge). -/
abbrev scalarRings (n : ℕ) : CommRingCat.{u+1} :=
  CommRingCat.of (ULift.{u+1} (Padic.coefficientExtensionRing l E (n+1)))

/-- The actual adjacent quotient, with only a universe lift.
Source: Stacks 0941 (blueprint: def-sf-integral-system-canonical-bridge). -/
abbrev scalarTransitions (n : ℕ) : scalarRings l E (n+1) ⟶ scalarRings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n+1)).ulift

/-- Ordinary direct-image presentation, fixed by identity on every component section.
This is the identity of underlying systems, rather than unrelated finite-level lifts.
Source: Stacks 03D7, 0941
(blueprint: def-sf-integral-system-canonical-bridge). -/
structure CanonicalBridge (o : Operations l E) where
  ordinary : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pullbackTensorSequenceDirect l E f ≅
      ProEtale.SemilinearProperOpen.push (scalarRings l E) (scalarTransitions l E) f
  sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f).obj M).val.obj (op (n, V))),
    ((ordinary f).hom.app M).val.app (op (n, V)) x = x

/-- Inverse-image presentation is uniquely fixed by the ordinary direct-image identity.
Source: Stacks 03D7 (blueprint: def-sf-integral-system-canonical-bridge). -/
def CanonicalBridge.pull {o : Operations l E} (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : pull l E f ≅
      ProEtale.SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) f :=
  letI := ProEtale.SemilinearProperOpen.pull_additive
    (scalarRings l E) (scalarTransitions l E) f
  letI := ProEtale.SemilinearProperOpen.pull_limits
    (scalarRings l E) (scalarTransitions l E) f
  letI := ProEtale.SemilinearProperOpen.pull_colimits
    (scalarRings l E) (scalarTransitions l E) f
  Functor.mapDerivedCategoryNatIso
    (((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight (b.ordinary f)).leftAdjointUniq
      (ProEtale.SemilinearProperOpen.ordinaryAdj
        (scalarRings l E) (scalarTransitions l E) f))

/-- Derived direct-image presentation is the adjoint conjugate of inverse image.
Source: Stacks 07A7 (blueprint: def-sf-integral-system-canonical-bridge). -/
def CanonicalBridge.push {o : Operations l E} (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Operations.push l E o f ≅
      ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) f :=
  conjugateIsoEquiv (o.direct f).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) f)
    (b.pull l E f).symm

/-- Open presentation is uniquely fixed by the actual open adjunction unit.
Source: Stacks 03DI (blueprint: def-sf-integral-system-canonical-bridge). -/
def CanonicalBridge.shriek {o : Operations l E} (b : CanonicalBridge l E o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Operations.shriek l E o j ≅
      ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) j :=
  ((o.extension j).adj.ofNatIsoRight (b.pull l E j)).leftAdjointUniq
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j)

/-- The ordinary completed-ring inverse image used in its canonical module adjunction.
Source: Stacks 03D7 (blueprint: def-sf-integral-system-canonical-bridge). -/
abbrev integralOrdinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModulePullback f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)

/-- The canonical module inverse image is additive.
Source: Stacks 03D7 (blueprint: def-sf-integral-system-canonical-bridge). -/
instance integralOrdinaryPullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralOrdinaryPull l E f).Additive :=
  proEtaleRingModulePullback_additive f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)

/-- Scalar restriction leaves every underlying section unchanged. This identity
function supplies the canonical coordinate transport, rather than a free equivalence.
Source: Stacks 03DA (blueprint: def-sf-integral-system-canonical-bridge). -/
def restrictionSection {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S) (M : SheafOfModules.{s} S) (V : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars φ).obj M).val.obj V → M.val.obj V := fun x ↦ x

/-- The actual ordinary limit projection in the finite evaluation coordinates.
Its transport is the published equality of restriction followed by evaluation.
Source: Stacks 0941 (blueprint: def-sf-integral-system-canonical-bridge). -/
def ordinaryLimitProjection (W : Scheme.{u}) (M : coefficientSequenceModules l E W)
    (n : ℕ) (V : W.ProEt) :
    ((pullbackTensorOrdinaryLimit l E W).obj M).val.obj (op V) →
      ((coefficientSequenceEvaluation l E W n).obj M).val.obj (op V) :=
  fun x ↦ restrictionSection
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n))
    ((coefficientSequenceEvaluation l E W n).obj M) (op V)
    (((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app M).val.app
      (op V) (((limit.π ((coefficientSequenceRestriction l E W).obj M) (op n)).val.app (op V)) x))

/-- Underlying sections of the actual completed-ring direct image. The coefficient
map changes the action only, so this canonical coordinate map is the identity.
Source: Stacks 03D1 (blueprint: def-sf-integral-system-canonical-bridge). -/
def integralPushSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X ((PurCompactSupport.completed l E).ring X)) (V : Y.ProEt) :
    ((proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).obj M).val.obj (op V) →
    M.val.obj (op ((proEtaleBaseChange f).obj V)) := fun x ↦ x

/-- Underlying sections of the finite constant-coefficient direct image, again the
identity coordinate map for the published pushforward.
Source: Stacks 03D1 (blueprint: def-sf-integral-system-canonical-bridge). -/
def finitePushSection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : normalizedDVRModules l E X n) (V : Y.ProEt) :
    ((coefficientProEtaleModuleDirectImage.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).obj M).val.obj
        (op V) → M.val.obj (op ((proEtaleBaseChange f).obj V)) := fun x ↦ x

/-- Direct image commutes with ordinary limits by the identity on every projected
section. This ordinary characterization is jointly faithful; it is not a claim about
faithfulness of derived evaluations. Source: Stacks 03D7, 0941
(blueprint: def-sf-integral-system-canonical-bridge). -/
structure OrdinaryLimitModel where
  comparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pullbackTensorSequenceDirect l E f ⋙ pullbackTensorOrdinaryLimit l E Y ≅
      pullbackTensorOrdinaryLimit l E X ⋙
        proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
  /-- The ordinary limit projections are compared by the actual sectionwise
      comparison, as an equality of the actual projected sections. -/
  projections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f ⋙
      pullbackTensorOrdinaryLimit l E Y).obj M).val.obj (op V)),
    ordinaryLimitProjection l E X M n ((proEtaleBaseChange f).obj V)
      (integralPushSection l E f ((pullbackTensorOrdinaryLimit l E X).obj M) V
        (((comparison f).hom.app M).val.app (op V) x)) =
    finitePushSection l E f n ((coefficientSequenceEvaluation l E X n).obj M) V
      (((pullbackTensorSequenceDirectEvaluation l E f n).hom.app M).val.app (op V)
        (ordinaryLimitProjection l E Y ((pullbackTensorSequenceDirect l E f).obj M) n V x))

/-- Ordinary quotient/pullback interchange, conjugate to the actual limit comparison.
Source: Stacks 07A7 (blueprint: def-sf-integral-system-canonical-bridge). -/
def OrdinaryLimitModel.reductionPull (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralOrdinaryPull l E f ⋙ pullbackTensorOrdinaryReduction l E X ≅
      pullbackTensorOrdinaryReduction l E Y ⋙ pullbackTensorSequenceInverse l E f :=
  ((conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)).comp
        (pullbackTensorOrdinaryAdjunction l E X))
    ((pullbackTensorOrdinaryAdjunction l E Y).comp
      (pullbackTensorSequenceAdjunction l E f))).symm (a.comparison f).symm).symm

/-- The same canonical ordinary comparison on whole complexes. Writing its degree
components retains the two actual functor factorizations, without changing categories.
Source: Stacks 07A6 (blueprint: def-sf-integral-system-canonical-bridge). -/
def OrdinaryLimitModel.reductionPullComplex (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ⟶
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := (a.reductionPull l E f).hom.app (P.X i)
  comm' i j _ := ((a.reductionPull l E f).hom.naturality (P.d i j)).symm

/-- Canonical derived quotient/pullback interchange is fixed on whole K-flat systems
by the ordinary adjoint-conjugate comparison. The normalization is in the system
category, before finite evaluation. Source: Stacks 07A4, 07A6 and 0941
(blueprint: def-sf-integral-system-canonical-bridge). -/
structure RealizationModel (o : Operations l E) where
  ordinary : OrdinaryLimitModel l E
  reductionPull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
      (calculus l E X).reduction ≅
    (calculus l E Y).reduction ⋙ pull l E f
  model : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (h : integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj)),
    (reductionPull f).hom.app (DerivedCategory.Q.obj P.obj) ≫
      (pull l E f).map ((pullbackTensorReductionModel l E Y).hom.app P) ≫
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj) =
    (calculus l E X).reduction.map
      ((integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app P.obj) ≫
      (pullbackTensorReductionModel l E X).hom.app
        ⟨((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj, h⟩ ≫
      DerivedCategory.Q.map
        (ordinary.reductionPullComplex l E f P.obj)

/-- The proper direct-image realization is exactly the right-adjoint conjugate of
canonical reduction/pullback. It therefore specifies the actual integral direct-image
functor, including the derived adjunction. Source: Stacks 07A7 and 0941
(blueprint: def-sf-integral-system-canonical-bridge). -/
def RealizationModel.push {o : Operations l E} (a : RealizationModel l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Operations.push l E o f ⋙ coefficientSequenceLimit l E Y ≅
      coefficientSequenceLimit l E X ⋙ PurCompactSupport.push (PurCompactSupport.completed l E) f :=
  conjugateIsoEquiv ((calculus l E Y).adjunction.comp (o.direct f).adj)
    ((proEtaleRingDerivedAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)).comp
        (calculus l E X).adjunction)
    (a.reductionPull f)

/-- Open reduction is the inverse open-adjunction mate of the fixed pullback square.
Source: Stacks 03DI, 07A7 (blueprint: def-sf-integral-system-canonical-bridge). -/
def RealizationModel.openReduction {o : Operations l E} (a : RealizationModel l E o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (calculus l E U).reduction ⋙ Operations.shriek l E o j ⟶
      (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).mapDerivedCategory ⋙
        (calculus l E X).reduction :=
  (mateEquiv (PurCompactSupport.openDerivedAdjunction (PurCompactSupport.completed l E) j)
    (o.extension j).adj).symm (a.reductionPull j).hom

/-- Canonical ordinary-to-completed models, retaining their published pure tensor
and quotient-augmentation normalizations. Source: Stacks 099N, 07A4
(blueprint: def-sf-integral-system-canonical-bridge). -/
structure RingedModels where
  tensor : ∀ W : Scheme.{u}, OpenFactorCoherence.Tensor l E W
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), OpenFactorCoherence.Pull l E f
  tensorClosed : ∀ W : Scheme.{u},
    (tensor W).ordinary.tensor = (calculus l E W).integralClosed.tensor
  /-- The functor equality also preserves the specified total-complex representatives. -/
  tensorRepresentative : ∀ (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) P)
    (hQ : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) Q),
    (tensor W).ordinary.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      (eqToIso (congrArg (fun T ↦ T.obj (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) (tensorClosed W))).hom =
    ((calculus l E W).integralTensorModel.iso (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (calculus l E W).integralClosed P Q ((tensor W).good P hP).1
        ((tensor W).good Q hQ).1).hom

/-- The actual localized completed-ring pullback, before completion.
Source: Stacks 03D7 (blueprint: def-sf-integral-system-canonical-bridge). -/
abbrev ringedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  PurCompactSupport.pull (PurCompactSupport.completed l E) f

/-- The actual localized completed-ring proper image.
Source: Stacks 07A5 (blueprint: def-sf-integral-system-canonical-bridge). -/
abbrev ringedPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  PurCompactSupport.push (PurCompactSupport.completed l E) f

/-- The actual localized completed-ring open extension.
Source: Stacks 03DI (blueprint: def-sf-integral-system-canonical-bridge). -/
abbrev ringedOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (PurCompactSupport.openExtension (PurCompactSupport.completed l E) f).mapDerivedCategory

/-- The actual localized completed-ring geometric adjunction.
Source: Stacks 07A6 (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : ringedPull l E f ⊣ ringedPush l E f :=
  proEtaleRingDerivedAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)

/-- The actual localized completed-ring open adjunction.
Source: Stacks 03DI (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedOpenAdj {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    ringedOpen l E f ⊣ ringedPull l E f :=
  PurCompactSupport.openDerivedAdjunction (PurCompactSupport.completed l E) f

/-- The published representative-normalized geometric pullback compositor.
Source: Stacks 0D6D (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ringedPull l E (f ≫ g) ≅ ringedPull l E g ⋙ ringedPull l E f :=
  PurCompactSupport.geometricPullComposition (PurCompactSupport.completed l E) f g
    (PurCompactSupport.completedPull_comp l E f g)

/-- Direct-image composition is the conjugate of that very compositor.
Source: Stacks 0D6D (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ringedPush l E f ⋙ ringedPush l E g ≅ ringedPush l E (f ≫ g) :=
  conjugateIsoEquiv ((ringedAdj l E g).comp (ringedAdj l E f))
    (ringedAdj l E (f ≫ g)) (ringedPullComp l E f g)

/-- Open composition is fixed by the localized open adjunction.
Source: Stacks 03DI (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedOpenComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    ringedOpen l E f ⋙ ringedOpen l E g ≅ ringedOpen l E (f ≫ g) :=
  Adjunction.leftAdjointCompIso (ringedOpenAdj l E f) (ringedOpenAdj l E g)
    (ringedOpenAdj l E (f ≫ g)) (ringedPullComp l E f g).symm

/-- The canonical localized ringed-site square.
Source: Stacks 07A7 (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedSquare {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    ringedPull l E i ⋙ ringedPull l E r ≅ ringedPull l E p ⋙ ringedPull l E k :=
  (ringedPullComp l E r i).symm ≪≫
    eqToIso (congrArg (ringedPull l E) h.symm) ≪≫ ringedPullComp l E k p

/-- The recorded K-flat normalized tensor/pullback comparison on completed ring sheaves.
Source: Stacks 07A4 (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedTensorPull (d : RingedModels l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleCanonicalTensorComparison f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
    (d.tensor Y).ordinary (d.tensor X).ordinary

/-- The localized ringed-site interpretation underlying the completed expressions.
Source: Stacks 07A4, 099N (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedInterpretation (d : RingedModels l E) : Interpretation (Integral l E) where
  pull := ringedPull l E
  push := ringedPush l E
  shriek := ringedOpen l E
  tensor W := (d.tensor W).ordinary.tensor
  compactSupport _f c := PurCompactSupport.image (PurCompactSupport.completed l E) c

/-- Ordinary tensor reassociation transported from the recorded closed tensor model.
Source: Stacks 07A4 (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedAssociator (d : RingedModels l E) (W : Scheme.{u}) (A B C : Integral l E W) :
    (d.tensor W).ordinary.tensor.obj ((d.tensor W).ordinary.tensor.obj (A, B), C) ≅
      (d.tensor W).ordinary.tensor.obj (A, (d.tensor W).ordinary.tensor.obj (B, C)) :=
  eqToIso (congrArg (fun T : Integral l E W × Integral l E W ⥤ Integral l E W ↦
    T.obj (T.obj (A, B), C)) (d.tensorClosed W)) ≪≫
  (calculus l E W).integralClosed.monoidal.associator A B C ≪≫
  eqToIso (congrArg (fun T : Integral l E W × Integral l E W ⥤ Integral l E W ↦
    T.obj (A, T.obj (B, C))) (d.tensorClosed W).symm)

/-- The actual completion-unit comparison of expressions, defined recursively before
any invertibility assertion. In particular no realization c_V defines this map.
Source: Stacks 099N; blueprint fix-prop-coherence, localized integral maps
(blueprint: def-sf-integral-system-canonical-bridge). -/
def Expression.completionMap (d : RingedModels l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W)
    (K : ∀ i, Integral l E (X i).left) :
    (e.evaluate (ringedInterpretation l E d)).obj K ⟶
      (e.evaluate (integralInterpretation l E)).obj K :=
  match e with
  | .var _ => 𝟙 _
  | .pull f e => (ringedPull l E f.left).map (e.completionMap d K) ≫
      ((d.pull f.left).unit l E).app ((e.evaluate (integralInterpretation l E)).obj K)
  | .push f _ e => (ringedPush l E f.left).map (e.completionMap d K)
  | .shriek j hj _ e =>
    letI := hj
    (ringedOpen l E j.left).map (e.completionMap d K)
  | .compactSupport _ c e =>
    (PurCompactSupport.image (PurCompactSupport.completed l E) c).map (e.completionMap d K)
  | .tensor e t => (d.tensor W.left).ordinary.tensor.map
      (Prod.mkHom (e.completionMap d K) (t.completionMap d K)) ≫
    ((d.tensor W.left).chi l E).app
      ((e.evaluate (integralInterpretation l E)).obj K,
        (t.evaluate (integralInterpretation l E)).obj K)
/-- The left side of the open projection comparison.
Source: Stacks 0E8I (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedTensorLeft (d : RingedModels l E) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Integral l E U × Integral l E X ⥤ Integral l E X :=
  (ringedOpen l E j).prod (𝟭 _) ⋙ (d.tensor X).ordinary.tensor

/-- The right side of the open projection comparison, with restriction in its second slot.
Source: Stacks 0E8I (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedTensorRight (d : RingedModels l E) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Integral l E U × Integral l E X ⥤ Integral l E X :=
  (𝟭 _).prod (ringedPull l E j) ⋙ (d.tensor U).ordinary.tensor ⋙
    ringedOpen l E j

/-- Open comparisons with precisely their open-unit normalizations. The base-change
comparison is indexed by a cartesian square. Its inverse, and the inverse projection
comparison, are fixed by the displayed adjunction transposes. The clopen comparison
uses the inverse of the open unit under the direct-image adjunction.
Source: Stacks 03DI, 09AE, 0E8I; blueprint fix-prop-coherence
(blueprint: def-sf-integral-system-canonical-bridge). -/
structure RingedOpenComparisons (d : RingedModels l E) where
  unitIso : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Integral l E U), IsIso ((ringedOpenAdj l E j).unit.app M)
  beta : ∀ {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (_h : a ≫ j = j' ≫ g) (_sq : IsPullback a j' j g),
    ringedOpen l E j ⋙ ringedPull l E g ≅ ringedPull l E a ⋙ ringedOpen l E j'
  beta_transpose : ∀ {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) (M : Integral l E U),
    ((ringedOpenAdj l E j').homEquiv _ _) ((beta a j' j g h sq).inv.app M) =
      (ringedPull l E a).map ((ringedOpenAdj l E j).unit.app M) ≫
        (ringedSquare l E a j' j g h).inv.app ((ringedOpen l E j).obj M)
  projection : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    ringedTensorLeft l E d j ≅ ringedTensorRight l E d j
  projection_transpose : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : Integral l E U) (N : Integral l E X),
    ((ringedOpenAdj l E j).homEquiv _ _) ((projection j).inv.app (M, N)) =
      (d.tensor U).ordinary.tensor.map
        (Prod.mkHom ((ringedOpenAdj l E j).unit.app M) (𝟙 ((ringedPull l E j).obj N))) ≫
      (ringedTensorPull l E d j).inv.app
        ((ringedOpen l E j).obj M, N)
  clopen : ∀ {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j],
    ringedOpen l E j ≅ ringedPush l E j
  clopen_transpose : ∀ {U X : Scheme.{u}} (j : U ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion j] (M : Integral l E U),
    (clopen j).hom.app M =
      ((ringedAdj l E j).homEquiv _ _)
        (@inv _ _ _ _ ((ringedOpenAdj l E j).unit.app M) (unitIso j M))

/-- Canonical open-unit isomorphism, assembled from its actual components.
Source: Stacks 03DI (blueprint: def-sf-integral-system-canonical-bridge). -/
def RingedOpenComparisons.unit (d : RingedModels l E)
    (a : RingedOpenComparisons l E d) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : 𝟭 (Integral l E U) ≅
      ringedOpen l E j ⋙ ringedPull l E j :=
  NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ ((ringedOpenAdj l E j).unit.app M)
    (a.unitIso j M)) (fun f ↦ (ringedOpenAdj l E j).unit.naturality f)

/-- Open-extension equality transport is fixed by the inverse-image adjunction.
Source: Stacks 03DI (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedOpenCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    ringedOpen l E f ≅ ringedOpen l E g :=
  (ringedOpenAdj l E f).leftAdjointUniq
    ((ringedOpenAdj l E g).ofNatIsoRight (eqToIso (congrArg (ringedPull l E) h.symm)))

/-- Open restriction of direct image is conjugate to the normalized open base change.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedCartesianConjugate (d : RingedModels l E)
    (a : RingedOpenComparisons l E d) {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion i] :
    ringedPush l E p ⋙ ringedPull l E i ≅
      ringedPull l E (pullback.fst p i) ⋙ ringedPush l E (pullback.snd p i) :=
  conjugateIsoEquiv ((ringedOpenAdj l E i).comp (ringedAdj l E p))
    ((ringedAdj l E (pullback.snd p i)).comp (ringedOpenAdj l E (pullback.fst p i)))
    (a.beta (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).symm

/-- Restriction of k-extension to the pulled-back open is s-extension. The inverse
open unit fixes this identification, including the empty open.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedRestrictFactor (d : RingedModels l E)
    (a : RingedOpenComparisons l E d) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ringedOpen l E k ⋙ ringedPull l E (pullback.fst p i) ≅
      ringedOpen l E (ProEtale.StrictTower.squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((ringedOpenComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)) ≪≫
      ringedOpenCongr l E (pullback.lift_fst k r h)).symm (ringedPull l E (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (ringedOpen l E
    (ProEtale.StrictTower.squareLift k r p i h)) (a.unit l E d (pullback.fst p i)).symm ≪≫
  Functor.rightUnitor _

/-- The prescribed lambda: restrict p, factor k through its clopen lift s, identify
J_s with S_s using the open unit, and compose the direct images.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-canonical-bridge). -/
def ringedProperOpenLambda (d : RingedModels l E)
    (a : RingedOpenComparisons l E d) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    (ringedOpen l E k ⋙ ringedPush l E p) ⋙ ringedPull l E i ≅
      ringedPush l E r :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (ringedOpen l E k) (ringedCartesianConjugate l E d a p i) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (ringedRestrictFactor l E d a k r p i h)
    (ringedPush l E (pullback.snd p i)) ≪≫
  Functor.isoWhiskerRight (a.clopen (ProEtale.StrictTower.squareLift k r p i h))
    (ringedPush l E (pullback.snd p i)) ≪≫
  ringedPushComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i) ≪≫
  eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h))

/-- The localized ringed-site proper/open map is pinned by the actual lambda transpose.
No independent map or endomorphism is accepted as its normalization.
Source: Stacks 0F7B (blueprint: def-sf-integral-system-canonical-bridge). -/
structure RingedProperOpen (d : RingedModels l E) (a : RingedOpenComparisons l E d) where
  gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
    ringedPush l E r ⋙ ringedOpen l E i ⟶ ringedOpen l E k ⋙ ringedPush l E p
  adjunct : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Integral l E U),
    (ringedOpenAdj l E i).homEquiv _ _ ((gamma k r p i h).app M) =
      (ringedProperOpenLambda l E d a k r p i h).inv.app M

end WeilConjectures.IntegralSystemRealization
