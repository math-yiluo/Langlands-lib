/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleComparisonLocalization

/-! # Coherent composition of finite-coefficient pullback on strict systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, and sites-modules.tex,
Tags 03D3, 03D7, 03D8. The strict-system refinement uses componentwise adjunctions
and coherence before localization
(blueprint: lem-pod-finite-system-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Replaying sectionwise transport proofs for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures.SemilinearSections

namespace WeilConjectures

-- DS fixes this localization; use it also when inferring exact derived functors.
attribute [local instance 3000] SemilinearSections.hasDerived

/-- The existing sheafification witness at the specified coefficient universe.
Source: Stacks 00W1 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance (priority := 4000) finiteSystemRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} X

/-- The existing small-site witness, retaining the original two site universes.
Source: Stacks 09A5 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance (priority := 4000) finiteSystemSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- Smallness of the sequence site in the very same coefficient universe.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance (priority := 4000) finiteSystemSequenceSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  SemilinearSections.sequenceSmall.{u + 1, u, u + 1}

variable (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n)

/-- Strict semilinear systems on the actual ringed sequence site.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystems (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.VaryingRing.Modules
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X

/-- Ordinary unbounded derived systems, rather than diagrams of derived modules.
Source: Stacks 05RU (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemDerived (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.VaryingRing.Derived
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X

/-- Exact evaluation at a coefficient level.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemEvaluation (X : Scheme.{u}) (n : ℕ) :
    finiteSystems A τ X ⥤ proEtaleRingModules X (proEtaleConstantRing X (A n)) :=
  AlgebraicGeometry.ProEtale.VaryingRing.eval
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X n


/-- Sectionwise direct image with its specified constant-section scalar action.
Source: Stacks 03D3, 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystems.{u} A τ X ⥤ finiteSystems.{u} A τ Y :=
  AlgebraicGeometry.ProEtale.VaryingRing.push
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f


/-- The universal left adjoint of the explicit sectionwise system direct image.
Its universal property determines it up to the unique adjunction-compatible iso.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AlgebraicGeometry.ProEtale.VaryingRing.pull
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f

/-- The actual system adjunction, fixing its units and all conjugate comparisons.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystemPullback A τ f ⊣ finiteSystemPushforward A τ f :=
  AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f

/-- Finite-coefficient inverse image on systems is componentwise exact.
Source: Stacks 03D3, 0941 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: the componentwise adjunction identifies each evaluation with the finite
constant-coefficient module inverse image. That inverse image is exact by
prop-weil-pbc-proetale-constant-exact. Kernels, cokernels and addition of strict
systems are componentwise by lem-coef-semilinear-derived-sections. -/
theorem finiteSystemPullback_exact [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteSystemPullback.{u} A τ f).Additive ∧
      PreservesFiniteLimits (finiteSystemPullback.{u} A τ f) ∧
      PreservesFiniteColimits (finiteSystemPullback.{u} A τ f) := by
  let R : ℕ → CommRingCat.{u + 1} := fun n ↦
    CommRingCat.of (ULift.{u + 1, u} (A n))
  let φ : ∀ n, R (n + 1) ⟶ R n := fun n ↦
    CommRingCat.ofHom ((τ n).hom.ulift)
  exact AlgebraicGeometry.ProEtale.VaryingRing.pull_exact R φ f

/-- Additivity of the actual finite-system inverse image.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance finiteSystemPullbackAdditive [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (finiteSystemPullback.{u} A τ f).Additive :=
  (finiteSystemPullback_exact.{u} A τ f).1

/-- Preservation of finite limits by actual finite-system inverse image.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance finiteSystemPullbackLimits [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (finiteSystemPullback.{u} A τ f) :=
  (finiteSystemPullback_exact.{u} A τ f).2.1

/-- Preservation of finite colimits by actual finite-system inverse image.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
instance finiteSystemPullbackColimits [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (finiteSystemPullback.{u} A τ f) :=
  (finiteSystemPullback_exact.{u} A τ f).2.2

/-- The stipulated exact, termwise functor on ordinary unbounded derived systems.
Source: Stacks 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemDerivedPullback [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystemDerived.{u} A τ Y ⥤ finiteSystemDerived.{u} A τ X :=
  (finiteSystemPullback.{u} A τ f).mapDerivedCategory

/-- The unique ordinary comparison with the sectionwise fibre-product conjugate.
Source: Stacks 03D8, 0B65 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: restriction along the fibre-product isomorphism is natural in sections,
linear because the coefficient maps preserve constants, and commutes with every
horizontal transition. It fixes d uniquely. Conjugation through the actual system
adjunctions gives the unique a; the conjugation bijection proves uniqueness. -/
theorem finiteSystemComposition_existsUnique
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    ∃! a : finiteSystemPullback.{u} A τ (h ≫ k) ≅
        finiteSystemPullback.{u} A τ k ⋙ finiteSystemPullback.{u} A τ h,
      ∃ d : finiteSystemPushforward.{u} A τ h ⋙ finiteSystemPushforward.{u} A τ k ≅
          finiteSystemPushforward.{u} A τ (h ≫ k),
        conjugateIsoEquiv ((finiteSystemAdjunction.{u} A τ k).comp
          (finiteSystemAdjunction.{u} A τ h)) (finiteSystemAdjunction.{u} A τ (h ≫ k)) a = d ∧
        ∀ (M : finiteSystems.{u} A τ Z) (n : ℕ) (U : V.ProEt)
          (x : ((finiteSystemPushforward.{u} A τ h ⋙
            finiteSystemPushforward.{u} A τ k).obj M).val.obj (op (n, U))),
          (d.hom.app M).val.app (op (n, U)) x =
            M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
              ((MorphismProperty.Over.pullbackComp h k (h ≫ k) rfl).hom.app U)).op x := by
  let R : ℕ → CommRingCat.{u + 1} := fun n ↦
    CommRingCat.of (ULift.{u + 1, u} (A n))
  let φ : ∀ n, R (n + 1) ⟶ R n := fun n ↦
    CommRingCat.ofHom ((τ n).hom.ulift)
  obtain ⟨d, hd, huniq⟩ :=
    AlgebraicGeometry.ProEtale.VaryingRing.modulePComp_existsUnique R φ h k
  let e := conjugateIsoEquiv ((finiteSystemAdjunction.{u} A τ k).comp
    (finiteSystemAdjunction.{u} A τ h)) (finiteSystemAdjunction.{u} A τ (h ≫ k))
  refine ⟨e.symm d, ⟨d, e.apply_symm_apply d, hd⟩, ?_⟩
  intro a ha
  obtain ⟨d', he, hd'⟩ := ha
  apply e.injective
  rw [e.apply_symm_apply]
  exact he.trans (huniq d' hd')

/-- Select the comparison determined uniquely by the full system adjunction.
Source: Stacks 03D8 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemComposition {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :=
  (finiteSystemComposition_existsUnique.{u} A τ h k).exists.choose

/-- The comparison on complexes, before localization, applied degreewise.
Source: Stacks 0D6D (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemComplexComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :=
  NatIso.mapHomologicalComplex (finiteSystemComposition.{u} A τ h k) (ComplexShape.up ℤ)

/-- The derived comparison is the localization of the specified whole-system map.
Source: Stacks 0D6D, 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemDerivedComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemDerivedPullback.{u} A τ (h ≫ k) ≅
      finiteSystemDerivedPullback.{u} A τ k ⋙ finiteSystemDerivedPullback.{u} A τ h :=
  Functor.mapDerivedCategoryNatIso (finiteSystemComposition.{u} A τ h k) ≪≫
    (Functor.mapDerivedCategoryCompIso (finiteSystemPullback.{u} A τ k)
      (finiteSystemPullback.{u} A τ h)).symm

/-- Exact evaluation on the ordinary derived system category.
Source: Stacks 0941 (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemDerivedEvaluation (X : Scheme.{u}) (n : ℕ) :
    finiteSystemDerived.{u} A τ X ⥤ proEtaleDerivedCategory.{u} X (A n) :=
  @CategoryTheory.Functor.mapDerivedCategory (finiteSystems.{u} A τ X) _ _ _
    (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X (A n))) _
    (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing.{u} X (A n)))
      (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
      (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology X)))
    (proEtaleRingModules_hasDerivedCategory.{u} X (proEtaleConstantRing.{u} X (A n)))
    (finiteSystemEvaluation.{u} A τ X n) _ _ _

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.leftAdjoint proEtaleRingModulePullback
  proEtaleRingDirectImageMap proEtaleRingModuleAdjunction
  AlgebraicGeometry.ProEtale.VaryingRing.ringMap
  AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP
  AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj

attribute [local irreducible] WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.rings

private theorem varyingDirectEvaluation_apply
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : AlgebraicGeometry.ProEtale.VaryingRing.Modules R φ X) (U : Y.ProEt)
    (x : ((AlgebraicGeometry.ProEtale.VaryingRing.push R φ f).obj N).val.obj
      (op (n, U))) :
    ((AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP R φ f n).hom.app N).val.app
      (op U) x = x := by
  unfold AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP
  exact (AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP_existsUnique
    R φ f n).choose_spec.1 N U x

-- The sectionwise equations compare modules with different scalar presentations.
private theorem varyingEvaluationUnit_iff
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (q : AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f ⋙
        AlgebraicGeometry.ProEtale.VaryingRing.eval R φ X n ≅
      AlgebraicGeometry.ProEtale.VaryingRing.eval R φ Y n ⋙
        AlgebraicGeometry.ProEtale.StrictTower.modulePullback (R n) f) :
    (∀ N : AlgebraicGeometry.ProEtale.VaryingRing.Modules R φ Y,
        (AlgebraicGeometry.ProEtale.VaryingRing.eval R φ Y n).map
          ((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app N) ≫
        (AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP R φ f n).hom.app
          ((AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f).obj N) ≫
        (AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage (R n) f).map
          (q.hom.app N) =
        (proEtaleRingModuleAdjunction f
          (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R Y n)
          (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R X n)
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso (R n) f)).unit.app
            ((AlgebraicGeometry.ProEtale.VaryingRing.eval R φ Y n).obj N)) ↔
      ∀ (M : AlgebraicGeometry.ProEtale.VaryingRing.Modules R φ Y) (U : Y.ProEt)
        (m : M.val.obj (op (n, U))),
        (q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
          (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app M).val.app
            (op (n, U)) m) =
          ((proEtaleRingModuleAdjunction f
            (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R Y n)
            (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R X n)
            (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso (R n) f)).unit.app
              ((AlgebraicGeometry.ProEtale.VaryingRing.eval R φ Y n).obj M)).val.app
                (op U) m := by
  have hd := varyingDirectEvaluation_apply R φ f n
  constructor
  · intro hq M U m
    have he := congrArg (fun t ↦ t.val.app (op U) m) (hq M)
    change (q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (((AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP R φ f n).hom.app
        ((AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f).obj M)).val.app (op U)
          (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app M).val.app
            (op (n, U)) m)) = _ at he
    exact (congrArg ((q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U)))
      (hd ((AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f).obj M) U
        (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app M).val.app
          (op (n, U)) m))).symm.trans he
  · intro hb M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U.unop))
      (((AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP R φ f n).hom.app
        ((AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f).obj M)).val.app U
          (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app M).val.app
            (op (n, U.unop)) m)) = _
    exact (congrArg ((q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U.unop)))
      (hd ((AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f).obj M) U.unop
        (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app M).val.app
          (op (n, U.unop)) m))).trans (hb M U.unop m)

private theorem varyingPullbackEvaluation
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! q : AlgebraicGeometry.ProEtale.VaryingRing.pull R φ f ⋙
        AlgebraicGeometry.ProEtale.VaryingRing.eval R φ X n ≅
      AlgebraicGeometry.ProEtale.VaryingRing.eval R φ Y n ⋙
        AlgebraicGeometry.ProEtale.StrictTower.modulePullback (R n) f,
      ∀ (M : AlgebraicGeometry.ProEtale.VaryingRing.Modules R φ Y) (U : Y.ProEt)
        (m : M.val.obj (op (n, U))),
        (q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
          (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj R φ f).unit.app M).val.app
            (op (n, U)) m) =
          ((proEtaleRingModuleAdjunction f
            (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R Y n)
            (AlgebraicGeometry.ProEtale.VaryingRing.coefficients R X n)
            (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso (R n) f)).unit.app
              ((AlgebraicGeometry.ProEtale.VaryingRing.eval R φ Y n).obj M)).val.app
                (op U) m := by
  exact (existsUnique_congr (varyingEvaluationUnit_iff R φ f n)).mp
    (AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalG_existsUnique R φ f n)

/-- The component identification is uniquely fixed on adjunction-unit generators.
Source: Stacks 03D3, 03D7 (blueprint: lem-pod-finite-system-pullback-coherence).
Proof: restrict the componentwise Hom adjunction to compatible system maps.
Evaluation of the system unit is the level unit. The level pullback is generated
locally by these unit sections and their scalar multiples, so a module map
satisfying this formula is unique. The componentwise construction gives its
inverse. No test for equality of derived maps is used. -/
theorem finiteSystemPullbackEvaluation_existsUnique [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! q : finiteSystemPullback.{u} A τ f ⋙ finiteSystemEvaluation.{u} A τ X n ≅
        finiteSystemEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingPullback (A n) f,
      ∀ (M : finiteSystems.{u} A τ Y) (U : Y.ProEt)
        (m : ((finiteSystemEvaluation.{u} A τ Y n).obj M).val.obj (op U)),
        (q.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
            (((finiteSystemAdjunction.{u} A τ f).unit.app M).val.app (op (n, U)) m) =
          (((proEtaleConstantRingAdjunction (A n) f).unit.app
            ((finiteSystemEvaluation.{u} A τ Y n).obj M)).val.app (op U)) m := by
  exact varyingPullbackEvaluation
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f n

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unit-normalized ordinary component identification.
Source: Stacks 03D3 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemPullback.{u} A τ f ⋙ finiteSystemEvaluation.{u} A τ X n ≅
      finiteSystemEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingPullback (A n) f :=
  (finiteSystemPullbackEvaluation_existsUnique.{u} A τ f n).exists.choose

/-- The derived evaluation identification is exactly the termwise localization.
Source: Stacks 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemDerivedPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemDerivedPullback.{u} A τ f ⋙ finiteSystemDerivedEvaluation.{u} A τ X n ≅
      finiteSystemDerivedEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingDerivedPullback (A n) f := by
  letI : Abelian (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X (A n))) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing.{u} X (A n)))
      (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
      (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology X))
  letI : Abelian (proEtaleRingModules.{u} Y (proEtaleConstantRing.{u} Y (A n))) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} Y.ProEt _ (ProEt.topology Y)
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing.{u} Y (A n)))
      (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} Y)
      (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology Y))
  letI : HasDerivedCategory (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X (A n))) :=
    proEtaleRingModules_hasDerivedCategory.{u} X (proEtaleConstantRing.{u} X (A n))
  letI : HasDerivedCategory (proEtaleRingModules.{u} Y (proEtaleConstantRing.{u} Y (A n))) :=
    proEtaleRingModules_hasDerivedCategory.{u} Y (proEtaleConstantRing.{u} Y (A n))
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (finiteSystemPullbackEvaluation.{u} A τ f n) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The existing canonical module comparison, fixed by its fibre-product conjugate.
The property in the published existence theorem determines its map uniquely:
sectionwise restriction fixes the right comparison, and conjugation is bijective.
Source: Stacks 03D8 (blueprint: lem-pod-finite-system-pullback-coherence). -/
def finiteSystemModuleComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ) :
    proEtaleConstantRingPullback (A n) (h ≫ k) ≅
      proEtaleConstantRingPullback (A n) k ⋙ proEtaleConstantRingPullback (A n) h :=
  (proEtaleConstantRingModulePullbackComposition h k (A n)).choose

/-- Complex pullback is termwise on arbitrary unbounded complexes.
Source: Stacks 015F (blueprint: lem-pod-finite-system-pullback-coherence). -/
abbrev finiteSystemComplexPullback [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (finiteSystemPullback.{u} A τ f).mapHomologicalComplex (ComplexShape.up ℤ)

attribute [local irreducible] finiteSystemComposition finiteSystemPullbackEvaluation
  finiteSystemDerivedComposition finiteSystemDerivedPullbackEvaluation
  finiteSystemModuleComposition finiteSystemComplexComposition

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.modulePComp

private abbrev systemCoefficientRings (A : ℕ → CommRingCat.{u}) : ℕ → CommRingCat.{u + 1} := fun n ↦
  CommRingCat.of (ULift.{u + 1, u} (A n))

private abbrev systemCoefficientMaps (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) (n : ℕ) :
    systemCoefficientRings.{u} A (n + 1) ⟶ systemCoefficientRings.{u} A n :=
  CommRingCat.ofHom ((τ n).hom.ulift)

@[irreducible] private def systemDirectComposition (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemPushforward.{u} A τ h ⋙ finiteSystemPushforward.{u} A τ k ≅
      finiteSystemPushforward.{u} A τ (h ≫ k) :=
  AlgebraicGeometry.ProEtale.VaryingRing.modulePComp
    (systemCoefficientRings.{u} A) (systemCoefficientMaps.{u} A τ) h k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem systemDirectComposition_apply (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) (N : finiteSystems.{u} A τ Z) (n : ℕ) (U : V.ProEt)
    (x : ((finiteSystemPushforward.{u} A τ h ⋙
      finiteSystemPushforward.{u} A τ k).obj N).val.obj (op (n, U))) :
    ((systemDirectComposition A τ h k).hom.app N).val.app (op (n, U)) x =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op x := by
  unfold systemDirectComposition AlgebraicGeometry.ProEtale.VaryingRing.modulePComp
  exact (AlgebraicGeometry.ProEtale.VaryingRing.modulePComp_existsUnique
    (systemCoefficientRings.{u} A) (systemCoefficientMaps.{u} A τ) h k).choose_spec.1 N n U x

private theorem systemComposition_eq (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemComposition.{u} A τ h k =
      (Adjunction.leftAdjointCompIso (finiteSystemAdjunction.{u} A τ k)
        (finiteSystemAdjunction.{u} A τ h) (finiteSystemAdjunction.{u} A τ (h ≫ k))
          (systemDirectComposition A τ h k)).symm := by
  unfold finiteSystemComposition
  obtain ⟨d, he, hd⟩ := (finiteSystemComposition_existsUnique.{u} A τ h k).exists.choose_spec
  have hde : d = systemDirectComposition A τ h k := by
    unfold systemDirectComposition AlgebraicGeometry.ProEtale.VaryingRing.modulePComp
    exact (AlgebraicGeometry.ProEtale.VaryingRing.modulePComp_existsUnique
      (systemCoefficientRings.{u} A) (systemCoefficientMaps.{u} A τ) h k).choose_spec.2 d hd
  apply (conjugateIsoEquiv ((finiteSystemAdjunction.{u} A τ k).comp
    (finiteSystemAdjunction.{u} A τ h)) (finiteSystemAdjunction.{u} A τ (h ≫ k))).injective
  rw [he, hde]
  exact ((conjugateIsoEquiv ((finiteSystemAdjunction.{u} A τ k).comp
    (finiteSystemAdjunction.{u} A τ h)) (finiteSystemAdjunction.{u} A τ (h ≫ k))).apply_symm_apply
      (systemDirectComposition A τ h k)).symm

private theorem systemDirectTransport (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : finiteSystems.{u} A τ X) (n : ℕ) (U : Y.ProEt)
    (m : ((finiteSystemPushforward.{u} A τ f).obj N).val.obj (op (n, U))) :
    ((eqToIso (congrArg (finiteSystemPushforward.{u} A τ) e)).hom.app N).val.app
        (op (n, U)) m =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
        (eqToHom (congrArg (fun t ↦ (proEtaleBaseChange t).obj U) e.symm))).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem systemDirectMap (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N N' : finiteSystems.{u} A τ X} (a : N ⟶ N') (n : ℕ) (U : Y.ProEt)
    (m : ((finiteSystemPushforward.{u} A τ f).obj N).val.obj (op (n, U))) :
    (((finiteSystemPushforward.{u} A τ f).map a).val.app (op (n, U))) m =
      a.val.app (op (n, (proEtaleBaseChange f).obj U)) m := rfl

private theorem systemDirectRestriction (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : finiteSystems.{u} A τ X) (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((finiteSystemPushforward.{u} A τ f).obj N).val.obj (op (n, V))) :
    (((finiteSystemPushforward.{u} A τ f).obj N).val.map
      (CategoryTheory.Prod.mkHom (𝟙 n) a).op) m =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n) ((proEtaleBaseChange f).map a)).op m := rfl

private theorem pasting_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : fg = f ≫ g) (U : P.Over Q Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g fg e).hom.app U =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U) e) ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app U := by
  cases e
  simp

private theorem site_pasting
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z W : C} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (U : P.Over Q X) :
    (MorphismProperty.Over.pullbackComp j (h ≫ k)).hom.app U ≫
        (MorphismProperty.Over.pullback P Q j).map
          ((MorphismProperty.Over.pullbackComp h k).hom.app U) =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.assoc j h k).symm) ≫
        (MorphismProperty.Over.pullbackComp (j ≫ h) k).hom.app U ≫
        (MorphismProperty.Over.pullbackComp j h).hom.app
          ((MorphismProperty.Over.pullback P Q k).obj U) := by
  have hp := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := Q) j h k)) U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hp
  rw [pasting_transport (j ≫ h) k (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
  simpa only [Category.assoc] using hp

private theorem restriction_pasting
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules R)
    {U V T U' V' : C} (a : U ⟶ V) (b : V ⟶ T)
    (c : U ⟶ U') (d : U' ⟶ V') (e : V' ⟶ T)
    (h : a ≫ b = c ≫ d ≫ e) (m : N.obj (op T)) :
    N.map a.op (N.map b.op m) = N.map c.op (N.map d.op (N.map e.op m)) := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem systemDirectCoherence
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n) {X Y Z W : Scheme.{u}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) :
    Functor.isoWhiskerLeft (finiteSystemPushforward.{u} A τ j)
        (systemDirectComposition A τ h k) ≪≫ systemDirectComposition A τ j (h ≫ k) =
      (Functor.associator (finiteSystemPushforward.{u} A τ j)
        (finiteSystemPushforward.{u} A τ h) (finiteSystemPushforward.{u} A τ k)).symm ≪≫
        Functor.isoWhiskerRight (systemDirectComposition A τ j h)
          (finiteSystemPushforward.{u} A τ k) ≪≫ systemDirectComposition A τ (j ≫ h) k ≪≫
        eqToIso (congrArg (finiteSystemPushforward.{u} A τ) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, U⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  erw [systemDirectMap A τ k ((systemDirectComposition A τ j h).hom.app N) n U]
  erw [systemDirectComposition_apply A τ j h N n ((proEtaleBaseChange k).obj U)]
  erw [systemDirectComposition_apply A τ (j ≫ h) k N n U]
  conv_rhs => erw [systemDirectTransport A τ (Category.assoc j h k) N n U]
  conv_lhs => erw [systemDirectComposition_apply A τ h k
    ((finiteSystemPushforward.{u} A τ j).obj N) n U m]
  conv_lhs => erw [systemDirectComposition_apply A τ j (h ≫ k) N n U]
  conv_lhs => erw [systemDirectRestriction A τ j N n
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U)]
  apply restriction_pasting N.val
  apply CategoryTheory.Prod.hom_ext
  · simp
  · exact site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U

private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

private theorem systemOrdinaryCoherence
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n)
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (M : finiteSystems.{u} A τ X) :
    (finiteSystemComposition.{u} A τ j (h ≫ k)).hom.app M ≫
        (finiteSystemPullback.{u} A τ j).map ((finiteSystemComposition.{u} A τ h k).hom.app M) =
      (eqToIso (congrArg (finiteSystemPullback.{u} A τ)
        (Category.assoc j h k).symm)).hom.app M ≫
        (finiteSystemComposition.{u} A τ (j ≫ h) k).hom.app M ≫
        (finiteSystemComposition.{u} A τ j h).hom.app ((finiteSystemPullback.{u} A τ k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (finiteSystemAdjunction.{u} A τ k) (finiteSystemAdjunction.{u} A τ h)
    (finiteSystemAdjunction.{u} A τ j)
    (finiteSystemAdjunction.{u} A τ (h ≫ k)) (finiteSystemAdjunction.{u} A τ (j ≫ h))
    (finiteSystemAdjunction.{u} A τ (j ≫ h ≫ k))
    (systemDirectComposition A τ h k) (systemDirectComposition A τ j h)
    ((systemDirectComposition A τ (j ≫ h) k) ≪≫
      eqToIso (congrArg (finiteSystemPushforward.{u} A τ) (Category.assoc j h k)))
    (systemDirectComposition A τ j (h ≫ k)) (systemDirectCoherence A τ j h k)
  have ht := mate_transport (finiteSystemPullback.{u} A τ)
    (finiteSystemPushforward.{u} A τ) (fun f ↦ finiteSystemAdjunction.{u} A τ f)
    (finiteSystemAdjunction.{u} A τ k) (finiteSystemAdjunction.{u} A τ (j ≫ h))
    (Category.assoc j h k)
    (systemDirectComposition A τ (j ≫ h) k)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [systemComposition_eq, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem descend_coherence
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (F02 : C ⥤ E) (F13 : D ⥤ B) (F03 F03' : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [F02.Additive] [F13.Additive]
    [F03.Additive] [F03'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F02] [PreservesFiniteColimits F02]
    [PreservesFiniteLimits F13] [PreservesFiniteColimits F13]
    [PreservesFiniteLimits F03] [PreservesFiniteColimits F03]
    [PreservesFiniteLimits F03'] [PreservesFiniteColimits F03']
    (a02 : F02 ≅ F ⋙ G) (a13 : F13 ≅ G ⋙ H)
    (a0 : F03 ≅ F02 ⋙ H) (a1 : F03' ≅ F ⋙ F13) (e : F03 ≅ F03')
    (ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13) :
    (Functor.mapDerivedCategoryNatIso a0).hom ≫
        (Functor.mapDerivedCategoryCompIso F02 H).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a02).hom
          H.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).inv
          H.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryNatIso a1).hom ≫
        (Functor.mapDerivedCategoryCompIso F F13).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso a13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryCompIso G H).inv := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hR := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a02 H
  have hL := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F a13
  have hC := Functor.mapDerivedCategoryCompIso_assoc F G H
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F02 H).inv,
    ← hR, Category.assoc, ← hC]
  have ht := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso G H).inv) hd
  calc
    _ = ((Functor.mapDerivedCategoryNatIso e).hom ≫
          (Functor.mapDerivedCategoryNatIso a1).hom ≫
          (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F a13)).hom) ≫
        (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso G H).inv := by
            simpa only [Category.assoc] using ht
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft F a13)).hom, hL]
      simp only [Category.assoc]

private theorem systemDerivedTransport
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n) [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (finiteSystemPullback.{u} A τ) e))).hom =
      (eqToIso (congrArg (finiteSystemDerivedPullback.{u} A τ) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem systemDerivedCoherence
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n) [∀ n, Finite (A n)]
    {Y Z W V : Scheme.{u}} (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
    (S : finiteSystemDerived.{u} A τ V) :
    (eqToHom (congrArg (finiteSystemDerivedPullback.{u} A τ) (Category.assoc j h k))).app S ≫
      (finiteSystemDerivedComposition.{u} A τ j (h ≫ k)).hom.app S ≫
      (finiteSystemDerivedPullback.{u} A τ j).map
        ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) =
      (finiteSystemDerivedComposition.{u} A τ (j ≫ h) k).hom.app S ≫
      (finiteSystemDerivedComposition.{u} A τ j h).hom.app
        ((finiteSystemDerivedPullback.{u} A τ k).obj S) := by
  let F := finiteSystemPullback.{u} A τ k
  let G := finiteSystemPullback.{u} A τ h
  let H := finiteSystemPullback.{u} A τ j
  let F02 := finiteSystemPullback.{u} A τ (h ≫ k)
  let F13 := finiteSystemPullback.{u} A τ (j ≫ h)
  let a02 := finiteSystemComposition.{u} A τ h k
  let a13 := finiteSystemComposition.{u} A τ j h
  let a0 := finiteSystemComposition.{u} A τ j (h ≫ k)
  let a1 := finiteSystemComposition.{u} A τ (j ≫ h) k
  let e := eqToIso (congrArg (finiteSystemPullback.{u} A τ) (Category.assoc j h k).symm)
  have ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13 := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact systemOrdinaryCoherence A τ j h k N
  have hh := descend_coherence F G H F02 F13
    (finiteSystemPullback.{u} A τ (j ≫ h ≫ k))
    (finiteSystemPullback.{u} A τ ((j ≫ h) ≫ k)) a02 a13 a0 a1 e ho
  have hm := NatTrans.congr_app hh S
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  have he := congrArg (fun t ↦ t.app S)
    (systemDerivedTransport A τ (Category.assoc j h k).symm)
  change (Functor.mapDerivedCategoryNatIso e).hom.app S = _ at he
  rw [he] at hm
  let E := eqToIso (congrArg (finiteSystemDerivedPullback.{u} A τ)
    (Category.assoc j h k).symm)
  have hm' : (finiteSystemDerivedComposition.{u} A τ j (h ≫ k)).hom.app S ≫
      (finiteSystemDerivedPullback.{u} A τ j).map
        ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) =
      E.hom.app S ≫ (finiteSystemDerivedComposition.{u} A τ (j ≫ h) k).hom.app S ≫
        (finiteSystemDerivedComposition.{u} A τ j h).hom.app
          ((finiteSystemDerivedPullback.{u} A τ k).obj S) := by
    simpa only [finiteSystemDerivedComposition, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using hm
  have hf := congrArg (fun t ↦ E.inv.app S ≫ t) hm'
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hf
  simpa only [Category.assoc, E, eqToIso.inv] using hf

private theorem systemComplexCoherence
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n) [∀ n, Finite (A n)]
    {Y Z W V : Scheme.{u}} (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) :
    eqToHom (congrArg (finiteSystemComplexPullback.{u} A τ) (Category.assoc j h k)) ≫
        (finiteSystemComplexComposition.{u} A τ j (h ≫ k)).hom ≫
        Functor.whiskerRight (finiteSystemComplexComposition.{u} A τ h k).hom
          (finiteSystemComplexPullback.{u} A τ j) =
      (finiteSystemComplexComposition.{u} A τ (j ≫ h) k).hom ≫
        Functor.whiskerLeft (finiteSystemComplexPullback.{u} A τ k)
          (finiteSystemComplexComposition.{u} A τ j h).hom ≫
        (Functor.associator (finiteSystemComplexPullback.{u} A τ k)
          (finiteSystemComplexPullback.{u} A τ h)
          (finiteSystemComplexPullback.{u} A τ j)).inv := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f, finiteSystemComplexComposition,
    NatIso.mapHomologicalComplex_hom_app_f]
  let E := eqToIso (congrArg (finiteSystemPullback.{u} A τ) (Category.assoc j h k).symm)
  have hf := congrArg (fun t ↦ E.inv.app (K.X i) ≫ t)
    (systemOrdinaryCoherence A τ j h k (K.X i))
  simp only [← Category.assoc] at hf
  exact hf

private theorem evaluatedTranspose
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    {L : C ⥤ D} {R : D ⥤ C} {l : c ⥤ d} {r : d ⥤ c}
    (adj : L ⊣ R) (level : l ⊣ r) (E : C ⥤ c) (F : D ⥤ d)
    (q : L ⋙ F ≅ E ⋙ l) (p : R ⋙ E ≅ F ⋙ r)
    (hu : ∀ M, E.map (adj.unit.app M) ≫ p.hom.app (L.obj M) ≫
      r.map (q.hom.app M) = level.unit.app (E.obj M))
    {M : C} {N : D} (a : L.obj M ⟶ N) :
    E.map ((adj.homEquiv M N) a) ≫ p.hom.app N =
      (level.homEquiv _ _) (q.inv.app M ≫ F.map a) := by
  rw [adj.homEquiv_unit, level.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hp := p.hom.naturality a
  dsimp only [Functor.comp_map] at hp
  rw [hp]
  have hu' : E.map (adj.unit.app M) ≫ p.hom.app (L.obj M) =
      level.unit.app (E.obj M) ≫ r.map (q.inv.app M) := by
    rw [← hu M]
    simp only [Category.assoc, ← r.map_comp, Iso.hom_inv_id_app]
    erw [r.map_id, Category.comp_id]
  rw [← Category.assoc, hu', Category.assoc]

private theorem evaluatedConjugate
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} {l₁ l₂ : c ⥤ d} {r₁ r₂ : d ⥤ c}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (level₁ : l₁ ⊣ r₁) (level₂ : l₂ ⊣ r₂) (E : C ⥤ c) (F : D ⥤ d)
    (q₁ : L₁ ⋙ F ≅ E ⋙ l₁) (p₁ : R₁ ⋙ E ≅ F ⋙ r₁)
    (q₂ : L₂ ⋙ F ≅ E ⋙ l₂) (p₂ : R₂ ⋙ E ≅ F ⋙ r₂)
    (hu₁ : ∀ M, E.map (adj₁.unit.app M) ≫ p₁.hom.app (L₁.obj M) ≫
      r₁.map (q₁.hom.app M) = level₁.unit.app (E.obj M))
    (hu₂ : ∀ M, E.map (adj₂.unit.app M) ≫ p₂.hom.app (L₂.obj M) ≫
      r₂.map (q₂.hom.app M) = level₂.unit.app (E.obj M))
    (a : L₁ ≅ L₂) (b : R₂ ≅ R₁) (α : l₁ ≅ l₂) (β : r₂ ≅ r₁)
    (ha : ∀ M, adj₁.unit.app M ≫ R₁.map (a.hom.app M) =
      adj₂.unit.app M ≫ b.hom.app (L₂.obj M))
    (hα : ∀ M, level₁.unit.app M ≫ r₁.map (α.hom.app M) =
      level₂.unit.app M ≫ β.hom.app (l₂.obj M))
    (hb : ∀ N, E.map (b.hom.app N) ≫ p₁.hom.app N =
      p₂.hom.app N ≫ β.hom.app (F.obj N)) (M : C) :
    F.map (a.hom.app M) ≫ q₂.hom.app M = q₁.hom.app M ≫ α.hom.app (E.obj M) := by
  apply (cancel_epi (q₁.inv.app M)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (level₁.homEquiv _ _).injective
  rw [level₁.homEquiv_naturality_right]
  rw [← evaluatedTranspose adj₁ level₁ E F q₁ p₁ hu₁]
  rw [Adjunction.homEquiv_unit, ha, Functor.map_comp]
  simp only [Category.assoc]
  rw [level₁.homEquiv_unit]
  rw [reassoc_of% hb]
  have hn := β.hom.naturality (q₂.hom.app M)
  simp only [Functor.comp_obj] at hn
  rw [← hn]
  have hh := congrArg (fun t ↦ t ≫ β.hom.app (l₂.obj (E.obj M))) (hu₂ M)
  rw [← hα (E.obj M)] at hh
  simpa only [Category.assoc] using hh

private def squareHorizontal
    {C D E c d e : Type*}
    [Category C] [Category D] [Category E] [Category c] [Category d] [Category e]
    {F : C ⥤ D} {G : D ⥤ E} {f : c ⥤ d} {g : d ⥤ e}
    {E₀ : C ⥤ c} {E₁ : D ⥤ d} {E₂ : E ⥤ e}
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g) :
    (F ⋙ G) ⋙ E₂ ≅ E₀ ⋙ (f ⋙ g) :=
  Functor.associator F G E₂ ≪≫ Functor.isoWhiskerLeft F qG ≪≫
    (Functor.associator F E₁ g).symm ≪≫ Functor.isoWhiskerRight qF g ≪≫
      Functor.associator E₀ f g

private theorem squareHorizontal_hom_app
    {C D E c d e : Type*}
    [Category C] [Category D] [Category E] [Category c] [Category d] [Category e]
    {F : C ⥤ D} {G : D ⥤ E} {f : c ⥤ d} {g : d ⥤ e}
    {E₀ : C ⥤ c} {E₁ : D ⥤ d} {E₂ : E ⥤ e}
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g) (M : C) :
    (squareHorizontal qF qG).hom.app M = qG.hom.app (F.obj M) ≫ g.map (qF.hom.app M) := by
  simp only [squareHorizontal, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem compositeEvaluationUnit
    {C D E c d e : Type*}
    [Category C] [Category D] [Category E] [Category c] [Category d] [Category e]
    {F : C ⥤ D} {G : D ⥤ E} {RF : D ⥤ C} {RG : E ⥤ D}
    {f : c ⥤ d} {g : d ⥤ e} {rf : d ⥤ c} {rg : e ⥤ d}
    (adjF : F ⊣ RF) (adjG : G ⊣ RG) (levelF : f ⊣ rf) (levelG : g ⊣ rg)
    (E₀ : C ⥤ c) (E₁ : D ⥤ d) (E₂ : E ⥤ e)
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g)
    (pF : RF ⋙ E₀ ≅ E₁ ⋙ rf) (pG : RG ⋙ E₁ ≅ E₂ ⋙ rg)
    (huF : ∀ M, E₀.map (adjF.unit.app M) ≫ pF.hom.app (F.obj M) ≫
      rf.map (qF.hom.app M) = levelF.unit.app (E₀.obj M))
    (huG : ∀ M, E₁.map (adjG.unit.app M) ≫ pG.hom.app (G.obj M) ≫
      rg.map (qG.hom.app M) = levelG.unit.app (E₁.obj M)) (M : C) :
    E₀.map ((adjF.comp adjG).unit.app M) ≫
      (squareHorizontal pG pF).hom.app ((F ⋙ G).obj M) ≫
      (rg ⋙ rf).map ((squareHorizontal qF qG).hom.app M) =
        (levelF.comp levelG).unit.app (E₀.obj M) := by
  simp only [squareHorizontal_hom_app, Adjunction.comp_unit_app, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  have hp := pF.hom.naturality (adjG.unit.app (F.obj M))
  dsimp only [Functor.comp_map] at hp
  rw [reassoc_of% hp]
  have hG := congrArg rf.map (huG (F.obj M))
  simp only [Functor.map_comp] at hG
  rw [reassoc_of% hG]
  have hn := levelG.unit.naturality (qF.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
  erw [← rf.map_comp, ← hn, rf.map_comp]
  have hF := congrArg (fun t ↦ t ≫ rf.map (levelG.unit.app (f.obj (E₀.obj M)))) (huF M)
  simpa only [Category.assoc] using hF

private theorem conjugateUnit
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (a : L₁ ≅ L₂) (b : R₂ ≅ R₁)
    (ha : conjugateIsoEquiv adj₂ adj₁ a = b) (M : C) :
    adj₁.unit.app M ≫ R₁.map (a.hom.app M) =
      adj₂.unit.app M ≫ b.hom.app (L₂.obj M) := by
  have hh := unit_conjugateEquiv adj₂ adj₁ a.hom M
  have he := congrArg Iso.hom ha
  change conjugateEquiv adj₂ adj₁ a.hom = b.hom at he
  rw [he] at hh
  exact hh.symm

private abbrev systemEvalP (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemPushforward.{u} A τ f ⋙ finiteSystemEvaluation.{u} A τ Y n ≅
      finiteSystemEvaluation.{u} A τ X n ⋙ proEtaleConstantRingPushforward (A n) f :=
  AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP
    (systemCoefficientRings.{u} A) (systemCoefficientMaps.{u} A τ) f n

private theorem systemEvalP_apply
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (N : finiteSystems.{u} A τ X)
    (U : Y.ProEt) (x : ((finiteSystemPushforward.{u} A τ f).obj N).val.obj (op (n, U))) :
    ((systemEvalP.{u} A τ f n).hom.app N).val.app (op U) x = x := by
  exact varyingDirectEvaluation_apply (systemCoefficientRings.{u} A)
    (systemCoefficientMaps.{u} A τ) f n N U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem systemEvaluationUnit (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (M : finiteSystems.{u} A τ Y) :
    (finiteSystemEvaluation.{u} A τ Y n).map
      ((finiteSystemAdjunction.{u} A τ f).unit.app M) ≫
      (systemEvalP.{u} A τ f n).hom.app ((finiteSystemPullback.{u} A τ f).obj M) ≫
      (proEtaleConstantRingPushforward (A n) f).map
        ((finiteSystemPullbackEvaluation.{u} A τ f n).hom.app M) =
      (proEtaleConstantRingAdjunction (A n) f).unit.app
        ((finiteSystemEvaluation.{u} A τ Y n).obj M) := by
  have hs := (finiteSystemPullbackEvaluation_existsUnique.{u} A τ f n).exists.choose_spec
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨U⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((finiteSystemPullbackEvaluation.{u} A τ f n).hom.app M).val.app
    (op ((proEtaleBaseChange f).obj U))
      (((systemEvalP.{u} A τ f n).hom.app ((finiteSystemPullback.{u} A τ f).obj M)).val.app (op U)
        (((finiteSystemAdjunction.{u} A τ f).unit.app M).val.app (op (n, U)) x)) = _
  have hh := congrArg (((finiteSystemPullbackEvaluation.{u} A τ f n).hom.app M).val.app
    (op ((proEtaleBaseChange f).obj U)))
      (varyingDirectEvaluation_apply (systemCoefficientRings.{u} A)
        (systemCoefficientMaps.{u} A τ) f n
        ((finiteSystemPullback.{u} A τ f).obj M) U
        (((finiteSystemAdjunction.{u} A τ f).unit.app M).val.app (op (n, U)) x))
  apply hh.trans
  unfold finiteSystemPullbackEvaluation
  with_unfolding_all exact hs M U x

private theorem systemEvaluationComposition
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n) [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (M : finiteSystems.{u} A τ V) (n : ℕ) :
    (finiteSystemEvaluation.{u} A τ Z n).map
        ((finiteSystemComposition.{u} A τ h k).hom.app M) ≫
      (finiteSystemPullbackEvaluation.{u} A τ h n).hom.app
        ((finiteSystemPullback.{u} A τ k).obj M) ≫
      (proEtaleConstantRingPullback (A n) h).map
        ((finiteSystemPullbackEvaluation.{u} A τ k n).hom.app M) =
    (finiteSystemPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app M ≫
      (finiteSystemModuleComposition.{u} A h k n).hom.app
        ((finiteSystemEvaluation.{u} A τ V n).obj M) := by
  obtain ⟨d, he, hd⟩ :=
    (finiteSystemComposition_existsUnique.{u} A τ h k).exists.choose_spec
  obtain ⟨δ, hδ, hα⟩ := (proEtaleConstantRingModulePullbackComposition h k (A n)).choose_spec
  have hsys : conjugateIsoEquiv
      ((finiteSystemAdjunction.{u} A τ k).comp (finiteSystemAdjunction.{u} A τ h))
      (finiteSystemAdjunction.{u} A τ (h ≫ k)) (finiteSystemComposition.{u} A τ h k) = d := by
    simpa only [finiteSystemComposition] using he
  have hlev : conjugateIsoEquiv
      ((proEtaleConstantRingAdjunction (A n) k).comp
        (proEtaleConstantRingAdjunction (A n) h))
      (proEtaleConstantRingAdjunction (A n) (h ≫ k))
      (finiteSystemModuleComposition.{u} A h k n) = δ := by
    simpa only [finiteSystemModuleComposition] using hα
  have hb : ∀ N : finiteSystems.{u} A τ Z,
      (finiteSystemEvaluation.{u} A τ V n).map (d.hom.app N) ≫
        (systemEvalP.{u} A τ (h ≫ k) n).hom.app N =
      (squareHorizontal (systemEvalP.{u} A τ h n)
        (systemEvalP.{u} A τ k n)).hom.app N ≫
        δ.hom.app ((finiteSystemEvaluation.{u} A τ Z n).obj N) := by
    intro N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain ⟨U⟩ := U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [squareHorizontal_hom_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, CategoryTheory.comp_apply]
    change ((systemEvalP.{u} A τ (h ≫ k) n).hom.app N).val.app (op U)
        ((d.hom.app N).val.app (op (n, U)) x) =
      (δ.hom.app ((finiteSystemEvaluation.{u} A τ Z n).obj N)).val.app (op U)
        (((systemEvalP.{u} A τ h n).hom.app N).val.app
          (op ((proEtaleBaseChange k).obj U))
          (((systemEvalP.{u} A τ k n).hom.app
            ((finiteSystemPushforward.{u} A τ h).obj N)).val.app (op U) x))
    have hl := systemEvalP_apply A τ (h ≫ k) n N U
      ((d.hom.app N).val.app (op (n, U)) x)
    have hr := congrArg (fun y ↦
      (δ.hom.app ((finiteSystemEvaluation.{u} A τ Z n).obj N)).val.app (op U)
        (((systemEvalP.{u} A τ h n).hom.app N).val.app
          (op ((proEtaleBaseChange k).obj U)) y))
      (systemEvalP_apply A τ k n ((finiteSystemPushforward.{u} A τ h).obj N) U x)
    have hr' := congrArg
      ((δ.hom.app ((finiteSystemEvaluation.{u} A τ Z n).obj N)).val.app (op U))
      (systemEvalP_apply A τ h n N ((proEtaleBaseChange k).obj U) x)
    exact hl.trans ((hd N n U x).trans
      ((hδ ((finiteSystemEvaluation.{u} A τ Z n).obj N) U x).symm.trans
        (hr.trans hr').symm))
  have hh := evaluatedConjugate
    (finiteSystemAdjunction.{u} A τ (h ≫ k))
    ((finiteSystemAdjunction.{u} A τ k).comp (finiteSystemAdjunction.{u} A τ h))
    (proEtaleConstantRingAdjunction (A n) (h ≫ k))
    ((proEtaleConstantRingAdjunction (A n) k).comp
      (proEtaleConstantRingAdjunction (A n) h))
    (finiteSystemEvaluation.{u} A τ V n) (finiteSystemEvaluation.{u} A τ Z n)
    (finiteSystemPullbackEvaluation.{u} A τ (h ≫ k) n)
    (systemEvalP.{u} A τ (h ≫ k) n)
    (squareHorizontal (finiteSystemPullbackEvaluation.{u} A τ k n)
      (finiteSystemPullbackEvaluation.{u} A τ h n))
    (squareHorizontal (systemEvalP.{u} A τ h n) (systemEvalP.{u} A τ k n))
    (systemEvaluationUnit A τ (h ≫ k) n)
    (compositeEvaluationUnit (finiteSystemAdjunction.{u} A τ k)
      (finiteSystemAdjunction.{u} A τ h) (proEtaleConstantRingAdjunction (A n) k)
      (proEtaleConstantRingAdjunction (A n) h)
      (finiteSystemEvaluation.{u} A τ V n) (finiteSystemEvaluation.{u} A τ W n)
      (finiteSystemEvaluation.{u} A τ Z n)
      (finiteSystemPullbackEvaluation.{u} A τ k n)
      (finiteSystemPullbackEvaluation.{u} A τ h n)
      (systemEvalP.{u} A τ k n) (systemEvalP.{u} A τ h n)
      (systemEvaluationUnit A τ k n) (systemEvaluationUnit A τ h n))
    (finiteSystemComposition.{u} A τ h k) d (finiteSystemModuleComposition.{u} A h k n) δ
    (conjugateUnit _ _ _ _ hsys) (conjugateUnit _ _ _ _ hlev) hb M
  simpa only [squareHorizontal_hom_app] using hh

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section CanonicalLevelStructures

-- Fix the same level structures as the canonical finite-coefficient derived operations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable local instance (priority := 4000) coefficientAbelian (X : Scheme.{u})
    (B : Type u) [CommRing B] :
    Abelian (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X B)) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing.{u} X B))
    (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
    (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology X))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable local instance (priority := 4000) coefficientDerived (X : Scheme.{u})
    (B : Type u) [CommRing B] :
    HasDerivedCategory (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X B)) :=
  proEtaleRingModules_hasDerivedCategory.{u} X (proEtaleConstantRing.{u} X B)

private theorem systemDerivedEvaluationComposition
    (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n) [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ)
    (hOrd : ∀ M : finiteSystems.{u} A τ V,
      (finiteSystemEvaluation.{u} A τ Z n).map
        ((finiteSystemComposition.{u} A τ h k).hom.app M) ≫
        (finiteSystemPullbackEvaluation.{u} A τ h n).hom.app
          ((finiteSystemPullback.{u} A τ k).obj M) ≫
        (proEtaleConstantRingPullback (A n) h).map
          ((finiteSystemPullbackEvaluation.{u} A τ k n).hom.app M) =
      (finiteSystemPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app M ≫
        (finiteSystemModuleComposition.{u} A h k n).hom.app
          ((finiteSystemEvaluation.{u} A τ V n).obj M))
    (S : finiteSystemDerived.{u} A τ V) :
    (finiteSystemDerivedEvaluation.{u} A τ Z n).map
        ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) ≫
      (finiteSystemDerivedPullbackEvaluation.{u} A τ h n).hom.app
        ((finiteSystemDerivedPullback.{u} A τ k).obj S) ≫
      (proEtaleConstantRingDerivedPullback (A n) h).map
        ((finiteSystemDerivedPullbackEvaluation.{u} A τ k n).hom.app S) =
    (finiteSystemDerivedPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app S ≫
      (proEtaleConstantRingPullbackComposition h k (A n)).inv.app
        ((finiteSystemDerivedEvaluation.{u} A τ V n).obj S) := by
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (finiteSystemPullback.{u} A τ k) (finiteSystemPullback.{u} A τ h)
    (finiteSystemPullback.{u} A τ (h ≫ k))
    (proEtaleConstantRingPullback (A n) k) (proEtaleConstantRingPullback (A n) h)
    (proEtaleConstantRingPullback (A n) (h ≫ k))
    (finiteSystemEvaluation.{u} A τ V n) (finiteSystemEvaluation.{u} A τ W n)
    (finiteSystemEvaluation.{u} A τ Z n)
    (finiteSystemPullbackEvaluation.{u} A τ k n)
    (finiteSystemPullbackEvaluation.{u} A τ h n)
    (finiteSystemPullbackEvaluation.{u} A τ (h ≫ k) n)
    (finiteSystemComposition.{u} A τ h k) (finiteSystemModuleComposition.{u} A h k n) hOrd
  have hi {X Y : Scheme.{u}} (f : X ⟶ Y) :
      (Functor.mapDerivedCategorySquareIso
        (finiteSystemPullbackEvaluation.{u} A τ f n)) =
      (finiteSystemDerivedPullbackEvaluation.{u} A τ f n) := by
    with_unfolding_all rfl
  have hc : (proEtaleConstantRingPullbackComposition h k (A n)).symm =
      (Functor.mapDerivedCategoryNatIso (finiteSystemModuleComposition.{u} A h k n) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (proEtaleConstantRingPullback (A n) k)
          (proEtaleConstantRingPullback (A n) h)).symm) := by
    simpa only [finiteSystemModuleComposition] using
      proEtaleConstantRingPullbackComposition_eq_mapModuleComparison h k (A n)
  simp only [hi] at hd
  rw [← hc] at hd
  have hn :
      Functor.isoWhiskerRight (finiteSystemDerivedComposition.{u} A τ h k)
          (finiteSystemDerivedEvaluation.{u} A τ Z n) ≪≫
        squareHorizontal (finiteSystemDerivedPullbackEvaluation.{u} A τ k n)
          (finiteSystemDerivedPullbackEvaluation.{u} A τ h n) =
      finiteSystemDerivedPullbackEvaluation.{u} A τ (h ≫ k) n ≪≫
        Functor.isoWhiskerLeft (finiteSystemDerivedEvaluation.{u} A τ V n)
          (proEtaleConstantRingPullbackComposition h k (A n)).symm := by
    simpa only [finiteSystemDerivedComposition, finiteSystemDerivedEvaluation,
      finiteSystemDerivedPullback, proEtaleConstantRingDerivedPullback, squareHorizontal] using hd
  have hm := NatTrans.congr_app (congrArg Iso.hom hn) S
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, squareHorizontal_hom_app] using hm

end CanonicalLevelStructures

/-- The finite-system comparisons have their specified levelwise realizations and
satisfy associativity before and after ordinary localization.
Source: Stacks 03D3, 03D7, 03D8, 0B65, 015F, 0D6D
(blueprint: lem-pod-finite-system-pullback-coherence).
Proof: (1) Constant-section naturality gives compatibility with coefficient maps,
including the adjoint coefficient square for direct image. Restrict the level
module adjunctions to transition-compatible families to obtain the system
adjunction with its componentwise unit. (2) The fibre-product restriction maps
commute with every sheaf map and scalar action, giving whole-system right-adjoint
comparisons. Their two triple composites have equal fibre-product projections,
hence agree. (3) Conjugate these maps under the system adjunctions. Evaluation of
the unit equation is the level unit equation, so conjugation uniqueness identifies
each evaluated map with the published canonical module comparison. In particular
these maps commute with semilinear transitions before deriving. (4) Apply
leftAdjointCompIso_assoc to the six adjunctions and invert the resulting equation.
Apply it degreewise to complexes: naturality in the differential makes these
chain maps, and the equation is an equation of natural transformations of complex
functors. (5) Exactness permits ordinary termwise localization. The localization
universal property transports the equation to derived systems. (6) Evaluation is
exact and termwise. On a flat-term K-flat resolution the published finite derived
comparison is the localization of precisely the same module map, by Tag 0D6D.
Exactness preserves the resolution quasi-isomorphisms, so naturality extends this
identification to every complex. No transition is tensored along a coefficient
map, and no normalization or boundedness is used. -/
theorem finiteSystemPullbackCoherence [∀ n, Finite (A n)]
    {Y Z W V : Scheme.{u}} (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) :
    (∀ (M : finiteSystems.{u} A τ V) (n : ℕ),
      (finiteSystemEvaluation.{u} A τ Z n).map ((finiteSystemComposition.{u} A τ h k).hom.app M) ≫
          (finiteSystemPullbackEvaluation.{u} A τ h n).hom.app
            ((finiteSystemPullback.{u} A τ k).obj M) ≫
          (proEtaleConstantRingPullback (A n) h).map
            ((finiteSystemPullbackEvaluation.{u} A τ k n).hom.app M) =
        (finiteSystemPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app M ≫
          (finiteSystemModuleComposition.{u} A h k n).hom.app
            ((finiteSystemEvaluation.{u} A τ V n).obj M)) ∧
    (∀ (S : finiteSystemDerived.{u} A τ V) (n : ℕ),
      (finiteSystemDerivedEvaluation.{u} A τ Z n).map
          ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) ≫
          (finiteSystemDerivedPullbackEvaluation.{u} A τ h n).hom.app
            ((finiteSystemDerivedPullback.{u} A τ k).obj S) ≫
          (proEtaleConstantRingDerivedPullback (A n) h).map
            ((finiteSystemDerivedPullbackEvaluation.{u} A τ k n).hom.app S) =
        (finiteSystemDerivedPullbackEvaluation.{u} A τ (h ≫ k) n).hom.app S ≫
          (proEtaleConstantRingPullbackComposition h k (A n)).inv.app
            ((finiteSystemDerivedEvaluation.{u} A τ V n).obj S)) ∧
    (eqToHom (congrArg (finiteSystemComplexPullback.{u} A τ) (Category.assoc j h k)) ≫
        (finiteSystemComplexComposition.{u} A τ j (h ≫ k)).hom ≫
        Functor.whiskerRight (finiteSystemComplexComposition.{u} A τ h k).hom
          (finiteSystemComplexPullback.{u} A τ j) =
      (finiteSystemComplexComposition.{u} A τ (j ≫ h) k).hom ≫
        Functor.whiskerLeft (finiteSystemComplexPullback.{u} A τ k)
          (finiteSystemComplexComposition.{u} A τ j h).hom ≫
        (Functor.associator (finiteSystemComplexPullback.{u} A τ k)
          (finiteSystemComplexPullback.{u} A τ h) (finiteSystemComplexPullback.{u} A τ j)).inv) ∧
    (∀ S : finiteSystemDerived.{u} A τ V,
      (eqToHom (congrArg (finiteSystemDerivedPullback.{u} A τ) (Category.assoc j h k))).app S ≫
          (finiteSystemDerivedComposition.{u} A τ j (h ≫ k)).hom.app S ≫
          (finiteSystemDerivedPullback.{u} A τ j).map
            ((finiteSystemDerivedComposition.{u} A τ h k).hom.app S) =
        (finiteSystemDerivedComposition.{u} A τ (j ≫ h) k).hom.app S ≫
          (finiteSystemDerivedComposition.{u} A τ j h).hom.app
            ((finiteSystemDerivedPullback.{u} A τ k).obj S)) := by
  refine ⟨?_, ?_, systemComplexCoherence A τ j h k, systemDerivedCoherence A τ j h k⟩
  · intro M n
    exact systemEvaluationComposition A τ h k M n
  · intro S n
    exact systemDerivedEvaluationComposition A τ h k n
      (fun M ↦ systemEvaluationComposition A τ h k M n) S

end WeilConjectures
