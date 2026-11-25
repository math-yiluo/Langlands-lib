/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.SixFunctors.BundledTensorComparison
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryTensorPullbackData
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Ambient constant-coefficient pullback and tensor coherence

Source: Stacks Project, sites-modules.tex, Tags 03D3 and 03EL; sites.tex, Tag 03CB;
sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-sf-ambient-pullback-site-constructions).

`some n` denotes the positive finite exponent n+1; `none` denotes the entire
semilinear system on the ringed sequence site. All system morphisms below live
on that site, including their horizontal restriction maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor

/-- The actual finite or sequence site. Source: Stacks 0941 and 09A5
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
def Site (X : Scheme.{t}) : Option ℕ → Type (t + 1)
  | some _ => X.ProEt
  | none => ℕ × X.ProEt

/-- The unchanged category structure of the chosen site. Source: Stacks 0941
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
instance siteCategory (X : Scheme.{t}) (s : Option ℕ) : Category.{t} (Site X s) :=
  match s with
  | some _ => inferInstanceAs (Category.{t} X.ProEt)
  | none => inferInstanceAs (Category.{t} (ℕ × X.ProEt))

/-- Vertical covering topology, or the ordinary small pro-etale topology.
Source: Stacks 0941 and 09A5 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def topology (X : Scheme.{t}) : (s : Option ℕ) → GrothendieckTopology (Site X s)
  | some _ => Scheme.ProEt.topology X
  | none => coefficientSequenceTopology (Scheme.ProEt.topology X)

/-- The original small site is small relative to the coefficient universe.
Source: Stacks 0941 (blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: the pro-etale site has object universe t+1 and Hom universe t. Its product
with the countable poset has the same bound; take its small model and enlarge
only the coefficient universe. -/
@[instance] theorem siteSmall (X : Scheme.{t}) (s : Option ℕ) :
    EssentiallySmall.{max u (t + 1)} (Site X s) := by
  cases s <;> exact essentiallySmallSelf _

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Precisely the recorded quotient ring sheaf or ringed sequence ring sheaf.
Source: Stacks 0941 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def coefficients (X : Scheme.{t}) :
    (s : Option ℕ) → Sheaf (topology X s) CommRingCat.{max u (t + 1)}
  | some n => integralCoefficientCommRingSheaf ell E X n
  | none => coefficientSequenceCommRingSheaf ell E X

/-- Canonical module sheaves, with arbitrary semilinear horizontal restrictions.
Source: Stacks 03D1 and 0941 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
abbrev Modules (X : Scheme.{t}) (s : Option ℕ) :=
  WeilConjectures.SemilinearSections.Mod.{t + 1, t, max u (t + 1)}
    (topology X s) (coefficients ell E X s)

/-- Ordinary unbounded derived category; no completion or cartesian condition.
Source: Stacks 05RU (blueprint: lem-sf-ambient-pullback-site-constructions). -/
abbrev Derived (X : Scheme.{t}) (s : Option ℕ) :=
  WeilConjectures.SemilinearSections.D.{t + 1, t, max u (t + 1)}
    (topology X s) (coefficients ell E X s)

/-- Base change acts simultaneously on the entire sequence site.
Source: Stacks 03CB and 0941 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def base {X Y : Scheme.{t}} (f : X ⟶ Y) : (s : Option ℕ) → Site Y s ⥤ Site X s
  | some _ => Scheme.proEtaleBaseChange f
  | none => (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Base change is continuous for vertical covers. Source: Stacks 03CB and 0941
(blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: pull back a vertical covering sieve at the same index, using continuity
of pro-etale base change. This works also on horizontal arrows by stability
of vertical covers under pullback. -/
@[instance] theorem baseContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (base f s).IsContinuous (topology Y s) (topology X s) := by
  cases s with
  | some n =>
    change (Scheme.proEtaleBaseChange f).IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)
    infer_instance
  | none => exact ProEtale.VaryingRing.baseChange_continuous f

/-- The prescribed map on constant-ring sections, at each actual sequence index.
Source: Stacks 0H7J and 0941 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def ringComponent {X Y : Scheme.{t}} (f : X ⟶ Y) : (s : Option ℕ) →
    ∀ U : (Site Y s)ᵒᵖ, (coefficients ell E Y s).obj.obj U ⟶
      (coefficients ell E X s).obj.obj ((base f s).op.obj U)
  | some n, U => (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing ell E (n + 1))))
        ).hom.app U
  | none, U => (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing ell E (U.unop.1 + 1))))).hom.app (op U.unop.2)

private theorem constantMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
      Scheme.coefficientProEtaleDirectRingMap.{t, u} f B =
    Scheme.coefficientProEtaleDirectRingMap.{t, u} f A ≫
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv _ _)
      ((presheafToSheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}).map
        ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.coefficientProEtaleDirectRingMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun z ↦ z.app ((Scheme.proEtaleBaseChange f).op.obj U))
    ((toSheafification (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

/-- Constant-section maps commute with every vertical and horizontal restriction.
Source: Stacks 0H7J, 03CB and 0941 (blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: vertical naturality is that of the sheafification extension. At a quotient
transition, both composites send each constant coefficient to its reduced constant
section. Sheafification uniqueness proves equality. Composite transitions follow
by composition, with no assumption on a module transition. -/
theorem ringComponent_naturality {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    {U V : (Site Y s)ᵒᵖ} (a : U ⟶ V) :
    (coefficients ell E Y s).obj.map a ≫ ringComponent ell E f s V =
      ringComponent ell E f s U ≫ (coefficients ell E X s).obj.map ((base f s).op.map a) := by
  cases s with
  | some n =>
    exact (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing ell E (n + 1))))).hom.naturality a
  | none =>
    let δ : coefficientSequenceCommRingSystem ell E Y ⟶
        coefficientSequenceCommRingSystem ell E X ⋙
          (Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
              (Scheme.ProEt.topology X) :=
      NatTrans.ofOpSequence
        (fun n ↦ Scheme.coefficientProEtaleDirectRingMap.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing ell E (n + 1))))) (by
          intro n
          dsimp only [coefficientSequenceCommRingSystem, Functor.comp_map]
          simp only [Functor.ofOpSequence_map_homOfLE_succ]
          let a : CommRingCat.of
              (ULift.{t + 1} (Padic.coefficientExtensionRing ell E (n + 2))) ⟶
              CommRingCat.of
                (ULift.{t + 1} (Padic.coefficientExtensionRing ell E (n + 1))) :=
            CommRingCat.ofHom
              ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
                ((Padic.coefficientExtensionTransition ell E (n + 1)).comp
                  (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
          have ht (W : Scheme.{t}) : coefficientSequenceCommRingTransition ell E W n =
              (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).map a := by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext V
            apply CommRingCat.hom_ext
            rfl
          rw [ht Y, ht X]
          exact constantMap_naturality f a)
    let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := Y.ProEt)).functor
      (Functor.uncurry.map (Functor.whiskerRight δ
        (sheafToPresheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})))
    exact ε.naturality a

/-- The constructed coefficient morphism on the ringed site, before any evaluation.
Source: Stacks 03D3 and 0941 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def ringUnit {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    coefficients ell E Y s ⟶
      ((base f s).sheafPushforwardContinuous CommRingCat (topology Y s)
        (topology X s)).obj (coefficients ell E X s) :=
  ⟨{ app := ringComponent ell E f s
     naturality := fun {_ _} a ↦ ringComponent_naturality ell E f s a }⟩

/-- Constant-ring direct image on the very same site.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
abbrev ringPush {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :=
  (base f s).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (topology Y s) (topology X s)

/-- The ring-sheaf inverse-image adjunction exists without identifying universes.
Source: Stacks 00VC and 03CB (blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: use left Kan extension followed by sheafification on a coefficient-sized
small model of the site, and transport the adjunction back to the original site.
The product sequence site has the same size bound. -/
@[instance] theorem ringPushRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (ringPush.{t, u} f s).IsRightAdjoint := by
  have : PreservesFilteredColimitsOfSize.{max u (t + 1), max u (t + 1)}
      (CategoryTheory.forget CommRingCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink _
  let K := (equivSmallModel.{max u (t + 1)} (Site X s)).inverse.inducedTopology
    (topology X s)
  have : HasSheafify K CommRingCat.{max u (t + 1)} := by infer_instance
  have : HasSheafify (topology X s) CommRingCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite (topology X s) CommRingCat.{max u (t + 1)}
  have : ∀ P : (Site Y s)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)},
      (base f s).op.HasLeftKanExtension P := by
    intro P
    have : ∀ U : (Site X s)ᵒᵖ,
        HasColimitsOfShape (CostructuredArrow (base f s).op U)
          CommRingCat.{max u (t + 1)} := fun _ ↦
      hasColimitsOfShape_of_essentiallySmall _ _
    infer_instance
  unfold ringPush
  infer_instance

/-- Canonical inverse image of ring sheaves, with its specified adjunction.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
abbrev ringPull {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :=
  (ringPush.{t, u} f s).leftAdjoint

/-- The actual coefficient morphism c_f, the adjunct of constant sections.
Source: Stacks 0H7J and 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def ringMap {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (ringPull.{t, u} f s).obj (coefficients ell E Y s) ⟶ coefficients ell E X s :=
  ((Adjunction.ofIsRightAdjoint (ringPush.{t, u} f s)).homEquiv _ _).symm
    (ringUnit ell E f s)

/-- Underlying ring map for the recorded module-pushforward construction.
Source: Stacks 03D1 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def moduleRingUnit {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    ring (topology Y s) (coefficients ell E Y s) ⟶
      ((base f s).sheafPushforwardContinuous RingCat (topology Y s)
        (topology X s)).obj (ring (topology X s) (coefficients ell E X s)) :=
  ⟨Functor.whiskerRight (ringUnit ell E f s).hom (forget₂ CommRingCat RingCat)⟩

/-- Actual sectionwise module direct image, with the canonical scalar action.
Source: Stacks 03D1 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def push {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    Modules ell E X s ⥤ Modules ell E Y s :=
  SheafOfModules.pushforward (moduleRingUnit ell E f s)

/-- The ordinary adjoint exists on the same ringed site. Source: Stacks 03D7
(blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: apply module pullback existence in the coefficient universe containing
both site universes, using free presentations followed by module sheafification.
The unit is the usual insertion m ↦ m tensor 1. -/
@[instance] theorem pushRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (push ell E f s).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (moduleRingUnit ell E f s)

/-- The recorded module pullback construction applied to the actual ringed site.
Source: Stacks 03D7 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def pull {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    Modules ell E Y s ⥤ Modules ell E X s :=
  (push ell E f s).leftAdjoint

/-- The specified insertion-normalized ordinary adjunction.
Source: Stacks 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def adjunction {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    pull ell E f s ⊣ push ell E f s :=
  Adjunction.ofIsRightAdjoint (push ell E f s)

set_option maxHeartbeats 35000 in
-- Bound elaboration while checking the adjunction comparison.
private theorem finitePullLimits {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits (pull ell E f (some n)) := by
  let A := CommRingCat.of (ULift.{t + 1}
    (Padic.coefficientExtensionRing ell E (n + 1)))
  have := (Scheme.coefficientProEtaleModulePullback_exact.{t, u} f A).1
  let e := (adjunction ell E f (some n)).leftAdjointUniq
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f A)
  exact preservesFiniteLimits_of_natIso e.symm

attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

private local instance sliceNoneContinuous (X : Scheme.{t}) (n : ℕ) :
    (Prod.sectR n X.ProEt).IsContinuous (Scheme.ProEt.topology X) (topology X none) :=
  inferInstanceAs ((Prod.sectR n X.ProEt).IsContinuous (Scheme.ProEt.topology X)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)))

private local instance sliceSomeContinuous (X : Scheme.{t}) (n : ℕ) :
    (Prod.sectR n X.ProEt).IsContinuous (topology X (some n))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) :=
  inferInstanceAs ((Prod.sectR n X.ProEt).IsContinuous (Scheme.ProEt.topology X)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)))

private local instance mixedBaseContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (base f none).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (topology X none) := baseContinuous f none

private theorem moduleRingUnit_slice {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) (U : Y.ProEtᵒᵖ) :
    (moduleRingUnit ell E f none).hom.app (op (n, U.unop)) =
      (moduleRingUnit ell E f (some n)).hom.app U := rfl

private theorem ringPush_map_app.{w} {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] {R S : Sheaf K RingCat.{w}} (a : R ⟶ S)
    (U : Cᵒᵖ) :
    ((F.sheafPushforwardContinuous RingCat.{w} J K).map a).hom.app U =
      a.hom.app (F.op.obj U) := rfl

set_option maxHeartbeats 35000 in
-- Bound elaboration while checking the ring transports.
private def sequencePushEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    push ell E f none ⋙ coefficientSequenceEvaluation ell E Y n ≅
      coefficientSequenceEvaluation ell E X n ⋙ push ell E f (some n) := by
  let a := eqToHom (coefficientSequenceEvaluationRing_eq ell E Y n).symm
  let b := eqToHom (coefficientSequenceEvaluationRing_eq ell E X n).symm
  have : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := baseContinuous f none
  have : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
      (topology Y none) (topology X none) := baseContinuous f none
  have := Functor.isContinuous_comp (Prod.sectR n Y.ProEt)
    ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)) (Scheme.ProEt.topology Y)
      (topology Y none) (topology X none)
  have := Functor.isContinuous_comp (Scheme.proEtaleBaseChange f) (Prod.sectR n X.ProEt)
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (topology X none)
  letI : (Prod.sectR n Y.ProEt).IsContinuous
      (Scheme.ProEt.topology Y) (topology Y none) := sliceNoneContinuous Y n
  letI : (base f none).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (topology X none) :=
    mixedBaseContinuous f
  letI : (Prod.sectR n Y.ProEt ⋙ base f none).IsContinuous
      (Scheme.ProEt.topology Y) (topology X none) :=
    Functor.isContinuous_comp _ _ _ (topology Y none) _
  letI : (Prod.sectR n X.ProEt).IsContinuous (topology X (some n))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := sliceSomeContinuous X n
  have h : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat
      (Scheme.ProEt.topology Y) (topology Y none)).map (moduleRingUnit ell E f none) =
      moduleRingUnit ell E f (some n) ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have ha : a.hom.app U = 𝟙 _ := by
      dsimp only [a]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hb : b.hom.app ((Scheme.proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
      dsimp only [b]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ringPush_map_app, ha, Category.id_comp]
    rw [hb]
    exact (moduleRingUnit_slice ell E f n U).trans
      (CategoryTheory.Category.comp_id _).symm
  exact SheafOfModules.pushforwardComp a (moduleRingUnit ell E f none) ≪≫
    SheafOfModules.pushforwardCongr h ≪≫
      (SheafOfModules.pushforwardComp (moduleRingUnit ell E f (some n)) b).symm

attribute [local irreducible] sequencePushEvaluation

set_option maxHeartbeats 35000 in
-- Bound elaboration while checking the mate interface.
private def sequencePullEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    pull ell E f none ⋙ coefficientSequenceEvaluation ell E X n ≅
      coefficientSequenceEvaluation ell E Y n ⋙ pull ell E f (some n) := by
  have : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := baseContinuous f none
  have : IsIso ((mateEquiv (adjunction ell E f none)
      (adjunction ell E f (some n))).symm (sequencePushEvaluation ell E f n).hom) :=
    WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (Scheme.proEtaleBaseChange f)
      _ _ n (moduleRingUnit ell E f none) _ _
      (coefficientSequenceEvaluationRing_eq ell E Y n)
      (coefficientSequenceEvaluationRing_eq ell E X n)
      (moduleRingUnit ell E f (some n)) (pull ell E f none) (pull ell E f (some n))
      (adjunction ell E f none) (adjunction ell E f (some n))
      (sequencePushEvaluation ell E f n)
  exact (asIso ((mateEquiv (adjunction ell E f none)
    (adjunction ell E f (some n))).symm (sequencePushEvaluation ell E f n).hom)).symm

attribute [local irreducible] sequencePullEvaluation

/-- Exactness on the entire system category. Source: Stacks 03D3 and 0941
(blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: constant coefficient inverse image is exact at every level. Kernels and
sheafified cokernels of semilinear systems are componentwise, so the simultaneous
ringed-site pullback is additive and exact without restrictions on transitions. -/
theorem pullExact {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (pull ell E f s).Additive ∧ PreservesFiniteLimits (pull ell E f s) ∧
      PreservesFiniteColimits (pull ell E f s) := by
  have : (push ell E f s).Additive := by
    constructor
    intro M N a b
    ext U m
    rfl
  have hadd : (pull ell E f s).Additive :=
    (adjunction ell E f s).left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} (pull ell E f s) :=
    (adjunction ell E f s).leftAdjoint_preservesColimits
  refine ⟨hadd, ?_, PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _⟩
  cases s with
  | some n => exact finitePullLimits ell E f n
  | none =>
    have hlim (n : ℕ) :
        PreservesFiniteLimits (pull ell E f none ⋙ coefficientSequenceEvaluation ell E X n) := by
      have := finitePullLimits ell E f n
      have := (coefficientSequenceEvaluation_exact ell E Y n).1
      exact preservesFiniteLimits_of_natIso (sequencePullEvaluation ell E f n).symm
    generalize hF : pull ell E f none = F at hlim ⊢
    let Rseq := (sheafCompose (topology X none)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficients ell E X none)
    let T := SheafOfModules.forget Rseq ⋙ PresheafOfModules.toPresheaf Rseq.obj
    have : PreservesFiniteLimits (F ⋙ T) := by
      constructor
      intro I _ _
      apply preservesLimitsOfShape_of_evaluation
      intro V
      have := hlim V.unop.1
      let Rn := (sheafCompose (topology X (some V.unop.1))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficients ell E X (some V.unop.1))
      let Tn := SheafOfModules.forget Rn ⋙ PresheafOfModules.toPresheaf Rn.obj
      let e : (F ⋙ T) ⋙ (CategoryTheory.evaluation _ _).obj V ≅
          (F ⋙ coefficientSequenceEvaluation ell E X V.unop.1) ⋙ Tn ⋙
            (CategoryTheory.evaluation _ _).obj (op V.unop.2) :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
      have : PreservesLimitsOfShape I
          ((F ⋙ coefficientSequenceEvaluation ell E X V.unop.1) ⋙ Tn ⋙
            (CategoryTheory.evaluation _ _).obj (op V.unop.2)) := inferInstance
      exact preservesLimitsOfShape_of_natIso e.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F T

/-- Additivity of the actual module inverse image. Source: Stacks 03D3
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
instance pullAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    (pull ell E f s).Additive := (pullExact ell E f s).1

/-- Left exactness of the actual module inverse image. Source: Stacks 03D3
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
instance pullLimits {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    PreservesFiniteLimits (pull ell E f s) := (pullExact ell E f s).2.1

/-- Right exactness of the actual module inverse image. Source: Stacks 03D3
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
instance pullColimits {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    PreservesFiniteColimits (pull ell E f s) := (pullExact ell E f s).2.2

/-- Exact localization of the specified pullback on unbounded complexes.
Source: Stacks 015F (blueprint: lem-sf-ambient-pullback-site-constructions). -/
abbrev derivedPull {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    Derived ell E Y s ⥤ Derived ell E X s := (pull ell E f s).mapDerivedCategory

/-- Canonical fibre-product comparison on sites, retaining the sequence index.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def baseComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (s : Option ℕ) → base (f ≫ g) s ≅ base g s ⋙ base f s
  | some _ => MorphismProperty.Over.pullbackComp f g
  | none => NatIso.prod (Iso.refl (𝟭 ℕ)) (MorphismProperty.Over.pullbackComp f g)

/-- Canonical direct-image composition for ring sheaves.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def ringPushComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :
    ringPush.{t, u} f s ⋙ ringPush.{t, u} g s ≅ ringPush.{t, u} (f ≫ g) s :=
  Functor.sheafPushforwardContinuousComp' (eFG := (baseComp f g s).symm)
    CommRingCat.{max u (t + 1)} (topology Z s) (topology Y s) (topology X s)

/-- The canonical inverse-image compositor alpha, as an adjunction mate.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def ringComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :
    ringPull.{t, u} (f ≫ g) s ≅ ringPull.{t, u} g s ⋙ ringPull.{t, u} f s :=
  (Adjunction.leftAdjointCompIso
    (Adjunction.ofIsRightAdjoint (ringPush.{t, u} g s))
    (Adjunction.ofIsRightAdjoint (ringPush.{t, u} f s))
    (Adjunction.ofIsRightAdjoint (ringPush.{t, u} (f ≫ g) s))
    (ringPushComp f g s)).symm

private theorem constantMap_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (Scheme.coefficientProEtaleDirectRingMap.{t, u} f A).hom.app U =
    (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((Scheme.proEtaleBaseChange f).op.obj U) := by
  have h := (sheafificationAdjunction (Scheme.ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
            (Scheme.ProEt.topology X)).obj
              ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem constantMap_comp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : CommRingCat.{max u (t + 1)}) (U : Z.ProEtᵒᵖ) :
    (Scheme.coefficientProEtaleDirectRingMap.{t, u} g A).hom.app U ≫
      (Scheme.coefficientProEtaleDirectRingMap.{t, u} f A).hom.app
        ((Scheme.proEtaleBaseChange g).op.obj U) ≫
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop).op =
    (Scheme.coefficientProEtaleDirectRingMap.{t, u} (f ≫ g) A).hom.app U := by
  have h : Scheme.coefficientProEtaleDirectRingMap.{t, u} g A ≫
      ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous CommRingCat
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)).map
          (Scheme.coefficientProEtaleDirectRingMap.{t, u} f A) ≫
      (Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp f g).symm)
        CommRingCat (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).hom.app
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A) =
      Scheme.coefficientProEtaleDirectRingMap.{t, u} (f ≫ g) A := by
    apply (sheafificationAdjunction (Scheme.ProEt.topology Z)
      CommRingCat.{max u (t + 1)}).homEquiv _ _ |>.injective
    apply NatTrans.ext
    funext V
    change _ ≫ _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, ← Category.assoc, constantMap_unit]
    change ((toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange g).op.obj V) ≫
      (Scheme.coefficientProEtaleDirectRingMap.{t, u} f A).hom.app
        ((Scheme.proEtaleBaseChange g).op.obj V)) ≫
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op =
      (toSheafify (Scheme.ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj A)).app V ≫
        (Scheme.coefficientProEtaleDirectRingMap.{t, u} (f ≫ g) A).hom.app V
    rw [constantMap_unit, constantMap_unit]
    have hn := (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
        ((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op
    change 𝟙 A ≫ _ = _ at hn
    exact hn.symm.trans (Category.id_comp _)
  exact congrArg (fun z ↦ z.hom.app U) h

private theorem sequenceRing_map_vertical (X : Scheme.{t}) (n : ℕ)
    {U V : X.ProEt} (a : U ⟶ V) :
    (coefficientSequenceCommRingSheaf ell E X).obj.map (Prod.mkHom (𝟙 n) a).op =
      (integralCoefficientCommRingSheaf ell E X n).obj.map a.op := by
  change ((coefficientSequenceCommRingSystem ell E X).map (𝟙 (op n))).hom.app (op V) ≫
    (integralCoefficientCommRingSheaf ell E X n).obj.map a.op = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The right-adjoint compositor is fixed by its fibre-product section formula.
Source: Stacks 03CB and 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: the inverse baseComp comparison acts on sections by restriction. Its
coefficient linearity follows by checking the constant-section maps on constants.
For systems this includes all quotient restrictions by ringComponent_naturality.
The inverse restriction gives the inverse natural map. Sectionwise equality gives
uniqueness, including on the empty site. -/
theorem pushComp_existsUnique {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : Option ℕ) :
    ∃! e : push ell E (f ≫ g) s ≅ push ell E f s ⋙ push ell E g s,
      ∀ (M : Modules ell E X s) (U : Site Z s)
        (m : M.val.obj (op ((base (f ≫ g) s).obj U))),
        (e.hom.app M).val.app (op U) m =
          M.val.map ((baseComp f g s).inv.app U).op m := by
  have := Functor.isContinuous_comp (base g s) (base f s)
    (topology Z s) (topology Y s) (topology X s)
  let a : ring (topology Z s) (coefficients ell E Z s) ⟶
      ((base g s ⋙ base f s).sheafPushforwardContinuous RingCat (topology Z s)
        (topology X s)).obj (ring (topology X s) (coefficients ell E X s)) :=
    moduleRingUnit ell E g s ≫
    ((base g s).sheafPushforwardContinuous RingCat (topology Z s) (topology Y s)).map
      (moduleRingUnit ell E f s)
  have h : a ≫ (Functor.sheafPushforwardContinuousNatTrans (baseComp f g s).hom
      RingCat (topology Z s) (topology X s)).app
        (ring (topology X s) (coefficients ell E X s)) = moduleRingUnit ell E (f ≫ g) s := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    cases s with
    | some n => exact (forget₂ CommRingCat RingCat).congr_map (constantMap_comp f g _ U)
    | none =>
      change (forget₂ CommRingCat RingCat).map
        ((Scheme.coefficientProEtaleDirectRingMap.{t, u} g _).hom.app (op U.unop.2) ≫
          (Scheme.coefficientProEtaleDirectRingMap.{t, u} f _).hom.app
            (op ((Scheme.proEtaleBaseChange g).obj U.unop.2)) ≫
          (coefficientSequenceCommRingSheaf ell E X).obj.map
          (Prod.mkHom (𝟙 U.unop.1)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop.2)).op) =
        (forget₂ CommRingCat RingCat).map
          ((Scheme.coefficientProEtaleDirectRingMap.{t, u} (f ≫ g) _).hom.app (op U.unop.2))
      rw [sequenceRing_map_vertical]
      exact (forget₂ CommRingCat RingCat).congr_map (constantMap_comp f g _ (op U.unop.2))
  let d : push ell E f s ⋙ push ell E g s ≅ push ell E (f ≫ g) s :=
    SheafOfModules.pushforwardComp (moduleRingUnit ell E g s) (moduleRingUnit ell E f s) ≪≫
      SheafOfModules.pushforwardNatIso
        (F := base (f ≫ g) s) (G := base g s ⋙ base f s) a (baseComp f g s) ≪≫
        SheafOfModules.pushforwardCongr h
  have hd : ∀ (M : Modules ell E X s) (U : Site Z s)
      (m : M.val.obj (op ((base (f ≫ g) s).obj U))),
      (d.inv.app M).val.app (op U) m =
        M.val.map ((baseComp f g s).inv.app U).op m := by
    intros
    rfl
  refine ⟨d.symm, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (he M U.unop m).trans (hd M U.unop m).symm

/-- The canonical direct-image comparison, uniquely fixed on every section.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def pushComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :=
  (pushComp_existsUnique ell E f g s).exists.choose

/-- Its mate under the specified composite adjunction is the module compositor.
Source: Stacks 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def comp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :
    pull ell E g s ⋙ pull ell E f s ≅ pull ell E (f ≫ g) s :=
  Adjunction.leftAdjointCompIso (adjunction ell E g s) (adjunction ell E f s)
    (adjunction ell E (f ≫ g) s) (pushComp ell E f g s).symm

/-- The identity direct-image comparison, uniquely fixed as restriction by base-change identity.
Source: Stacks 03CB (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def baseId (X : Scheme.{t}) : (s : Option ℕ) → base (𝟙 X) s ≅ 𝟭 (Site X s)
  | some _ => MorphismProperty.Over.pullbackId (@WeaklyEtale) ⊤ X
  | none => NatIso.prod (Iso.refl (𝟭 ℕ)) (MorphismProperty.Over.pullbackId (@WeaklyEtale) ⊤ X)

private theorem constantMap_id (X : Scheme.{t}) (A : CommRingCat.{max u (t + 1)})
    (U : X.ProEtᵒᵖ) :
    (Scheme.coefficientProEtaleDirectRingMap.{t, u} (𝟙 X) A).hom.app U ≫
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U.unop).op = 𝟙 _ := by
  have h : Scheme.coefficientProEtaleDirectRingMap.{t, u} (𝟙 X) A ≫
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat
          (Scheme.ProEt.topology X)).hom.app
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A) =
              𝟙 _ := by
    apply (sheafificationAdjunction (Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)}).homEquiv _ _ |>.injective
    apply NatTrans.ext
    funext V
    change _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, constantMap_unit]
    change (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange (𝟙 X)).op.obj V) ≫
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app V ≫ 𝟙 _
    rw [Category.comp_id]
    have hn := (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op
    change 𝟙 A ≫ _ = _ at hn
    exact hn.symm.trans (Category.id_comp _)
  exact congrArg (fun z ↦ z.hom.app U) h

/-- The direct image identity is fixed sectionwise. Source: Stacks 03CB and 03D3
(blueprint: lem-sf-ambient-pullback-site-constructions).
Proof: restriction along baseId.inv is linear because the constant ring map on
an identity sends constants to themselves. It commutes with all restrictions.
The inverse restriction proves invertibility and uniqueness is sectionwise. -/
theorem pushId_existsUnique (X : Scheme.{t}) (s : Option ℕ) :
    ∃! e : push ell E (𝟙 X) s ≅ 𝟭 (Modules ell E X s),
      ∀ (M : Modules ell E X s) (U : Site X s)
        (m : M.val.obj (op ((base (𝟙 X) s).obj U))),
        (e.hom.app M).val.app (op U) m = M.val.map ((baseId X s).inv.app U).op m := by
  have h : moduleRingUnit ell E (𝟙 X) s ≫
      (Functor.sheafPushforwardContinuousNatTrans (baseId X s).inv RingCat
        (topology X s) (topology X s)).app
          (ring (topology X s) (coefficients ell E X s)) = 𝟙 _ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    cases s with
    | some n => exact (forget₂ CommRingCat RingCat).congr_map (constantMap_id X _ U)
    | none =>
      change (forget₂ CommRingCat RingCat).map
        (_ ≫ (coefficientSequenceCommRingSheaf ell E X).obj.map
          (Prod.mkHom (𝟙 U.unop.1)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U.unop.2)).op) = _
      rw [sequenceRing_map_vertical]
      exact (forget₂ CommRingCat RingCat).congr_map (constantMap_id X _ (op U.unop.2))
  let d : push ell E (𝟙 X) s ≅ 𝟭 (Modules ell E X s) :=
    SheafOfModules.pushforwardNatIso (moduleRingUnit ell E (𝟙 X) s) (baseId X s).symm ≪≫
      SheafOfModules.pushforwardCongr h ≪≫ SheafOfModules.pushforwardId _
  have hd : ∀ (M : Modules ell E X s) (U : Site X s)
      (m : M.val.obj (op ((base (𝟙 X) s).obj U))),
      (d.hom.app M).val.app (op U) m = M.val.map ((baseId X s).inv.app U).op m := by
    intros
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (he M U.unop m).trans (hd M U.unop m).symm

/-- The section-normalized identity direct image. Source: Stacks 03CB
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
def pushId (X : Scheme.{t}) (s : Option ℕ) := (pushId_existsUnique ell E X s).exists.choose

/-- The action unitor as the adjunction mate of the specified identity comparison.
Source: Stacks 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def identity (X : Scheme.{t}) (s : Option ℕ) :
    pull ell E (𝟙 X) s ≅ 𝟭 (Modules ell E X s) :=
  Adjunction.leftAdjointIdIso (adjunction ell E (𝟙 X) s) (pushId ell E X s)

/-- The exact-localization compositor. Source: Stacks 015F and 04VG
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
def derivedComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :
    derivedPull ell E g s ⋙ derivedPull ell E f s ≅ derivedPull ell E (f ≫ g) s :=
  Functor.mapDerivedCategoryCompNatIso (comp ell E f g s)

/-- The exact-localization identity comparison. Source: Stacks 015F and 04VG
(blueprint: lem-sf-ambient-pullback-site-constructions). -/
def derivedIdentity (X : Scheme.{t}) (s : Option ℕ) :
    derivedPull ell E (𝟙 X) s ≅ 𝟭 (Derived ell E X s) :=
  Functor.mapDerivedCategoryNatIso (identity ell E X s) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- A local inverse-image/tensor generator, using the specified adjunction unit.
Source: Stacks 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def generator {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (M : Modules ell E Y s) (U : Site Y s) (V : Site X s)
    (a : V ⟶ (base f s).obj U) (m : M.val.obj (op U))
    (r : (coefficients ell E X s).obj.obj (op V)) :
    ((pull ell E f s).obj M).val.obj (op V) :=
  @SMul.smul _ _ (((pull ell E f s).obj M).val.obj (op V)).isModule.toSMul r
    (((pull ell E f s).obj M).val.map a.op
      (((adjunction ell E f s).unit.app M).val.app (op U) m))

/-- The image c_f(a) of a local scalar in inverse-image coordinates.
Source: Stacks 03D3 (blueprint: lem-sf-ambient-pullback-site-constructions). -/
def scalar {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (U : Site Y s) (V : Site X s) (a : V ⟶ (base f s).obj U)
    (r : (coefficients ell E Y s).obj.obj (op U)) :
    (coefficients ell E X s).obj.obj (op V) :=
  ((coefficients ell E X s).obj.map a.op).hom
    ((ringComponent ell E f s (op U)).hom r)

end WeilConjectures.AmbientPullbackTensor
