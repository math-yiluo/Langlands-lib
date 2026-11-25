/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.SmoothPurity.Rational.RationalPullbackScalarTower
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs

/-! # Pullback comparisons on the normalized coefficient stages

Source: the common-stage pullback construction in prose-03-02.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] rationalDerivedPullback sfRationalScalarExtension
  rationalPullbackScalarComparison sfRationalScalarComp HasDerivedCategory.standard
  ObjectProperty.FullSubcategory.category Padic.coefficientExtensionIntegers
  ScalarLocalization.category ScalarLocalization.composition sfIntegralConstructibleLinear
  integralCoefficientLinear Linear.homModule Preadditive.homGroup
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.normalizedAssociator
  AlgebraicallyClosedCoefficients.coefficientInclusion

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

private theorem comparison_reflexive
    {A : Type a₁} [Category.{b₁} A] {B : Type a₂} [Category.{b₂} B]
    {C : Type a₃} [Category.{b₃} C] {D : Type a₄} [Category.{b₄} D]
    (F : A ⥤ B) (G : C ⥤ D) (S : A ⥤ C) (T : B ⥤ D)
    (p : T = T) (q : S = S) (e : F ⋙ T ≅ S ⋙ G) :
    Functor.isoWhiskerLeft F (eqToIso p) ≪≫ e ≪≫
      Functor.isoWhiskerRight (eqToIso q).symm G = e := by
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.refl_symm,
    Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl]

private theorem transport_pair_coherent
    {I : Type w} [Preorder I]
    {C : I → Type a₁} [∀ i, Category.{b₁} (C i)]
    {D : I → Type a₂} [∀ i, Category.{b₂} (D i)]
    (S S₀ : StageSystem C) (T T₀ : StageSystem D)
    (φ : ∀ i, C i ⥤ D i) (hS : S = S₀) (hT : T = T₀)
    (s : ∀ {i j} (h : i ≤ j), S.T h = S₀.T h)
    (t : ∀ {i j} (h : i ≤ j), T.T h = T₀.T h)
    (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T₀.T h ≅ S₀.T h ⋙ φ j)
    (hb : StageSystem.pairFunctorCoherent S₀ T₀ φ b) :
    StageSystem.pairFunctorCoherent S T φ
      (fun {i j} h ↦ Functor.isoWhiskerLeft (φ i) (eqToIso (t h)) ≪≫ b h ≪≫
        Functor.isoWhiskerRight (eqToIso (s h)).symm (φ j)) := by
  subst S T
  have hc {i j : I} (h : i ≤ j) :=
    comparison_reflexive (φ i) (φ j) (S₀.T h) (T₀.T h) (t h) (s h) (b h)
  intro i j k h h' X
  simpa only [hc] using hb h h' X

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Conjugate the prescribed rational scalar comparison by the recorded transitions.
Source: the common-stage pullback paragraph
(blueprint: lem-weil-rational-pullback-stage-coherence). -/
def rationalPullbackStageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {E L : Index l Ω} (h : E ≤ L) :
    rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⋙ (stageSystem l Ω X).T h ≅
      (stageSystem l Ω Y).T h ⋙ rationalDerivedPullback l (Coefficient.{u} l Ω L) f :=
  Functor.isoWhiskerLeft _
      (eqToIso ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h)) ≪≫
    rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f ≪≫
    Functor.isoWhiskerRight
      (eqToIso ((stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h)).symm _

private def canonicalSystem (W : Scheme.{u}) : StageSystem (Stage l Ω W) :=
  ⟨fun {_ _} h ↦ transition l Ω W _ _ h,
    fun {_ _ _} h k ↦ associator l Ω W _ _ _ h k,
    fun {_ _ _ _} h k m P ↦ associator_cocycle l Ω W _ _ _ _ h k m P⟩

private theorem stageSystem_eq_canonical (W : Scheme.{u}) :
    stageSystem l Ω W = canonicalSystem l Ω W := by
  apply (stageSystem_existsUnique l Ω W).unique
  · exact (stageSystem_existsUnique l Ω W).exists.choose_spec
  · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩

private theorem scalar_tower_with_endpoint
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (κ : E →ₐ[ℚ_[l]] M)
    (e : j.comp ι = κ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).map
        ((rationalPullbackScalarComparison l E L ι f).hom.app K) ≫
      (rationalPullbackScalarComparison l L M j f).hom.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
      (rationalDerivedPullback l M f).map
        ((scalarAssociator l E L M ι j κ e Y).hom.app K) =
    (scalarAssociator l E L M ι j κ e X).hom.app
        ((rationalDerivedPullback l E f).obj K) ≫
      (rationalPullbackScalarComparison l E M κ f).hom.app K := by
  subst κ
  simpa only [scalarAssociator, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_refl, NatTrans.id_app, Category.comp_id] using
      rationalPullbackScalarComparison_tower l E L M ι j f K

private theorem scalar_tower_nat
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (κ : E →ₐ[ℚ_[l]] M)
    (e : j.comp ι = κ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    Functor.whiskerRight (rationalPullbackScalarComparison l E L ι f).hom
        (sfRationalScalarExtension l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j) ≫
      Functor.whiskerLeft
        (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
        (rationalPullbackScalarComparison l L M j f).hom ≫
      Functor.whiskerRight (scalarAssociator l E L M ι j κ e Y).hom
        (rationalDerivedPullback l M f) =
    Functor.whiskerLeft (rationalDerivedPullback l E f) (scalarAssociator l E L M ι j κ e X).hom ≫
      (rationalPullbackScalarComparison l E M κ f).hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    scalar_tower_with_endpoint l E L M ι j κ e f K

private theorem canonical_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    Functor.whiskerRight
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom
        (transition l Ω X L M k) ≫
      Functor.whiskerLeft (transition l Ω Y E L h)
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω L)
          (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) f).hom ≫
      Functor.whiskerRight (associator l Ω Y E L M h k).hom
        (rationalDerivedPullback l (Coefficient.{u} l Ω M) f) =
    Functor.whiskerLeft (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
        (associator l Ω X E L M h k).hom ≫
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E M (h.trans k)) f).hom := by
  -- Simplify the associators without rechecking the whole transported equality as a rewrite motive.
  simp only [GeneralAlgebraicallyClosedCoefficients.associator_formula l Ω Y E L M h k,
    GeneralAlgebraicallyClosedCoefficients.associator_formula l Ω X E L M h k]
  delta GeneralAlgebraicallyClosedCoefficients.normalizedAssociator transition
  exact scalar_tower_nat l
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
    (coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) f

private theorem canonical_coherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    StageSystem.pairFunctorCoherent (canonicalSystem l Ω Y) (canonicalSystem l Ω X)
      (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
      (fun {E L} h ↦ rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f) := by
  intro E L M h k K
  have hc := NatTrans.congr_app (canonical_natural l Ω f E L M h k) K
  simpa only [canonicalSystem, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] using hc

/-- The recorded pullback comparisons satisfy the stage-system tower equation.
Source: rationalPullbackScalarComparison_tower and the normalized stage construction
(blueprint: lem-weil-rational-pullback-stage-coherence).
Proof: uniqueness identifies the recorded stage system with the explicit system of
scalar transitions and their normalized associators. Its transition equality
transports become identity isomorphisms. Substitute the scalar associators and
the coefficient-inclusion composition law into the rational pullback tower
identity as natural transformations before evaluating at an object. This keeps the
coefficient-equality witnesses out of large functor-object conversions, and gives
the required equation with both recorded associators. -/
theorem rationalPullbackStageComparison_coherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
      (fun {_ _} h ↦ rationalPullbackStageComparison l Ω f h) := by
  intro E L M h k K
  simpa only [rationalPullbackStageComparison, canonicalSystem] using
    transport_pair_coherent (stageSystem l Ω Y) (canonicalSystem l Ω Y)
      (stageSystem l Ω X) (canonicalSystem l Ω X)
      (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
      (stageSystem_eq_canonical l Ω Y) (stageSystem_eq_canonical l Ω X)
      (fun {E L} h ↦ (stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h)
      (fun {E L} h ↦ (stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h)
      (fun {E L} h ↦ rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f)
      (canonical_coherent l Ω f) h k K

end WeilConjectures
