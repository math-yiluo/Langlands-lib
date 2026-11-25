/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
import WeilConjectures.TraceFormula.Supporting.SimultaneousIntegralPullbackComparisons
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackCompletionNormalization
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismSquareStageCompatibility
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackSquareDescent
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleIntegralShiftData
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleIntegralShiftWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackComposition
import WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero

/-! # The finite and integral automorphism stage constructions

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph, first two sentences
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).

## Main statements

- `automorphismConstructibleStage_finite`, `automorphismConstructibleStage_integral_rational`,
  and `automorphismConstructibleStage_qbar`: the four prescribed exact equivalences.
- `automorphismConstructibleStage_strata` and `automorphismConstructibleStage_reduction`:
  the specified partitions and entire quotient systems.
- The comparison constructors and coherence statements retain the actual completion,
  composition, shift, scalar extension, rationalization and common-stage comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v r s u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped TensorProduct
local instance (priority := 5000) instEssentiallySmallProEt_automorphismConstructibleStageCore
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] sfIntrinsicModuleEquivalence
  HasDerivedCategory.standard integralDerivedPullback scalarReductionExistence
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted

/-- Prime-to-characteristic coefficients are invertible on each scheme in the statement.
Source: the global finite-field datum and the Weil-structures paragraph
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the cardinality of k₀ gives characteristic p, also on its algebraic closure.
The prime l is distinct from p, hence nonzero and a unit in k. Every local ring
and residue field of a k-scheme inherits this unit under its structure map. -/
theorem automorphismConstructibleStage_units
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T : Over (Spec (.of D.k))) :
    (∀ x : T.left, IsUnit (l : T.left.presheaf.stalk x)) ∧
      (∀ x : T.left, IsUnit (l : T.left.residueField x)) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have hs (x : T.left) : IsUnit (l : T.left.presheaf.stalk x) := by
    simpa only [map_natCast] using hk.map
      (StructureSheaf.toStalk (CommRingCat.of D.k) (T.hom x) ≫ T.hom.stalkMap x).hom
  exact ⟨hs, fun x ↦ by
    simpa only [map_natCast] using (hs x).map (T.left.residue x).hom⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.hasShift ObjectProperty.commShiftι

set_option allowUnsafeReducibility true in
attribute [local irreducible] ObjectProperty.hasShift ObjectProperty.commShiftι

attribute [local semireducible] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Positive coefficient levels have their existing finite-ring structure.
Source: the coefficient convention in the Weil-structures paragraph
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
instance automorphismConstructibleStage_finiteRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (finiteCoefficientRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The finite commuting-square map is the prescribed pair of pullback compositors.
Source: Weil-structures paragraph, the maps b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageFiniteSquare (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    sfIntrinsicDerivedPullback A f ⋙ sfIntrinsicDerivedPullback A eY.asIso.hom ≅
      sfIntrinsicDerivedPullback A eX.asIso.hom ⋙ sfIntrinsicDerivedPullback A f :=
  (sfIntrinsicDerivedPullbackComp A eY.asIso.hom f).symm ≪≫
    eqToIso (congrArg (sfIntrinsicDerivedPullback A) h) ≪≫
      sfIntrinsicDerivedPullbackComp A f eX.asIso.hom

private theorem integral_composition_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) :
    ∃ c : constructibleIntegralPullback l E (h ≫ k) ≅
        constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h,
      ∀ K, (c.hom.app K).hom = (integralComparisonComposition l E C h k K).hom := by
  let P := sfIntegralConstructible l E V
  let U := integralComparisonDerivedSequencePullback l E h
  let L := coefficientSequenceLimit l E Z
  let β : P.ι ⋙ integralDerivedPullback l E k ⋙ ((C.coefficient E).system W).reduction ≅
      P.ι ⋙ ((C.coefficient E).system V).reduction ⋙
        integralComparisonDerivedSequencePullback l E k :=
    NatIso.ofComponents (fun K ↦
      @asIso _ _ _ _ _ ((C.coefficient E).effective k K)) (fun {K J} r ↦ by
        exact (integralComparisonPullbackCounit l E k
          ((C.coefficient E).system V) ((C.coefficient E).system W)
          ((C.coefficient E).roos W) ((C.coefficient E).pullback k)).naturality r.hom)
  let η : P.ι ⋙ integralDerivedPullback l E k ⋙ integralDerivedPullback l E h ≅
      P.ι ⋙ ((C.coefficient E).system V).reduction ⋙
        integralComparisonDerivedSequencePullback l E k ⋙ U ⋙ L :=
    Functor.isoWhiskerLeft (P.ι ⋙ integralDerivedPullback l E k)
        ((C.coefficient E).pullback h).realization ≪≫
      Functor.isoWhiskerRight β (U ⋙ L)
  let γ : P.ι ⋙ integralDerivedPullback l E (h ≫ k) ≅
      P.ι ⋙ integralDerivedPullback l E k ⋙ integralDerivedPullback l E h :=
    Functor.isoWhiskerLeft P.ι ((C.coefficient E).pullback (h ≫ k)).realization ≪≫
      Functor.isoWhiskerLeft (P.ι ⋙ ((C.coefficient E).system V).reduction)
        (Functor.isoWhiskerRight (integralComparisonSystemComposition l E h k) L) ≪≫ η.symm
  refine ⟨NatIso.ofComponents (fun K ↦ (sfIntegralConstructible l E Z).isoMk (γ.app K))
    (fun {K J} r ↦ ?_), fun K ↦ ?_⟩
  · apply ObjectProperty.hom_ext
    exact γ.hom.naturality r
  · rfl

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integral_congr_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] {g g' : Y ⟶ X} (h : g = g')
    (K : sfIntegralConstructibleCategory l E X) :
    ((eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g)
      h)).hom.app K).hom =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) := by
  cases h
  rfl

/-- The normalized integral commuting-square comparison is uniquely specified by the
actual completed pullback compositors. Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: invert the compositor for e_Y followed by f, identify the two equal scheme maps,
and apply the compositor for f followed by e_X. Each compositor is natural, so the
result is a natural isomorphism. Its displayed components determine it uniquely. -/
theorem automorphismStageIntegralSquare_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    ∃! b : constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.asIso.hom ≅
        constructibleIntegralPullback l E eX.asIso.hom ⋙ constructibleIntegralPullback l E f,
      ∀ K : sfIntegralConstructibleCategory l E X,
        (b.hom.app K).hom =
          (integralComparisonComposition l E C eY.asIso.hom f K).inv ≫
            eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
              (integralComparisonComposition l E C f eX.asIso.hom K).hom := by
  obtain ⟨c, hc⟩ := integral_composition_natural l E C eY.asIso.hom f
  obtain ⟨d, hd⟩ := integral_composition_natural l E C f eX.asIso.hom
  let b := c.symm ≪≫
    eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g) h) ≪≫ d
  have hb (K : sfIntegralConstructibleCategory l E X) :
      (b.hom.app K).hom =
        (integralComparisonComposition l E C eY.asIso.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
            (integralComparisonComposition l E C f eX.asIso.hom K).hom := by
    have hc' : (c.inv.app K).hom =
        (integralComparisonComposition l E C eY.asIso.hom f K).inv := by
      apply (cancel_mono (integralComparisonComposition l E C eY.asIso.hom f K).hom).1
      calc
        _ = (c.inv.app K).hom ≫ (c.hom.app K).hom := by rw [hc K]
        _ = 𝟙 _ := congrArg (fun r ↦ r.hom) (c.inv_hom_id_app K)
        _ = _ := (Iso.inv_hom_id _).symm
    simp only [b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, hc', hd]
    rw [integral_congr_component l E h K]
  refine ⟨b, hb, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (ha K).trans (hb K).symm

/-- The actual integral square, with the component normalization just stated.
Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :=
  (automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose

set_option backward.isDefEq.respectTransparency.types false

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem rawIso_existsUnique
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (c : Localization.Away t → Localization.Away b)
    (U V : C ⥤ D) (e : U ≅ V)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D b)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨U.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨V.obj K.obj⟩)
    (mF : ∀ (K L : C) (a : K ⟶ L) (z : Localization.Away t),
      HEq (F.map (z ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c z ⊗ₜ[S] U.map a))
    (mG : ∀ (K L : C) (a : K ⟶ L) (z : Localization.Away t),
      HEq (G.map (z ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c z ⊗ₜ[S] V.map a)) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (e.hom.app K.obj)) := by
  let Q := ScalarLocalization.localization S D b
  let a (K : ScalarLocalization R C t) :=
    eqToIso (hF K) ≪≫ Q.mapIso (e.app K.obj) ≪≫ (eqToIso (hG K)).symm
  have ha (K : ScalarLocalization R C t) :
      HEq (a K).hom (Q.map (e.hom.app K.obj)) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom]
    exact ((conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl)
  have hn (K L : ScalarLocalization R C t) (f : K ⟶ L) :
      F.map f ≫ (a L).hom = (a K).hom ≫ G.map f := by
    induction f using TensorProduct.inductionOn with
    | tmul z f =>
      have h₁ := heq_comp (hF K) (hF L) (hG L) (mF K.obj L.obj f z) (ha L)
      have h₂ := heq_comp (hF K) (hG K) (hG L) (ha K) (mG K.obj L.obj f z)
      apply eq_of_heq
      refine h₁.trans (HEq.trans ?_ h₂.symm)
      apply heq_of_eq
      change ScalarLocalization.composition S D b _ _ _
          (1 ⊗ₜ[S] e.hom.app L.obj) (c z ⊗ₜ[S] U.map f) =
        ScalarLocalization.composition S D b _ _ _
          (c z ⊗ₜ[S] V.map f) (1 ⊗ₜ[S] e.hom.app K.obj)
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, e.hom.naturality]
    | add x y hx hy => simp only [F.map_add, G.map_add,
        Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  refine ⟨NatIso.ofComponents a (fun {K L} f ↦ hn K L f), ha, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (ha K).symm)

/-- Rationalization retains the normalized integral square on every component.
Source: Weil-structures paragraph, rationalized b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: apply the integral-to-rational localization to each component. Integral
naturality extends to pure tensors by linearity and then to sums by additivity.
The localized inverse gives a natural inverse. The specified components determine
the natural isomorphism uniquely. -/
theorem automorphismStageRationalSquare_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    ∃! b : rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.asIso.hom ≅
        rationalDerivedPullback l E eX.asIso.hom ⋙ rationalDerivedPullback l E f,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (b.hom.app K)
          ((sfRationalConstructibleLocalization l E Y).map
            ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K.obj)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let U := constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.asIso.hom
  let V := constructibleIntegralPullback l E eX.asIso.hom ⋙ constructibleIntegralPullback l E f
  let F := rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.asIso.hom
  let G := rationalDerivedPullback l E eX.asIso.hom ⋙ rationalDerivedPullback l E f
  have ho {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W)
      (K : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj K =
        ScalarLocalization.mk ((constructibleIntegralPullback l E g).obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 K
  have hm {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W)
      (K M : sfIntegralConstructibleCategory l E W) (a : K ⟶ M)
      (z : Localization.Away t) :
      HEq ((rationalDerivedPullback l E g).map (z ⊗ₜ[R] a))
        (z ⊗ₜ[R] (constructibleIntegralPullback l E g).map a) := by
    simpa only [rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 K M a z
  have hadd {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W) :
      (rationalDerivedPullback l E g).Additive :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.1
  let : (rationalDerivedPullback l E f).Additive := hadd f
  let : (rationalDerivedPullback l E eX.asIso.hom).Additive := hadd eX.asIso.hom
  let : (rationalDerivedPullback l E eY.asIso.hom).Additive := hadd eY.asIso.hom
  apply rawIso_existsUnique t t id U V
    (automorphismStageIntegralSquare l E C f eX eY h) F G
  · intro K
    exact (ho eY.asIso.hom _).trans (congrArg
      (fun Z : sfRationalConstructibleCategory l E Y ↦
        ScalarLocalization.mk ((constructibleIntegralPullback l E eY.asIso.hom).obj Z.obj))
      (ho f K))
  · intro K
    exact (ho f _).trans (congrArg
      (fun Z : sfRationalConstructibleCategory l E X ↦
        ScalarLocalization.mk ((constructibleIntegralPullback l E f).obj Z.obj))
      (ho eX.asIso.hom K))
  · intro K M a z
    exact (map_heq (rationalDerivedPullback l E eY.asIso.hom)
      (ho f _) (ho f _) (hm f K M a z)).trans
        (hm eY.asIso.hom _ _ ((constructibleIntegralPullback l E f).map a) z)
  · intro K M a z
    exact (map_heq (rationalDerivedPullback l E f)
      (ho eX.asIso.hom _) (ho eX.asIso.hom _) (hm eX.asIso.hom K M a z)).trans
        (hm f _ _ ((constructibleIntegralPullback l E eX.asIso.hom).map a) z)

/-- The rational square is exactly the rationalization of the integral one.
Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageRationalSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :=
  (automorphismStageRationalSquare_existsUnique l E C f eX eY h).exists.choose

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section QbarSquare

set_option allowUnsafeReducibility true in
attribute [local irreducible] HasDerivedCategory.standard
  automorphismStageIntegralSquare automorphismStageRationalSquare
  rationalDerivedPullback commonStageDerivedPullback constructibleIntegralPullback
  sfRationalConstructibleLocalization integralComparisonComposition

/-- Common-stage b and d have exactly the rational components over each representative's
coefficient field. Source: Weil-structures paragraph, common-stage b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the integral scalar-composition equation gives the square for b by cancellation
of the invertible compositors, and likewise for d. Rationalize that equation. Thus the
rational component families descend through coherent finite-field descent. The actual
prescribed operation formulas identify the resulting functors with the displayed ones.
Every object is a literal pair, so these components uniquely determine the comparison. -/
theorem automorphismStageQbarSquare_existsUnique
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    ∃! b : commonStageDerivedPullback l Ω f ⋙ commonStageDerivedPullback l Ω eY.asIso.hom ≅
        commonStageDerivedPullback l Ω eX.asIso.hom ⋙ commonStageDerivedPullback l Ω f,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        HEq (b.hom.app K)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) K.stage).map
            ((automorphismStageRationalSquare l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)
              C f eX eY h).hom.app K.obj)) := by
  exact commonStagePullbackSquare_existsUnique l Ω f eX eY
    (fun E ↦ automorphismStageRationalSquare l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) C f eX eY h)
    (fun {E L} w K ↦ automorphismSquareStageCompatibility l Ω C f eX eY h
      (fun E _ _ _ ↦ automorphismStageIntegralSquare l E C f eX eY h)
      (fun E _ _ _ K ↦ by
        simpa only [automorphismStageIntegralSquare] using
          (automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose_spec K)
      (fun E _ _ _ ↦ automorphismStageRationalSquare l E C f eX eY h)
      (fun E _ _ _ K ↦ by
        simpa only [automorphismStageRationalSquare] using
          (automorphismStageRationalSquare_existsUnique l E C f eX eY h).exists.choose_spec K)
      E L w K)

/-- The common-stage square with the exact specified representative normalization.
Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageQbarSquare
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :=
  (automorphismStageQbarSquare_existsUnique l Ω C f eX eY h).exists.choose

end QbarSquare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section FiniteCoherence
open CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard sfIntrinsicPullback
  sfIntrinsicPullbackComp sfIntrinsicPullbackId sfIntrinsicSquarePullback Functor.mapDerivedCategory
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

private theorem identity_transport
    {C D : Type*} [Category C] [Category D] {X Y : Scheme.{u}}
    (P : (X ⟶ X) → C ⥤ C) (Q : (Y ⟶ Y) → D ⥤ D)
    (H : (Y ⟶ X) → C ⥤ D)
    (B : ∀ (a : Y ⟶ Y) (f : Y ⟶ X) (b : X ⟶ X),
      a ≫ f = f ≫ b → (H f ⋙ Q a ≅ P b ⋙ H f))
    (uX : P (𝟙 X) ≅ 𝟭 _) (uY : Q (𝟙 Y) ≅ 𝟭 _)
    (f : Y ⟶ X)
    (hi : ∀ (w : 𝟙 Y ≫ f = f ≫ 𝟙 X) (K : C),
      (B (𝟙 Y) f (𝟙 X) w).hom.app K ≫ (H f).map (uX.hom.app K) =
        uY.hom.app ((H f).obj K))
    (a : Y ⟶ Y) (b : X ⟶ X) (ha : a = 𝟙 Y) (hb : b = 𝟙 X)
    (w : a ≫ f = f ≫ b) (K : C) :
    (B a f b w).hom.app K ≫
      (H f).map ((eqToIso (congrArg P hb) ≪≫ uX).hom.app K) =
      (eqToIso (congrArg Q ha) ≪≫ uY).hom.app ((H f).obj K) := by
  subst a
  subst b
  simpa only [eqToIso_refl, Iso.refl_trans] using hi w K

private theorem finite_shift (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    NatTrans.CommShift (automorphismStageFiniteSquare A f eX eY h).hom ℤ := by
  have he : NatTrans.CommShift
      (eqToIso (congrArg (sfIntrinsicDerivedPullback A) h)).hom ℤ := by
    have eqshift {Z W : Scheme.{u}} (a b : Z ⟶ W) (w : a = b) :
        NatTrans.CommShift (eqToIso (congrArg (sfIntrinsicDerivedPullback A) w)).hom ℤ := by
      subst b
      change NatTrans.CommShift (𝟙 _) ℤ
      infer_instance
    exact eqshift _ _ h
  have hc {Z W V : Scheme.{u}} (a : Z ⟶ W) (b : W ⟶ V) :
      NatTrans.CommShift (sfIntrinsicDerivedPullbackComp A a b).hom ℤ := by
    dsimp only [sfIntrinsicDerivedPullbackComp, Iso.trans_hom]
    infer_instance
  have := hc eY.asIso.hom f
  have := hc f eX.asIso.hom
  dsimp only [automorphismStageFiniteSquare, Iso.trans_hom, Iso.symm_hom]
  infer_instance

end FiniteCoherence

/-- Integral reduction in the prescribed intrinsic finite-coefficient coordinates.
Source: Weil-structures paragraph, displayed reduction comparison
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (a : (DerivedCategory.Q (C := scalarReductionSource l E X)).obj P.obj ≅ K.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        ((constructibleIntegralPullback l E f).obj K).obj ≅
      (finiteDerivedPullback l E n f).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) :=
  integralSystemPullbackReductionIso l E f K P a n ≪≫
    (openSquareDerivedPullbackModel (finiteCoefficientRing l E (n + 1)) f).app
      ((scalarReductionDerivedExtension l E X n).obj K.obj)

section ScalarComparisonAgreement

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] integralDerivedPullback scalarPullbackCompleted
  integralComparisonLambda integralComparisonMu

/-- A simultaneous normalized calculus and its coherent scalar comparisons exist.
Source: Weil-structures paragraph, scalar-extension and composition coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: use the quotient coefficient diagrams simultaneously for all finite fields.
Their tensor generators fix the scalar units, associators and pullback compositors.
Derive these strict diagrams, apply their actual counits, and realize by Roos
limits. The identity, associativity and scalar equations on whole systems survive
realization. Uniqueness of the representative-normalized comparisons identifies
these with the scalar maps used by the prescribed common-stage operations. -/
theorem automorphismConstructibleStage_comparison_system (l : ℕ) [Fact l.Prime] :
    ∃ C : IntegralComparisonSystem.{u} l,
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
        (ι : E →ₐ[ℚ_[l]] L),
        IntegralComparisonRealizationCoherence l E L ι C ∧
        ∀ (X Y : Scheme.{u})
          [∀ x : X, Invertible (l : X.residueField x)]
          [∀ y : Y, Invertible (l : Y.residueField y)] (f : Y ⟶ X)
          (K : sfIntegralConstructibleCategory l E X),
          (integralComparisonScalar l E L ι C f K).hom =
            (integralPullbackScalarComparison l E L ι f K).hom.hom := by
  obtain ⟨C, hC⟩ := integralPullbackComparisonRealization_simultaneous.{u} l
  refine ⟨C, ?_⟩
  intro E _ _ _ L _ _ _ ι
  refine ⟨hC E L ι, ?_⟩
  intro X Y _ _ f K
  have h := integralScalarPullbackCompletion_normalization l E L ι C f K
    (((constructibleIntegralPullback l E f).obj K).property.1)
  simpa only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    integralPullbackScalarComparison, ObjectProperty.isoMk, ObjectProperty.homMk] using
    ((Iso.eq_comp_inv (integralComparisonMu l E L ι C f K)).mpr h).symm

end ScalarComparisonAgreement

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section ReductionCoherenceProof

set_option backward.defeqAttrib.useBackward false

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback ObjectProperty.lift ObjectProperty.ι

end ReductionCoherenceProof

section IntegralCoherence

set_option backward.defeqAttrib.useBackward false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback ObjectProperty.lift ObjectProperty.ι
  Functor.comp Iso.refl Iso.symm
attribute [local irreducible] integralComparisonComposition integralComparisonUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (C : IntegralComparisonSystem.{u} l)

end IntegralCoherence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Keep the recorded pullback interfaces opaque while checking their shift structures.
set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback

/-- A restricted integral shift is the signed Roos shift descended from good representatives.
This predicate only spells out the normalization of the comparison in this node.
Source: Weil-structures paragraph, canonical shift clause
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralShiftNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : (constructibleIntegralPullback l E f).CommShift ℤ) : Prop :=
  ∃ (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d : (integralDerivedPullback l E f).CommShift ℤ),
    IntegralCompletedComparison.ShiftCoordinates l E f c ∧
      IntegralCompletedComparison.ShiftDescent l E f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l E X) (r : ℤ),
        HEq (((constructibleIntegralPullback l E f).commShiftIso (self := s) r).hom.app K).hom
          (((integralDerivedPullback l E f).commShiftIso (self := d) r).hom.app K.obj)

/-- The rational shift is the localization of the normalized integral shift.
At one the localization comparisons are identities, giving the displayed component formula.
For every integer the identity-component comparison retains both localization shift factors;
its `CommShift` condition expresses the coherent localization square.
Source: Weil-structures paragraph, rationalization of shifts
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageRationalShiftNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : (rationalDerivedPullback l E f).CommShift ℤ) : Prop :=
  ∃ c : (constructibleIntegralPullback l E f).CommShift ℤ,
    automorphismStageIntegralShiftNormalization l E f c ∧
      (letI := c
       let := s
       (∀ K : sfRationalConstructibleCategory l E X,
         HEq (((rationalDerivedPullback l E f).commShiftIso (1 : ℤ)).hom.app K)
           ((sfRationalConstructibleLocalization l E Y).map
             (((constructibleIntegralPullback l E f).commShiftIso (1 : ℤ)).hom.app K.obj))) ∧
       ∃ b : sfRationalConstructibleLocalization l E X ⋙ rationalDerivedPullback l E f ≅
           constructibleIntegralPullback l E f ⋙ sfRationalConstructibleLocalization l E Y,
         (∀ K, HEq (b.hom.app K)
           (𝟙 ((rationalDerivedPullback l E f).obj
             ((sfRationalConstructibleLocalization l E X).obj K)))) ∧
         NatTrans.CommShift b.hom ℤ)

/-- The algebraically closed shift is the same normalized rational shift in every finite stage.
Source: Weil-structures paragraph, coherent finite-field descent of shifts
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageQbarShiftNormalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : (commonStageDerivedPullback l Ω f).CommShift ℤ) : Prop :=
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ c : (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).CommShift ℤ,
      automorphismStageRationalShiftNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f c ∧
      ∀ (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) (r : ℤ),
        HEq (((commonStageDerivedPullback l Ω f).commShiftIso (self := s) r).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) E).obj K))
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) E).map
            (((rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).commShiftIso
                (self := c) r).hom.app K))

/-- Canonical signed shifts descend to all the integral pullbacks in a commuting square.
Source: Weil-structures paragraph, canonical shift comparisons
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: shift the good representative and its quotient tower termwise. The product
shift fixes the unshifted Roos coordinate and multiplies the shifted coordinate
by (-1)^r. This is precisely ShiftCoordinates. Localization gives ShiftDescent.
The full constructible inclusion inherits that shift comparison. The specified
compositors come from the same shifted system maps, so their square commutes
with shifts. Cone sequences of representatives are termwise split and preserved
by the entire construction, proving exactness. -/
theorem automorphismConstructibleStage_integral_shifts
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
    (∀ (Z W : Scheme.{u}) (g : Z ⟶ W),
      ∃ (c : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
        (d : (integralDerivedPullback l E g).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E g c ∧
          IntegralCompletedComparison.ShiftDescent l E g c d) ∧
    ∃ (cf : (constructibleIntegralPullback l E f).CommShift ℤ)
      (cX : (constructibleIntegralPullback l E eX.asIso.hom).CommShift ℤ)
      (cY : (constructibleIntegralPullback l E eY.asIso.hom).CommShift ℤ),
      automorphismStageIntegralShiftNormalization l E f cf ∧
      automorphismStageIntegralShiftNormalization l E eX.asIso.hom cX ∧
      automorphismStageIntegralShiftNormalization l E eY.asIso.hom cY ∧
      (fun [sf : (constructibleIntegralPullback l E f).CommShift ℤ]
        [sX : (constructibleIntegralPullback l E eX.asIso.hom).CommShift ℤ]
        [sY : (constructibleIntegralPullback l E eY.asIso.hom).CommShift ℤ] ↦
        (constructibleIntegralPullback l E f).IsTriangulated ∧
          (constructibleIntegralPullback l E eX.asIso.hom).IsTriangulated ∧
          (constructibleIntegralPullback l E eY.asIso.hom).IsTriangulated ∧
          NatTrans.CommShift (automorphismStageIntegralSquare l E C f eX eY h).hom ℤ)
        (sf := cf) (sX := cX) (sY := cY) := by
  constructor
  · exact automorphismConstructibleStage_integral_shift_data l E
  · let b := automorphismStageIntegralSquare l E C f eX eY h
    have hb := (automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose_spec
    obtain ⟨cf, cX, cY, hf, hX, hY, hall⟩ :=
      automorphismConstructibleStage_integral_shift_witness l E C f eX eY h b hb
    refine ⟨cf, cX, cY, ?_, ?_, ?_, ?_⟩
    · simpa only [automorphismStageIntegralShiftNormalization] using hf
    · simpa only [automorphismStageIntegralShiftNormalization] using hX
    · simpa only [automorphismStageIntegralShiftNormalization] using hY
    · exact hall

end WeilConjectures
