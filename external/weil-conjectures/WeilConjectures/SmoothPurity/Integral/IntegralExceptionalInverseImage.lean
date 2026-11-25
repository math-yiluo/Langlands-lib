/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import Mathlib.RingTheory.AdicCompletion.Topology
import WeilConjectures.CategoryTheory.Scalar.ScalarAdjunctionDescent

import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemEvaluationBound
import all WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportConstruction
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownGeometricComparisons
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportScalarAction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.Proper.ProperDerivedDirectImageCoproducts
import WeilConjectures.NumberTheory.Padics.NonunitCoefficientStages
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite

/-! # Integral exceptional inverse image from actual coefficient systems

Source: blueprint sec-smooth-purity/sk-def-sf-operations,
theorem-f-shriek-finite-coefficients, integral construction
(blueprint: def-pur-adic-exceptional-system-realization).

The ordinary coordinate functor below changes only quotient-ring presentations.
The exceptional operation is the composite of strict derived reduction, the actual
system comparison, the ordinary etale system right adjoint, inverse comparison,
and the total derived inverse limit. No coherent lift is chosen from level objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
section GenericComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe ua va uu vv w d
variable {C : Type ua} [Category.{va} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type uu} [Category.{vv} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

private theorem exceptionalComparisonForEvaluation [PreservesFiniteLimits L]
    (hregular : ∀ x : O, ell * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({ell} : Set O)) O]
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell)) :
    ∃ (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
      (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)),
      Nonempty (CoefficientSystemDerivedImage O ell L V adj S PY PX) := by
  obtain ⟨S⟩ := coefficientSystemOrdinaryImage_exists O ell L V adj
  obtain ⟨PX⟩ := coefficientEvaluationDerivedLeftAdjoint (J := K) hregular
  obtain ⟨T⟩ := coefficientSystemUnboundedComparison O ell L V adj S PY PX
  let image := T.evaluation
  let scalar := T.scalar
  have hlim : PreservesFiniteLimits S.inverse := S.systemExact.1
  have hcolim : PreservesFiniteColimits S.inverse := S.systemExact.2
  have hlevelLim (n : ℕ) : PreservesFiniteLimits (S.lift n).modules :=
    (S.inverseExact n).1
  have hlevelColim (n : ℕ) : PreservesFiniteColimits (S.lift n).modules :=
    (S.inverseExact n).2
  refine ⟨S, PX, ⟨{
    construction := T
    detectsIso := coefficientEvaluation_detectsIso O ell PX
    boundedBelow := ?_
    origin := ?_ }⟩⟩
  · rintro M ⟨a, ha⟩
    exact ⟨a, exactDerivedAdjunction_isGE S.inverse image.system.inverse
      image.system.inverseFactors image.system.adjunction M a⟩
  · intro hfull M hM horigin
    have hc (n : ℕ) :
        IsIso ((image.level n).adjunction.counit.app ((PX.evaluation n).obj M)) := by
      obtain ⟨H, hH, ⟨e⟩⟩ := horigin n
      exact exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
        (image.level n).inverse (image.level n).inverseFactors
        (image.level n).adjunction
        (hfull n) _ H hH e
    constructor
    · apply (coefficientEvaluation_detectsIso O ell PX _).2
      intro n
      rw [← image.counit n M]
      infer_instance
    · intro hnorm m n h
      have hreflect : (image.level n).inverse.ReflectsIsomorphisms :=
        exactDerived_reflectsIso_of_boundedBelow_faithful (S.lift n).modules
          (image.level n).inverse (image.level n).inverseFactors
          (fun A B hA hB ↦ (hfull n A B hA hB).1)
      have hnorm' := hnorm h
      exact isIso_scalar_transpose_of_mate (PY.scalar h).derivedAdj
        (PX.scalar h).derivedAdj (image.level m).adjunction (image.level n).adjunction
        (scalar.derivedTensor h) (scalar.restrictedDirect h) (scalar.restrictedDirect_mate h)
        ((image.directEvaluation m).app M) ((image.directEvaluation n).app M)
        ((PY.transition h).app (image.system.direct.obj M)) ((PX.transition h).app M)
        (scalar.directTransition h M)

end GenericComparison

namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived
/-- The generic evaluation-conjugacy argument for an arbitrary complete coefficient ring.
This is the proof underlying `etaleSystemEvaluationBound`, with no coefficient-field
presentation imposed on the ring. -/
private theorem exceptionalEvaluation
    {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O t c}
    (B : StrictEtaleBrownConstruction O t c S)
    {G : DerivedCategory (strictEtaleCoefficientSystem Y O t) ⥤
      DerivedCategory (strictEtaleCoefficientSystem X O t)}
    (adj : S.functor ⊣ G)
    {g : ∀ n : ℕ, DerivedCategory (strictEtaleLevel Y O t n) ⥤
      DerivedCategory (strictEtaleLevel X O t n)}
    (adjN : ∀ n : ℕ, S.levelFunctor n ⊣ g n) :
    Nonempty (StrictEtaleEvaluationBound B adj adjN) := by
  refine ⟨{
    theta := evaluationIso B adj adjN
    hom_chain := evaluationIso_hom_chain B adj adjN
    unique := evaluationIso_unique B adj adjN
    counit := evaluationIso_counit B adj adjN
    unit := evaluationIso_unit B adj adjN
    coefficient_transpose := coefficient_transpose B adjN
    transition := evaluationIso_transition B adj adjN
    coefficient_identity := coefficient_identity B adjN
    coefficient_composition := coefficient_composition B adjN
    transition_identity := right_transition_identity B adjN
    transition_composition := right_transition_composition B adjN
    lower_bound := right_lower_bound B adjN (evaluationIso B adj adjN) }⟩
end AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] constantSheaf

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing integer ring, lifted only to the site-value universe.
Source: blueprint integral coefficient systems
(blueprint: def-pur-adic-exceptional-system-realization). -/
abbrev integralExceptionalIntegers := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)

/-- The same chosen uniformizer in the lifted ring.
Source: blueprint integral coefficient systems
(blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalUniformizer : integralExceptionalIntegers l E :=
  ULift.up (Padic.coefficientExtensionUniformizer l E)

/-- The quotient ideal is carried to the original quotient ideal by size lowering.
Source: blueprint integral construction, coefficient identifications
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: a ring equivalence carries the principal ideal generated by the lifted
uniformizer to the ideal generated by the original one, and commutes with powers. -/
theorem integralExceptionalIdeal (n : ℕ) :
    Padic.coefficientExtensionIdeal l E (n + 1) =
      ((Ideal.span ({integralExceptionalUniformizer l E} :
        Set (integralExceptionalIntegers l E))) ^ (n + 1)).map
          (ULift.ringEquiv : integralExceptionalIntegers l E ≃+*
            Padic.coefficientExtensionIntegers l E).toRingHom := by
  change (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
    Set (Padic.coefficientExtensionIntegers l E))) ^ (n + 1) = _
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  rfl

/-- The explicit quotient equivalence, induced by the identity on integer coefficients.
Source: blueprint integral construction, coefficient identifications
(blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalQuotient (n : ℕ) :
    (integralExceptionalIntegers l E ⧸
      (Ideal.span ({integralExceptionalUniformizer l E} :
        Set (integralExceptionalIntegers l E))) ^ (n + 1)) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) :=
  (Ideal.quotientEquiv _ _
    (ULift.ringEquiv : integralExceptionalIntegers l E ≃+*
      Padic.coefficientExtensionIntegers l E) (integralExceptionalIdeal l E n)).trans
    (ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
      Padic.coefficientExtensionRing l E (n + 1)).symm

/-- Completeness, regularity, finiteness and prime-power torsion survive the explicit
lift of the integer ring and its quotient-coordinate equivalences. -/
private theorem exceptionalStages :
    IsAdicComplete (Ideal.span ({integralExceptionalUniformizer l E} :
      Set (integralExceptionalIntegers l E))) (integralExceptionalIntegers l E) ∧
    (∀ x : integralExceptionalIntegers l E,
      integralExceptionalUniformizer l E * x = 0 → x = 0) ∧
    (∀ n : ℕ, Finite (strictEtaleBrownRing
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)) ∧
    (∀ n : ℕ, ∃ a : ℕ, (l ^ a : strictEtaleBrownRing
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) = 0) := by
  let O := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  have hdvr := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsLocalRing O := hdvr.2.2.2.1
  have : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({t} : Set O) = IsLocalRing.maximalIdeal O :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.trans
      (IsLocalRing.eq_maximalIdeal (R := O) hdvr.2.2.2.2.1)
  have ht : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hgen.symm
  obtain ⟨hfinite, htorsion, _, hcomplete⟩ :=
    Padic.nonunit_coefficient_stages l E t ht.ne_zero ht.not_isUnit
  have hcompl : IsAdicComplete
      (Ideal.span {integralExceptionalUniformizer l E}) (integralExceptionalIntegers l E) := by
    have h := (IsAdicComplete.congr_ringEquiv (Ideal.span ({t} : Set O))
      (ULift.ringEquiv.symm : O ≃+* integralExceptionalIntegers l E)).mpr hcomplete
    rw [Ideal.map_span, Set.image_singleton] at h
    exact h
  refine ⟨hcompl, ?_, ?_, ?_⟩
  · intro x hx
    apply ULift.ext
    exact (mul_eq_zero.mp (congrArg ULift.down hx)).resolve_left ht.ne_zero
  · intro n
    have : Finite (Padic.coefficientExtensionRing l E (n + 1)) := hfinite n
    exact Finite.of_equiv _ (integralExceptionalQuotient l E n).toEquiv.symm
  · intro n
    obtain ⟨a, ha⟩ := htorsion n
    refine ⟨a, (integralExceptionalQuotient l E n).injective ?_⟩
    simp only [map_zero]
    apply ULift.ext
    exact ha

variable (W : Scheme.{u})

/-- Fix additive-group sheafification in the coefficient universe.
Source: the existing essentially-small-site sheafification
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: specialize `integralCoefficientAbSheafify` to the site-value universe. -/
theorem integralExceptionalSiteAbSheafify :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

/-- Fix the existing local-bijectivity criterion in the coefficient universe.
Source: the existing essentially-small-site sheafification
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: specialize `integralCoefficientAbLocallyBijective` to that universe. -/
theorem integralExceptionalSiteAbLocallyBijective :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

attribute [local instance 50000] integralExceptionalSiteAbSheafify
  integralExceptionalSiteAbLocallyBijective

/-- Fix commutative-ring sheafification once for all coefficient constructions.
Source: Mathlib sheafification on essentially small sites; integral coefficient systems
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: use the existing concrete-category sheafification instance on the pro-etale site. -/
theorem integralExceptionalSiteWeakSheafify :
    HasWeakSheafify (Scheme.ProEt.topology W) CommRingCat.{u + 1} := inferInstance

attribute [local instance] integralExceptionalSiteWeakSheafify

/-- The quotient-coordinate ring map, obtained by constant sheafification.
Source: blueprint integral construction, coefficient identifications
(blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalRingMap (n : ℕ) :
    (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientQuotientSheaf (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) ⟶
      integralCoefficientSheaf l E W n :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((constantSheaf _ CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (integralExceptionalQuotient l E n).toRingHom))

/-- Restriction along the explicit quotient-coordinate isomorphism.
Source: blueprint integral construction, coefficient identifications
(blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalLevel (n : ℕ) :=
  SheafOfModules.restrictScalars.{u + 1} (integralExceptionalRingMap l E W n)

private def exceptionalQuotientRings : ℕᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj n := CommRingCat.of (integralExceptionalIntegers l E ⧸
    (Ideal.span {integralExceptionalUniformizer l E}) ^ (n.unop + 1))
  map f := CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1)))
  map_id _ := by
    apply CommRingCat.hom_ext
    exact Ideal.Quotient.factor_eq
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact (Ideal.Quotient.factor_comp
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))).symm

private def exceptionalCoordinateNaturality :
    exceptionalQuotientRings l E ⋙ constantSheaf (Scheme.ProEt.topology W)
      CommRingCat.{u + 1} ⋙ sheafCompose _ (forget₂ CommRingCat RingCat) ⟶
        integralCoefficientSheafSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ integralExceptionalRingMap l E W n) (by
    intro n
    dsimp only [Functor.comp_map, exceptionalQuotientRings]
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    dsimp only [integralExceptionalRingMap, integralCoefficientSheafTransition]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    ext x
    rfl)

/-- The quotient-coordinate maps commute with all quotient transitions.
Source: blueprint integral construction, quotient cocycle
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: both ring maps send the class of an integer to its class modulo the smaller
power. Quotient surjectivity gives equality, and constant sheafification preserves it. -/
theorem integralExceptionalRingMap_comp {m n : ℕ} (h : n ≤ m) :
    integralExceptionalRingMap l E W m ≫ normalizedDVRQuotient l E W h =
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientQuotientMap (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) h) ≫
            integralExceptionalRingMap l E W n := by
  exact ((exceptionalCoordinateNaturality l E W).naturality (homOfLE h).op).symm

section CoordinateFunctorConstruction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] integralExceptionalQuotient integralExceptionalRingMap

/-- Scalar-restriction associativity, with no change to underlying sections.
Source: blueprint integral construction, quotient cocycle
(blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalLevelComp {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ integralExceptionalLevel l E W m ≅
      integralExceptionalLevel l E W n ⋙
        coefficientRestriction (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) h :=
  normalizedDVRRestrictionCompIso _ _ ≪≫
    eqToIso (congrArg (fun a ↦ SheafOfModules.restrictScalars.{u + 1} a)
      (integralExceptionalRingMap_comp l E W h)) ≪≫
    (normalizedDVRRestrictionCompIso _ _).symm

attribute [local irreducible] integralExceptionalLevelComp

/-- A strict coefficient system in the generic quotient presentation. Its transitions
are the actual horizontal restrictions of the original module on the sequence site.
Source: blueprint integral construction, strict systems
(blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalCoordinatesObj (M : coefficientSequenceModules l E W) :
    CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) where
  level n := (integralExceptionalLevel l E W n).obj
    ((coefficientSequenceEvaluation l E W n).obj M)
  transition n := (integralExceptionalLevel l E W (n + 1)).map
    ((coefficientSequenceTransition l E W (Nat.le_succ n)).app M) ≫
      (integralExceptionalLevelComp l E W (Nat.le_succ n)).hom.app
        ((coefficientSequenceEvaluation l E W n).obj M)

private theorem transitionNaturality
    {A B A' B' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    (r : B ⥤ A) (a : A ⥤ A') (b : B ⥤ B') (s : B' ⥤ A')
    (e : r ⋙ a ≅ b ⋙ s)
    {X X' : A} {Y Y' : B} (f : X ⟶ X') (g : Y ⟶ Y')
    (t : X ⟶ r.obj Y) (t' : X' ⟶ r.obj Y')
    (h : f ≫ t' = t ≫ r.map g) :
    a.map f ≫ (a.map t' ≫ e.hom.app Y') =
      (a.map t ≫ e.hom.app Y) ≫ s.map (b.map g) := by
  rw [← Category.assoc, ← a.map_comp, h, a.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ a.map t ≫ k) (e.hom.naturality g)

/-- Componentwise maps preserve the actual horizontal restrictions.
Source: blueprint integral construction, strict systems
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: naturality of coefficientSequenceTransition and of the restriction-composition
isomorphism gives the square; scalar restriction preserves composition. -/
theorem integralExceptionalCoordinates_comm
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N) (n : ℕ) :
    (integralExceptionalLevel l E W (n + 1)).map
      ((coefficientSequenceEvaluation l E W (n + 1)).map f) ≫
        (integralExceptionalCoordinatesObj l E W N).transition n =
      (integralExceptionalCoordinatesObj l E W M).transition n ≫
        (coefficientRestriction (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
          (Nat.le_succ n)).map
            ((integralExceptionalLevel l E W n).map
              ((coefficientSequenceEvaluation l E W n).map f)) := by
  let hn : n ≤ n + 1 := Nat.le_succ n
  exact transitionNaturality
    (normalizedDVRModuleRes l E W hn)
    (integralExceptionalLevel l E W (n + 1)) (integralExceptionalLevel l E W n)
    (coefficientRestriction (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) hn)
    (integralExceptionalLevelComp l E W hn)
    ((coefficientSequenceEvaluation l E W (n + 1)).map f)
    ((coefficientSequenceEvaluation l E W n).map f)
    ((coefficientSequenceTransition l E W hn).app M)
    ((coefficientSequenceTransition l E W hn).app N)
    ((coefficientSequenceTransition l E W hn).naturality f)

/-- Componentwise coordinate change on a system morphism.
Source: blueprint integral systems (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalCoordinatesMap {M N : coefficientSequenceModules l E W} (f : M ⟶ N) :
    integralExceptionalCoordinatesObj l E W M ⟶ integralExceptionalCoordinatesObj l E W N :=
  { app := fun n ↦ (integralExceptionalLevel l E W n).map
      ((coefficientSequenceEvaluation l E W n).map f)
    comm := integralExceptionalCoordinates_comm l E W f }

private theorem exceptionalSystemHomExt
    {M N : CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  exact system_hom_ext (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) f g h

/-- The coordinate change preserves identities and composition.
Source: blueprint integral systems (blueprint: def-pur-adic-exceptional-system-realization).
Proof: the components are compositions of functor maps. The identity and composition
laws hold at each level; equality of system morphisms is componentwise equality. -/
theorem integralExceptionalCoordinates_laws :
    (∀ M : coefficientSequenceModules l E W,
      integralExceptionalCoordinatesMap l E W (𝟙 M) = 𝟙 _) ∧
    (∀ {M N P : coefficientSequenceModules l E W} (f : M ⟶ N) (g : N ⟶ P),
      integralExceptionalCoordinatesMap l E W (f ≫ g) =
        integralExceptionalCoordinatesMap l E W f ≫ integralExceptionalCoordinatesMap l E W g) := by
  constructor
  · intro M
    apply exceptionalSystemHomExt
    funext n
    change (integralExceptionalLevel l E W n).map
      ((coefficientSequenceEvaluation l E W n).map (𝟙 M)) = 𝟙 _
    simp
  · intro M N P f g
    apply exceptionalSystemHomExt
    funext n
    change (integralExceptionalLevel l E W n).map
      ((coefficientSequenceEvaluation l E W n).map (f ≫ g)) = _
    simp only [Functor.map_comp]
    rfl

/-- The coordinate change on actual strict systems, retaining all horizontal restrictions.
Source: blueprint integral systems (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalCoordinates : coefficientSequenceModules l E W ⥤
    CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) where
  obj := integralExceptionalCoordinatesObj l E W
  map := integralExceptionalCoordinatesMap l E W
  map_id := (integralExceptionalCoordinates_laws l E W).1
  map_comp := (integralExceptionalCoordinates_laws l E W).2

end CoordinateFunctorConstruction

section CoordinateEquivalenceProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] integralExceptionalQuotient integralExceptionalRingMap
  integralExceptionalLevelComp

/-- Scalar restriction is invariant under equality of the coefficient map.
Source: blueprint quotient-coordinate cocycle; Stacks 03DA
(blueprint: def-pur-adic-exceptional-system-realization). -/
private def integralExceptionalRestrictionCongr
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} {a b : R ⟶ S} (h : a = b) :
    SheafOfModules.restrictScalars.{u + 1} a ≅ SheafOfModules.restrictScalars b :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ (ModuleCat.restrictScalarsCongr
        (congrArg (fun c : R ⟶ S ↦ (c.hom.app U).hom) h)).app (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem integralExceptionalRestrictionCongr_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} {a b : R ⟶ S} (h : a = b) :
    integralExceptionalRestrictionCongr h =
      eqToIso (congrArg (fun f : R ⟶ S ↦ SheafOfModules.restrictScalars.{u + 1} f) h) := by
  cases h
  ext M U x
  rfl

private def scalarSquare
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R R' : Sheaf K RingCat.{u + 1}} {S S' : Sheaf J RingCat.{u + 1}}
    (r : R ⟶ R') (a : S ⟶ S')
    (φ : S' ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R')
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (h : a ≫ φ = ψ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map r) :
    pushforward.{u + 1} φ ⋙ restrictScalars a ≅
      restrictScalars r ⋙ pushforward ψ :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ (ModuleCat.restrictScalarsCongr
        (congrArg (fun c : S ⟶
          (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R' ↦
            (c.hom.app U).hom) h)).app (M.val.obj (op (F.obj U.unop))))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

attribute [local irreducible] scalarSquare

private theorem coordinateRingMap_eq (n : ℕ) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
        (integralExceptionalQuotient l E n).toCommRingCatIso.hom) =
      integralExceptionalRingMap l E W n := by
  unfold integralExceptionalRingMap
  simp only [RingEquiv.toCommRingCatIso, RingEquiv.toRingHom_eq_coe]
  rfl

private theorem nativeSuccessor (n : ℕ) :
    normalizedDVRQuotient l E W (Nat.le_succ n) =
      integralCoefficientSheafTransition l E W n := by
  exact Functor.ofOpSequence_map_homOfLE_succ
    (integralCoefficientSheafTransition l E W) n

private theorem coordinateRingsSuccessor (n : ℕ) :
    (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)).map
        (homOfLE (Nat.le_succ n)).op ≫
      (constantSheaf _ CommRingCat.{u + 1}).map
        (integralExceptionalQuotient l E n).toCommRingCatIso.hom =
      (constantSheaf _ CommRingCat.{u + 1}).map
        (integralExceptionalQuotient l E (n + 1)).toCommRingCatIso.hom ≫
      (coefficientSequenceCommRingSystem l E W).map
        (homOfLE (Nat.le_succ n)).op := by
  let hn : n ≤ n + 1 := Nat.le_succ n
  have hD :
      (sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (coefficientSequenceCommRingTransition l E W n) =
        integralCoefficientSheafTransition l E W n := by
    ext U x
    rfl
  apply (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  simp only [coefficientRings, coefficientSequenceCommRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  erw [Functor.map_comp, Functor.map_comp, hD,
    coordinateRingMap_eq l E W (n + 1), coordinateRingMap_eq l E W n]
  have h := integralExceptionalRingMap_comp l E W hn
  rw [nativeSuccessor] at h
  exact h.symm

private def coordinateRingsMap :
    coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) ⟶
        coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence
    (F := coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (G := coefficientSequenceCommRingSystem l E W)
    (fun n ↦ (constantSheaf _ CommRingCat.{u + 1}).map
      (integralExceptionalQuotient l E n).toCommRingCatIso.hom)
    (coordinateRingsSuccessor l E W)

private def coordinateRingsIso :
    coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) ≅
        coefficientSequenceCommRingSystem l E W :=
  NatIso.ofComponents
    (fun n ↦ (constantSheaf _ CommRingCat.{u + 1}).mapIso
      (integralExceptionalQuotient l E n.unop).toCommRingCatIso)
    (fun f ↦ (coordinateRingsMap l E W).naturality f)

private def scalarRestrictionCancel
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def restrictionEquivalence
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
  CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (scalarRestrictionCancel e.inv e.hom e.inv_hom_id).symm
    (scalarRestrictionCancel e.hom e.inv e.hom_inv_id)

private def sequenceIsoOfIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [EssentiallySmall.{u + 1} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u + 1}} (e : A ≅ B) :
    systemSequenceRing A ≅ systemSequenceRing B :=
  { hom := ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := C)).functor
      (Functor.uncurry.map (Functor.whiskerRight e.hom
        (sheafToPresheaf J CommRingCat.{u + 1})))⟩
    inv := ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := C)).functor
      (Functor.uncurry.map (Functor.whiskerRight e.inv
        (sheafToPresheaf J CommRingCat.{u + 1})))⟩
    hom_inv_id := by
      ext X x
      exact congrArg (fun f ↦ f.hom.app (op X.unop.2) x)
        (Iso.hom_inv_id_app e (op X.unop.1))
    inv_hom_id := by
      ext X x
      exact congrArg (fun f ↦ f.hom.app (op X.unop.2) x)
        (Iso.inv_hom_id_app e (op X.unop.1)) }

private theorem nativeSequenceRing_eq :
    systemSequenceRing (coefficientSequenceCommRingSystem l E W) =
      coefficientSequenceCommRingSheaf l E W := by
  rfl

private def coordinateSequenceIso :
    systemSequenceRing.{u + 1, u, u + 1}
      (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)) ≅
      coefficientSequenceCommRingSheaf l E W :=
  sequenceIsoOfIso (coordinateRingsIso l E W) ≪≫ eqToIso (nativeSequenceRing_eq l E W)

private theorem coordinateSequenceIso_hom (n : ℕ) (U : W.ProEtᵒᵖ) :
    (((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (coordinateSequenceIso l E W)).hom.hom.app (op (n, U.unop))) =
        (integralExceptionalRingMap l E W n).hom.app U := by
  unfold coordinateSequenceIso sequenceIsoOfIso coordinateRingsIso integralExceptionalRingMap
  simp only [RingEquiv.toCommRingCatIso, RingEquiv.toRingHom_eq_coe]
  rfl

attribute [local irreducible] coordinateSequenceIso coordinateRingsIso

private def coordinateModel : coefficientSequenceModules l E W ⥤
    CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) :=
  SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (coordinateSequenceIso l E W)).hom ⋙
    sequenceToStrictSystemFunctor
      (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)) ⋙
    coefficientFromStrict.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)

private theorem coordinateModel_equivalence : (coordinateModel l E W).IsEquivalence := by
  have hr : (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (coordinateSequenceIso l E W)).hom).IsEquivalence :=
    inferInstanceAs (restrictionEquivalence
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (coordinateSequenceIso l E W))).functor.IsEquivalence
  have hs : (sequenceToStrictSystemFunctor
      (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E)
        (ell := integralExceptionalUniformizer l E))).IsEquivalence :=
    inferInstanceAs (strictSystemSequenceEquivalence.{u + 1, u, u + 1}
      (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E)
        (ell := integralExceptionalUniformizer l E))).inverse.IsEquivalence
  have hc : (coefficientFromStrict.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E)).IsEquivalence :=
    inferInstanceAs (coefficientSystemEquivalence.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E)).inverse.IsEquivalence
  unfold coordinateModel
  infer_instance

private theorem squareOfIdentityComponents
    {C : Type*} [Category C] {A B : C} (a r : A ⟶ B) (p : B ⟶ B) (q : A ⟶ A)
    (hp : p = 𝟙 B) (hq : q = 𝟙 A) (hr : r = a) : a ≫ p = q ≫ r := by
  rw [hp, hq, hr, Category.comp_id, Category.id_comp]

private theorem coordinateScalarSquare (n : ℕ) :
    integralExceptionalRingMap l E W n ≫
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm =
      systemSequenceVerticalRingMap
          (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
            (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
          n ≫
        ((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology W) (coefficientSequenceTopology
            (Scheme.ProEt.topology W))).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
            (coordinateSequenceIso l E W)).hom := by
  let A := coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
  let r := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (coordinateSequenceIso l E W)
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  let ψ := systemSequenceVerticalRingMap A n
  let a := integralExceptionalRingMap l E W n
  have hφ (U : W.ProEtᵒᵖ) : φ.hom.app U = 𝟙 _ := by
    dsimp only [φ]
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  have hψ (U : W.ProEtᵒᵖ) : ψ.hom.app U = 𝟙 _ := by
    rfl
  have hs : a ≫ φ = ψ ≫
      ((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology W) (coefficientSequenceTopology
          (Scheme.ProEt.topology W))).map r.hom := by
    apply (sheafToPresheaf (Scheme.ProEt.topology W) RingCat.{u + 1}).map_injective
    apply NatTrans.ext
    funext U
    change a.hom.app U ≫ φ.hom.app U =
      ψ.hom.app U ≫ r.hom.hom.app (op (n, U.unop))
    exact squareOfIdentityComponents (a.hom.app U)
      (r.hom.hom.app (op (n, U.unop))) (φ.hom.app U) (ψ.hom.app U)
      (hφ U) (hψ U) (coordinateSequenceIso_hom l E W n U)
  exact hs

private theorem coordinatesEvaluation_eq (n : ℕ) :
    integralExceptionalCoordinates l E W ⋙
        coefficientEvaluation (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n =
      coefficientSequenceEvaluation l E W n ⋙ integralExceptionalLevel l E W n := by
  rfl

private theorem coordinateModelEvaluation_eq (n : ℕ) :
    coordinateModel l E W ⋙
        coefficientEvaluation (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n =
      SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
            (coordinateSequenceIso l E W)).hom ⋙
        systemSequenceEvaluation
          (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
            (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
          n := by
  rfl

attribute [local irreducible] coefficientSystemAbelian
-- Normalize the explicit scalar action on one vertical slice.
private def coordinateLevelComparison (n : ℕ) :
    integralExceptionalCoordinates l E W ⋙
      coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n ≅
      coordinateModel l E W ⋙
        coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n := by
  exact eqToIso (coordinatesEvaluation_eq l E W n) ≪≫
    scalarSquare (Prod.sectR n W.ProEt)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (coordinateSequenceIso l E W)).hom
      (integralExceptionalRingMap l E W n)
      (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)
      (systemSequenceVerticalRingMap
        (coefficientRings.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)) n)
      (coordinateScalarSquare l E W n) ≪≫
    (eqToIso (coordinateModelEvaluation_eq l E W n)).symm

private def underlyingSectionMap
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (f : M ⟶ N) (U : Cᵒᵖ) : M.val.presheaf.obj U ⟶ N.val.presheaf.obj U :=
  (forget₂ (ModuleCat.{u + 1} (R.obj.obj U)) AddCommGrpCat.{u + 1}).map (f.val.app U)

attribute [local irreducible] underlyingSectionMap

private def restrictionComparisonIdentity
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S S' T : Sheaf J RingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) (f' : R ⟶ S') (g' : S' ⟶ T)
    (e : SheafOfModules.restrictScalars.{u + 1} g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars g' ⋙ SheafOfModules.restrictScalars f') : Prop :=
  ∀ (M : SheafOfModules.{u + 1} T) (U : Cᵒᵖ) (x : M.val.presheaf.obj U),
    underlyingSectionMap (e.hom.app M) U x = x

private theorem restrictionComparisonIdentity_comp
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S S' T : Sheaf J RingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) (f' : R ⟶ S') (g' : S' ⟶ T)
    (h : f ≫ g = f' ≫ g') :
    restrictionComparisonIdentity f g f' g'
      (normalizedDVRRestrictionCompIso f g ≪≫
        eqToIso (congrArg (fun a : R ⟶ T ↦ SheafOfModules.restrictScalars.{u + 1} a) h) ≪≫
          (normalizedDVRRestrictionCompIso f' g').symm) := by
  rw [← integralExceptionalRestrictionCongr_eq h]
  intro M U x
  unfold underlyingSectionMap
  rfl

private theorem coordinateLevelComp_hom {m n : ℕ} (h : n ≤ m) :
    restrictionComparisonIdentity
      (integralExceptionalRingMap l E W m) (normalizedDVRQuotient l E W h)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientQuotientMap (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) h))
      (integralExceptionalRingMap l E W n) (integralExceptionalLevelComp l E W h) := by
  unfold integralExceptionalLevelComp
  exact restrictionComparisonIdentity_comp _ _ _ _ (integralExceptionalRingMap_comp l E W h)

private theorem additiveConjugate_fun_heq
    {A A' B B' : AddCommGrpCat.{u + 1}} (eA : A = A') (eB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'}
    (h : eqToHom eA.symm ≫ f ≫ eqToHom eB = g) :
    HEq (fun x : A ↦ f x) (fun x : A' ↦ g x) := by
  cases eA
  cases eB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  cases h
  rfl

private def sectionMapAs
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (f : M ⟶ N) (U : Cᵒᵖ) {A B : AddCommGrpCat.{u + 1}} (g : A ⟶ B) : Prop :=
  HEq (fun x : M.val.presheaf.obj U ↦ underlyingSectionMap f U x) (fun x : A ↦ g x)

private theorem scalarComparisonSections
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {S T A B : Sheaf J RingCat.{u + 1}}
    (r : S ⟶ T) (a : A ⟶ S) (b : B ⟶ T) (q : A ⟶ B)
    (e : SheafOfModules.restrictScalars.{u + 1} r ⋙ SheafOfModules.restrictScalars a ≅
      SheafOfModules.restrictScalars b ⋙ SheafOfModules.restrictScalars q)
    (he : restrictionComparisonIdentity a r q b e)
    {M : SheafOfModules.{u + 1} S} {N : SheafOfModules.{u + 1} T}
    (t : M ⟶ (SheafOfModules.restrictScalars r).obj N) (U : Cᵒᵖ) :
    sectionMapAs ((SheafOfModules.restrictScalars a).map t ≫ e.hom.app N) U
      ((forget₂ (ModuleCat.{u + 1} (S.obj.obj U)) AddCommGrpCat.{u + 1}).map
        (t.val.app U)) := by
  unfold sectionMapAs underlyingSectionMap
  unfold restrictionComparisonIdentity underlyingSectionMap at he
  apply heq_of_eq
  funext x
  exact he N U ((t.val.app U) x)

private theorem scalarTransitionSections
    {C : Type*} [Category C]
    {J : GrothendieckTopology C} {S T A B : Sheaf J RingCat.{u + 1}}
    (r : S ⟶ T) (a : A ⟶ S) (b : B ⟶ T) (q : A ⟶ B)
    (e : SheafOfModules.restrictScalars.{u + 1} r ⋙ SheafOfModules.restrictScalars a ≅
      SheafOfModules.restrictScalars b ⋙ SheafOfModules.restrictScalars q)
    (he : restrictionComparisonIdentity a r q b e)
    {M : SheafOfModules.{u + 1} S} {N : SheafOfModules.{u + 1} T}
    (t : M ⟶ (SheafOfModules.restrictScalars r).obj N) (U : Cᵒᵖ)
    {V V' : AddCommGrpCat.{u + 1}} (g : V ⟶ V')
    (hF : M.val.presheaf.obj U = V)
    (hG : ((SheafOfModules.restrictScalars r).obj N).val.presheaf.obj U = V')
    (ht : eqToHom hF.symm ≫
      (forget₂ (ModuleCat.{u + 1} (S.obj.obj U)) AddCommGrpCat.{u + 1}).map
        (t.val.app U) ≫ eqToHom hG = g) :
    sectionMapAs ((SheafOfModules.restrictScalars a).map t ≫ e.hom.app N) U g := by
  exact (scalarComparisonSections r a b q e he t U).trans
    (additiveConjugate_fun_heq hF hG ht)

private theorem nativeTransition_spec {m n : ℕ} (h : n ≤ m) :
    ∀ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ),
      eqToHom (coefficientSequenceEvaluationAb_eq l E W M m U).symm ≫
        (forget₂ (ModuleCat.{u + 1} ((integralCoefficientSheaf l E W m).obj.obj U))
          AddCommGrpCat.{u + 1}).map
            (((coefficientSequenceTransition l E W h).app M).val.app U) ≫
        eqToHom (coefficientSequenceRestrictedEvaluationAb_eq l E W M h U) =
          M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op :=
  (coefficientSequenceTransition_exists l E W h).exists.choose_spec

private theorem coordinateTransitionSections (M : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) :
    sectionMapAs (((integralExceptionalCoordinates l E W).obj M).transition n) U
      (M.val.presheaf.map
        (Prod.mkHom (homOfLE (show n ≤ n + 1 from Nat.le_succ n)) (𝟙 U.unop)).op) := by
  let hn : n ≤ n + 1 := Nat.le_succ n
  exact scalarTransitionSections
    (normalizedDVRQuotient l E W hn)
    (integralExceptionalRingMap l E W (n + 1)) (integralExceptionalRingMap l E W n)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientQuotientMap (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) hn))
    (integralExceptionalLevelComp l E W hn)
    (coordinateLevelComp_hom l E W hn)
    ((coefficientSequenceTransition l E W hn).app M) U
    (M.val.presheaf.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op)
    (coefficientSequenceEvaluationAb_eq l E W M (n + 1) U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W M hn U)
    (nativeTransition_spec l E W hn M U)

private def coordinateSystemIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {M N : CoefficientSystem (J := J) O ell}
    (e : ∀ n, M.level n ≅ N.level n)
    (he : ∀ n, (e (n + 1)).hom ≫ N.transition n = M.transition n ≫
      (coefficientRestriction (J := J) O ell
        (Nat.le_succ n)).map (e n).hom) : M ≅ N where
  hom := { app := fun n ↦ (e n).hom, comm := he }
  inv := {
    app := fun n ↦ (e n).inv
    comm := by
      intro n
      apply (cancel_epi (e (n + 1)).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [he n, Category.assoc]
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rw [(coefficientRestriction (J := J) O ell
        (Nat.le_succ n)).map_id]
      exact (Category.comp_id _).symm }
  hom_inv_id := by
    apply coefficient_hom_ext
    intro n
    exact (e n).hom_inv_id
  inv_hom_id := by
    apply coefficient_hom_ext
    intro n
    exact (e n).inv_hom_id

private theorem functionSquare
    {A B A' B' : Type (u + 1)} (hA : A = B) (hB : A' = B')
    (f : A → B) (g : A' → B') (t : A → A') (t' : B → B')
    (hf : HEq f (id : A → A)) (hg : HEq g (id : A' → A'))
    (ht : HEq t t') : t' ∘ f = g ∘ t := by
  cases hA
  cases hB
  have hf' := eq_of_heq hf
  have hg' := eq_of_heq hg
  have ht' := eq_of_heq ht
  subst f
  subst g
  exact ht'.symm

private theorem moduleSquare
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (r : R ⟶ S)
    {A B : SheafOfModules.{u + 1} R} {A' B' : SheafOfModules.{u + 1} S}
    (f : A ⟶ B) (g : A' ⟶ B')
    (t : A ⟶ (SheafOfModules.restrictScalars r).obj A')
    (t' : B ⟶ (SheafOfModules.restrictScalars r).obj B')
    (hA : ∀ U, A.val.presheaf.obj U = B.val.presheaf.obj U)
    (hB : ∀ U, A'.val.presheaf.obj U = B'.val.presheaf.obj U)
    (hf : ∀ U, HEq (fun x : A.val.presheaf.obj U ↦ underlyingSectionMap f U x)
      (id : A.val.presheaf.obj U → A.val.presheaf.obj U))
    (hg : ∀ U, HEq (fun x : A'.val.presheaf.obj U ↦ underlyingSectionMap g U x)
      (id : A'.val.presheaf.obj U → A'.val.presheaf.obj U))
    (ht : ∀ U, HEq (fun x : A.val.presheaf.obj U ↦ underlyingSectionMap t U x)
      (fun x : B.val.presheaf.obj U ↦ underlyingSectionMap t' U x)) :
    f ≫ t' = t ≫ (SheafOfModules.restrictScalars r).map g := by
  ext U x
  have hh := congrFun (functionSquare
    (congrArg (fun V : AddCommGrpCat.{u + 1} ↦ (V : Type (u + 1))) (hA U))
    (congrArg (fun V : AddCommGrpCat.{u + 1} ↦ (V : Type (u + 1))) (hB U))
    (fun x : A.val.presheaf.obj U ↦ underlyingSectionMap f U x)
    (fun x : A'.val.presheaf.obj U ↦ underlyingSectionMap g U x)
    (fun x : A.val.presheaf.obj U ↦ underlyingSectionMap t U x)
    (fun x : B.val.presheaf.obj U ↦ underlyingSectionMap t' U x)
    (hf U) (hg U) (ht U)) x
  unfold underlyingSectionMap at hh
  exact hh

private def isoSectionsIdentity
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) : Prop :=
  ∀ U, M.val.presheaf.obj U = N.val.presheaf.obj U ∧
    HEq (fun x : M.val.presheaf.obj U ↦ underlyingSectionMap e.hom U x)
      (id : M.val.presheaf.obj U → M.val.presheaf.obj U)

private theorem coordinateLevelComparison_identity (n : ℕ)
    (M : coefficientSequenceModules l E W) :
    isoSectionsIdentity ((coordinateLevelComparison l E W n).app M) := by
  intro U
  constructor
  · rfl
  · unfold underlyingSectionMap coordinateLevelComparison scalarSquare
    rfl

private theorem modelTransitionSections (M : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) :
    sectionMapAs (((coordinateModel l E W).obj M).transition n) U
      (M.val.presheaf.map
        (Prod.mkHom (homOfLE (show n ≤ n + 1 from Nat.le_succ n)) (𝟙 U.unop)).op) := by
  unfold sectionMapAs underlyingSectionMap
  rfl

private def coordinateComparison : integralExceptionalCoordinates l E W ≅
    coordinateModel l E W :=
  NatIso.ofComponents (fun M ↦ coordinateSystemIso
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
    (fun n ↦ (coordinateLevelComparison l E W n).app M) (by
      intro n
      apply moduleSquare
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (coefficientQuotientMap (J := Scheme.ProEt.topology W)
            (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
            (Nat.le_succ n)))
      · intro U
        exact (coordinateLevelComparison_identity l E W (n + 1) M U).1
      · intro U
        exact (coordinateLevelComparison_identity l E W n M U).1
      · intro U
        exact (coordinateLevelComparison_identity l E W (n + 1) M U).2
      · intro U
        exact (coordinateLevelComparison_identity l E W n M U).2
      · intro U
        exact (coordinateTransitionSections l E W M n U).trans
          (modelTransitionSections l E W M n U).symm)) (by
    intro M N g
    apply coefficient_hom_ext
    intro n
    exact (coordinateLevelComparison l E W n).hom.naturality g)

private theorem coordinateProperties :
    (integralExceptionalCoordinates l E W).IsEquivalence ∧
      (integralExceptionalCoordinates l E W).Additive := by
  have : (coordinateModel l E W).IsEquivalence := coordinateModel_equivalence l E W
  have hE : (integralExceptionalCoordinates l E W).IsEquivalence :=
    Functor.isEquivalence_of_iso (coordinateComparison l E W).symm
  exact ⟨hE, Functor.additive_of_preserves_binary_products _⟩

end CoordinateEquivalenceProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] integralExceptionalCoordinates integralExceptionalCoordinatesObj
  integralExceptionalCoordinatesMap integralExceptionalLevelComp integralExceptionalRingMap
  integralExceptionalQuotient

/-- The coordinate functor is an additive equivalence.
Source: blueprint integral construction, strict systems
(blueprint: def-pur-adic-exceptional-system-realization).
Proof: the quotient equivalences give an isomorphism of the sequence-ring sheaves.
Restriction of scalars along it is an equivalence. Compose with the sequence-site
and adjacent-transition system equivalences. The level comparisons are identities
on sections; the specified native transition formula proves their system squares.
This gives a natural isomorphism with the coordinate functor. Transfer equivalence;
an equivalence preserves binary products and hence addition. -/
theorem integralExceptionalCoordinates_properties :
    (integralExceptionalCoordinates l E W).IsEquivalence ∧
      (integralExceptionalCoordinates l E W).Additive := by
  exact coordinateProperties l E W

/-- The actual coordinate equivalence. Source: blueprint integral systems
(blueprint: def-pur-adic-exceptional-system-realization). -/
instance integralExceptionalCoordinates_equivalence :
    (integralExceptionalCoordinates l E W).IsEquivalence :=
  (integralExceptionalCoordinates_properties l E W).1

/-- Addition is unchanged by quotient coordinates. Source: blueprint integral systems
(blueprint: def-pur-adic-exceptional-system-realization). -/
instance integralExceptionalCoordinates_additive :
    (integralExceptionalCoordinates l E W).Additive :=
  (integralExceptionalCoordinates_properties l E W).2

/-- The standard localization of the generic pro-etale strict-system category.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
instance integralExceptionalSystemDerived : HasDerivedCategory.{u + 2}
    (CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)) :=
  HasDerivedCategory.standard _

/-- The same standard localization at each quotient.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
instance integralExceptionalLevelDerived (n : ℕ) : HasDerivedCategory.{u + 2}
    (coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) :=
  HasDerivedCategory.standard _

/-- Exact change of coordinates on the actual derived system category.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalDerivedCoordinates :=
  (integralExceptionalCoordinates l E W).mapDerivedCategory

attribute [local irreducible] integralExceptionalDerivedCoordinates

/-- The inverse coordinate equivalence is additive.
Source: blueprint integral systems (blueprint: def-pur-adic-exceptional-system-realization).
Proof: apply the faithful additive coordinate functor. Its unit/counit identify the
image of each sum with the sum of the images, proving the original equality. -/
theorem integralExceptionalCoordinatesInv_additive :
    (integralExceptionalCoordinates l E W).asEquivalence.inverse.Additive := by
  let : (integralExceptionalCoordinates l E W).asEquivalence.functor.Additive :=
    inferInstanceAs (integralExceptionalCoordinates l E W).Additive
  infer_instance

attribute [instance] integralExceptionalCoordinatesInv_additive

/-- The inverse exact coordinate change, retaining all strict transitions.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalDerivedCoordinatesInv :=
  (integralExceptionalCoordinates l E W).asEquivalence.inverse.mapDerivedCategory

attribute [local irreducible] integralExceptionalDerivedCoordinatesInv

/-- The set inverse image of the actual etale/pro-etale site comparison.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
abbrev integralExceptionalSetInverse :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt W)
    (Type (u + 1)) W.smallEtaleTopology (Scheme.ProEt.topology W)

/-- The set direct image of the same geometric morphism.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
abbrev integralExceptionalSetDirect :=
  (Scheme.toProEt W).sheafPushforwardContinuous
    (Type (u + 1)) W.smallEtaleTopology (Scheme.ProEt.topology W)

attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived

/-- The canonical comparison on actual systems. The constituent ordinary image is
fixed on all coefficient sections and transitions; the derived image is fixed by
its universal K-injective factorization and its adjunction-mate equations.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
structure IntegralExceptionalComparison
    (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E)) where
  ordinary : CoefficientSystemOrdinaryImage
    (J := W.smallEtaleTopology) (K := Scheme.ProEt.topology W)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
    (integralExceptionalSetInverse W) (integralExceptionalSetDirect W)
    (Scheme.proEtaleSiteComparison W)
  evaluation : CoefficientEvaluationDerivedPackage (J := Scheme.ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
  derived : CoefficientSystemDerivedImage
    (J := W.smallEtaleTopology) (K := Scheme.ProEt.topology W)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
    (integralExceptionalSetInverse W) (integralExceptionalSetDirect W)
    (Scheme.proEtaleSiteComparison W) ordinary P evaluation

/-- Existence of the specified geometric system comparison, at any normalized
etale evaluation package. Its universal properties determine the construction up
to its unique compatible isomorphism; it is not a choice of levelwise lifts.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization).
Proof: apply lem-pur-coefficient-system-derived-comparison to the actual site
comparison. The lifted integer ring is complete and its uniformizer regular.
Changing the evaluation package uses its unique exact-localization comparison.
The defining section equations, transposes, and transition squares are retained. -/
theorem integralExceptionalComparison_exists
    (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E)) :
    Nonempty (IntegralExceptionalComparison l E W P) := by
  classical
  let : PreservesFiniteLimits (integralExceptionalSetInverse W) :=
    Scheme.preservesFiniteLimits_proEtaleSiteComparison W
  obtain ⟨hc, hregular, _, _⟩ := exceptionalStages l E
  let := hc
  obtain ⟨S, PX, ⟨T⟩⟩ := exceptionalComparisonForEvaluation
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
    (integralExceptionalSetInverse W) (integralExceptionalSetDirect W)
    (Scheme.proEtaleSiteComparison W) hregular P
  exact ⟨{ ordinary := S, evaluation := PX, derived := T }⟩

/-- The actual comparison, selected with all its universal normalizations.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalComparison
    (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E)) :=
  Classical.choice (integralExceptionalComparison_exists l E W P)

attribute [local irreducible] integralExceptionalComparison

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The Nagata compactification supplied by the finite-type field setting.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalCompactification : Compactification f :=
  letI := hasCompactification_of_finiteType_over_field D.k X Y f
  HasCompactification.compactification f

set_option linter.unusedSectionVars false in
include D hl in
/-- The Brown construction and normalized evaluation argument depend only on the
complete regular ring and its finite prime-power-torsion quotients. -/
private theorem exceptionalSupportFromStages
    (O : Type (u + 1)) [CommRing O] (t : O)
    (hregular : ∀ x : O, t * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({t} : Set O)) O]
    (hfinite : ∀ n : ℕ, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n : ℕ, ∃ a : ℕ, (l ^ a : strictEtaleBrownRing O t n) = 0)
    (c : Compactification f) :
    ∃ S : StrictEtaleCompactSupport O t c,
      Nonempty (StrictEtaleExceptionalAdjoint O t c S) := by
  classical
  obtain ⟨S, _, _⟩ := etaleCompactSupport_construction O t hregular c
  let (n : ℕ) : (S.properImage.lift n).modules.Additive :=
    S.properImage.inverseAdditive n
  let (n : ℕ) : (S.properImage.right n).Additive := S.properImage.rightAdditive n
  have hB : Nonempty (StrictEtaleBrownConstruction O t c S) := by
    obtain ⟨geom⟩ := etaleBrownGeometricComparisons D l hl O t hfinite htorsion f c S
    let CX := brownComponents X O t S.PX
    let CZ := brownComponents c.Z O t S.PZ
    let CY := brownComponents Y O t S.PY
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
    have : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
    have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
    have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
    have hp (n : ℕ) (I : Type (u + 1)) :
        PreservesColimitsOfShape (Discrete I) (S.properDerived.level n).direct := by
      have := hfinite n
      have : (geom.realizationZ.derived n).IsEquivalence :=
        geom.realizationZ.val.equivalence n
      have : (geom.realizationY.derived n).IsEquivalence :=
        geom.realizationY.val.equivalence n
      have : PreservesColimitsOfShape (Discrete I)
          ((Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.g).rightDerivedFunctor) :=
        (Etale.proper_rightDerivedLowerStar_preservesCoproducts
          (strictEtaleBrownRing O t n) c.g).1 I
      exact preserveViaEquivalences (S.properDerived.level n).direct
        ((Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          c.g).rightDerivedFunctor) (geom.realizationZ.derived n)
        (geom.realizationY.derived n) (geom.properRealization n).right
    have hcoproducts := brownCoproducts S CX CY hp
    obtain ⟨hadd, hs, hexact⟩ := towerExact S
    let : S.functor.Additive := hadd
    let : S.functor.CommShift ℤ := hs
    have : S.functor.IsTriangulated := hexact
    have := CX.grothendieck
    have := CY.grothendieck
    have := CX.derivedCoproducts
    have := CY.derivedCoproducts
    have : S.functor.IsLeftAdjoint := brownSized S.functor hcoproducts
    let G := S.functor.rightAdjoint
    let adj : S.functor ⊣ G := Adjunction.ofIsLeftAdjoint S.functor
    have : G.Additive := adj.right_adjoint_additive
    let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
    have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    have : G.IsTriangulated := adj.isTriangulated_rightAdjoint
    obtain ⟨scalarX, scalarY, hlinear⟩ := etaleCompactSupport_scalarAction S
    refine ⟨{ componentsX := CX
              componentsZ := CZ
              componentsY := CY
              additive := hadd
              shift := hs
              exact := hexact
              coproducts := hcoproducts
              scalarX := scalarX
              scalarY := scalarY
              linear := hlinear
              right := G
              adjunction := adj
              rightAdditive := inferInstance
              rightShift := inferInstance
              shiftAdjunction := inferInstance
              rightExact := inferInstance
              rightLinear := ?_
              unitLinear := ?_
              counitLinear := ?_
              realizationX := geom.realizationX
              realizationZ := geom.realizationZ
              realizationY := geom.realizationY
              properRealization := geom.properRealization
              openRealization := geom.openRealization
              openComparison := geom.openComparison
              openComparison_mate := geom.openComparison_mate
              levelComparison := geom.levelComparison
              levelComparison_def := geom.levelComparison_def
              openProjection := geom.openProjection
              openMate := geom.openMate
              properProjection := geom.properProjection
              properMate := geom.properMate
              projection := geom.projection
              projection_def := geom.projection_def
              projection_recorded_q := geom.projection_recorded_q
              properInsertion := strictEtaleBrownProperInsertion _ t c S
              properInsertion_conjugate := strictEtaleBrownProperInsertion_conjugate _ t c S
              properInsertionMate :=
                strictEtaleBrownProperInsertionMate _ t c S geom.properInsertionBelow
              properInsertionMate_def := fun _ ↦ rfl
              openInsertion := strictEtaleBrownOpenInsertion _ t c S
              openInsertion_conjugate := strictEtaleBrownOpenInsertion_conjugate _ t c S
              leftExtension :=
                strictEtaleBrownLeftExtension _ t c S geom.properInsertionBelow
              leftExtension_def := fun _ ↦ rfl
              leftExtension_below := geom.leftExtension_below }⟩
    · intro r M
      exact (scalar_adjunction adj (scalarX.derived r) (scalarY.derived r)
        (hlinear r)).2.2 M
    · intro r M
      simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
        (scalarX.derived r).naturality (adj.unit.app M)
    · intro r M
      simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
        ((scalarY.derived r).naturality (adj.counit.app M)).symm
  obtain ⟨B⟩ := hB
  have : B.right.Additive := B.rightAdditive
  have : B.right.CommShift ℤ := B.rightShift
  have hleft (n : ℕ) : (S.levelFunctor n).IsLeftAdjoint := by
    let : CommRing (strictEtaleBrownRing O t n) :=
      Ideal.Quotient.commRing ((Ideal.span ({t} : Set O)) ^ (n + 1))
    have : Finite (strictEtaleBrownRing O t n) := hfinite n
    have := B.realizationX.val.equivalence n
    have := B.realizationY.val.equivalence n
    have := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
      (strictEtaleBrownRing O t n) c
    have : (S.levelFunctor n ⋙ B.realizationY.derived n).IsLeftAdjoint :=
      Functor.isLeftAdjoint_of_iso (B.levelComparison n).symm
    exact (Functor.isLeftAdjoint_comp_iff_left (S.levelFunctor n)
      (B.realizationY.derived n)).mp inferInstance
  let g (n : ℕ) := @Functor.rightAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  let adjN (n : ℕ) : S.levelFunctor n ⊣ g n :=
    @Adjunction.ofIsLeftAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  obtain ⟨H⟩ := exceptionalEvaluation B B.adjunction adjN
  have : Fact D.p.Prime := ⟨D.prime⟩
  let := Fintype.ofFinite D.k₀
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  obtain ⟨N, hN⟩ := AlgebraicGeometry.brownFiniteAmplitude D.k D.p l hl
    (X ↘ Spec (.of D.k)) (Y ↘ Spec (.of D.k)) f (comp_over f _)
  have hamp (n : ℕ) (b : ℤ) (K : DerivedCategory (strictEtaleLevel X O t n))
      (hK : K.IsLE b) : ((S.levelFunctor n).obj K).IsLE (b + (N : ℤ)) := by
    have : Finite (strictEtaleBrownRing O t n) := hfinite n
    have hb := @hN c (strictEtaleBrownRing O t n)
      (Ideal.Quotient.commRing ((Ideal.span ({t} : Set O)) ^ (n + 1))) (hfinite n)
      (by simpa only [Nat.cast_pow] using htorsion n) b ((B.realizationX.derived n).obj K)
      ((AlgebraicGeometry.brownRealization_isLE_iff B.realizationX n K b).mpr hK)
    apply (AlgebraicGeometry.brownRealization_isLE_iff B.realizationY n _ _).mp
    exact ⟨(DerivedCategory.TStructure.t.le (b + (N : ℤ))).prop_of_iso
      ((B.levelComparison n).app K).symm hb.le⟩
  have hbound := H.lower_bound N hamp
  have hquot {m n : ℕ} (h : n ≤ m) :
      IsIso (strictEtaleBrownQuotientMate B adjN h) :=
    AlgebraicGeometry.brownQuotientMate_isIso D l hl f c S B hfinite
      (fun n ↦ by simpa only [Nat.cast_pow] using htorsion n) g adjN h
  let data : StrictEtaleExceptionalAdjointData O t c S :=
    { right := B.right
      rightAdditive := B.rightAdditive
      shift := B.rightShift
      adjunction := B.adjunction
      scalarX := B.scalarX
      scalarY := B.scalarY
      levelRight := g
      levelAdjunction := adjN
      evaluation := H.theta
      quotientOpen := B.openProjection
      quotientProper := B.properProjection
      quotientProjection := B.projection
      quotientComparison := fun h ↦ @asIso _ _ _ _
        (strictEtaleBrownQuotientMate B adjN h) (hquot h) }
  refine ⟨S, ⟨⟨data, ?_⟩⟩⟩
  refine ⟨B.rightExact, B.rightLinear, ?_, B.openMate, B.properMate,
    B.projection_def, ?_, H.coefficient_identity, H.coefficient_composition,
    ?_, ⟨N, hbound⟩, ?_⟩
  · intro n
    ext M
    apply (adjN n).homEquiv _ _ |>.symm.injective
    simpa only [Adjunction.homEquiv_counit] using
      (H.counit n M).trans (mateEquiv_counit B.adjunction (adjN n)
        (.mk _ _ _ _ (S.evaluation n).inv) M).symm
  · intro m n h
    rfl
  · intro m n h M
    exact (H.transition h M).symm
  · intro M hM hnormalized
    obtain ⟨a, ha⟩ := hM
    refine ⟨⟨a - N, hbound a M ha⟩,
      ?_⟩
    intro m n h
    have hinput : IsIso (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
      ((S.PY.transition h).app M)) := hnormalized h
    have hi : IsIso
        ((S.PX.scalar h).derived.map ((H.theta m).hom.app M) ≫
          strictEtaleBrownRightSystemTransition B adjN h M) := by
      dsimp only [strictEtaleBrownRightSystemTransition]
      have := hquot h
      infer_instance
    rw [← H.transition h M] at hi
    exact IsIso.of_isIso_comp_right _ ((H.theta n).hom.app M)

include hl in
/-- The ordinary etale compact-support system functor has its Brown right adjoint.
The data are the normalized open extension, proper K-injective direct image and
adjunction from lem-pur-etale-coefficient-system-adjoint, with only a size lift of O_E.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization).
Proof: work with ULift O_E and its lifted uniformizer in that node's construction.
Its quotient rings are exactly the explicit quotient equivalences above; regularity,
completeness and finiteness of quotients are invariant under this ring equivalence.
Extension by zero is the left adjoint of the actual system inverse image; proper
pushforward is its universal derived functor. Their composite preserves coproducts
by finite-level proper torsion cohomology. Brown representability supplies the right
adjoint on actual systems, whose evaluation and quotient mates are those of the node. -/
theorem integralExceptionalSupport_exists :
    ∃ S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) (integralExceptionalCompactification D f),
      Nonempty (StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) (integralExceptionalCompactification D f) S) := by
  obtain ⟨hcomplete, hregular, hfinite, htorsion⟩ := exceptionalStages l E
  let := hcomplete
  exact exceptionalSupportFromStages l D hl f
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
    hregular hfinite htorsion (integralExceptionalCompactification D f)

/-- The uniquely normalized ordinary etale compact-support system construction.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalSupport := (integralExceptionalSupport_exists l E D hl f).choose

/-- The system right adjoint with its actual finite evaluation and quotient mates.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalAdjoint :=
  Classical.choice (integralExceptionalSupport_exists l E D hl f).choose_spec

/-- The integral exceptional inverse image, literally the total inverse limit of
nu_X^* G_f Rnu_Y,* of the strict derived coefficient reduction. G_f is the ordinary
etale compact-support system right adjoint. All functors act on actual systems;
quotient coefficient actions are retained until the specified scalar-restricted limit.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalSystem :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      coefficientSequenceDerived l E X :=
  (pullbackTensorCalculus l E Y).reduction ⋙
    integralExceptionalDerivedCoordinates l E Y ⋙
    (integralExceptionalComparison l E Y
      (integralExceptionalSupport l E D hl f).PY).derived.system.direct ⋙
    (integralExceptionalAdjoint l E D hl f).right ⋙
    (integralExceptionalComparison l E X
      (integralExceptionalSupport l E D hl f).PX).derived.system.inverse ⋙
    integralExceptionalDerivedCoordinatesInv l E X

/-- The actual derived inverse limit of the exceptional coefficient system.
Source: blueprint integral construction (blueprint: def-pur-adic-exceptional-system-realization). -/
def integralExceptionalInverseImage :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
  integralExceptionalSystem l E D hl f ⋙ coefficientSequenceLimit l E X

end WeilConjectures
