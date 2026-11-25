/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteRealizationExists
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarExtensionLaws
import all WeilConjectures.SmoothPurity.Compact.CompactSupportNativeNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportProjectionAdjunct
import WeilConjectures.SmoothPurity.Compact.CompactSupportRoosTriangleTransport
import WeilConjectures.SmoothPurity.Compact.CompactSupportRoosTriangleUniqueness
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Normalized compact-support finite action

Source: blueprint order 1494, coherent strict-tower realization and rationalization
(blueprint: def-weil-compact-support-finite-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.proofsInPublic true

set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct Opposite
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientSequenceTransition constantSheaf
  sfIntegralCompactSupportValue
  Padic.coefficientExtensionIdeal compactSupportOrdinaryCoefficientTransition

open CategoryTheory.Pretriangulated in
private theorem roos_unique
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : ℕ → C} [HasProduct T] (t : ∀ n, T (n + 1) ⟶ T n)
    {M N : C} (p : M ⟶ ∏ᶜ T) (q : N ⟶ ∏ᶜ T)
    (δ : ∏ᶜ T ⟶ M⟦(1 : ℤ)⟧) (ε : ∏ᶜ T ⟶ N⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle t M p δ) (hq : IsDerivedLimitTriangle t N q ε) :
    ∃ e : M ≅ N, e.hom ≫ q = p := by
  exact compactSupportRoosTriangleUniqueness t p q δ ε hp hq

open CategoryTheory.Pretriangulated in
private theorem roos_transport {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X Y : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    {K L : C} (e : K ≅ L) (a : ∀ n, X n ≅ Y n)
    (p : ∀ n, K ⟶ X n) (q : ∀ n, L ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p n ≫ (a n).hom = e.hom ≫ q n)
    (h : ∃ hprod : HasProduct X, letI := hprod
      ∃ δ : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f K (Pi.lift p) δ) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ : (∏ᶜ Y) ⟶ L⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g L (Pi.lift q) δ := by
  exact compactSupportRoosTriangleTransport f g e a p q ht hp h

private theorem derivedTransition_congr
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : A ⥤ C) (R R' : C ⥤ B)
    [F.Additive] [G.Additive] [R.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (h : R = R') (τ : F ⟶ G ⋙ R) (τ' : F ⟶ G ⋙ R')
    (hτ : τ ≫ Functor.whiskerLeft G (eqToHom h) = τ') :
    CategoryTheory.derivedTransition F G R τ ≫
      Functor.whiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (eqToIso h)).hom =
      CategoryTheory.derivedTransition F G R' τ' := by
  exact CompactSupportNativeNormalization.derivedTransition_congr F G R R' h τ τ' hτ

section TowerHelpers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance directQuotient_limits (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _

private instance directQuotient_colimits (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _

private def finiteRestrictionIso (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory := by
  exact CompactSupportNativeNormalization.finiteRestrictionIso l E W h

private theorem ordinaryTransition_app_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E W) :
    (coefficientSequenceTransition.{u, u} l E W h).app M ≫
      eqToHom (congrArg
        (fun F : normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m ↦
          F.obj ((coefficientSequenceEvaluation.{u, u} l E W n).obj M))
        (compactSupportModuleRes_eq l E W h)) =
      (compactSupportOrdinaryCoefficientTransition l E W h).app M := by
  exact CompactSupportNativeNormalization.ordinaryTransition_app_eq l E W h M

private theorem derivedTransition_direct (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedTransition.{u, u} l E W h ≫
      Functor.whiskerLeft (coefficientSequenceDerivedEvaluation.{u, u} l E W n)
        (finiteRestrictionIso l E W h).hom =
      compactSupportCoefficientTransition l E W h := by
  unfold finiteRestrictionIso
  exact CompactSupportNativeNormalization.derivedTransition_direct l E W h

private theorem adjacentRestrictionComp (W : Scheme.{u}) (j : ℕ) :
    compactSupportRestrictionComp l E W (j + 1) j j.le_succ =
      sfCompactSupportDerivedRestrictionComp l E W j := by
  rfl

private theorem adjacentReductionMap (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) (j : ℕ) :
    compactSupportReductionMap l E W (j + 1) j j.le_succ K =
      sfCompactSupportReductionTransition l E W K j := by
  rfl

private theorem adjacentQuotient (j : ℕ) :
    compactSupportLevelQuotient l E (j + 1) j j.le_succ =
      Padic.coefficientExtensionTransition l E (j + 1) := by
  rfl

private theorem finiteConstructible_iso (W : Scheme.{u}) (n : ℕ)
    {A B : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : A ≅ B)
    (h : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W A) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W B := by
  exact CompactSupportNativeNormalization.finiteConstructible_iso l E W n e h

private theorem constantTowerTransition_eq (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRTowerTransition l E W D hl h =
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h := by
  rfl

end TowerHelpers

private theorem scalarExtension_laws
    {R : Type*} [CommRing R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (p : R) (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (∀ K : C, (F.mapLinearMap R).baseChange (Localization.Away p)
      ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) = (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (a : Localization.Away p ⊗[R] (K ⟶ L))
        (b : Localization.Away p ⊗[R] (L ⟶ M)),
      (F.mapLinearMap R).baseChange (Localization.Away p)
        (ScalarLocalization.composition R C p K L M b a) =
      ScalarLocalization.composition R D p (F.obj K) (F.obj L) (F.obj M)
        ((F.mapLinearMap R).baseChange (Localization.Away p) b)
        ((F.mapLinearMap R).baseChange (Localization.Away p) a)) := by
  exact compactSupportScalarExtensionLaws p F

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

attribute [local irreducible] SfCompactSupportFiniteRealizationSpec

/-- The already normalized integral compact-support functor, retaining its coherent
strict-tower construction and the fixed projections of sfCompactSupportTerm.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action). -/
@[irreducible] def sfCompactSupportFiniteIntegralFunctor
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfCompactSupportFiniteRealization l K₀ hl c E).choose

/-- Linearity of the fixed integral realization.
Source: blueprint order 1494, proof steps 3--4
(blueprint: def-weil-compact-support-finite-action).
Proof: project the additive and integral-linear conjuncts for the chosen integral
functor in sfCompactSupportFiniteRealization. -/
theorem sfCompactSupportFiniteIntegralFunctor_linear (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).Additive ∧
      (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).Linear
        (Padic.coefficientExtensionIntegers l
          E) := by
  unfold sfCompactSupportFiniteIntegralFunctor
  have h := (sfCompactSupportFiniteRealization l K₀ hl c E).choose_spec
  with_unfolding_all
    exact ⟨h.1, h.2.1⟩

/-- The actual tensor extension of the fixed integral Hom map.
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteHomMap (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K L : sfRationalConstructibleCategory l E X) :
    (K ⟶ L) →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l
      E)]
      ((⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩ :
        sfRationalConstructibleCategory l E Y) ⟶
        (⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj L.obj⟩ :
          sfRationalConstructibleCategory l E Y)) :=
  letI := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).1
  letI := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).2
  ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).mapLinearMap
    (Padic.coefficientExtensionIntegers l
      E)).baseChange
        (Localization.Away (Padic.coefficientExtensionUniformizer l
          E))

/-- The tensor Hom map preserves identities and composition.
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action).
Proof: on pure tensors, baseChange sends a tensor v to a tensor F(v). Apply the
integral functor laws and the prescribed tensor-composition formula. Extend by
additivity in both variables, since pure tensors generate the localized Hom modules. -/
theorem sfCompactSupportFiniteHomMap_laws (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (∀ K : sfRationalConstructibleCategory l E X,
      sfCompactSupportFiniteHomMap l K₀ hl c E K K (𝟙 K) =
        𝟙 (⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩ :
          sfRationalConstructibleCategory l E Y)) ∧
    (∀ (K L N : sfRationalConstructibleCategory l E X) (a : K ⟶ L) (b : L ⟶ N),
      sfCompactSupportFiniteHomMap l K₀ hl c E K N (a ≫ b) =
        sfCompactSupportFiniteHomMap l K₀ hl c E K L a ≫
          sfCompactSupportFiniteHomMap l K₀ hl c E L N b) := by
  let := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).2
  exact scalarExtension_laws (Padic.coefficientExtensionUniformizer l E)
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E) |>.imp
      (fun h K ↦ h K.obj) (fun h K L N a b ↦ h K.obj L.obj N.obj a b)

/-- The raw Hom scalar extension of the fixed integral action. Objects and all
morphisms are constructed explicitly; on pure tensors the map is a tensor F(v).
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteFunctor (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y where
  obj K := ⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩
  map {K L} a := sfCompactSupportFiniteHomMap l K₀ hl c E K L a
  map_id K := (sfCompactSupportFiniteHomMap_laws l K₀ hl c E).1 K
  map_comp a b := (sfCompactSupportFiniteHomMap_laws l K₀ hl c E).2 _ _ _ a b

/-- The value equality retained in the fixed integral realization.
Source: blueprint order 1494, integral realization clause
(blueprint: def-weil-compact-support-finite-action).
Proof: project the object-normalization conjunct of the already recorded
exists_compactSupportRepresentativeComparison package used in the definition. -/
theorem sfCompactSupportFiniteIntegralFunctor_obj
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X) :
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K =
      sfIntegralCompactSupportValue l E K₀ hl c K := by
  unfold sfCompactSupportFiniteIntegralFunctor
  have h := (sfCompactSupportFiniteRealization l K₀ hl c E).choose_spec
  with_unfolding_all
    exact h.2.2.1 K

/-- The canonical n-th reduction comparison is the tensor/restriction adjoint of
the fixed n-th projection in the definition of sfIntegralCompactSupportValue.
Source: blueprint definition order 1490 and proposition-six-operations-change-coefficients
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportChosenReduction (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E
      Y n).obj (sfIntegralCompactSupportValue l
        E K₀ hl c K).obj ⟶
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l
      E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) := by
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K.obj) (sfCompactSupportTransition l E c K.obj)).1
  let hM : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) (Classical.choose h) :=
    Classical.choose_spec h
  unfold IsDerivedLimit at hM
  unfold sfIntegralCompactSupportValue
  exact ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
      (Classical.choose hM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n)

/-- The specified projection adjunct is invertible, without an extra Tor or
finite-base-field assumption.
Source: definition order 1490; proposition-six-operations-change-coefficients, compact-support
paragraph (blueprint: def-weil-compact-support-finite-action).
Proof: the source is the chosen derived limit of the actual compact-support tower.
Proper direct image commutes with the perfect two-term quotient tensor, and open
extension is exact and commutes with that tensor. These are the normalized unit/counit
mates. Their reduction cocycle identifies the displayed adjunct with the finite-level
comparison. The proper/open coefficient-change theorem makes it invertible. -/
theorem sfCompactSupportChosenReduction_isIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) : IsIso (sfCompactSupportChosenReduction l K₀ hl c E K n) := by
  classical
  let := integralOperationsDerivedCountableProducts l E Y
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K.obj) (sfCompactSupportTransition l E c K.obj)).1
  let M := Classical.choose h
  let hM : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) M :=
    Classical.choose_spec h
  have hi := compactSupportProjectionAdjunct_isIso l K₀ hl c E K n M
    hM.choose hM.choose_spec.choose hM.choose_spec.choose_spec
  unfold sfCompactSupportChosenReduction sfIntegralCompactSupportValue
  exact hi

/-- Reduction of the fixed integral functor, using its actual value equality and
the uniquely specified projection adjunct, rather than a freely chosen isomorphism.
Source: definition order 1490; proposition-six-operations-change-coefficients
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteReductionIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E
      Y n).obj ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≅
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l
      E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) :=
  (scalarReductionDerivedExtension l E Y n).mapIso
      ((sfIntegralConstructible l E Y).ι.mapIso
        (eqToIso (sfCompactSupportFiniteIntegralFunctor_obj l K₀ hl c E K))) ≪≫
    @asIso _ _ _ _ (sfCompactSupportChosenReduction l K₀ hl c E K n)
      (sfCompactSupportChosenReduction_isIso l K₀ hl c E K n)

end FiniteAction
end WeilConjectures
