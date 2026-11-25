/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarReductionTowerBalancing
public import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData

import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteQuotientModuleBalancing

import all WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Canonical evaluation data for strict compact-support scalar mates

Source: Stacks 07A6, 0B56, 0940 and 0E8I.
(blueprint: def-pur-strict-scalar-mate-evaluation-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.exactAdj
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcScalarAdjunction
  AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
  WeilConjectures.PurCompactSupport.finiteChange
  WeilConjectures.PurCompactSupport.projection
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] AlgebraicGeometry.ProEtale.StrictTower.adj
  scalarAdj properRestriction

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Positive arithmetic selection preserves K-injective tower complexes.
Source: Stacks 0940; tower evaluation argument
(blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: the left adjoint replaces level m+1 by level ceil((m+1)/e) and uses
composite transitions. It is exact because it is pointwise evaluation. The
adjunction on complexes is termwise, so the exact-left-adjoint criterion applies. -/
theorem subsequence_preservesKInjective (W : Scheme.{u}) (e : ℕ) (he : 1 ≤ e) :
    (ordinarySubsequence l F W e).PreservesKInjectiveComplexes := by
  constructor
  intro K hK
  exact CategoryTheory.StrictTowerArithmetic.restriction_preservesKInjectives
    (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) e he K

/-- The sectionwise identity square for ordinary pushforward and selection.
Source: Stacks 03DA, 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def reindexProperOrdinary {X Y : Scheme.{u}} (g : X ⟶ Y) (e : ℕ) :
    towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙
        ordinarySubsequence l F Y e ≅
      ordinarySubsequence l F X e ⋙
        towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g :=
  Iso.refl _

/-- Derived reindexing of proper image, with its standard derived-composite units.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def reindexProper {X Y : Scheme.{u}} (g : X ⟶ Y) (e : ℕ) (he : 1 ≤ e) :
    R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙ subsequence l F Y e ≅
      subsequence l F X e ⋙ R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g :=
  haveI := subsequence_preservesKInjective l F X e he
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
    (ordinarySubsequence l F Y e)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (reindexProperOrdinary l F g e) ≪≫
    Functor.rightDerivedFunctorCompIso (ordinarySubsequence l F X e)
      (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g) ≪≫
    Functor.isoWhiskerRight
      (ordinarySubsequence l F X e).rightDerivedFunctorIsoMapDerivedCategory _

/-- The ordinary exact open comparison with arithmetic selection is identity.
Source: Stacks 0E8I, 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def reindexOpenOrdinary {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (e : ℕ) :
    towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j ⋙
        ordinarySubsequence l F Y e ≅
      ordinarySubsequence l F X e ⋙
        towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j :=
  Iso.refl _

/-- The canonical exact localization of the open selection square.
Source: Stacks 0E8I, 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def reindexOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (e : ℕ) :
    J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j ⋙ subsequence l F Y e ≅
      subsequence l F X e ⋙ J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j :=
  Functor.mapDerivedCategorySquareIso (reindexOpenOrdinary l F j e)

/-- Selection through the separately derived proper/open functor.
Source: Stacks 0E8I, 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def reindexImage {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : ℕ) (he : 1 ≤ e) :
    image l F c ⋙ subsequence l F Y e ≅ subsequence l F X e ⋙ image l F c :=
  Functor.isoWhiskerLeft
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c.i)
    (reindexProper l F c.g e he) ≪≫
    Functor.isoWhiskerRight (reindexOpen l F c.i e) _

/-- The actual B-linear strict support-tower map. The middle factors are the
proper scalar mate and proper image of open tensor balancing in that order.
All endpoint identifications are fixed by whole-diagram units and tensor formulas.
Source: Stacks 07A6, 0B56, 0E8I, 0940
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def arrow {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    support l E c S ⋙ T l E F i Y ⟶
      pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
        support l F c S' ⋙ subsequence l F Y e :=
  (Functor.isoWhiskerRight (supportModel l E c S) (T l E F i Y)).hom ≫
    Functor.whiskerLeft (reduction l E X S) (comparison l E F i c) ≫
    Functor.whiskerRight (reductionBalancing l E F i X S S' e he hepos).hom (image l F c) ≫
    (Functor.isoWhiskerLeft
      (pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙ reduction l F X S')
      (reindexImage l F c e hepos).symm).hom ≫
    (Functor.isoWhiskerLeft (pbcDerivedExtend (completedCoefficientMap l E F i X))
      (Functor.isoWhiskerRight (supportModel l F c S').symm (subsequence l F Y e))).hom

private theorem exact_of_tower {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D)
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)] :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  let H := (Functor.whiskeringRight ℕᵒᵖ C D).obj F
  let V := (evaluation ℕᵒᵖ D).obj (op 0)
  have : PreservesFiniteLimits (H ⋙ V) := comp_preservesFiniteLimits H V
  have : PreservesFiniteColimits (H ⋙ V) := comp_preservesFiniteColimits H V
  have hL := comp_preservesFiniteLimits (Functor.const ℕᵒᵖ : C ⥤ _) (H ⋙ V)
  have hC := comp_preservesFiniteColimits (Functor.const ℕᵒᵖ : C ⥤ _) (H ⋙ V)
  exact ⟨hL, hC⟩

/-- Positive-exponent finite restriction to the constant integral ring.
Source: Stacks 03DA (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def ordinaryPositiveRestriction (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :=
  pbcRestrict (PurCompactSupport.projection l E m hm W) ⋙ constantRestriction l E W

/-- The positive-exponent restriction is additive and exact.
Source: Stacks 03DA (blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: both restrictions preserve the underlying abelian sheaf and its maps, hence
preserve kernels, cokernels and addition of morphisms. -/
theorem ordinaryPositiveRestriction_exact (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    (ordinaryPositiveRestriction l E W m hm).Additive ∧
      PreservesFiniteLimits (ordinaryPositiveRestriction l E W m hm) ∧
        PreservesFiniteColimits (ordinaryPositiveRestriction l E W m hm) := by
  have := (towerConstantRestriction_exact l E W).1
  have := (towerConstantRestriction_exact l E W).2
  have h := exact_of_tower (constantRestriction l E W)
  have := h.1
  have := h.2
  unfold ordinaryPositiveRestriction
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity at a positive exponent. Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
instance positiveRestriction_additive (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    (ordinaryPositiveRestriction l E W m hm).Additive :=
  (ordinaryPositiveRestriction_exact l E W m hm).1

/-- Finite limits at a positive exponent. Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
instance positiveRestriction_limits (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    PreservesFiniteLimits (ordinaryPositiveRestriction l E W m hm) :=
  (ordinaryPositiveRestriction_exact l E W m hm).2.1

/-- Finite colimits at a positive exponent. Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
instance positiveRestriction_colimits (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    PreservesFiniteColimits (ordinaryPositiveRestriction l E W m hm) :=
  (ordinaryPositiveRestriction_exact l E W m hm).2.2

/-- The specified positive-exponent exact restriction on derived categories.
Source: Stacks 03DA (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def positiveRestriction (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :=
  (ordinaryPositiveRestriction l E W m hm).mapDerivedCategory

/-- Restriction of a positive finite quotient to the actual constant integral ring.
Source: Stacks 03DA (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def ordinaryFiniteRestriction (W : Scheme.{u}) (n : ℕ) :=
  ordinaryPositiveRestriction l E W (n + 1) (Nat.le_add_left 1 n)

/-- Exactness and additivity of this specified coefficient restriction.
Source: Stacks 03DA (blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: both restrictions leave the underlying abelian sheaf unchanged. Kernels,
cokernels and addition of morphisms are consequently preserved. -/
theorem ordinaryFiniteRestriction_exact (W : Scheme.{u}) (n : ℕ) :
    (ordinaryFiniteRestriction l E W n).Additive ∧
      PreservesFiniteLimits (ordinaryFiniteRestriction l E W n) ∧
        PreservesFiniteColimits (ordinaryFiniteRestriction l E W n) := by
  exact ordinaryPositiveRestriction_exact l E W (n + 1) (Nat.le_add_left 1 n)

/-- Additivity of finite restriction. Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
instance finiteRestriction_additive (W : Scheme.{u}) (n : ℕ) :
    (ordinaryFiniteRestriction l E W n).Additive :=
  (ordinaryFiniteRestriction_exact l E W n).1

/-- Finite limits under finite restriction. Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
instance finiteRestriction_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (ordinaryFiniteRestriction l E W n) :=
  (ordinaryFiniteRestriction_exact l E W n).2.1

/-- Finite colimits under finite restriction. Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
instance finiteRestriction_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (ordinaryFiniteRestriction l E W n) :=
  (ordinaryFiniteRestriction_exact l E W n).2.2

/-- The specified exact finite restriction on ordinary unbounded derived categories.
Source: Stacks 03DA (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def finiteRestriction (W : Scheme.{u}) (n : ℕ) :=
  (ordinaryFiniteRestriction l E W n).mapDerivedCategory

private theorem id_heq_of_eq {A B : Type u} (h : A = B) : HEq (@id A) (@id B) := by
  cases h
  rfl

private theorem moduleSheafFunctor_identity_iso
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} (F G : D ⥤ SheafOfModules R) (h : F = G)
    (T : D → Cᵒᵖ → Type*) (hT : ∀ N U, ((G.obj N).val.obj U : Type _) = T N U) :
    ∃! d : F ≅ G, ∀ (N : D) (U : Cᵒᵖ),
      HEq (fun x ↦ (d.hom.app N).val.app U x)
        (id : T N U → T N U) := by
  subst G
  refine ⟨Iso.refl F, ?_, ?_⟩
  · intro N U
    exact id_heq_of_eq (hT N U)
  · intro d hd
    apply Iso.ext
    ext N U x
    have hd' := (hd N U).trans (id_heq_of_eq (hT N U)).symm
    exact congrFun (eq_of_heq hd') x

/-- Evaluation and restriction have a unique identity-on-sections identification.
Source: Stacks 03DA, 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: both functors give the same section groups, actions and restriction maps.
Identity on every section is natural and invertible, and determines the comparison. -/
theorem evaluationRestriction_existsUnique (W : Scheme.{u}) (n : ℕ) :
    ∃! d : systemRestriction l E W ⋙
          (evaluation ℕᵒᵖ
            (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)).obj (op n) ≅
        coefficientSequenceEvaluation.{u, u} l E W n ⋙ ordinaryFiniteRestriction l E W n,
      ∀ (N : coefficientSequenceModules.{u, u} l E W) (U : W.ProEtᵒᵖ),
        HEq (fun x ↦ ((d.hom.app N).val.app U) x)
          (id : N.val.obj (op (n, U.unop)) → N.val.obj (op (n, U.unop))) := by
  have hr : scalarReductionRestriction.{u, u} l E W n ⋙ constantRestriction l E W =
      ordinaryFiniteRestriction l E W n := by
    unfold ordinaryFiniteRestriction ordinaryPositiveRestriction PurCompactSupport.projection
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  let h := coefficientSequenceRestriction_evaluation.{u, u} l E W n
  have h' : systemRestriction l E W ⋙
      (evaluation ℕᵒᵖ
        (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)).obj (op n) =
      coefficientSequenceEvaluation.{u, u} l E W n ⋙
        ordinaryFiniteRestriction l E W n := by
    change (coefficientSequenceRestriction.{u, u} l E W ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)) ⋙
        constantRestriction l E W = _
    rw [h, Functor.assoc, hr]
  refine moduleSheafFunctor_identity_iso _ _ h'
    (fun N U ↦ N.val.obj (op (n, U.unop))) ?_
  intro N U
  dsimp only [Functor.comp_obj, ordinaryFiniteRestriction, ordinaryPositiveRestriction,
    constantRestriction, pbcRestrict, proEtaleRingRestrictScalars,
    SheafOfModules.restrictScalars, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.obj', coefficientSequenceEvaluation,
    SheafOfModules.pushforward, PresheafOfModules.pushforward,
    PresheafOfModules.pushforward₀, PresheafOfModules.pushforward₀Obj]
  rfl

/-- The unique ordinary evaluation/restriction identification.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def evaluationRestrictionOrdinary (W : Scheme.{u}) (n : ℕ) :=
  (evaluationRestriction_existsUnique l E W n).choose

attribute [local irreducible] evaluationRestrictionOrdinary

/-- Exact descent of the identity-on-sections evaluation/restriction square.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def evaluationRestriction (W : Scheme.{u}) (n : ℕ) :
    systemU l E W ⋙ ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W n ≅
      coefficientSequenceDerivedEvaluation.{u, u} l E W n ⋙ finiteRestriction l E W n :=
  haveI := systemRestriction_additive l E W
  haveI := systemRestriction_limits l E W
  haveI := systemRestriction_colimits l E W
  haveI := finiteRestriction_additive l E W n
  haveI := finiteRestriction_limits l E W n
  haveI := finiteRestriction_colimits l E W n
  haveI := coefficientSequenceEvaluation_additiveInstance l E W n
  haveI := coefficientSequenceEvaluation_limits l E W n
  haveI := coefficientSequenceEvaluation_colimits l E W n
  Functor.mapDerivedCategorySquareIso (evaluationRestrictionOrdinary l E W n)

/-- Canonical evaluation of the native support tower restricted to constants. It
uses the recorded singleton-adjunction comparison, then its normalized finite
proper/open and coefficient reduction identifications.
Source: Stacks 0D6E, 0E8I, 0940
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def supportEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (n : ℕ) :
    support l E c S ⋙ ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n ≅
      pbcDerivedExtend (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X) ⋙
        PurCompactSupport.image (PurCompactSupport.finite l E (n + 1)
          (Nat.le_add_left 1 n)) c ⋙ finiteRestriction l E Y n :=
  Functor.isoWhiskerLeft
      (S.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
          ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.g)
      (evaluationRestriction l E Y n) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n)) _ ≪≫
    Functor.isoWhiskerRight (S.reductionEvaluation n)
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        finiteRestriction l E Y n) ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E X n).symm
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        finiteRestriction l E Y n) ≪≫
    Functor.isoWhiskerLeft
      (pbcDerivedExtend (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X))
      (Functor.isoWhiskerRight (PurCompactSupport.finiteImageIso l E n c).symm _)

/-- Ordinary constant scalar extension is exact, also on single module sheaves.
Source: Stacks 03CY (blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: one finite A-basis of B identifies its restriction with a finite biproduct.
This detects exactness, including the zero module and empty site objects. -/
theorem baseTensor_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (pbcExtend (constantMap l E F i W)) ∧
      PreservesFiniteColimits (pbcExtend (constantMap l E F i W)) := by
  have := (tensor_exact l E F i W).1
  have := (tensor_exact l E F i W).2
  exact exact_of_tower (pbcExtend (constantMap l E F i W))

/-- The actual exact constant scalar functor on a single site.
Source: Stacks 03CY (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def baseTensor (W : Scheme.{u}) :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  (pbcExtend (constantMap l E F i W)).mapDerivedCategory

/-- Evaluation of constant tensor is localization of its ordinary identity square.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def tensorEvaluation (W : Scheme.{u}) (n : ℕ) :
    T l E F i W ⋙ ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W n ≅
      ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W n ⋙ baseTensor l E F i W :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  Functor.mapDerivedCategorySquareIso (Iso.refl _)

/-- Exact constant tensor has its canonical complex-to-derived computation map.
Source: Stacks 06YY (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def baseTensorCounit (W : Scheme.{u})
    (P : CochainComplex (Modules
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) :
    (baseTensor l E F i W).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).obj P) :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  (pbcExtend (constantMap l E F i W)).mapDerivedCategoryFactors.hom.app P

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensorUnit_hom_ext (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules W R) (N : pbcModules W S)
    (f g : (pbcExtend a).obj M ⟶ N)
    (h : ∀ (V : W.ProEtᵒᵖ) (x : M.val.obj V),
      f.val.app V (pbcTensorSection a M V 1 x) =
        g.val.app V (pbcTensorSection a M V 1 x)) : f = g := by
  apply ((pbcScalarAdjunction a).homEquiv M N).injective
  ext V x
  change f.val.app V (((pbcScalarAdjunction a).unit.app M).val.app V x) =
    g.val.app V (((pbcScalarAdjunction a).unit.app M).val.app V x)
  have hu : ((pbcScalarAdjunction a).unit.app M).val.app V x =
      pbcTensorSection a M V 1 x :=
    by
      unfold pbcScalarAdjunction
      exact (pbcScalarAdjunction_exists a).exists.choose_spec M V x
  exact (congrArg (f.val.app V) hu).trans
    ((h V x).trans (congrArg (g.val.app V) hu).symm)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensorUnit_map (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : pbcModules W R} (f : M ⟶ N) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((pbcExtend a).map f).val.app V (pbcTensorSection a M V 1 x) =
      pbcTensorSection a N V 1 (f.val.app V x) := by
  have h := congrArg (fun k ↦ k.val.app V x)
    ((pbcScalarAdjunction a).unit.naturality f)
  change ((pbcScalarAdjunction a).unit.app N).val.app V (f.val.app V x) =
    ((pbcExtend a).map f).val.app V
      (((pbcScalarAdjunction a).unit.app M).val.app V x) at h
  have hM : ((pbcScalarAdjunction a).unit.app M).val.app V x =
      pbcTensorSection a M V 1 x :=
    by
      unfold pbcScalarAdjunction
      exact (pbcScalarAdjunction_exists a).exists.choose_spec M V x
  have hN : ((pbcScalarAdjunction a).unit.app N).val.app V (f.val.app V x) =
      pbcTensorSection a N V 1 (f.val.app V x) :=
    by
      unfold pbcScalarAdjunction
      exact (pbcScalarAdjunction_exists a).exists.choose_spec N V (f.val.app V x)
  exact (congrArg (((pbcExtend a).map f).val.app V) hM).symm.trans (h.symm.trans hN)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary restriction/tensor balancing at a positive ramified quotient is
uniquely determined by b tensor x mapping to the quotient of b tensor x.
Source: Stacks 03EK, 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: use B tensor_A An=Bn and the finite quotient identification from tB=v^eB.
The formula and its inverse respect balanced relations and sheafification. Local
pure tensors generate, so these comparisons are natural and unique. -/
theorem finiteOrdinaryBalancing_existsUnique (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    ∃! β : ordinaryFiniteRestriction l E W n ⋙ pbcExtend (constantMap l E F i W) ≅
        pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map W) ⋙
            ordinaryPositiveRestriction l F W (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n)),
      ∀ (M : pbcModules W ((PurCompactSupport.finite l E (n + 1)
          (Nat.le_add_left 1 n)).ring W)) (U : W.ProEtᵒᵖ)
        (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.app M).val.app U
            (pbcTensorSection (constantMap l E F i W)
              ((ordinaryFiniteRestriction l E W n).obj M) U b x) =
          pbcTensorSection
            ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
              (Nat.le_add_left 1 n)).map W) M U
            (((PurCompactSupport.projection l F (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W).hom.app U)
              (((integralConstantToCompletionOfUniverses l F W).hom.app U) b)) x := by
  classical
  let b := fun M ↦
    (finiteQuotientModuleBalancing_exists l E F i W e he hepos n M).choose
  have hb (M : pbcModules W ((PurCompactSupport.finite l E (n + 1)
      (Nat.le_add_left 1 n)).ring W)) (V : W.ProEtᵒᵖ)
      (c : ((constants l F).ring W).obj.obj V) (x : M.val.obj V) :
      (b M).hom.val.app V
          (pbcTensorSection (constantMap l E F i W)
            ((ordinaryFiniteRestriction l E W n).obj M) V c x) =
        pbcTensorSection
          ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
            (Nat.le_add_left 1 n)).map W) M V
          (((PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W).hom.app V)
            (((integralConstantToCompletionOfUniverses l F W).hom.app V) c)) x :=
    (finiteQuotientModuleBalancing_exists l E F i W e he hepos n M).choose_spec V c x
  have hb₁ (M : pbcModules W ((PurCompactSupport.finite l E (n + 1)
      (Nat.le_add_left 1 n)).ring W)) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
      (b M).hom.val.app V
          (pbcTensorSection (constantMap l E F i W)
            ((ordinaryFiniteRestriction l E W n).obj M) V 1 x) =
        pbcTensorSection
          ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
            (Nat.le_add_left 1 n)).map W) M V 1 x := by
    exact (hb M V 1 x).trans (congrArg (fun c ↦ pbcTensorSection
      ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W) M V c x) (by
        exact (congrArg
          ((PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W).hom.app V).hom
          (((integralConstantToCompletionOfUniverses l F W).hom.app V).hom.map_one)).trans
          (((PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W).hom.app V).hom.map_one)))
  let β : ordinaryFiniteRestriction l E W n ⋙ pbcExtend (constantMap l E F i W) ≅
      pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W) ⋙
          ordinaryPositiveRestriction l F W (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) :=
    NatIso.ofComponents b (by
      intro M N f
      apply tensorUnit_hom_ext W (constantMap l E F i W)
      intro V x
      change (b N).hom.val.app V
        (((pbcExtend (constantMap l E F i W)).map
          ((ordinaryFiniteRestriction l E W n).map f)).val.app V
            (pbcTensorSection (constantMap l E F i W) _ V 1 x)) =
        ((pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map W)).map f).val.app V
            ((b M).hom.val.app V _)
      have hsrc := congrArg ((b N).hom.val.app V)
        (tensorUnit_map W (constantMap l E F i W)
          ((ordinaryFiniteRestriction l E W n).map f) V x)
      have hmid := (hb₁ N V (f.val.app V x)).trans
        (tensorUnit_map W ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map W) f V x).symm
      have htar := congrArg
        (((pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map W)).map f).val.app V) (hb₁ M V x).symm
      exact hsrc.trans (hmid.trans htar))
  refine ⟨β, ?_, ?_⟩
  · intro M V c x
    exact hb M V c x
  · intro γ hγ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply tensorUnit_hom_ext W (constantMap l E F i W)
    intro V x
    exact (hγ M V 1 x).trans (hb M V 1 x).symm

/-- The ordinary finite scalar comparison fixed on every local pure tensor.
Source: Stacks 03EK (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def finiteOrdinaryBalancing (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    ordinaryFiniteRestriction l E W n ⋙ pbcExtend (constantMap l E F i W) ≅
      pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W) ⋙
          ordinaryPositiveRestriction l F W (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) :=
  (finiteOrdinaryBalancing_existsUnique l E F i W e he hepos n).choose

attribute [local irreducible] finiteOrdinaryBalancing

private theorem isoChainCancellation
    {C : Type*} [Category C] {a b c d e f : C}
    (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (s : e ≅ d) (t : f ≅ e) :
    p ≫ q ≫ r ≫ s.inv ≫ t.inv ≫ t.hom ≫ s.hom = p ≫ q ≫ r := by
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem localizedBalancing
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (H : A ⥤ B) (T : B ⥤ C) (E : A ⥤ D) (U : D ⥤ C)
    [H.Additive] [T.Additive] [E.Additive] [U.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : DerivedCategory A ⥤ DerivedCategory D)
    (c : DerivedCategory.Q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (b : H ⋙ T ≅ E ⋙ U) :
    ∃! κ : H.mapDerivedCategory ⋙ T.mapDerivedCategory ≅ F ⋙ U.mapDerivedCategory,
      ∀ P : CochainComplex A ℤ,
        κ.hom.app (DerivedCategory.Q.obj P) ≫
            U.mapDerivedCategory.map (c.hom.app P) ≫
            U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
          T.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
            T.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) := by
  let Q := DerivedCategory.Q (C := A)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let t : Q ⋙ (H.mapDerivedCategory ⋙ T.mapDerivedCategory) ≅
      Q ⋙ (F ⋙ U.mapDerivedCategory) :=
    Functor.isoWhiskerRight H.mapDerivedCategoryFactors T.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ)) T.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex b (.up ℤ)) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ))
        U.mapDerivedCategoryFactors.symm ≪≫
      Functor.isoWhiskerRight c.symm U.mapDerivedCategory
  let κ := Localization.liftNatIso Q W _ _
    (H.mapDerivedCategory ⋙ T.mapDerivedCategory) (F ⋙ U.mapDerivedCategory) t
  have hk (P : CochainComplex A ℤ) : κ.hom.app (Q.obj P) = t.hom.app P := by
    simp only [κ, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
  have ht (P : CochainComplex A ℤ) :
      t.hom.app P ≫ U.mapDerivedCategory.map (c.hom.app P) ≫
          U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
        T.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
          T.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) := by
    dsimp only [t, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
    simp only [Category.assoc]
    exact isoChainCancellation
      (T.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P))
      (T.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P))
      (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P))
      (U.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P))
      (U.mapDerivedCategory.mapIso (c.app P))
  refine ⟨κ, ?_, ?_⟩
  · intro P
    rw [hk]
    exact ht P
  · intro κ' hκ'
    apply Iso.ext
    apply Localization.natTrans_ext Q W
    intro P
    apply (cancel_mono (U.mapDerivedCategory.map (c.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P))).mp
    rw [hk, ht]
    exact hκ' P

private theorem restrictionComposite_conservative
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat} (a : R ⟶ S) (b : S ⟶ T) :
    (SheafOfModules.restrictScalars b ⋙
      SheafOfModules.restrictScalars a).ReflectsIsomorphisms := by
  refine ⟨fun f _ ↦ ?_⟩
  have : IsIso ((SheafOfModules.toSheaf T).map f) := by
    change IsIso ((SheafOfModules.toSheaf R).map
      ((SheafOfModules.restrictScalars b ⋙ SheafOfModules.restrictScalars a).map f))
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf T)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The finite derived balancing is uniquely fixed on all cochain counits, using
the same ordinary tensor map, without selecting independently evaluated maps.
Source: Stacks 06YY (blueprint: def-pur-strict-scalar-mate-evaluation-data).
Proof: finite freeness makes both scalar tensors exact. The canonical universal
counit identifies their derived functors with termwise tensor. Localize the ordinary
balancing and its pure-tensor formula. The universal property gives uniqueness. -/
theorem finiteBalancing_existsUnique (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    ∃! κ : finiteRestriction l E W n ⋙ baseTensor l E F i W ≅
        pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map W) ⋙
            positiveRestriction l F W (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n)),
      ∀ P : CochainComplex (pbcModules W ((PurCompactSupport.finite l E (n + 1)
          (Nat.le_add_left 1 n)).ring W)) ℤ,
        κ.hom.app (DerivedCategory.Q.obj P) ≫
            (positiveRestriction l F W (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (pbcComplexCounit ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
                (Nat.le_add_left 1 n)).map W) P) ≫
            (ordinaryPositiveRestriction l F W (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).mapDerivedCategoryFactors.hom.app
              (((pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
                (Nat.le_add_left 1 n)).map W)).mapHomologicalComplex (.up ℤ)).obj P) =
          (baseTensor l E F i W).map
              ((ordinaryFiniteRestriction l E W n).mapDerivedCategoryFactors.hom.app P) ≫
            baseTensorCounit l E F i W
              (((ordinaryFiniteRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (finiteOrdinaryBalancing l E F i W e he hepos n) (.up ℤ)).hom.app P) := by
  let a := (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
    (Nat.le_add_left 1 n)).map W
  let U := ordinaryPositiveRestriction l F W (e * (n + 1))
    (Nat.mul_pos hepos (Nat.le_add_left 1 n))
  have := (baseTensor_exact l E F i W).1
  have := (baseTensor_exact l E F i W).2
  have : U.ReflectsIsomorphisms :=
    restrictionComposite_conservative (integralConstantToCompletionOfUniverses l F W)
      ((adicLisseForget W).map (PurCompactSupport.projection l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W))
  have : PreservesFiniteLimits (pbcExtend a ⋙ U) :=
    preservesFiniteLimits_of_natIso (finiteOrdinaryBalancing l E F i W e he hepos n)
  have : PreservesFiniteColimits (pbcExtend a ⋙ U) :=
    preservesFiniteColimits_of_natIso (finiteOrdinaryBalancing l E F i W e he hepos n)
  have : PreservesFiniteLimits (pbcExtend a) :=
    preservesFiniteLimits_of_reflects_of_preserves (pbcExtend a) U
  have : PreservesFiniteColimits (pbcExtend a) :=
    preservesFiniteColimits_of_reflects_of_preserves (pbcExtend a) U
  have := pbcDerivedExtension_universal a
  let c := exactScalarCochainIso (pbcExtend a) (pbcDerivedExtend a) (pbcExtensionCounit a)
  have hc (P : CochainComplex (pbcModules W ((PurCompactSupport.finite l E (n + 1)
      (Nat.le_add_left 1 n)).ring W)) ℤ) : c.hom.app P = pbcComplexCounit a P := by
    simp only [c, exactScalarCochainIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      asIso_hom, Category.id_comp, pbcComplexCounit]
  simpa only [hc, baseTensorCounit, baseTensor, finiteRestriction, positiveRestriction] using
    localizedBalancing (ordinaryFiniteRestriction l E W n)
      (pbcExtend (constantMap l E F i W)) (pbcExtend a) U (pbcDerivedExtend a) c
      (finiteOrdinaryBalancing l E F i W e he hepos n)

/-- The canonical derived finite coefficient balancing.
Source: Stacks 06YY (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def finiteBalancing (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    finiteRestriction l E W n ⋙ baseTensor l E F i W ≅
      pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W) ⋙
          positiveRestriction l F W (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) :=
  (finiteBalancing_existsUnique l E F i W e he hepos n).choose

attribute [local irreducible] finiteBalancing

/-- Positive-exponent evaluation, retaining the exponent rather than renaming its
predecessor. Source: Stacks 0940
(blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def positiveSupportEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (m : ℕ) (hm : 1 ≤ m) :
    support l E c S ⋙ ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y (m - 1) ≅
      pbcDerivedExtend (PurCompactSupport.projection l E m hm X) ⋙
        PurCompactSupport.image (PurCompactSupport.finite l E m hm) c ⋙
          positiveRestriction l E Y m hm :=
  match m, hm with
  | 0, h => False.elim (Nat.not_succ_le_zero 0 h)
  | n + 1, _ => supportEvaluation l E c S n

/-- Evaluation of the exact arithmetic selection uses the actual retained index.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-mate-evaluation-data). -/
def subsequenceEvaluation (W : Scheme.{u}) (e n : ℕ) :
    subsequence l F W e ⋙
        ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W n ≅
      ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W (e * (n + 1) - 1) :=
  Functor.mapDerivedCategoryCompIso (ordinarySubsequence l F W e)
    ((evaluation ℕᵒᵖ
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)).obj (op n))

end WeilConjectures.PurStrictScalar
