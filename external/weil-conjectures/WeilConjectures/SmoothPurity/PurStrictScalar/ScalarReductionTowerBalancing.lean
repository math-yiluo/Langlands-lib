/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import WeilConjectures.SmoothPurity.PurStrictScalar.OrdinaryScalarBalancingLevel
import WeilConjectures.SmoothPurity.PurStrictScalar.OrdinaryScalarReductionGenerators
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarSourceCounitUniversal
import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarTargetCounitUniversal

/-! # Finite scalar proper/open mate on strict compact-support reduction towers

Source: Stacks 07A6, 0B56, 0940 and 0E8I.
(blueprint: def-pur-strict-scalar-reduction-balancing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The retained arithmetic levels n+1 go to e(n+1), with composite transitions.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
abbrev subsequence (W : Scheme.{u}) (e : ℕ) :=
  CategoryTheory.StrictTowerArithmetic.derivedRestriction
    (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) e

/-- The underlying exact arithmetic restriction on module towers.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
abbrev ordinarySubsequence (W : Scheme.{u}) (e : ℕ) :=
  CategoryTheory.StrictTowerArithmetic.restriction
    (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) e

/-- Exactness of the constant finite-free tensor, with the fixed coefficient map.
Source: Stacks 03CY (blueprint: def-pur-strict-scalar-reduction-balancing). -/
instance scalarTensor_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (tensor l E F i W) := (tensor_exact l E F i W).1

/-- Exactness of the same tensor on cokernels.
Source: Stacks 03CY (blueprint: def-pur-strict-scalar-reduction-balancing). -/
instance scalarTensor_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (tensor l E F i W) := (tensor_exact l E F i W).2

/-- The actual ordinary quotient reduction, then restriction to discrete scalars.
Source: Stacks 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def ordinaryConstantReduction (W : Scheme.{u}) :
    scalarReductionSource l E W ⥤
      Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W :=
  ordinaryReduction l E W ⋙ systemRestriction l E W

/-- Additivity of ordinary constant reduction.
Source: Stacks 03EK (blueprint: def-pur-strict-scalar-reduction-balancing). -/
instance ordinaryConstantReduction_additive (W : Scheme.{u}) :
    (ordinaryConstantReduction l E W).Additive :=
  haveI := ordinaryReduction_additive l E W
  haveI := systemRestriction_additive l E W
  inferInstanceAs ((ordinaryReduction l E W ⋙ systemRestriction l E W).Additive)

/-- The level of the actual ordinary adjunction unit. It is 1 tensor x in the
quotient module, with no basis chosen.
Source: Stacks 03EK (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def ordinaryReductionUnitSection (W : Scheme.{u}) (M : scalarReductionSource l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :=
  (((ordinaryReductionAdj l E W).unit.app M ≫
    limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
      ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x

/-- The canonical cochain reduction counit, obtained from the specified whole-system
adjunction, before finite evaluation.
Source: Stacks 06YY, 0941 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def nativeReductionCounit (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :=
  S.reduction.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (systemReductionCounit l E W S).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((ordinaryReduction l E W).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)

/-- Its exact coefficient restriction to the constant integral tower category.
Source: Stacks 06YY, 0941 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def constantReductionCounit (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (reduction l E W S).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryConstantReduction l E W).mapHomologicalComplex (.up ℤ)).obj P) :=
  (systemU l E W).map (nativeReductionCounit l E W S P) ≫
    (systemRestriction l E W).mapDerivedCategoryFactors.hom.app
      (((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)

/-- Source of ordinary ramified balancing on whole strict towers.
Source: Stacks 03EK, 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def ordinaryScalarSource (W : Scheme.{u}) :=
  ordinaryConstantReduction l E W ⋙ tensor l E F i W

/-- Target of ordinary ramified balancing, including its retained transitions.
Source: Stacks 03EK, 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def ordinaryScalarTarget (W : Scheme.{u}) (e : ℕ) :=
  pbcExtend (completedCoefficientMap l E F i W) ⋙
    ordinaryConstantReduction l F W ⋙ ordinarySubsequence l F W e

/-- Additivity of the ordinary balancing source.
Source: Stacks 03EK (blueprint: def-pur-strict-scalar-reduction-balancing). -/
instance ordinaryScalarSource_additive (W : Scheme.{u}) :
    (ordinaryScalarSource l E F i W).Additive :=
  inferInstanceAs ((ordinaryConstantReduction l E W ⋙ tensor l E F i W).Additive)

/-- Additivity of the ordinary balancing target.
Source: Stacks 03EK (blueprint: def-pur-strict-scalar-reduction-balancing). -/
instance ordinaryScalarTarget_additive (W : Scheme.{u}) (e : ℕ) :
    (ordinaryScalarTarget l E F i W e).Additive :=
  inferInstanceAs ((pbcExtend (completedCoefficientMap l E F i W) ⋙
    ordinaryConstantReduction l F W ⋙ ordinarySubsequence l F W e).Additive)

private theorem tensorSection_map (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : pbcModules W R} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (b : S.obj.obj U) (x : M.val.obj U) :
    ((pbcExtend a).map f).val.app U (pbcTensorSection a M U b x) =
      pbcTensorSection a N U b (f.val.app U x) := by
  have h := congrArg (fun k ↦ k.val.app U x)
    ((pbcScalarAdjunction a).unit.naturality f)
  change ((pbcScalarAdjunction a).unit.app N).val.app U (f.val.app U x) =
    ((pbcExtend a).map f).val.app U
      (((pbcScalarAdjunction a).unit.app M).val.app U x) at h
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec,
    (pbcScalarAdjunction_exists a).exists.choose_spec] at h
  have hs (M : pbcModules W R) (x : M.val.obj U) :
      pbcTensorSection a M U b x = b • pbcTensorSection a M U 1 x := by
    change completedAdicChangeTensor W a M U b x =
      b • completedAdicChangeTensor W a M U 1 x
    simpa only [mul_one] using completedTensor_smul W a M U b 1 x
  rw [hs, map_smul, h.symm, ← hs]

private theorem reductionUnit_map (W : Scheme.{u})
    {M N : scalarReductionSource l E W} (f : M ⟶ N)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((ordinaryConstantReduction l E W).map f).app (op n)).val.app U
      (ordinaryReductionUnitSection l E W M n U x) =
        ordinaryReductionUnitSection l E W N n U (f.val.app U x) := by
  have h := (ordinaryReductionAdj l E W).unit.naturality f
  have hlim := limMap_π
    ((coefficientSequenceRestriction.{u, u} l E W).map
      ((ordinaryReduction l E W).map f)) (op n)
  have hh :
      (ordinaryReductionAdj l E W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
          ((ordinaryReduction l E W).obj M)) (op n) ≫
          (((coefficientSequenceRestriction.{u, u} l E W).map
            ((ordinaryReduction l E W).map f)).app (op n)) =
      f ≫ (ordinaryReductionAdj l E W).unit.app N ≫
        limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
          ((ordinaryReduction l E W).obj N)) (op n) := by
    rw [← hlim, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ limit.π _ (op n)) h.symm
  exact congrArg (fun k ↦ k.val.app U x) hh

private theorem reductionUnit_transition (W : Scheme.{u})
    (M : scalarReductionSource l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((ordinaryConstantReduction l E W).obj M).map (homOfLE h).op).val.app U
      (ordinaryReductionUnitSection l E W M m U x) =
        ordinaryReductionUnitSection l E W M n U x := by
  have hh := congrArg
    (fun k ↦ (ordinaryReductionAdj l E W).unit.app M ≫ k)
    (limit.w ((coefficientSequenceRestriction.{u, u} l E W).obj
      ((ordinaryReduction l E W).obj M)) (homOfLE h).op)
  exact congrArg (fun k ↦ k.val.app U x) hh

/-- Ordinary ramified quotient balancing is fixed on local pure tensors and on
all horizontal transitions simultaneously.
Source: Stacks 03EK, 0940 (blueprint: def-pur-strict-scalar-reduction-balancing).
Proof: identify the ordinary quotient extension using its adjunction unit. The map
sends b tensor (1 tensor x) to 1 tensor (b tensor x). The equality tB=v^eB identifies
the target quotient. Tensor balancing gives its inverse. The same formula commutes
with all site restrictions, coefficient quotient maps and module morphisms. Local
pure tensors generate after sheafification, so the formula determines the iso uniquely. -/
theorem ordinaryBalancing_existsUnique (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    ∃! β : ordinaryScalarSource l E F i W ≅ ordinaryScalarTarget l E F i W e,
      ∀ (M : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (((β.hom.app M).app (op n)).val.app U)
            (pbcTensorSection (constantMap l E F i W)
              (((ordinaryConstantReduction l E W).obj M).obj (op n)) U b
              (ordinaryReductionUnitSection l E W M n U x)) =
          ordinaryReductionUnitSection l F W
            ((pbcExtend (completedCoefficientMap l E F i W)).obj M)
            (e * (n + 1) - 1) U
            (pbcTensorSection (completedCoefficientMap l E F i W) M U
              (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x) := by
  classical
  let b := fun M n ↦ (ordinaryScalarBalancingLevel_exists l E F i W e he hepos M n).choose
  have hb := fun M n ↦ (ordinaryScalarBalancingLevel_exists l E F i W e he hepos M n).choose_spec
  have hβ (M : scalarReductionSource l E W) (n : ℕ)
      (U : W.ProEtᵒᵖ) (c : ((constants l F).ring W).obj.obj U) (x : M.val.obj U) :
      ((b M n).hom.val.app U)
        (pbcTensorSection (constantMap l E F i W)
          (((ordinaryConstantReduction l E W).obj M).obj (op n)) U c
          (ordinaryReductionUnitSection l E W M n U x)) =
      ordinaryReductionUnitSection l F W
        ((pbcExtend (completedCoefficientMap l E F i W)).obj M)
        (e * (n + 1) - 1) U
        (pbcTensorSection (completedCoefficientMap l E F i W) M U
          ((integralConstantToCompletionOfUniverses l F W).hom.app U c) x) :=
    hb M n U c x
  have htrans (M : scalarReductionSource l E W) (m n : ℕ) (h : n ≤ m) :
      ((ordinaryScalarSource l E F i W).obj M).map (homOfLE h).op ≫
          (b M n).hom =
        (b M m).hom ≫ ((ordinaryScalarTarget l E F i W e).obj M).map
          (homOfLE h).op := by
    apply ordinaryScalarReduction_hom_ext l E F i W M m
    intro U c x
    change (b M n).hom.val.app U
      (((pbcExtend (constantMap l E F i W)).map
        (((ordinaryConstantReduction l E W).obj M).map (homOfLE h).op)).val.app U
          (pbcTensorSection (constantMap l E F i W) _ U c
            (ordinaryReductionUnitSection l E W M m U x))) = _
    rw [tensorSection_map, reductionUnit_transition, hβ]
    change _ = (((ordinaryConstantReduction l F W).obj
      ((pbcExtend (completedCoefficientMap l E F i W)).obj M)).map
      (homOfLE (Nat.sub_le_sub_right (Nat.mul_le_mul_left e
        (Nat.add_le_add_right h 1)) 1)).op).val.app U
        ((b M m).hom.val.app U _)
    exact ((congrArg
      (fun z ↦ (((ordinaryConstantReduction l F W).obj
        ((pbcExtend (completedCoefficientMap l E F i W)).obj M)).map
        (homOfLE (Nat.sub_le_sub_right (Nat.mul_le_mul_left e
          (Nat.add_le_add_right h 1)) 1)).op).val.app U z)
      (hβ M m U c x)).trans
        (reductionUnit_transition l F W _ _ U _)).symm
  let β (M : scalarReductionSource l E W) :
      (ordinaryScalarSource l E F i W).obj M ≅
        (ordinaryScalarTarget l E F i W e).obj M :=
    NatIso.ofComponents (fun n ↦ b M n.unop) (by
      intro m n f
      exact htrans M m.unop n.unop (leOfHom f.unop))
  have hnat {M N : scalarReductionSource l E W} (f : M ⟶ N) :
      (ordinaryScalarSource l E F i W).map f ≫ (β N).hom =
        (β M).hom ≫ (ordinaryScalarTarget l E F i W e).map f := by
    apply NatTrans.ext
    funext n
    apply ordinaryScalarReduction_hom_ext l E F i W M n.unop
    intro U c x
    change (b N n.unop).hom.val.app U
      (((pbcExtend (constantMap l E F i W)).map
        (((ordinaryConstantReduction l E W).map f).app n)).val.app U
          (pbcTensorSection (constantMap l E F i W) _ U c
            (ordinaryReductionUnitSection l E W M n.unop U x))) = _
    rw [tensorSection_map, reductionUnit_map, hβ]
    change _ = (((ordinaryConstantReduction l F W).map
      ((pbcExtend (completedCoefficientMap l E F i W)).map f)).app
        (op (e * (n.unop + 1) - 1))).val.app U
          ((b M n.unop).hom.val.app U _)
    exact ((congrArg
      (fun z ↦ (((ordinaryConstantReduction l F W).map
        ((pbcExtend (completedCoefficientMap l E F i W)).map f)).app
          (op (e * (n.unop + 1) - 1))).val.app U z)
      (hβ M n.unop U c x)).trans
        ((reductionUnit_map l F W _ _ U _).trans
          (congrArg (ordinaryReductionUnitSection l F W _ _ U)
            (tensorSection_map W (completedCoefficientMap l E F i W) f U _ x)))).symm
  let B := NatIso.ofComponents β (fun f ↦ hnat f)
  refine ⟨B, hβ, ?_⟩
  intro B' hB'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  apply ordinaryScalarReduction_hom_ext l E F i W M n.unop
  intro U c x
  exact (hB' M n.unop U c x).trans (hβ M n.unop U c x).symm

/-- The pure-tensor normalized whole-quotient balancing, with composite transitions.
Source: Stacks 03EK, 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def ordinaryBalancing (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :=
  (ordinaryBalancing_existsUnique l E F i W e he hepos).choose

/-- Canonical computation map for tensor of the E reduction on every complex.
Source: Stacks 06YY (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def sourceCounit (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (reduction l E W S ⋙ T l E F i W).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryScalarSource l E F i W).mapHomologicalComplex (.up ℤ)).obj P) :=
  (T l E F i W).map (constantReductionCounit l E W S P) ≫
    (tensor l E F i W).mapDerivedCategoryFactors.hom.app
      (((ordinaryConstantReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)

/-- Canonical computation map for ramified F reduction of completed scalar extension.
Source: Stacks 06YY (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def targetCounit (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l F W)
    (e : ℕ) (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
      reduction l F W S ⋙ subsequence l F W e).obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj
          (((ordinaryScalarTarget l E F i W e).mapHomologicalComplex (.up ℤ)).obj P) :=
  (subsequence l F W e).map
      ((reduction l F W S).map (pbcComplexCounit (completedCoefficientMap l E F i W) P)) ≫
    (subsequence l F W e).map (constantReductionCounit l F W S
      (((pbcExtend (completedCoefficientMap l E F i W)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    (ordinarySubsequence l F W e).mapDerivedCategoryFactors.hom.app
      (((ordinaryConstantReduction l F W).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend (completedCoefficientMap l E F i W)).mapHomologicalComplex (.up ℤ)).obj P))

/-- Whole-diagram derived balancing is uniquely determined by its universal counits
and the specified ordinary pure-tensor map. This condition is imposed before any
evaluation or inverse limit, so it does not use faithfulness of finite evaluation.
Source: Stacks 06YY, 0940 (blueprint: def-pur-strict-scalar-reduction-balancing).
Proof: derive the ordinary balancing square with simultaneous K-flat replacements
in the diagram category. Finite freeness of B over A makes constant tensor exact
and preserves the replacements. The recorded reduction adjunction and the canonical
right-derived unit give its universal counit. Derived-functor uniqueness yields the
iso and precisely the displayed counit equation on every complex. -/
theorem reductionBalancing_existsUnique (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F W) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    ∃! κ : reduction l E W S ⋙ T l E F i W ≅
        pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
          reduction l F W S' ⋙ subsequence l F W e,
      ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
        κ.hom.app (DerivedCategory.Q.obj P) ≫ targetCounit l E F i W S' e P =
          sourceCounit l E F i W S P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (ordinaryBalancing l E F i W e he hepos) (.up ℤ)).hom.app P) := by
  obtain ⟨α, hα, hsource⟩ := scalarSourceCounit_universal l E F i W S
  obtain ⟨β, hβ, htarget⟩ := scalarTargetCounit_universal l E F i W S' e
  let := hsource
  let := htarget
  let σ := Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (ordinaryBalancing l E F i W e he hepos) (.up ℤ))
    DerivedCategory.Q
  have hs (P : CochainComplex (scalarReductionSource l E W) ℤ) :
      α.app P = sourceCounit l E F i W S P := hα P
  have ht (P : CochainComplex (scalarReductionSource l E W) ℤ) :
      β.app P = targetCounit l E F i W S' e P := hβ P
  have hσ (P : CochainComplex (scalarReductionSource l E W) ℤ) :
      σ.hom.app P = DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ordinaryBalancing l E F i W e he hepos) (.up ℤ)).hom.app P) := rfl
  let κ := Functor.rightKanExtensionUniqueOfIso _ α σ _ β
  have hk (P : CochainComplex (scalarReductionSource l E W) ℤ) :
      κ.hom.app (DerivedCategory.Q.obj P) ≫ targetCounit l E F i W S' e P =
        sourceCounit l E F i W S P ≫ σ.hom.app P := by
    have h := Functor.liftOfIsRightKanExtension_fac_app _ β _ (α ≫ σ.hom) P
    change κ.hom.app (DerivedCategory.Q.obj P) ≫ β.app P =
      α.app P ≫ σ.hom.app P at h
    rw [hs, ht] at h
    exact h
  refine ⟨κ, fun P ↦ ?_, ?_⟩
  · rw [← hσ]
    exact hk P
  · intro κ' hκ'
    apply Iso.ext
    apply Functor.hom_ext_of_isRightKanExtension _ β
    apply NatTrans.ext
    funext P
    change κ'.hom.app (DerivedCategory.Q.obj P) ≫ β.app P =
      κ.hom.app (DerivedCategory.Q.obj P) ≫ β.app P
    rw [ht, hk, hσ]
    exact hκ' P

/-- The canonical balancing used in the actual strict-tower mate.
Source: Stacks 06YY, 0940 (blueprint: def-pur-strict-scalar-reduction-balancing). -/
def reductionBalancing (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F W) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :=
  (reductionBalancing_existsUnique l E F i W S S' e he hepos).choose

end WeilConjectures.PurStrictScalar
