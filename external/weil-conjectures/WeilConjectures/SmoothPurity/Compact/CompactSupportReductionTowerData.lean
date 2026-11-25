/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Coefficient data for compact-support reduction towers

These are the original coefficient definitions of `CompactSupportReductionTower`,
separated so that the geometric transition comparison can import them.
Source: Stacks 03DA, 06YY; Bhatt--Scholze 6.7.6
(blueprint: def-weil-compact-support-reduction-tower-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Positive finite coefficient levels are finite, using the recorded theorem.
Source: blueprint coefficient extension, clause 4
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
instance compactSupportLevelFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- The canonical quotient for any pair of positive coefficient levels.
Source: Stacks Tag 06YY; blueprint proof, step 2
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportLevelQuotient (m n : ℕ) (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The same quotient after constant sheafification on the small pro-etale site.
Source: Stacks Tag 06YY; blueprint proof, step 2
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportLevelSheafQuotient (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E W m ⟶ integralCoefficientCommRingSheaf l E W n :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (compactSupportLevelQuotient l E m n h).ulift)

private theorem compactSupportLevelSheafQuotient_self (W : Scheme.{u}) (n : ℕ) :
    compactSupportLevelSheafQuotient l E W n n le_rfl = 𝟙 _ := by
  unfold compactSupportLevelSheafQuotient
  have hq : compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ :=
    Ideal.Quotient.factor_eq
  rw [hq]
  exact (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_id _

private theorem compactSupportLevelSheafQuotient_step
    (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m) ≫
        compactSupportLevelSheafQuotient l E W m n h =
      compactSupportLevelSheafQuotient l E W (m + 1) n (h.trans (Nat.le_succ m)) := by
  unfold compactSupportLevelSheafQuotient
  rw [← Functor.map_comp]
  congr 1
  ext x
  change (compactSupportLevelQuotient l E m n h)
      ((compactSupportLevelQuotient l E (m + 1) m (Nat.le_succ m)) x.down) =
    (compactSupportLevelQuotient l E (m + 1) n (h.trans (Nat.le_succ m))) x.down
  exact Ideal.Quotient.factor_comp_apply _ _ x.down

/-- Limit projections commute with all coefficient quotients, including m=n.
Source: Stacks Tag 03CO; blueprint proof, steps 1--2
(blueprint: lem-weil-compact-support-reduction-tower-functor).
Proof: for adjacent levels this is the cone compatibility of the completed sheaf.
The quotient factor sends the class of a to the class of a, so successive factors
compose to the direct factor, and the equal-level factor is the identity. Apply
constant sheafification and induct on m-n to obtain compatibility for every pair. -/
theorem compactSupportProjection_comp (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    completedIntegralCommRingProjectionUnrestricted l E W m ≫
        compactSupportLevelSheafQuotient l E W m n h =
      completedIntegralCommRingProjectionUnrestricted l E W n := by
  induction m, h using Nat.le_induction with
  | base => simp only [compactSupportLevelSheafQuotient_self, Category.comp_id]
  | succ m h ih =>
    rw [← compactSupportLevelSheafQuotient_step l E W m n h, ← Category.assoc]
    have hs : completedIntegralCommRingProjectionUnrestricted l E W (m + 1) ≫
        compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m) =
        completedIntegralCommRingProjectionUnrestricted l E W m := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply (forget₂ CommRingCat RingCat).map_injective
      ext x
      have hw := congrArg (fun v ↦ (v.hom.app U).hom x)
        (limit.w (integralCoefficientSheafSystem l E W)
          (homOfLE (Nat.le_succ m)).op)
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      convert hw using 1 <;> rfl
    rw [hs]
    exact ih

/-- The canonical composition of exact restrictions along a limit projection and
its quotient, induced by the identity on underlying sections.
Source: Stacks Tag 03DA; blueprint proof, steps 4 and 6
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictionComp (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory ⋙
        scalarReductionDerivedRestriction l E W m ≅
      scalarReductionDerivedRestriction l E W n :=
  pbcDerivedRestrictComp
    (completedIntegralCommRingProjectionUnrestricted l E W m)
    (compactSupportLevelSheafQuotient l E W m n h)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W m n h)

/-- The quotient-induced derived reduction map. It is the transpose of the
reduction unit under the normalized derived tensor/restriction adjunction.
Thus this is id tensor q on K-flat representatives, rather than an arbitrary map.
Source: Stacks Tags 03CZ and 06YY; blueprint proof, steps 2 and 6
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportReductionMap (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (scalarReductionDerivedExtension l E W m).obj K ⟶
      ((proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory).obj
        ((scalarReductionDerivedExtension l E W n).obj K) :=
  (((derivedScalarExtensionRestrictionAdjunction l E W m).choose).homEquiv _ _).symm
    (((derivedScalarExtensionRestrictionAdjunction l E W n).choose).unit.app K ≫
      (compactSupportRestrictionComp l E W m n h).inv.app
        ((scalarReductionDerivedExtension l E W n).obj K))

/-- The specified finite-level composite, including its action on derived morphisms.
Source: Bhatt--Scholze, Definition 6.7.6; blueprint proof, step 4
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictedLevel {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  scalarReductionDerivedExtension l E X n ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      scalarReductionDerivedRestriction l E Y n

/-- The required transition: quotient-induced reduction, compact support at the
larger level, the specified coefficient comparison, and composition of restrictions.
Source: blueprint proof, step 6; Bhatt--Scholze, Lemma 6.7.7
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictedTransition {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (compactSupportRestrictedLevel l E c m).obj K ⟶
      (compactSupportRestrictedLevel l E c n).obj K :=
  (scalarReductionDerivedRestriction l E Y m).map
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
          (compactSupportReductionMap l E X m n h K) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)) ≫
    (compactSupportRestrictionComp l E Y m n h).hom.app
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- The canonical constant integral section of the completed coefficient sheaf.
It is obtained from the constant-to-completion map, whose projections are the actual
constant quotient sections. Source: blueprint proof, step 8
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportConstantScalar (W : Scheme.{u}) (U : W.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
  ((integralConstantToCompletion l E W).hom.app U)
    (((toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app U)
          (ULift.up a))

/-- Normalization of a linear structure by the actual constant-section action.
Source: blueprint proof, step 8
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def IsCompactSupportScalarAction (W : Scheme.{u})
    [Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E W)] : Prop :=
  ∀ (M N : scalarReductionSource l E W) (v : M ⟶ N)
    (a : Padic.coefficientExtensionIntegers l E) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
    (a • v).val.app U x = compactSupportConstantScalar l E W U a • v.val.app U x

end WeilConjectures
