/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
import all WeilConjectures.SixFunctors.Integral.IntegralReductionResidueHomology

/-! # Restriction of scalars to the completed coefficient ring

Restriction of scalars from a finite quotient `A_{n+1}` of the completed coefficient ring
sheaf `A` to `A` is fully faithful, since the projection `A → A_{n+1}` is locally surjective.
Restriction from `A_{k+1}` to `A` factors through restriction to any `A_{N+1}` with `k ≤ N`.

Source: Stacks Project, Tags 03CZ and 03DA (auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- Restriction of scalars from `A_{n+1}` to the completed coefficient ring is full.
Source: Stacks Project, Tag 03CZ (auxiliary; not a blueprint node). -/
instance scalarReductionRestriction_full (T : Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E T n).Full where
  map_surjective {M N} g := by
    let f := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted l E T n)
    let : Presheaf.IsLocallySurjective (ProEt.topology T) f.hom :=
      completedProjection_locallySurjective l E T n
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := ProEt.topology T) (M₁ := M.val) f.hom N.isSheaf
    refine ⟨⟨e.symm g.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply g.val

/-- Restriction of scalars from `A_{n+1}` to the completed coefficient ring is faithful.
Source: Stacks Project, Tag 03CZ (auxiliary; not a blueprint node). -/
instance scalarReductionRestriction_faithful (T : Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E T n).Faithful where
  map_injective := by
    intro M N f g h
    ext V x
    exact congrArg (fun a ↦ a.val.app V x) h

/-- The surjective transition `A_{N+1} → A_{k+1}` between finite coefficient rings, `k ≤ N`.
Source: Stacks Project, Tag 03CZ (auxiliary; not a blueprint node). -/
def coefficientExtensionRingMap {k N : ℕ} (h : k ≤ N) :
    Padic.coefficientExtensionRing l E (N + 1) →+* Padic.coefficientExtensionRing l E (k + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))

theorem coefficientExtensionRingMap_surjective {k N : ℕ} (h : k ≤ N) :
    Function.Surjective (coefficientExtensionRingMap l E h) :=
  Ideal.Quotient.factor_surjective _

/-- The constant-sheaf map induced by `coefficientExtensionRingMap`.
Source: Stacks Project, Tag 03CZ (auxiliary; not a blueprint node). -/
abbrev coefficientExtensionSheafMap (T : Scheme.{u}) {k N : ℕ} (h : k ≤ N) :
    proEtaleConstantRing T (Padic.coefficientExtensionRing l E (N + 1)) ⟶
      proEtaleConstantRing T (Padic.coefficientExtensionRing l E (k + 1)) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (coefficientExtensionRingMap l E h)))

/-- The coordinate projections of the completed coefficient ring are compatible with the
finite transitions.
Source: Stacks Project, Tag 03CO (auxiliary; not a blueprint node). -/
theorem completedIntegralCommRingProjectionUnrestricted_comp_sheafMap (T : Scheme.{u})
    {k N : ℕ} (h : k ≤ N) :
    completedIntegralCommRingProjectionUnrestricted.{u, u} l E T N ≫
        coefficientExtensionSheafMap l E T h =
      completedIntegralCommRingProjectionUnrestricted.{u, u} l E T k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero =>
    have hq : RingHom.ulift.{u + 1, u + 1} (coefficientExtensionRingMap l E h) =
        RingHom.id _ := by
      ext ⟨x⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    rw [coefficientExtensionSheafMap, hq, CommRingCat.ofHom_id]
    exact (congrArg (fun φ ↦ completedIntegralCommRingProjectionUnrestricted.{u, u} l E T k ≫ φ)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  | succ j ih =>
    have hq : RingHom.ulift.{u + 1, u + 1} (coefficientExtensionRingMap l E h) =
        (RingHom.ulift.{u + 1, u + 1} (coefficientExtensionRingMap l E (Nat.le_add_right k j))).comp
          (RingHom.ulift.{u + 1, u + 1}
            (Padic.coefficientExtensionTransition l E (k + j + 1))) := by
      ext ⟨x⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    rw [coefficientExtensionSheafMap, hq, CommRingCat.ofHom_comp, Functor.map_comp,
      ← Category.assoc]
    exact (congrArg (· ≫ _) (integralProjection_succ l E T (k + j))).trans
      (ih (Nat.le_add_right k j))

/-- Restriction from `A_{k+1}` to `A` is restriction from `A_{k+1}` to `A_{N+1}` followed by
restriction from `A_{N+1}` to `A`.
Source: Stacks Project, Tag 03DA (auxiliary; not a blueprint node). -/
def scalarReductionRestrictionTransitionIso (T : Scheme.{u}) {k N : ℕ} (h : k ≤ N) :
    proEtaleRingRestrictScalars (coefficientExtensionSheafMap l E T h) ⋙
        scalarReductionRestriction.{u, u} l E T N ≅
      scalarReductionRestriction.{u, u} l E T k :=
  pbcRestrictComp (completedIntegralCommRingProjectionUnrestricted.{u, u} l E T N)
    (coefficientExtensionSheafMap l E T h)
    (completedIntegralCommRingProjectionUnrestricted.{u, u} l E T k)
    (completedIntegralCommRingProjectionUnrestricted_comp_sheafMap l E T h)

end WeilConjectures
