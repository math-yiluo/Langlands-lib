/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The specialization unit of a constant family

For a `k`-scheme `Y`, the constant family `Y × S` over the strictly henselian trait
`S = Spec k'⟦t⟧` is the deformation of the zero ideal of `Y`
(`ProEtale.CondensedRing.deformationModel Y ⊥ k'`). Blueprint
`lemma-nearby-cycles-constant-family--1` asserts that its specialization unit
`σ_Y : Λ_{Y'} ⟶ Ψ_{Y × S}(Λ)` is an isomorphism.

The projection `Y × S ⟶ S` is a morphism of models from the constant family to the trait
(`ProEtale.CondensedRing.constantFamilyModelHom`), over the structure morphism `Y ⟶ Spec k`. By the
unit law of the pullback exchange (`NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app`) and
the point case (`ProEtale.CondensedRing.isIso_traitModel_unit`), the unit `σ_Y` is an isomorphism
as soon as the pullback exchange of this morphism of models is invertible at the unit
(`ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_isIso_pullbackExchange_app`), which is
the smooth base change statement for `Y × S ⟶ S` at the unit.

## Main results

- `ProEtale.CondensedRing.isIso_traitModel_unit`: the specialization unit of the trait is an
  isomorphism, for any commutative condensed ring `Λ`.
- `ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_isIso_pullbackExchange_app`: the
  reduction of the constant family case to smooth base change at the unit.
- `ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_isIso`: the specialization unit of the
  constant family of a `k`-scheme `Y ≅ Spec k` is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The point case** of blueprint `lemma-nearby-cycles-constant-family--1`, for any commutative
condensed ring `Λ`: the specialization unit `σ_s : Λ ⟶ Ψ_s Λ` of the strictly henselian trait is an
isomorphism. -/
theorem isIso_traitModel_unit (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']
    [IsSepClosed k'] : IsIso ((traitModel k k').unit Λ) := by
  have h : UpperStarInvertsLowerStarUnit Λ (traitGenericPoint k') (traitClosedPoint k') :=
    ⟨isIso_upperStar_traitClosedPoint_map_unit_app Λ k',
      isZero_upperStar_traitClosedPoint_obj_rightDerived Λ k'⟩
  exact (traitModel k k').isIso_unit_of_upperStarInvertsLowerStarUnit Λ h

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (k' : Type u) [Field k'] [Algebra k k']

/-- The projection `Y × S ⟶ S` from the constant family of `Y` to the trait, as a morphism of
models over the structure morphism `Y ⟶ Spec k`. -/
noncomputable def constantFamilyModelHom :
    (deformationModel Y ⊥ k').Hom (traitModel k k') Y.hom
      (deformationSpecialFibre Y ⊥ k').hom where
  total := deformationTotalToTrait Y ⊥ k'
  generic := pullback.snd (deformationTotalToTrait Y ⊥ k') (traitGenericPoint k')
  comm_j := pullback.condition.symm
  comm_i := (isPullback_deformationSpecialFibre Y ⊥ k').w.symm
  comm_ε := by
    rw [← traitModel_j_traitToBase, deformationModel_ε, Category.assoc,
      deformationTotalToBase_hom]
    exact (pullback.condition_assoc _).symm

@[simp]
lemma constantFamilyModelHom_total :
    (constantFamilyModelHom Y k').total = deformationTotalToTrait Y ⊥ k' :=
  rfl

@[simp]
lemma constantFamilyModelHom_generic :
    (constantFamilyModelHom Y k').generic =
      pullback.snd (deformationTotalToTrait Y ⊥ k') (traitGenericPoint k') :=
  rfl

/-- **Reduction of the constant family case to smooth base change** (blueprint
`lemma-nearby-cycles-constant-family--1`): if the pullback exchange
`L(Y' ⟶ Spec k')^* Ψ_s(Λ) ⟶ Ψ_{Y × S}(L(Y ⟶ Spec k)^* Λ)` of the projection `Y × S ⟶ S` is an
isomorphism at the unit, then the specialization unit of the constant family `Y × S` is an
isomorphism. This follows from the unit law of the pullback exchange and the point case
`ProEtale.CondensedRing.isIso_traitModel_unit`. -/
theorem isIso_deformationModel_bot_unit_of_isIso_pullbackExchange_app [IsSepClosed k']
    [IsIso (((constantFamilyModelHom Y k').pullbackExchange Λ).app (𝟙_ _))] :
    IsIso ((deformationModel Y ⊥ k').unit Λ) := by
  have := isIso_traitModel_unit Λ k k'
  have h := (constantFamilyModelHom Y k').map_unit_comp_pullbackExchange_app Λ
  have : IsIso ((leftDerivedUpperStarUnitIso Λ (deformationSpecialFibre Y ⊥ k').hom).hom ≫
      (deformationModel Y ⊥ k').unit Λ ≫
        ((deformationModel Y ⊥ k').nearbyCycles Λ).map
          (leftDerivedUpperStarUnitIso Λ Y.hom).inv) := by
    rw [← h]
    infer_instance
  have : IsIso ((deformationModel Y ⊥ k').unit Λ ≫
      ((deformationModel Y ⊥ k').nearbyCycles Λ).map
        (leftDerivedUpperStarUnitIso Λ Y.hom).inv) :=
    IsIso.of_isIso_comp_left
      (leftDerivedUpperStarUnitIso Λ (deformationSpecialFibre Y ⊥ k').hom).hom _
  exact IsIso.of_isIso_comp_right _
    (((deformationModel Y ⊥ k').nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ Y.hom).inv)

/-- The deformation space of the zero ideal of a `k`-scheme `Y ≅ Spec k` is the affine line. -/
instance [IsIso Y.hom] : IsIso (deformationSpaceToAffineLine Y ⊥) := by
  unfold deformationSpaceToAffineLine
  infer_instance

/-- The total space of the constant family of a `k`-scheme `Y ≅ Spec k` is the trait. -/
instance [IsIso Y.hom] : IsIso (deformationTotalToTrait Y ⊥ k') :=
  inferInstanceAs (IsIso (pullback.snd _ _))

/-- **The constant family of a point** (blueprint `lemma-nearby-cycles-constant-family--1`, the case
`Y ≅ Spec k`): if the structure morphism of `Y` is an isomorphism, the specialization unit of the
constant family `Y × S` is an isomorphism. The projection `Y × S ⟶ S` is then an isomorphism of
models, so its pullback exchange is invertible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isIso`). -/
theorem isIso_deformationModel_bot_unit_of_isIso [IsSepClosed k'] [IsIso Y.hom] :
    IsIso ((deformationModel Y ⊥ k').unit Λ) := by
  have : IsIso ((constantFamilyModelHom Y k').pullbackExchange Λ) := by
    have : IsIso (constantFamilyModelHom Y k').total :=
      inferInstanceAs (IsIso (deformationTotalToTrait Y ⊥ k'))
    have : IsIso (constantFamilyModelHom Y k').generic :=
      inferInstanceAs (IsIso (pullback.snd _ _))
    exact (constantFamilyModelHom Y k').isIso_pullbackExchange_of_isIso Λ
  exact isIso_deformationModel_bot_unit_of_isIso_pullbackExchange_app Λ Y k'

end AlgebraicGeometry.ProEtale.CondensedRing
