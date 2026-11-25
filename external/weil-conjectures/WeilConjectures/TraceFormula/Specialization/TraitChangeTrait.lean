/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Iso

/-!

# Change of trait for the trait itself

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` and `S' = Spec K⟦t⟧` for a separably
closed extension `K` of `k'`. The trait `S`, as a model of its geometric generic point `Spec Ω`
(`NearbyCyclesModel.traitGenericModel`), is a model of finite type over itself. Its change of trait
`S ×_S S'` (`NearbyCyclesModel.baseChange`) has invertible pullback exchange
`Lσ^* Ψ_S B ⟶ Ψ_{S'} B` on bounded constructible `ℚ̄_ℓ`-complexes `B` on `Spec Ω`
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_traitGenericModel`). This is the
case of relative dimension `0` of the invariance of nearby cycles under change of trait
(SGA 4½, [Th. finitude], §3; `NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`).

## Proof

* A morphism of models whose specialization units are invertible has invertible pullback exchange
  at the unit, by the unit law (`NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app`), hence
  at every finite direct sum of shifts of the unit, the exchange commuting with the shifts
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_shiftDecomposition`). Over `Spec Ω` every
  bounded constructible complex is such a sum.
* The specialization units of the traits `S` and `S'` are invertible: the cohomology of the
  geometric generic point of a strictly henselian trait is that of its closed point
  (`NearbyCyclesModel.isIso_unit_traitGenericModel`).
* The trait `S'` maps to the change of trait `S ×_S S'` by isomorphisms of total spaces and of
  geometric generic fibres (`NearbyCyclesModel.traitGenericModelToBaseChange`). The composite
  `S' ⟶ S ×_S S' ⟶ S` is a morphism between the two traits, so by the composition law of
  pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_comp_app`) the exchange of the change
  of trait is invertible after pullback along the isomorphism of special fibres, hence invertible.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-! ### Exchanges between models with invertible specialization units -/

section Reflect

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived pullback along an isomorphism reflects isomorphisms. -/
lemma _root_.AlgebraicGeometry.ProEtale.CondensedRing.isIso_of_isIso_map_leftDerivedUpperStar
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ⟶ B) (h : IsIso (L((g)^*⟦Λ⟧).map a)) : IsIso a := by
  have h₁ : IsIso ((L((g)^*⟦Λ⟧) ⋙ L((inv g)^*⟦Λ⟧)).map a) :=
    inferInstanceAs (IsIso (L((inv g)^*⟦Λ⟧).map (L((g)^*⟦Λ⟧).map a)))
  have h₂ := (NatIso.isIso_map_iff (leftDerivedUpperStarCompOfEq Λ (IsIso.inv_hom_id g)) a).2 h₁
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId Λ Y) a).1 h₂

end Reflect

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The pullback exchange of a morphism between models with invertible specialization units is
invertible at the unit, by the unit law of the pullback exchange. -/
lemma Hom.isIso_pullbackExchange_app_unit (φ : M.Hom N f f') [IsIso (M.unit Λ)]
    [IsIso (N.unit Λ)] : IsIso ((φ.pullbackExchange Λ).app (𝟙_ _)) := by
  have : IsIso (L((f')^*⟦Λ⟧).map (N.unit Λ) ≫ (φ.pullbackExchange Λ).app (𝟙_ _)) := by
    rw [φ.map_unit_comp_pullbackExchange_app Λ]
    infer_instance
  exact IsIso.of_isIso_comp_left (L((f')^*⟦Λ⟧).map (N.unit Λ)) _

/-- The pullback exchange of a morphism between models with invertible specialization units is
invertible at every finite direct sum of shifts of the unit. -/
lemma Hom.isIso_pullbackExchange_app_of_shiftDecomposition (φ : M.Hom N f f')
    [IsIso (M.unit Λ)] [IsIso (N.unit Λ)]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (hC : Nonempty (ShiftDecomposition (𝟙_ _) C)) :
    IsIso ((φ.pullbackExchange Λ).app C) :=
  hC.some.isIso_app_of_commShift (φ.pullbackExchange Λ) (φ.isIso_pullbackExchange_app_unit Λ)

/-- If `φ : M ⟶ N` has invertible pullback exchange and invertible map of special fibres, and the
composite `φ ≫ ψ` has invertible pullback exchange at `C`, then so has `ψ`: by the composition law
of the pullback exchanges. -/
lemma Hom.isIso_pullbackExchange_app_of_comp {Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
    {g : Y ⟶ Z} {g' : Y' ⟶ Z'} (φ : M.Hom N f f') (ψ : N.Hom P g g') (hf' : IsIso f')
    (hφ : IsIso (φ.pullbackExchange Λ))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (h : IsIso (((φ.comp ψ).pullbackExchange Λ).app C)) :
    IsIso ((ψ.pullbackExchange Λ).app C) :=
  have := hf'
  have := hφ
  isIso_of_isIso_map_leftDerivedUpperStar Λ f' _
    (isIso_of_comp_eq_comp_comp (φ.pullbackExchange_comp_app Λ ψ C))

variable (k' : Type u) [Field k'] [IsSepClosed k']

/-- The specialization unit of the strictly henselian trait, as a model of its geometric generic
point, is invertible. -/
theorem isIso_unit_traitGenericModel : IsIso ((traitGenericModel k').unit Λ) := by
  have h : UpperStarInvertsLowerStarUnit Λ (traitGenericPoint k') (traitClosedPoint k') :=
    ⟨isIso_upperStar_traitClosedPoint_map_unit_app Λ k',
      isZero_upperStar_traitClosedPoint_obj_rightDerived Λ k'⟩
  exact (traitGenericModel k').isIso_unit_of_upperStarInvertsLowerStarUnit Λ h

end Unit

/-! ### The change of trait of the trait -/

section TraitChange

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The special fibre `Spec k'` of the trait, as a scheme over `Spec k'`. -/
noncomputable abbrev traitSpecialOver : Over (Spec (.of k')) :=
  Over.mk (𝟙 (Spec (.of k')))

/-- The trait `S = Spec k'⟦t⟧` is a model of finite type over itself, as a model of its geometric
generic point. -/
lemma isTraitModelOver_traitGenericModel :
    (traitGenericModel k').IsTraitModelOver (X' := traitSpecialOver k') (𝟙 _) (𝟙 _) := by
  have : IsIso (traitSpecialOver k').hom := inferInstanceAs (IsIso (𝟙 _))
  exact ⟨inferInstance, inferInstance, inferInstance,
    IsPullback.of_vert_isIso ⟨by simp [traitGenericModel]⟩,
    IsPullback.of_vert_isIso ⟨by simp [traitGenericModel, traitSpecialOver]⟩⟩

/-- The projection `S ×_S S' ⟶ S` of the change of trait of the trait, along
`Spec K⟦t⟧ ⟶ S`. -/
noncomputable abbrev traitBaseChangeHom :=
  baseChangeHom (isTraitModelOver_traitGenericModel k') (𝟙 _) (Category.comp_id _)
    (traitMap k' K) (Category.comp_id _)

/-- The isomorphism `S' ⟶ S ×_S S'` of total spaces. -/
noncomputable def traitToBaseChangeTotal : trait K ⟶ pullback (𝟙 (trait k')) (traitMap k' K) :=
  pullback.lift (traitMap k' K) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
lemma traitToBaseChangeTotal_snd :
    traitToBaseChangeTotal k' K ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The isomorphism `Spec Ω_K ⟶ (S ×_S S') ×_{S'} Spec Ω_K` of geometric generic fibres. -/
noncomputable def traitToBaseChangeGeneric : Spec (.of (traitGenericField K)) ⟶
    pullback (pullback.snd (𝟙 (trait k')) (traitMap k' K)) (traitGenericPoint K) :=
  pullback.lift (traitGenericPoint K ≫ traitToBaseChangeTotal k' K) (𝟙 _) (by simp)

/-- The isomorphism `Spec K ⟶ (S ×_S S') ×_{S'} Spec K` of special fibres. -/
noncomputable def traitToBaseChangeSpecial : Spec (.of K) ⟶
    pullback (pullback.snd (𝟙 (trait k')) (traitMap k' K)) (traitClosedPoint K) :=
  pullback.lift (traitClosedPoint K ≫ traitToBaseChangeTotal k' K) (𝟙 _) (by simp)

instance : IsIso (traitToBaseChangeTotal k' K) := by
  have : IsIso (traitToBaseChangeTotal k' K ≫ pullback.snd _ _) := by
    rw [traitToBaseChangeTotal_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.snd _ _)

instance : IsIso (traitToBaseChangeGeneric k' K) := by
  have : IsIso (traitToBaseChangeGeneric k' K ≫ pullback.snd _ _) := by
    rw [traitToBaseChangeGeneric, pullback.lift_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.snd _ _)

instance : IsIso (traitToBaseChangeSpecial k' K) := by
  have : IsIso (traitToBaseChangeSpecial k' K ≫ pullback.snd _ _) := by
    rw [traitToBaseChangeSpecial, pullback.lift_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.snd _ _)

/-- The isomorphism of geometric generic fibres lies over `Spec Ω_K ⟶ Spec Ω`. -/
@[reassoc]
lemma traitToBaseChangeGeneric_baseChangeGenericMap :
    traitToBaseChangeGeneric k' K ≫ baseChangeGenericMap (isTraitModelOver_traitGenericModel k')
      (𝟙 _) (Category.comp_id _) (traitMap k' K) (Category.comp_id _) =
        traitGenericPointMap k' K := by
  have h := baseChangeGenericMap_g (isTraitModelOver_traitGenericModel k') (𝟙 _)
    (Category.comp_id _) (traitMap k' K) (Category.comp_id _)
  rw [Category.comp_id] at h
  rw [h]
  exact (pullback.lift_snd_assoc _ _ _ _).trans (Category.id_comp _)

/-- The morphism of models `S' ⟶ S ×_S S'` from the trait `S'` to the change of trait of `S`, by
isomorphisms of total spaces, geometric generic fibres and special fibres. -/
noncomputable def traitGenericModelToBaseChange :
    (traitGenericModel K).Hom (baseChange (isTraitModelOver_traitGenericModel k') (𝟙 _)
        (Category.comp_id _) (traitMap k' K) (Category.comp_id _))
      (traitGenericPointMap k' K) (traitToBaseChangeSpecial k' K) where
  total := traitToBaseChangeTotal k' K
  generic := traitToBaseChangeGeneric k' K
  comm_j := by simp [traitToBaseChangeGeneric, traitGenericModel]
  comm_i := by simp [traitToBaseChangeSpecial, traitGenericModel]
  comm_ε := by
    simp only [baseChange_ε, traitToBaseChangeGeneric_baseChangeGenericMap_assoc]
    rfl

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed K]

/-- **Change of trait for the trait itself**: for the trait `S = Spec k'⟦t⟧` as a model of its
geometric generic point and the change of trait `Spec K⟦t⟧ ⟶ S`, with `k'` and `K` separably
closed, the pullback exchange `Lσ^* Ψ_S B ⟶ Ψ_{S ×_S S'} B` is invertible for bounded constructible
`B` on `Spec Ω`. This is the case of relative dimension `0` of
`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`. -/
theorem isIso_pullbackExchange_baseChangeHom_traitMap_traitGenericModel
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k'))))
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (Spec (.of (traitGenericField k')))))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of (traitGenericField k')))) B) :
    IsIso (((traitBaseChangeHom k' K).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have := isIso_unit_traitGenericModel (Profinite.padicAlgClRingObj ℓ) k'
  have := isIso_unit_traitGenericModel (Profinite.padicAlgClRingObj ℓ) K
  have hφ : IsIso ((traitGenericModelToBaseChange k' K).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)) := by
    have : IsIso (traitGenericModelToBaseChange k' K).total :=
      inferInstanceAs (IsIso (traitToBaseChangeTotal k' K))
    have : IsIso (traitGenericModelToBaseChange k' K).generic :=
      inferInstanceAs (IsIso (traitToBaseChangeGeneric k' K))
    exact (traitGenericModelToBaseChange k' K).isIso_pullbackExchange_of_isIso _
  have hχ : IsIso ((((traitGenericModelToBaseChange k' K).comp
      (traitBaseChangeHom k' K)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) :=
    Hom.isIso_pullbackExchange_app_of_shiftDecomposition _ _
      (nonempty_shiftDecomposition_of_boundedConstructible ℓ (K := traitGenericField k') B hB)
  exact (traitGenericModelToBaseChange k' K).isIso_pullbackExchange_app_of_comp _
    (traitBaseChangeHom k' K) (inferInstanceAs (IsIso (traitToBaseChangeSpecial k' K))) hφ B
    hχ

end TraitChange

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
