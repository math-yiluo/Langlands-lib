/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnitSingle

/-!

# Nearby cycles of the trait itself

The trait `S = Spec k'⟦t⟧` is a model of the base point `Spec k` with special fibre `Spec k'`
(`ProEtale.CondensedRing.traitModel`): its geometric generic fibre `Spec Ω` maps to `Spec k`.
Its nearby cycles `Ψ_s` on bounded constructible complexes
(`ProEtale.CondensedRing.traitSpecialization`) are the target of the dualizing maps
`θ_X : Ψ_X ω_X ⟶ ω_{X'}`, which are read through the specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ`
(`ProEtale.CondensedRing.traitSpecializationUnit`).

## Implementation notes

Nothing uses these declarations yet. They are the base point of the compact-support exchange
`ν_{a_X}` of the structure map `a_X : X ⟶ Spec k`, which builds the dualizing maps `θ_X` from the
exceptional exchange `β_{a_X}` (`ProEtale.CondensedRing.dualizingExchange` takes `σ_s` as a
parameter). Reading `θ_X` through `σ_s⁻¹` needs `σ_s` to be an isomorphism
(`ProEtale.CondensedRing.isIso_traitSpecializationUnit`), the point case of blueprint
`lemma-nearby-cycles-constant-family--1`. It follows from the pro-étale computations over the
strictly henselian trait that `i^*` inverts the unit `ℚ̄_ℓ ⟶ j_* ℚ̄_ℓ` and kills `Rⁿ j_* ℚ̄_ℓ` for
`n > 0` (`WeilConjectures.TraceFormula.Specialization.TraitDirectImageUnit`,
`WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- For morphisms `j : G ⟶ T` and `i : X' ⟶ T`, the restriction `i^*` inverts the unit
`Λ ⟶ j_* j^* Λ` and kills the higher direct images `Rⁿ j_* (j^* Λ)`, `n > 0`. These are the
inputs of the computation of the specialization unit of a model with special fibre `i` and
geometric generic fibre `j`
(`ProEtale.CondensedRing.NearbyCyclesModel.isIso_unit_of_upperStarInvertsLowerStarUnit`).

It is bundled as a definition so that the kernel compares instances of it argument by argument
instead of unfolding the derived functors. -/
def UpperStarInvertsLowerStarUnit {T G X' : Scheme.{u}} (j : G ⟶ T) (i : X' ⟶ T) : Prop :=
  IsIso ((i)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ j).unit.app (𝟙_ _))) ∧
    ∀ n : ℕ, 0 < n → IsZero ((i)^*⟦Λ⟧.obj (((j)_*⟦Λ⟧.rightDerived n).obj ((j)^*⟦Λ⟧.obj (𝟙_ _))))

/-- The specialization unit `σ : Λ ⟶ i^* Rj_* j^* Λ` of a model is an isomorphism as soon as `i^*`
inverts the unit `Λ ⟶ j_* j^* Λ` and kills the higher direct images `Rⁿ j_* (j^* Λ)`, `n > 0`:
then `i^*` inverts the derived unit `Λ ⟶ Rj_* Lj^* Λ`
(`CategoryTheory.Adjunction.isIso_mapDerivedCategory_map_derivedAdjunction_unit_app`). -/
theorem NearbyCyclesModel.isIso_unit_of_upperStarInvertsLowerStarUnit {X X' : Scheme.{u}}
    (M : NearbyCyclesModel X X') (h : UpperStarInvertsLowerStarUnit Λ M.j M.i) :
    IsIso (M.unit Λ) := by
  have hη := (upperStarLowerStarAdjunction Λ M.j)
    |>.isIso_mapDerivedCategory_map_derivedAdjunction_unit_app (M.i)^*⟦Λ⟧ (𝟙_ _) h.1 h.2
  have hL : IsIso (L((M.i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ M.j).unit.app (𝟙_ _))) := by
    apply (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ M.i) _).2
    exact (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ M.j).unit D((M.i)^*⟦Λ⟧))
      (DerivedCategory.singleFunctorObjUnitIso _)).1 hη
  rw [NearbyCyclesModel.unit, Functor.map_comp]
  infer_instance

end Unit

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The trait `S = Spec k'⟦t⟧` as a model of the base point `Spec k` with special fibre
`Spec k'`: the geometric generic point `Spec Ω ⟶ S`, the closed point `Spec k' ⟶ S`, and the
structure map `Spec Ω ⟶ Spec k`. -/
noncomputable def traitModel : NearbyCyclesModel (point k).left (point k').left where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := traitClosedPoint k'
  ε := Spec.map (CommRingCat.ofHom ((algebraMap (PowerSeries k') (traitGenericField k')).comp
    (algebraMap k (PowerSeries k'))))

/-- The trait is a model of finite type over itself. -/
theorem isTraitModel_traitModel : (traitModel k k').IsTraitModel := by
  have : IsIso (point k').hom := inferInstanceAs (IsIso (𝟙 _))
  exact ⟨⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, inferInstance,
    IsPullback.of_vert_isIso ⟨by simp [traitModel]⟩,
    IsPullback.of_vert_isIso ⟨by simp [traitModel]⟩⟩⟩

/-- The generic identification of the trait model factors through the total space `S`. -/
lemma traitModel_j_traitToBase : (traitModel k k').j ≫ traitToBase k k' = (traitModel k k').ε := by
  change traitGenericPoint k' ≫ traitToBase k k' = Spec.map _
  rw [traitGenericPoint, traitToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- The nearby cycles `Ψ_s : Dᵇc(Spec k) ⥤ Dᵇc(Spec k')` of the trait. -/
noncomputable def traitSpecialization :
    Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    ((traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
      (isTraitModel_traitModel k k')
      ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩)

/-- The specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ` of the trait. -/
noncomputable def traitSpecializationUnit :
    𝟙_ _ ⟶ (traitSpecialization k k' (ℓ := ℓ)).obj (𝟙_ _) :=
  NearbyCyclesModel.boundedConstructibleUnit ℓ _

omit [Fact (ringChar k).Prime] in
/-- For the strictly henselian trait `S = Spec k'⟦t⟧`, the specialization unit
`σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ = i^* Rj_* ℚ̄_ℓ` is an isomorphism: the cohomology of the geometric
generic point of `S` is that of its closed point. This is the case `Y = Spec k'`, `L = ℚ̄_ℓ` of
blueprint `lemma-nearby-cycles-constant-family--1`. -/
theorem isIso_traitSpecializationUnit : IsIso (traitSpecializationUnit k k' (ℓ := ℓ)) := by
  have h : UpperStarInvertsLowerStarUnit (Profinite.padicAlgClRingObj ℓ) (traitGenericPoint k')
      (traitClosedPoint k') :=
    ⟨isIso_upperStar_traitClosedPoint_map_unit_app _ k',
      isZero_upperStar_traitClosedPoint_obj_rightDerived _ k'⟩
  have : IsIso ((ObjectProperty.ι _).map (traitSpecializationUnit k k' (ℓ := ℓ))) :=
    (traitModel k k').isIso_unit_of_upperStarInvertsLowerStarUnit _ h
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

end AlgebraicGeometry.ProEtale.CondensedRing
