/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DisjointUnion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!

# Module objects on a finite disjoint union

Let `Z` be the disjoint union of finitely many schemes `T i`, through the open immersions
`f i : T i ⟶ Z`. A module object `M` over `Λ_Z` on the pro-étale site of `Z` is the product of the
pushforwards `(f i)_* (f i)^* M` of its restrictions, the projections being the units of the
adjunctions `(f i)^* ⊣ (f i)_*`
(`AlgebraicGeometry.ProEtale.CondensedRing.isLimitFanUnitOfIsColimitCofan`). On underlying
sheaves the unit of module objects is the unit of sheaves followed by an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarLowerStarAdjunction_unit_app_hom`), so this
is the statement for sheaves (`AlgebraicGeometry.ProEtale.isLimitFanUnitOfIsColimitCofan`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The comparison `f^* M ⟶ (f^* M)` between the pullback of the underlying sheaf and the
underlying sheaf of the pullback of a module object is an isomorphism, the extension of scalars
being along the isomorphism `α_f`. -/
instance isIso_upperStarUnitHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (upperStarUnitHom Λ f M) := by
  have h := extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M)
  let x := ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M)).hom
  have : IsIso x := inferInstance
  exact ⟨⟨x, h, by rw [← cancel_mono x, Category.assoc]; erw [h, Category.comp_id]⟩⟩

/-- On underlying sheaves, the unit of `f^* ⊣ f_*` on module objects is the unit on sheaves
followed by `f_*` of the comparison `upperStarUnitHom`. -/
lemma upperStarLowerStarAdjunction_unit_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((upperStarLowerStarAdjunction Λ f).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (f)_*[Ab.{u + 1}].map (upperStarUnitHom Λ f M) := by
  have h := upperStarLowerStarAdjunction_homEquiv_hom Λ f M _ (𝟙 _)
  rw [Adjunction.homEquiv_unit] at h
  simp only [CategoryTheory.Functor.map_id, Mod.id_hom'] at h
  exact h

/-- The identity of the underlying sheaf of `f_* f^* M`, written as a morphism from the pushforward
of the underlying sheaf of `f^* M`. -/
noncomputable def lowerStarUpperStarForgetHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)_*[Ab.{u + 1}].obj ((f)^*⟦Λ⟧.obj M).X ⟶
      (Mod.forget (condensedRingObj Λ Y)).obj (((f)^*⟦Λ⟧ ⋙ (f)_*⟦Λ⟧).obj M) :=
  𝟙 _

instance {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (lowerStarUpperStarForgetHom Λ f M) :=
  inferInstanceAs (IsIso (𝟙 _))

/-- `upperStarLowerStarAdjunction_unit_app_hom`, through `lowerStarUpperStarForgetHom`. -/
lemma forget_map_upperStarLowerStarAdjunction_unit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (f)_*[Ab.{u + 1}].map (upperStarUnitHom Λ f M) ≫ lowerStarUpperStarForgetHom Λ f M =
      (Mod.forget _).map ((upperStarLowerStarAdjunction Λ f).unit.app M) :=
  (Category.comp_id _).trans (upperStarLowerStarAdjunction_unit_app_hom Λ f M).symm

/-- **Module objects on a finite disjoint union**: if `f i : T i ⟶ Z` exhibit `Z` as the disjoint
union of finitely many schemes `T i`, a module object `M` on `Z` is the product of the
`(f i)_* (f i)^* M`, with the units of `(f i)^* ⊣ (f i)_*` as projections. -/
noncomputable def isLimitFanUnitOfIsColimitCofan {ι : Type u} [Finite ι] {Z : Scheme.{u}}
    {T : ι → Scheme.{u}} {f : ∀ i, T i ⟶ Z} (hf : IsColimit (Cofan.mk Z f))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsLimit (Fan.mk M fun i ↦ (upperStarLowerStarAdjunction Λ (f i)).unit.app M) := by
  have : ReflectsLimitsOfShape (Discrete ι)
      (Mod.forget (condensedRingObj Λ Z) :
        Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤ _) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact Fan.isLimitOfIsLimitMapComp (Mod.forget _) _ _
    (ProEtale.isLimitFanUnitOfIsColimitCofan Ab.{u + 1} hf M.X)
    (fun i ↦ (f i)_*[Ab.{u + 1}].map (upperStarUnitHom Λ (f i) M) ≫
      lowerStarUpperStarForgetHom Λ (f i) M)
    fun i ↦ forget_map_upperStarLowerStarAdjunction_unit_app Λ (f i) M

/-- `isLimitFanUnitOfIsColimitCofan` for a disjoint union `Z` of copies of a single scheme `U`,
stated without the constant family of schemes. -/
noncomputable def isLimitFanUnitOfIsColimitCofanConst {ι : Type u} [Finite ι] {U Z : Scheme.{u}}
    {f : ι → (U ⟶ Z)} (hf : IsColimit (Cofan.mk Z f))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsLimit (Fan.mk M fun i ↦ (upperStarLowerStarAdjunction Λ (f i)).unit.app M) := by
  have : ReflectsLimitsOfShape (Discrete ι)
      (Mod.forget (condensedRingObj Λ Z) :
        Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤ _) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact Fan.isLimitOfIsLimitMapComp (Mod.forget _) _ _
    (ProEtale.isLimitFanUnitOfIsColimitCofan Ab.{u + 1} hf M.X)
    (fun i ↦ (f i)_*[Ab.{u + 1}].map (upperStarUnitHom Λ (f i) M) ≫
      lowerStarUpperStarForgetHom Λ (f i) M)
    fun i ↦ forget_map_upperStarLowerStarAdjunction_unit_app Λ (f i) M

end AlgebraicGeometry.ProEtale.CondensedRing
