/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTransAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite

/-!
# Split units of `Lg^* ⊣ Rg_*` from an underived trace

For a finite étale morphism `g : Y ⟶ X` of degree `d`, the classical trace `g_* g^* F ⟶ F`
composes with the unit `F ⟶ g_* g^* F` to multiplication by `d`; when `d` is invertible in the
coefficients the unit is thus a split monomorphism. This file shows that the *underived* trace
suffices to split the unit of the *derived* adjunction `Lg^* ⊣ Rg_*`, using the functoriality
`CategoryTheory.Functor.mapDerivedCategoryNatTrans_comp` and `_id` of derived transformations:

* `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_retract`:
  if `g` is finite of finite presentation (so that `g_*` is exact) and the identity of `Mod_{Λ_X}`
  is a retract of `g^* ⋙ g_*`, then the unit of `Lg^* ⊣ Rg_*` is a split monomorphism at every
  complex. Indeed `Rg_* Lg^* ≅ D(g_*) D(g^*) ≅ D(g^* ⋙ g_*)`, of which the identity of the
  derived category is then a retract;
* `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_trace`:
  the same conclusion from a trace `r : g^* ⋙ g_* ⟶ 𝟭` whose composite with the unit is an
  isomorphism;
* for `ℚ̲̄_ℓ`-coefficients it suffices that the composite of the trace with the unit is
  multiplication by a nonzero integer `d`: this is
  `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_nsmul`, in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTracePadicAlgCl`.

An abstract form of the Galois averaging construction of the trace is
`CategoryTheory.Adjunction.exists_comp_eq_nsmul_of_average`: if the unit is an equalizer and an
endomorphism `T` of `g_* g^* F` (the sum of the automorphisms of the cover) equalizes the two
descent maps and restricts to multiplication by `d` along the unit, then `T` factors through
the unit as a trace `r` with `η ≫ r = d • 𝟙`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Preadditive C] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R)

/-- **Galois averaging, abstractly**: let the unit `η_F : F ⟶ R L F` be an equalizer of two maps
`p₁ p₂ : R L F ⟶ Q` (the descent maps). If an endomorphism `T` of `R L F` equalizes `p₁` and `p₂`
and `η_F ≫ T = d • η_F`, then `T` factors as `r ≫ η_F` through a trace `r : R L F ⟶ F` with
`η_F ≫ r = d • 𝟙`. -/
lemma exists_comp_eq_nsmul_of_average {F : C} {Q : C} {p₁ p₂ : R.obj (L.obj F) ⟶ Q}
    {w : adj.unit.app F ≫ p₁ = adj.unit.app F ≫ p₂} (hF : IsLimit (Fork.ofι _ w))
    (T : R.obj (L.obj F) ⟶ R.obj (L.obj F)) (hT : T ≫ p₁ = T ≫ p₂) (d : ℕ)
    (hd : adj.unit.app F ≫ T = d • adj.unit.app F) :
    ∃ r : R.obj (L.obj F) ⟶ F, r ≫ adj.unit.app F = T ∧ adj.unit.app F ≫ r = d • 𝟙 F := by
  obtain ⟨r, hr⟩ := Fork.IsLimit.lift' hF T hT
  refine ⟨r, hr, ?_⟩
  have hmono : Mono (adj.unit.app F) := Fork.IsLimit.mono hF
  rw [← cancel_mono (adj.unit.app F), Category.assoc]
  erw [hr]
  simp [hd]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] [LocallyOfFinitePresentation g]

/-- **Split derived units from an underived retraction**: let `g` be finite of finite
presentation, so that `g_*` on module objects is exact. If the identity functor of `Mod_{Λ_X}` is
a retract of `g^* ⋙ g_*`, through `s : 𝟭 ⟶ g^* ⋙ g_*` and `r : g^* ⋙ g_* ⟶ 𝟭` with `s ≫ r = 𝟙`,
then the unit of the derived adjunction `Lg^* ⊣ Rg_*` is a split monomorphism at every complex:
`G` is a retract of `D(g^* ⋙ g_*) G ≅ Rg_* Lg^* G`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_retract
    (s : 𝟭 _ ⟶ (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧) (r : (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ 𝟭 _) (hsr : s ≫ r = 𝟙 _)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ g).unit.app G) := by
  have := preservesFiniteColimits_lowerStar_of_isFinite Λ g
  let e : R((g)_*⟦Λ⟧).obj (L((g)^*⟦Λ⟧).obj G) ≅ ((g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧).mapDerivedCategory.obj G :=
    (g)_*⟦Λ⟧.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (g)_*⟦Λ⟧.mapDerivedCategory.mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app G) ≪≫
      (Functor.mapDerivedCategoryCompIso (g)^*⟦Λ⟧ (g)_*⟦Λ⟧).app G
  let i := (Functor.mapDerivedCategoryIdIso _).app G
  let adj := derivedUpperStarLowerStarAdjunction Λ g
  let s' := i.inv ≫ (Functor.mapDerivedCategoryNatTrans s).app G ≫ e.inv
  let r' := e.hom ≫ (Functor.mapDerivedCategoryNatTrans r).app G ≫ i.hom
  have hsr' : s' ≫ r' = 𝟙 G := by
    simp only [s', r', Category.assoc, Iso.inv_hom_id_assoc]
    rw [← NatTrans.comp_app_assoc, ← Functor.mapDerivedCategoryNatTrans_comp, hsr,
      Functor.mapDerivedCategoryNatTrans_id, NatTrans.id_app, Category.id_comp, Iso.inv_hom_id]
    rfl
  -- `G` is a retract of `Rg_* H` for `H = Lg^* G`, so the unit at `G` is split by
  -- `Rg_*(s'♭) ≫ r'`, where `s'♭ : Lg^* G ⟶ H` is the adjoint of `s'`.
  refine IsSplitMono.mk' ⟨R((g)_*⟦Λ⟧).map ((adj.homEquiv _ _).symm s') ≫ r', ?_⟩
  have h1 : adj.unit.app G ≫ R((g)_*⟦Λ⟧).map ((adj.homEquiv _ _).symm s') = s' := by
    have h2 := (adj.homEquiv _ _).apply_symm_apply s'
    rwa [Adjunction.homEquiv_unit] at h2
  rw [reassoc_of% h1, hsr']
  rfl

/-- **Split derived units from an underived trace**: let `g` be finite of finite presentation.
If there is a trace `r : g^* ⋙ g_* ⟶ 𝟭` on module objects whose composite with the unit of
`g^* ⊣ g_*` is an isomorphism (classically: multiplication by the degree, when it is invertible),
then the unit of the derived adjunction `Lg^* ⊣ Rg_*` is a split monomorphism at every
complex. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_trace
    (r : (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ 𝟭 _) [IsIso ((upperStarLowerStarAdjunction Λ g).unit ≫ r)]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ g).unit.app G) :=
  isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_retract Λ g
    (upperStarLowerStarAdjunction Λ g).unit
    (r ≫ inv ((upperStarLowerStarAdjunction Λ g).unit ≫ r))
    (by rw [← Category.assoc, IsIso.hom_inv_id]) G

end AlgebraicGeometry.ProEtale.CondensedRing
