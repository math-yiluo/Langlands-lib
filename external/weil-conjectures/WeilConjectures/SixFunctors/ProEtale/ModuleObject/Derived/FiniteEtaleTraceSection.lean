/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.SectionCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance

/-!
# The trace of a split cover

Let `g : Y ⟶ X` be a morphism of schemes with a section `s : X ⟶ Y`, `s ≫ g = 𝟙 X`. On pro-étale
module objects, the restriction along `s`,
```
g_* g^* M ⟶ g_* s_* s^* g^* M ≅ (s ≫ g)_* (s ≫ g)^* M ≅ M,
```
is a retraction of the unit `M ⟶ g_* g^* M` of `g^* ⊣ g_*`
(`ProEtale.CondensedRing.sectionRetraction`,
`ProEtale.CondensedRing.unit_comp_sectionRetraction`). For a trivial cover `g : ∐_{i ∈ ι} X ⟶ X`
with its `d = #ι` sections `s i`, the sum of these retractions is the classical trace
`g_* g^* ⟶ 𝟭`, whose composite with the unit is multiplication by `d`
(`ProEtale.CondensedRing.sectionTrace`, `ProEtale.CondensedRing.unit_comp_sectionTrace`).

On derived categories, if `s ≫ g` is a universal homeomorphism (e.g. `s ≫ g = 𝟙 X`), then every
complex `G` on `X` is isomorphic to `Rg_* H` for `H = Rs_* L(s ≫ g)^* G`, so the unit of
`Lg^* ⊣ Rg_*` is a split monomorphism at `G`, for any coefficients and without finiteness
assumption on `g`
(`ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_section`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- For `s ≫ g = 𝟙 X`, the identification `(s ≫ g)^* ≅ (𝟙 X)^* ≅ 𝟭` of pullbacks. -/
noncomputable def sectionUpperStarIso (s : X ⟶ Y) (h : s ≫ g = 𝟙 X) : (s ≫ g)^*⟦Λ⟧ ≅ 𝟭 _ :=
  upperStarCongr Λ h ≪≫ upperStarId Λ X

/-- For `s ≫ g = 𝟙 X`, the identification `(s ≫ g)_* ≅ (𝟙 X)_* ≅ 𝟭` of pushforwards. -/
noncomputable def sectionLowerStarIso (s : X ⟶ Y) (h : s ≫ g = 𝟙 X) : (s ≫ g)_*⟦Λ⟧ ≅ 𝟭 _ :=
  lowerStarCongr Λ h ≪≫ lowerStarId Λ X

lemma sectionUpperStarIso_eq (s : X ⟶ Y) (h : s ≫ g = 𝟙 X) :
    sectionUpperStarIso Λ g s h = upperStarCongr Λ h ≪≫ upperStarId Λ X := rfl

omit [IsCommMonObj Λ] in
lemma sectionLowerStarIso_eq (s : X ⟶ Y) (h : s ≫ g = 𝟙 X) :
    sectionLowerStarIso Λ g s h = lowerStarCongr Λ h ≪≫ lowerStarId Λ X := rfl

/-- The unit of `(s ≫ g)^* ⊣ (s ≫ g)_*` for `s ≫ g = 𝟙 X`, followed by the identification of
the pullback with the identity, is the inverse of the identification of the pushforward. -/
lemma unit_app_sectionUpperStarIso (s : X ⟶ Y) (h : s ≫ g = 𝟙 X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarLowerStarAdjunction Λ (s ≫ g)).unit.app M ≫
        (s ≫ g)_*⟦Λ⟧.map ((sectionUpperStarIso Λ g s h).hom.app M) =
      (sectionLowerStarIso Λ g s h).inv.app M := by
  rw [sectionUpperStarIso_eq, sectionLowerStarIso_eq]
  exact upperStarLowerStarAdjunction_unit_app_upperStarId Λ h M

/-- The **restriction along a section** `s` of `g`, `s ≫ g = 𝟙 X`: the natural map
`g_* g^* M ⟶ g_* s_* s^* g^* M ≅ (s ≫ g)_* (s ≫ g)^* M ≅ M`, a retraction of the unit of
`g^* ⊣ g_*` (`ProEtale.CondensedRing.unit_comp_sectionRetraction`). -/
noncomputable def sectionRetraction (s : X ⟶ Y) (h : s ≫ g = 𝟙 X) :
    (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ 𝟭 _ where
  app M := (g)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ s).unit.app ((g)^*⟦Λ⟧.obj M)) ≫
    (lowerStarComp Λ s g).hom.app ((s)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) ≫
    (s ≫ g)_*⟦Λ⟧.map ((upperStarComp Λ s g).inv.app M) ≫
    (s ≫ g)_*⟦Λ⟧.map ((sectionUpperStarIso Λ g s h).hom.app M) ≫
    (sectionLowerStarIso Λ g s h).hom.app M
  naturality M N f := by
    have h1 := (upperStarLowerStarAdjunction Λ s).unit.naturality ((g)^*⟦Λ⟧.map f)
    have h2 := (lowerStarComp Λ s g).hom.naturality ((s)^*⟦Λ⟧.map ((g)^*⟦Λ⟧.map f))
    have h3 := (upperStarComp Λ s g).inv.naturality f
    have h4 := (sectionUpperStarIso Λ g s h).hom.naturality f
    have h5 := (sectionLowerStarIso Λ g s h).hom.naturality f
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at h1 h2 h3 h4 h5 ⊢
    rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% h2,
      ← Functor.map_comp_assoc, h3, ← (s ≫ g)_*⟦Λ⟧.map_comp_assoc, Category.assoc, h4]
    simp only [Functor.map_comp, Category.assoc, h5]

lemma sectionRetraction_app (s : X ⟶ Y) (h : s ≫ g = 𝟙 X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (sectionRetraction Λ g s h).app M =
      (g)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ s).unit.app ((g)^*⟦Λ⟧.obj M)) ≫
        (lowerStarComp Λ s g).hom.app ((s)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) ≫
        (s ≫ g)_*⟦Λ⟧.map ((upperStarComp Λ s g).inv.app M) ≫
        (s ≫ g)_*⟦Λ⟧.map ((sectionUpperStarIso Λ g s h).hom.app M) ≫
        (sectionLowerStarIso Λ g s h).hom.app M :=
  rfl

/-- The restriction along a section is a retraction of the unit of `g^* ⊣ g_*`. -/
lemma unit_comp_sectionRetraction (s : X ⟶ Y) (h : s ≫ g = 𝟙 X) :
    (upperStarLowerStarAdjunction Λ g).unit ≫ sectionRetraction Λ g s h = 𝟙 _ := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  rw [NatTrans.comp_app, sectionRetraction_app, NatTrans.id_app,
    reassoc_of% (upperStarLowerStarAdjunction_unit_app_upperStarComp Λ s g M),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% (unit_app_sectionUpperStarIso Λ g s h M),
    Iso.inv_hom_id_app]

/-- The **trace of a split cover**: for a finite family of sections `s i` of `g`, the sum of the
restrictions along them. For the trivial cover `∐_{i ∈ ι} X ⟶ X` with its canonical sections,
this is the classical trace `g_* g^* ⟶ 𝟭`. -/
noncomputable def sectionTrace {ι : Type*} [Fintype ι] (s : ι → (X ⟶ Y))
    (h : ∀ i, s i ≫ g = 𝟙 X) : (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ 𝟭 _ :=
  ∑ i, sectionRetraction Λ g (s i) (h i)

/-- The trace of a split cover along `d` sections, composed with the unit of `g^* ⊣ g_*`, is
multiplication by `d`. -/
lemma unit_comp_sectionTrace {ι : Type*} [Fintype ι] (s : ι → (X ⟶ Y))
    (h : ∀ i, s i ≫ g = 𝟙 X) :
    (upperStarLowerStarAdjunction Λ g).unit ≫ sectionTrace Λ g s h = Fintype.card ι • 𝟙 _ := by
  rw [sectionTrace, Preadditive.comp_sum]
  simp only [unit_comp_sectionRetraction, Finset.sum_const, Finset.card_univ]

/-- **Split derived units from a section**: if `g : Y ⟶ X` has a section up to a universal
homeomorphism, i.e. `s : X ⟶ Y` with `s ≫ g` a universal homeomorphism (e.g. `s ≫ g = 𝟙 X`),
then the unit of the derived adjunction `Lg^* ⊣ Rg_*` is a split monomorphism at every complex
`G`: the unit of `L(s ≫ g)^* ⊣ R(s ≫ g)_*` is an isomorphism (topological invariance), so `G` is
isomorphic to `Rg_* H` for `H = Rs_* L(s ≫ g)^* G`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_section (s : X ⟶ Y)
    [IsUniversalHomeomorphism (s ≫ g)]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ g).unit.app G) := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ (s ≫ g)
  have : L((s ≫ g)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ (s ≫ g)).symm
  have : IsIso (derivedUpperStarLowerStarAdjunction Λ (s ≫ g)).unit :=
    (derivedUpperStarLowerStarAdjunction Λ (s ≫ g)).unit_isIso_of_L_fully_faithful
  let adj := derivedUpperStarLowerStarAdjunction Λ g
  let e : G ≅ R((g)_*⟦Λ⟧).obj (R((s)_*⟦Λ⟧).obj (L((s ≫ g)^*⟦Λ⟧).obj G)) :=
    asIso ((derivedUpperStarLowerStarAdjunction Λ (s ≫ g)).unit.app G) ≪≫
      ((rightDerivedLowerStarComp Λ s g).app _).symm
  refine IsSplitMono.mk' ⟨R((g)_*⟦Λ⟧).map ((adj.homEquiv _ _).symm e.hom) ≫ e.inv, ?_⟩
  have h1 : adj.unit.app G ≫ R((g)_*⟦Λ⟧).map ((adj.homEquiv _ _).symm e.hom) = e.hom := by
    have h2 := (adj.homEquiv _ _).apply_symm_apply e.hom
    rwa [Adjunction.homEquiv_unit] at h2
  rw [reassoc_of% h1, e.hom_inv_id]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
