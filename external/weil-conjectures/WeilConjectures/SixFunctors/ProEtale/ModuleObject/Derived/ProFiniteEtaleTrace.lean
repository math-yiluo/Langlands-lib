/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!
# Split units of `Lq^* ⊣ Rq_*` along pro-finite étale covers: the reduction to finite levels

Let `q : Y ⟶ X` be a cofiltered limit of finite étale covers `g_i : Y_i ⟶ X`, so that `q`
factors as `q = a_i ≫ g_i` for every `i`. For `ℚ̲̄_ℓ`-coefficients and `g_i` of constant nonzero
degree, the unit `G ⟶ Rg_i_* Lg_i^* G` is a split monomorphism
(`isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_finite_of_etale`).
This file reduces the splitting of the unit of `Lq^* ⊣ Rq_*` to an extension problem for these
finite-level retractions.

* `ProEtale.CondensedRing.derivedUnitTransition a g G : Rg_* Lg^* G ⟶ Rq_* Lq^* G`, for
  `q = a ≫ g`, is `Rg_*` of the unit of `La^* ⊣ Ra_*`, followed by the composition
  isomorphisms; the unit of `q` factors through it
  (`ProEtale.CondensedRing.unit_comp_derivedUnitTransition`).
* `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp_iff`:
  the unit of `q = a ≫ g` is split at `G` if and only if some retraction of the unit of `g` at
  `G` extends along `derivedUnitTransition a g G`.
* `CategoryTheory.isSplitMono_of_isWeakColimit`: abstractly, if `M` is a *weak colimit* (for maps
  to `G`) of a nonempty diagram `F` of objects `M_i` under `G`, and the `M_i` carry retractions
  `ρ_i` forming a cocone on `F`, then `G ⟶ M` is a split monomorphism.
* `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_proFinite`:
  for a system of factorizations `q = a_i ≫ g_i`, the unit of `q` is split at `G` provided
  (continuity) `Rq_* Lq^* G` is a weak colimit of the `Rg_i_* Lg_i^* G` for maps to `G`, and
  (compatibility of the normalised traces) there are retractions of the finite-level units
  forming a cocone. For finite étale `g_i` and `ℚ̲̄_ℓ`-coefficients each finite-level unit is
  split by the normalised trace; the compatibility of these retractions along the transition
  maps is not proved here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type*} [Category C] {I : Type*} [Category I]

/-- **Splitting through a weak colimit of retracts**: let `η : G ⟶ M`, let `F : I ⥤ C` be a
nonempty diagram with maps `η_i : G ⟶ F i` and a cocone `u : F ⟶ M` such that `η_i ≫ u_i = η`.
Suppose that `M` is a weak colimit of `F` for maps to `G` (every cocone on `F` with apex `G` is
induced by some map `M ⟶ G`), and that there is a cocone `ρ` on `F` with apex `G` whose
components are retractions of the `η_i`. Then `η` is a split monomorphism. -/
theorem isSplitMono_of_isWeakColimit [Nonempty I] {G M : C} (η : G ⟶ M) {F : I ⥤ C}
    (η' : ∀ i, G ⟶ F.obj i) (u : Cocone F) (hM : u.pt = M)
    (hη : ∀ i, η' i ≫ u.ι.app i ≫ eqToHom hM = η)
    (hweak : ∀ c : Cocone F, c.pt = G → ∃ f : u.pt ⟶ c.pt, ∀ i, u.ι.app i ≫ f = c.ι.app i)
    (ρ : Cocone F) (hρ : ρ.pt = G) (hρη : ∀ i, η' i ≫ ρ.ι.app i ≫ eqToHom hρ = 𝟙 G) :
    IsSplitMono η := by
  obtain ⟨f, hf⟩ := hweak ρ hρ
  obtain ⟨i⟩ := ‹Nonempty I›
  refine IsSplitMono.mk' ⟨eqToHom hM.symm ≫ f ≫ eqToHom hρ, ?_⟩
  rw [← hη i]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% hf i, hρη i]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (a : Y ⟶ Z) (g : Z ⟶ X)
  (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)))

/-- The **transition map** `Rg_* Lg^* G ⟶ R(a ≫ g)_* L(a ≫ g)^* G`: `Rg_*` of the unit of
`La^* ⊣ Ra_*` at `Lg^* G`, followed by the composition isomorphisms
`Rg_* Ra_* ≅ R(a ≫ g)_*` and `La^* Lg^* ≅ L(a ≫ g)^*`. -/
noncomputable def derivedUnitTransition :
    R((g)_*⟦Λ⟧).obj (L((g)^*⟦Λ⟧).obj G) ⟶
      R((a ≫ g)_*⟦Λ⟧).obj (L((a ≫ g)^*⟦Λ⟧).obj G) :=
  R((g)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ a).unit.app (L((g)^*⟦Λ⟧).obj G)) ≫
    (rightDerivedLowerStarComp Λ a g).hom.app _ ≫
    R((a ≫ g)_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ a g).inv.app G)

/-- The unit of `L(a ≫ g)^* ⊣ R(a ≫ g)_*` factors as the unit of `Lg^* ⊣ Rg_*` followed by the
transition map. -/
lemma unit_comp_derivedUnitTransition :
    (derivedUpperStarLowerStarAdjunction Λ g).unit.app G ≫ derivedUnitTransition Λ a g G =
      (derivedUpperStarLowerStarAdjunction Λ (a ≫ g)).unit.app G := by
  have h := unit_conjugateEquiv ((derivedUpperStarLowerStarAdjunction Λ g).comp
    (derivedUpperStarLowerStarAdjunction Λ a)) (derivedUpperStarLowerStarAdjunction Λ (a ≫ g))
    (leftDerivedUpperStarComp Λ a g).hom G
  simp only [Adjunction.comp_unit_app] at h
  simp only [derivedUnitTransition, conjugateIsoEquiv_apply_hom, Category.assoc] at h ⊢
  rw [reassoc_of% h, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

/-- **Split units along a composite, characterised**: the unit of `L(a ≫ g)^* ⊣ R(a ≫ g)_*` is
a split monomorphism at `G` if and only if some retraction `ρ` of the unit of `Lg^* ⊣ Rg_*` at
`G` extends along the transition map `Rg_* Lg^* G ⟶ R(a ≫ g)_* L(a ≫ g)^* G`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp_iff :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ (a ≫ g)).unit.app G) ↔
      ∃ (ρ : R((g)_*⟦Λ⟧).obj (L((g)^*⟦Λ⟧).obj G) ⟶ G)
        (r : R((a ≫ g)_*⟦Λ⟧).obj (L((a ≫ g)^*⟦Λ⟧).obj G) ⟶ G),
        (derivedUpperStarLowerStarAdjunction Λ g).unit.app G ≫ ρ = 𝟙 G ∧
          derivedUnitTransition Λ a g G ≫ r = ρ := by
  constructor
  · intro h
    let η := (derivedUpperStarLowerStarAdjunction Λ (a ≫ g)).unit.app G
    refine ⟨derivedUnitTransition Λ a g G ≫ retraction η, retraction η, ?_, rfl⟩
    rw [← Category.assoc, unit_comp_derivedUnitTransition]
    exact IsSplitMono.id η
  · rintro ⟨ρ, r, hρ, hr⟩
    refine IsSplitMono.mk' ⟨r, ?_⟩
    rw [← unit_comp_derivedUnitTransition, Category.assoc, hr, hρ]
    rfl

/-- **Split units along a pro-finite étale cover, from continuity and compatible traces**.
Let `q : Y ⟶ X` factor as `q = a_i ≫ g_i` for a nonempty family of morphisms `g_i : Y_i ⟶ X`
(typically finite étale covers of constant nonzero degree `d_i`, so that with `ℚ̲̄_ℓ`-coefficients
each unit `G ⟶ Rg_i_* Lg_i^* G` is split by the normalised trace `d_i⁻¹ tr_i`). Let
`F : I ⥤ D(X)` be a diagram with
`F i = Rg_i_* Lg_i^* G` and a cocone `u` on `F` with apex `Rq_* Lq^* G` whose components are the
transition maps. Assume

* (continuity) `Rq_* Lq^* G` is a weak colimit of `F` for maps to `G`;
* (compatibility of the normalised traces) there is a cocone `ρ` on `F` with apex `G` whose
  components are retractions of the units of the `g_i`.

Then the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at `G`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_proFinite
    {I : Type*} [Category I] [Nonempty I] {Y : Scheme.{u}} (q : Y ⟶ X)
    (Yi : I → Scheme.{u}) (a : ∀ i, Y ⟶ Yi i) (gi : ∀ i, Yi i ⟶ X) (hq : ∀ i, a i ≫ gi i = q)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (F : I ⥤ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hF : ∀ i, F.obj i = R((gi i)_*⟦Λ⟧).obj
      (L((gi i)^*⟦Λ⟧).obj G))
    (u : Cocone F)
    (hu : u.pt = R((q)_*⟦Λ⟧).obj
      (L((q)^*⟦Λ⟧).obj G))
    (hui : ∀ i, u.ι.app i ≫ eqToHom hu = eqToHom (hF i) ≫
      derivedUnitTransition Λ (a i) (gi i) G ≫
        eqToHom (by rw [hq i]))
    (hweak : ∀ c : Cocone F, c.pt = G → ∃ f : u.pt ⟶ c.pt, ∀ i, u.ι.app i ≫ f = c.ι.app i)
    (ρ : Cocone F) (hρ : ρ.pt = G)
    (hρη : ∀ i, (derivedUpperStarLowerStarAdjunction Λ
      (gi i)).unit.app G ≫ eqToHom (hF i).symm ≫ ρ.ι.app i ≫ eqToHom hρ = 𝟙 G) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ
      q).unit.app G) := by
  refine isSplitMono_of_isWeakColimit _
    (fun i ↦ (derivedUpperStarLowerStarAdjunction Λ
      (gi i)).unit.app G ≫ eqToHom (hF i).symm) u hu (fun i ↦ ?_) hweak ρ hρ
    (fun i ↦ by simp only [Category.assoc]; exact hρη i)
  rw [Category.assoc, hui i, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Category.assoc, unit_comp_derivedUnitTransition]
  obtain rfl := hq i
  simp

end AlgebraicGeometry.ProEtale.CondensedRing
