/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutAction

/-!

# Automorphisms of models that do not change a morphism of models act trivially

If `σ : M' ⟶ M'` is a morphism of models over the identities and `ρ : M' ⟶ M` is a morphism of
models over `f, f'` with `σ ≫ ρ = ρ` on total spaces and geometric generic fibres, then `σ` acts
trivially on `Ψ_{M'} (Lf^* C)` whenever the pullback exchange `α_ρ(C)` is invertible
(`NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`).

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId`:
  the left unit law for the transported composition isomorphisms.
- `NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`: the triviality of the action.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Left unit law** for the composition isomorphisms transported along `𝟙 X ≫ q = pq`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId {X Y : Scheme.{u}}
    {q pq : X ⟶ Y} (h : 𝟙 X ≫ q = pq)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompOfEq Λ h).hom.app K ≫
        (leftDerivedUpperStarId Λ X).hom.app (L((q)^*⟦Λ⟧).obj K) =
      eqToHom (by rw [← h, Category.id_comp, Functor.id_obj]) := by
  subst h
  exact leftDerivedUpperStarComp_id_left_app Λ q K

/-- The diagram chase behind `NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`, in an abstract
category: if `c` is a left inverse of the isomorphism `i` with inverse `j`, `j ≫ u = a ≫ k`,
`a ≫ m₁ = c ≫ u ≫ s` and `m₁ ≫ m₂ = 𝟙`, then `a ≫ k ≫ s ≫ m₂ = a`. -/
private lemma comp_autAction_aux {D : Type*} [Category D] {P P₁ Q Q₁ R : D} {a : P ⟶ Q}
    {c j : P ⟶ P₁} {i : P₁ ⟶ P} {u : P₁ ⟶ Q₁} {k : Q ⟶ Q₁} {s : Q₁ ⟶ R} {m₁ : Q ⟶ R}
    {m₂ : R ⟶ Q} (hc : c ≫ i = 𝟙 P) (hij : i ≫ j = 𝟙 P₁) (hnat : a ≫ k = j ≫ u)
    (hρ : a ≫ m₁ = c ≫ u ≫ s) (hm : m₁ ≫ m₂ = 𝟙 Q) :
    a ≫ k ≫ s ≫ m₂ = a := by
  obtain rfl : c = j := by
    rw [← Category.comp_id c, ← hij, ← Category.assoc, hc, Category.id_comp]
  rw [reassoc_of% hnat, ← reassoc_of% hρ, hm, Category.comp_id]

namespace NearbyCyclesModel

/-- An automorphism `σ` of `M'` that does not change a morphism of models `ρ : M' ⟶ M`
(`σ ≫ ρ = ρ` on total spaces and geometric generic fibres) acts trivially on `Ψ_{M'} (Lf^* C)`
when the pullback exchange `α_ρ(C)` is invertible. -/
lemma Hom.autAction_eq_id_of_isIso {X X' Y Y' : Scheme.{u}} {M' : NearbyCyclesModel X X'}
    {M : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (σ : M'.Hom M' (𝟙 X) (𝟙 X')) (ρ : M'.Hom M f f')
    (htot : σ.total ≫ ρ.total = ρ.total) (hgen : σ.generic ≫ ρ.generic = ρ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    [IsIso ((ρ.pullbackExchange Λ).app C)] :
    σ.autAction Λ (L((f)^*⟦Λ⟧).obj C) = 𝟙 _ := by
  have hc := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp f) C
  have hc' := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp f') ((M.nearbyCycles Λ).obj C)
  rw [eqToHom_refl] at hc hc'
  refine (cancel_epi ((ρ.pullbackExchange Λ).app C)).1 ((comp_autAction_aux hc'
    ((leftDerivedUpperStarId Λ X').hom_inv_id_app _)
    ((leftDerivedUpperStarId Λ X').inv.naturality _)
    (σ.pullbackExchange_comp_app_of_eq Λ ρ ρ (Category.id_comp f) (Category.id_comp f') htot
      hgen C)
    ?_).trans (Category.comp_id _).symm)
  rw [← CategoryTheory.Functor.map_comp, hc, CategoryTheory.Functor.map_id]
  rfl

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
