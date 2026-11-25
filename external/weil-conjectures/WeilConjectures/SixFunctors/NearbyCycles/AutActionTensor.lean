/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethEquivariant

/-!

# The action of self-maps of models on nearby cycles is monoidal

For a morphism of models `σ : M ⟶ M` over the identities, the action
`NearbyCyclesModel.Hom.autAction` of `σ` on the nearby cycles commutes with the lax tensor maps:
`μ_M ∘ (σ_A ⊗ σ_B) = σ_{A ⊗ B} ∘ μ_M` (`NearbyCyclesModel.Hom.autAction_tensor`). This follows
from the monoidality of the pullback exchange
(`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`) and of the identity
isomorphisms `L(𝟙)^* ≅ 𝟭` (`ProEtale.CondensedRing.δ_leftDerivedUpperStarId`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- An exchange `α : Ψ ⋙ I' ⟶ I ⋙ Ψ`, monoidal in the oplax form, transported along
isomorphisms `ι : I ≅ 𝟭`, `ι' : I' ≅ 𝟭` compatible with the comultiplications, gives an
endomorphism `ι'⁻¹ ≫ α ≫ Ψ ι` of `Ψ` commuting with the lax tensor map `μ` of `Ψ`. -/
lemma tensorHom_comp_eq_of_exchange {C D : Type*} [Category C] [MonoidalCategory C] [Category D]
    [MonoidalCategory D] {I : C ⥤ C} {I' : D ⥤ D} [I.OplaxMonoidal] [I'.OplaxMonoidal]
    (ι : I ≅ 𝟭 C) (ι' : I' ≅ 𝟭 D) (Ψ : C ⥤ D) (μ : ∀ A B, Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B))
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (α : Ψ ⋙ I' ⟶ I ⋙ Ψ)
    (hα : ∀ A B, I'.map (μ A B) ≫ α.app (A ⊗ B) ≫ Ψ.map (Functor.OplaxMonoidal.δ I A B) =
      Functor.OplaxMonoidal.δ I' _ _ ≫ (α.app A ⊗ₘ α.app B) ≫ μ _ _)
    (hι : ∀ A B, Functor.OplaxMonoidal.δ I A B ≫ (ι.hom.app A ⊗ₘ ι.hom.app B) =
      ι.hom.app (A ⊗ B))
    (hι' : ∀ A B, Functor.OplaxMonoidal.δ I' A B ≫ (ι'.hom.app A ⊗ₘ ι'.hom.app B) =
      ι'.hom.app (A ⊗ B)) (A B : C) :
    ((ι'.inv.app (Ψ.obj A) ≫ α.app A ≫ Ψ.map (ι.hom.app A)) ⊗ₘ
        (ι'.inv.app (Ψ.obj B) ≫ α.app B ≫ Ψ.map (ι.hom.app B))) ≫ μ A B =
      μ A B ≫ ι'.inv.app (Ψ.obj (A ⊗ B)) ≫ α.app (A ⊗ B) ≫ Ψ.map (ι.hom.app (A ⊗ B)) := by
  have hδ : ι'.inv.app (Ψ.obj A ⊗ Ψ.obj B) ≫ Functor.OplaxMonoidal.δ I' _ _ =
      ι'.inv.app (Ψ.obj A) ⊗ₘ ι'.inv.app (Ψ.obj B) := by
    rw [← cancel_mono (ι'.hom.app (Ψ.obj A) ⊗ₘ ι'.hom.app (Ψ.obj B)), Category.assoc, hι']
    simp
  have hnat := ι'.inv.naturality (μ A B)
  dsimp only [Functor.id_obj, Functor.id_map] at hnat
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, Category.assoc, Category.assoc,
    hμ (A' := A) (B' := B) (ι.hom.app A) (ι.hom.app B), ← hι, Ψ.map_comp, reassoc_of% hnat,
    reassoc_of% (hα A B), reassoc_of% hδ]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

/-- **The action of a self-map of a model on nearby cycles is monoidal**:
`μ_M ∘ (σ_A ⊗ σ_B) = σ_{A ⊗ B} ∘ μ_M` for the lax tensor map `μ_M` of nearby cycles. -/
lemma Hom.autAction_tensor (σ : M.Hom M (𝟙 X) (𝟙 X'))
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (σ.autAction Λ A ⊗ₘ σ.autAction Λ B) ≫ M.tensorMap Λ A B =
      M.tensorMap Λ A B ≫ σ.autAction Λ (A ⊗ B) :=
  tensorHom_comp_eq_of_exchange (leftDerivedUpperStarId Λ X) (leftDerivedUpperStarId Λ X')
    (M.nearbyCycles Λ) (M.tensorMap Λ) (fun x y ↦ M.tensorMap_natural Λ x y)
    (σ.pullbackExchange Λ) (σ.map_tensorMap_comp_pullbackExchange_app Λ)
    (δ_leftDerivedUpperStarId Λ X) (δ_leftDerivedUpperStarId Λ X') A B

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
