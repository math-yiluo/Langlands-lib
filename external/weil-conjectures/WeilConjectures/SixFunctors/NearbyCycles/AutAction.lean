/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# Automorphisms of models acting on nearby cycles

A morphism of models `σ : M ⟶ M` over the identities of `X` and `X'` (for instance an
automorphism of the geometric generic fibre over the generic point of the trait) acts on the
nearby cycles by its pullback exchange, transported along `L(𝟙)^* ≅ 𝟭`
(`NearbyCyclesModel.Hom.autAction`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

/-- The action `Ψ_M A ⟶ Ψ_M A` of a morphism of models `σ : M ⟶ M` over the identities: the
pullback exchange `α_σ(A) : L(𝟙)^* Ψ_M A ⟶ Ψ_M (L(𝟙)^* A)`, transported along `L(𝟙)^* ≅ 𝟭`. -/
noncomputable def Hom.autAction (σ : M.Hom M (𝟙 X) (𝟙 X'))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (M.nearbyCycles Λ).obj A ⟶ (M.nearbyCycles Λ).obj A :=
  (leftDerivedUpperStarId Λ X').inv.app _ ≫ (σ.pullbackExchange Λ).app A ≫
    (M.nearbyCycles Λ).map ((leftDerivedUpperStarId Λ X).hom.app A)

/-- The action of a morphism of models over the identities is natural. -/
@[reassoc]
lemma Hom.autAction_naturality (σ : M.Hom M (𝟙 X) (𝟙 X'))
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (g : A ⟶ A') :
    σ.autAction Λ A ≫ (M.nearbyCycles Λ).map g = (M.nearbyCycles Λ).map g ≫ σ.autAction Λ A' := by
  have h₁ := (leftDerivedUpperStarId Λ X').inv.naturality ((M.nearbyCycles Λ).map g)
  have h₂ := (σ.pullbackExchange Λ).naturality g
  have h₃ := (leftDerivedUpperStarId Λ X).hom.naturality g
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ h₃
  simp only [Hom.autAction, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, ← h₃, CategoryTheory.Functor.map_comp, ← reassoc_of% h₂]
  have h₁' := reassoc_of% h₁
  exact (h₁' _).symm

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
