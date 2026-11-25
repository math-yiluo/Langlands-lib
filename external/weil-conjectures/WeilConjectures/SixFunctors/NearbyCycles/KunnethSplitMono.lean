/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# Split monomorphy of the pullback of the Künneth map

In the square of the Künneth maps and pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`)
```
Lρ'^* Π_{A,B} ≫ a = δ ≫ (u_M ⊗ u_N) ≫ Π',
```
if `u_M` is a split monomorphism and `u_N` and the Künneth map `Π'` of the pullback models are
invertible, then `Lρ'^* Π_{A,B}` is a split monomorphism
(`NearbyCyclesModel.isSplitMono_map_kunnethMap_of_isSplitMono`). In the generic-slicing step of
Gabber's Künneth formula, `u_M` is the inclusion of the invariants of a pro-`p` group.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- In a square `x ≫ y = δ ≫ (u₁ ⊗ u₂) ≫ π` with `δ`, `u₂`, `π` invertible and `u₁` a split
monomorphism, `x` is a split monomorphism. -/
lemma isSplitMono_of_comp_eq_tensorHom {C : Type*} [Category C] [MonoidalCategory C]
    {U V V' S₁ S₂ T₁ T₂ : C} {x : U ⟶ V} {y : V ⟶ V'} {δ : U ⟶ S₁ ⊗ S₂} [IsIso δ]
    {u₁ : S₁ ⟶ T₁} [IsSplitMono u₁] {u₂ : S₂ ⟶ T₂} [IsIso u₂] {π : T₁ ⊗ T₂ ⟶ V'} [IsIso π]
    (h : x ≫ y = δ ≫ (u₁ ⊗ₘ u₂) ≫ π) : IsSplitMono x :=
  IsSplitMono.mk' ⟨y ≫ inv π ≫ (retraction u₁ ⊗ₘ inv u₂) ≫ inv δ, by
    rw [reassoc_of% h, IsIso.hom_inv_id_assoc, ← Category.assoc (u₁ ⊗ₘ u₂),
      tensorHom_comp_tensorHom, IsSplitMono.id, IsIso.hom_inv_id, tensorHom_id, id_whiskerRight,
      Category.id_comp, IsIso.hom_inv_id]⟩

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

-- the Künneth maps of the two products are large terms
/-- **The pullback of the Künneth map is a split monomorphism**: for morphisms of models
`ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` compatible with the projections, if the pullback
exchange `α_{ρ_M}(A)` is a split monomorphism and `α_{ρ_N}(B)` and the Künneth map `Π'` of the
pullback models are invertible, then `Lρ'^* Π_{A,B}` is a split monomorphism. -/
theorem isSplitMono_map_kunnethMap_of_isSplitMono (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂')
    (ρM : MU.Hom M r₁ r₁') (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hM : IsSplitMono ((ρM.pullbackExchange Λ).app A))
    (hN : IsIso ((ρN.pullbackExchange Λ).app B))
    (hK : IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) :
    IsSplitMono (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) :=
  isSplitMono_of_comp_eq_tensorHom (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP
    htot₁ hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
