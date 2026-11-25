/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutAction
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethRetract

/-!

# Retractions of the Künneth square by averaging

The retraction data of the square of the Künneth maps and pullbacks
(`CategoryTheory.IsTensorRetract` of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`)
arise from averaging over a finite family of automorphisms of the pullback models: if the
pullback exchanges `α_{ρ_M}(A)` and `α_{ρ_P}(A ⊠ B)` are split monomorphisms whose idempotents are
`1/n` times the sum of the actions of the automorphisms
(`NearbyCyclesModel.Hom.autAction`), the Künneth map of the pullback models is equivariant, and
the automorphisms act trivially on the nearby cycles of the second factor, then the square is a
tensor retract (`NearbyCyclesModel.isTensorRetract_of_average`). This is the formal part of the
projection formula for invariants (blueprint `prose-E-10`) in the
generic-slicing step of Gabber's Künneth formula.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

set_option maxHeartbeats 800000 in
-- the Künneth maps of the two products are large terms
/-- **Invariants under a finite group commute with the Künneth map** (blueprint
`prose-E-10`, in the form used in the generic-slicing step of
`proposition-external-kunneth-formula-nearby-cycles`). Let finite families of automorphisms `σM i`,
`σN i`, `σP i` of the pullback models act on nearby cycles (`NearbyCyclesModel.Hom.autAction`).
Suppose the Künneth map `Π'` of the pullback models is equivariant, the action on the second factor
is trivial, and `n` times the idempotents of split pullback exchanges `α_{ρ_M}(A)`,
`α_{ρ_P}(A ⊠ B)` are
the sums of the actions, i.e. the exchanges are the inclusions of the invariants. Then
`(E ⊗ B)^G = E^G ⊗ B`: the retractions are carried into each other by `Π'`
(`CategoryTheory.IsTensorRetract`). -/
theorem isTensorRetract_of_average (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁')
    (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
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
    {ι : Type*} (s : Finset ι) (n : ℕ)
    (hn : ∀ {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology ZU') Ab.{u + 1})
      (condensedRingObj Λ ZU'))} (f g : K ⟶ L), n • f = n • g → f = g)
    (σM : ι → MU.Hom MU (𝟙 XU) (𝟙 XU')) (σN : ι → NU.Hom NU (𝟙 YU) (𝟙 YU'))
    (σP : ι → PU.Hom PU (𝟙 ZU) (𝟙 ZU'))
    (hequiv : ∀ i, (L((e₁')^*⟦Λ⟧).map ((σM i).autAction Λ (L((r₁)^*⟦Λ⟧).obj A)) ⊗ₘ
        L((e₂')^*⟦Λ⟧).map ((σN i).autAction Λ (L((r₂)^*⟦Λ⟧).obj B))) ≫
          kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B) =
        kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B) ≫
          (σP i).autAction Λ (L((e₁)^*⟦Λ⟧).obj (L((r₁)^*⟦Λ⟧).obj A) ⊗
            L((e₂)^*⟦Λ⟧).obj (L((r₂)^*⟦Λ⟧).obj B)))
    (hN : ∀ i, (σN i).autAction Λ (L((r₂)^*⟦Λ⟧).obj B) = 𝟙 _)
    (rM : (L((r₁)^*⟦Λ⟧) ⋙ MU.nearbyCycles Λ).obj A ⟶ (M.nearbyCycles Λ ⋙ L((r₁')^*⟦Λ⟧)).obj A)
    (hrM : (ρM.pullbackExchange Λ).app A ≫ rM = 𝟙 _)
    (havgM : n • (rM ≫ (ρM.pullbackExchange Λ).app A) =
      ∑ i ∈ s, (σM i).autAction Λ (L((r₁)^*⟦Λ⟧).obj A))
    (rP : (L((r)^*⟦Λ⟧) ⋙ PU.nearbyCycles Λ).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ⟶
      (P.nearbyCycles Λ ⋙ L((r')^*⟦Λ⟧)).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B))
    (hrP : (ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫ rP = 𝟙 _)
    (havgP : n • (rP ≫ (ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)) =
      ∑ i ∈ s, (σP i).autAction Λ
        (L((r)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B))) :
    IsTensorRetract (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁
      hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B) := by
  refine isTensorRetract_of_sum' _ s n hn
    (L((e₁')^*⟦Λ⟧).map rM ≫
      (pullbackSquareComparison Λ (⟨hs₁⟩ : CommSq e₁' r' r₁' f₁')).inv.app _) rP ?_ hrP
    (fun i ↦ L((e₁')^*⟦Λ⟧).map ((σM i).autAction Λ (L((r₁)^*⟦Λ⟧).obj A)))
    (fun i ↦ (σP i).autAction Λ _) (fun i ↦ (σP i).autAction Λ _)
    (fun i ↦ Hom.autAction_naturality Λ (σP i) _) ?_ ?_ havgP
  · have e := congrArg L((e₁')^*⟦Λ⟧).map hrM
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at e
    simp only [Category.assoc, reassoc_of% e, Iso.hom_inv_id_app]
    rfl
  · intro i
    have h := hequiv i
    simp only [hN i, CategoryTheory.Functor.map_id, tensorHom_id] at h
    exact h
  · simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_nsmul, havgM, CategoryTheory.Functor.map_sum]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
