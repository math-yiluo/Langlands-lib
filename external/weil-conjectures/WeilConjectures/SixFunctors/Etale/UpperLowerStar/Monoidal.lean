/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!

# The pushforward `g_*` is lax symmetric monoidal, the pullback `g^*` is monoidal

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued étale sheaves is lax braided. This is the general statement
for the pushforward along a continuous functor of sites, applied to the base change functor;
when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

Being left adjoint to the lax monoidal functor `g_*`, the pullback `g^*` is oplax monoidal,
with comparison maps `g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` and `g^*𝟙 ⟶ 𝟙` adjoint to
`F ⊗ G ⟶ g_*g^*F ⊗ g_*g^*G ⟶ g_*(g^*F ⊗ g^*G)` and to the unit of `g_*`, and the
adjunction `g^* ⊣ g_*` is monoidal for these structures.

The comparison map `g^*𝟙 ⟶ 𝟙` is always an isomorphism. When tensoring in `A` moreover commutes
with filtered colimits (for example if `A` is closed), `g^*` is strong monoidal. This is the
general statement `CategoryTheory.Functor.sheafPullbackConstruction.isIso_δ_sheafPullback` for
the pullback along a functor of sites with filtered comma categories, applied to base change,
which is representably flat by `CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`.

## Main results

- `AlgebraicGeometry.Etale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.
- `AlgebraicGeometry.Etale.oplaxMonoidal_upperStar`: the pullback `g^*` is oplax monoidal.
- `AlgebraicGeometry.Etale.isMonoidal_upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*` is monoidal.
- `AlgebraicGeometry.Etale.isIso_upperStar_η`: the comparison map `g^*𝟙 ⟶ 𝟙` is an
  isomorphism.
- `AlgebraicGeometry.Etale.isIso_upperStar_δ`: if tensoring in `A` commutes with filtered
  colimits (e.g. if `A` is closed), the comparison map `g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` is an
  isomorphism.
- `AlgebraicGeometry.Etale.monoidal_upperStar`: under the same hypothesis, the pullback `g^*`
  is strong monoidal.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [(Y.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(Z.smallEtaleTopology.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pushforward `g_*` on étale sheaves is lax monoidal, being the pushforward along the
continuous base change functor. -/
noncomputable instance Etale.laxMonoidal_lowerStar : (g)_*[A].LaxMonoidal := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Y.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback g
  exact Functor.sheafPushforwardContinuousLaxMonoidal
    (MorphismProperty.Over.pullback @Etale ⊤ g) A Y.smallEtaleTopology Z.smallEtaleTopology

/-- The pushforward `g_*` on étale sheaves is lax braided. When `A` is symmetric, this says
that `g_*` is lax symmetric monoidal. -/
noncomputable instance Etale.laxBraided_lowerStar : (g)_*[A].LaxBraided := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Y.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback g
  exact Functor.sheafPushforwardContinuousLaxBraided
    (MorphismProperty.Over.pullback @Etale ⊤ g) A Y.smallEtaleTopology Z.smallEtaleTopology

/-- The pullback `g^*` on étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal pushforward `g_*`.

When `A` is braided and closed, the monoidal structure used here is the global instance
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`, by
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall_eq`. -/
noncomputable instance Etale.oplaxMonoidal_upperStar : (g)^*[A].OplaxMonoidal :=
  (Etale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

/-- The adjunction `g^* ⊣ g_*` on étale sheaves is monoidal, for the oplax structure
`Etale.oplaxMonoidal_upperStar` on `g^*` and the lax structure `Etale.laxMonoidal_lowerStar`
on `g_*`. -/
instance Etale.isMonoidal_upperStarLowerStarAdjunction :
    (Etale.upperStarLowerStarAdjunction A g).IsMonoidal := by
  let := (Etale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal
  infer_instance

set_option hygiene false in
/-- The adjunction `g^* ⊣ g_*` on étale sheaves. -/
local notation "adj" => Etale.upperStarLowerStarAdjunction A g

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The comparison map `δ : g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` of the oplax monoidal pullback `g^*`
is the pullback of `F ⊗ G ⟶ g_*g^*F ⊗ g_*g^*G ⟶ g_*(g^*F ⊗ g^*G)` followed by the counit
`ε`, i.e. the following diagram commutes, where `η` is the unit of `g^* ⊣ g_*` and `μ` the
lax structure of `g_*`:
```
  g^*(F ⊗ G) ──g^*(η_F ⊗ η_G)──▶ g^*(g_*g^*F ⊗ g_*g^*G)
      │                                   │
    δ │                                   │ g^*(μ)
      ▼                                   ▼
  g^*F ⊗ g^*G ◀────────ε────────── g^*g_*(g^*F ⊗ g^*G)
```
-/
lemma Etale.upperStar_δ (F G : Sheaf Y.smallEtaleTopology A) :
    δ (g)^*[A] F G =
      (g)^*[A].map (((adj).unit.app F ⊗ₘ (adj).unit.app G) ≫ μ (g)_*[A] _ _) ≫
        (adj).counit.app _ := by
  simp [Adjunction.leftAdjointOplaxMonoidal_δ, Adjunction.homEquiv_counit]

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The comparison map `η : g^*𝟙 ⟶ 𝟙` of the oplax monoidal pullback `g^*` is the pullback
of the unit `ε : 𝟙 ⟶ g_*𝟙` of the lax monoidal pushforward followed by the counit of
`g^* ⊣ g_*`, i.e. the following diagram commutes:
```
  g^*𝟙 ──g^*(ε)──▶ g^*g_*𝟙
     ╲                │
    η ╲               │ counit
       ▼              ▼
              𝟙
```
-/
lemma Etale.upperStar_η :
    η (g)^*[A] = (g)^*[A].map (ε (g)_*[A]) ≫ (adj).counit.app _ := by
  simp [Adjunction.leftAdjointOplaxMonoidal_η, Adjunction.homEquiv_counit]

open MonoidalCategory Functor.OplaxMonoidal

/-- The comparison map `η : g^*𝟙 ⟶ 𝟙` of the oplax monoidal pullback is an isomorphism. This is
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback` for the base change
functor, whose comma categories are connected, being filtered: base change is representably
flat by `CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`. -/
instance Etale.isIso_upperStar_η : IsIso (η (g)^*[A]) := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Y.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback g
  exact Functor.sheafPullbackConstruction.isIso_η_sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ g) A Y.smallEtaleTopology Z.smallEtaleTopology

section FilteredColimits

/- Tensoring in `A` on the left commutes with filtered colimits of the size of the comma
categories `CostructuredArrow` of base change, e.g. if `A` is closed. Via the braiding, so does
tensoring on the right. -/
variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the comparison
map `δ : g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` of the oplax monoidal pullback is an isomorphism. This is
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_δ_sheafPullback` for the base change
functor, whose comma categories are filtered since base change is representably flat
(`CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`). -/
instance Etale.isIso_upperStar_δ (F G : Sheaf Y.smallEtaleTopology A) :
    IsIso (δ (g)^*[A] F G) := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Y.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback g
  exact Functor.sheafPullbackConstruction.isIso_δ_sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ g) A Y.smallEtaleTopology Z.smallEtaleTopology F G

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the pullback
`g^*` on étale sheaves is strong monoidal, its oplax structure being
`Etale.oplaxMonoidal_upperStar` by definition. -/
noncomputable instance Etale.monoidal_upperStar : (g)^*[A].Monoidal :=
  .ofOplaxMonoidal _

example : (Etale.monoidal_upperStar A g).toOplaxMonoidal = Etale.oplaxMonoidal_upperStar A g :=
  rfl

end FilteredColimits

/-- For closed `A`, the pullback `g^*` on étale sheaves is strong monoidal. -/
noncomputable example [MonoidalClosed A] : (g)^*[A].Monoidal := inferInstance

end AlgebraicGeometry
