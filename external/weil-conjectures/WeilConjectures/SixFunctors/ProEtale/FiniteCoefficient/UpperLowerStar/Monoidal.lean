/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!

# The pushforward `g_*` is lax symmetric monoidal and the pullback `g^*` is monoidal

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`.

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued pro-étale sheaves is lax braided. This is the general
statement for the pushforward along a continuous functor of sites, applied to the base
change functor; when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

The pullback `g^*`, the left adjoint of `g_*`, is oplax monoidal and the adjunction
`g^* ⊣ g_*` is monoidal. Base change is representably flat, so if tensoring in `A` commutes
with filtered colimits, `g^*` is strong monoidal. If `g` is an isomorphism, the adjunction is
an equivalence, and then the pushforward `g_*` is strong monoidal as well.

## Main results

- `AlgebraicGeometry.ProEtale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*` is monoidal.
- `AlgebraicGeometry.ProEtale.monoidal_upperStar`: if tensoring in `A` commutes with filtered
  colimits, the pullback `g^*` is strong monoidal.
- `AlgebraicGeometry.ProEtale.isIso_lowerStar_μ` and `AlgebraicGeometry.ProEtale.isIso_lowerStar_ε`:
  the comparison maps of the pushforward along an isomorphism are invertible.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Z).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pushforward `g_*` on pro-étale sheaves is lax monoidal, being the pushforward along
the continuous base change functor. -/
noncomputable instance ProEtale.laxMonoidal_lowerStar : (g)_*[A].LaxMonoidal := by
  unfold ProEtale.lowerStar
  infer_instance

/-- The pushforward `g_*` on pro-étale sheaves is lax braided. When `A` is symmetric, this
says that `g_*` is lax symmetric monoidal. -/
noncomputable instance ProEtale.laxBraided_lowerStar : (g)_*[A].LaxBraided := by
  unfold ProEtale.lowerStar
  infer_instance

/-- The pullback `g^*` on pro-étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal pushforward `g_*`. -/
noncomputable instance ProEtale.oplaxMonoidal_upperStar : (g)^*[A].OplaxMonoidal :=
  (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

/-- The adjunction `g^* ⊣ g_*` on pro-étale sheaves is monoidal, for the oplax structure
`ProEtale.oplaxMonoidal_upperStar` on `g^*` and the lax structure `ProEtale.laxMonoidal_lowerStar`
on `g_*`. -/
instance ProEtale.isMonoidal_upperStarLowerStarAdjunction :
    (ProEtale.upperStarLowerStarAdjunction A g).IsMonoidal := by
  let := (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal
  infer_instance

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The comparison map `η : g^*𝟙 ⟶ 𝟙` of the oplax monoidal pullback is an isomorphism. This is
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback` for the base change
functor, whose comma categories are connected, being filtered: base change is representably
flat by `CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`. -/
instance ProEtale.isIso_upperStar_η : IsIso (η (g)^*[A]) := by
  unfold ProEtale.upperStar
  infer_instance

section FilteredColimits

/- Tensoring in `A` on the left commutes with filtered colimits of the size of the comma
categories `CostructuredArrow` of base change, e.g. if `A` is closed. Via the braiding, so does
tensoring on the right. -/
variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the comparison
map `δ : g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` of the oplax monoidal pullback is an isomorphism. This is
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_δ_sheafPullback` for the base change
functor, whose comma categories are filtered since base change is representably flat. -/
instance ProEtale.isIso_upperStar_δ (F G : Sheaf (Scheme.ProEt.topology Y) A) :
    IsIso (δ (g)^*[A] F G) := by
  unfold ProEtale.upperStar
  infer_instance

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the pullback
`g^*` on pro-étale sheaves is strong monoidal, its oplax structure being
`ProEtale.oplaxMonoidal_upperStar` by definition. -/
noncomputable instance ProEtale.monoidal_upperStar : (g)^*[A].Monoidal :=
  .ofOplaxMonoidal _

/-- The tensor comparison map `μ : g_*F ⊗ g_*G ⟶ g_*(F ⊗ G)` of the pushforward along an
isomorphism `g` is invertible: `g^* ⊣ g_*` is then a monoidal adjoint equivalence whose left
adjoint is strong monoidal (`CategoryTheory.Adjunction.isIso_μ_of_isIso_δ`). -/
instance ProEtale.isIso_lowerStar_μ [IsIso g] (F G : Sheaf (Scheme.ProEt.topology Z) A) :
    IsIso (μ (g)_*[A] F G) :=
  (ProEtale.upperStarLowerStarAdjunction A g).isIso_μ_of_isIso_δ F G

end FilteredColimits

/-- The unit comparison map `ε : 𝟙 ⟶ g_*𝟙` of the pushforward along an isomorphism `g` is
invertible: `g^* ⊣ g_*` is then a monoidal adjoint equivalence and `η : g^*𝟙 ⟶ 𝟙` is
invertible (`CategoryTheory.Adjunction.isIso_ε_of_isIso_η`). -/
instance ProEtale.isIso_lowerStar_ε [IsIso g] : IsIso (ε (g)_*[A]) :=
  (ProEtale.upperStarLowerStarAdjunction A g).isIso_ε_of_isIso_η

end AlgebraicGeometry
