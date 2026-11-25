/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# The composition isomorphism of étale pullbacks is monoidal

For `h₁ : T ⟶ S` and `h₂ : S ⟶ R`, the composition isomorphism
`(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks of étale sheaves
(`AlgebraicGeometry.Etale.upperStarComp`) is compatible with the oplax monoidal structures of
the pullbacks: it is the conjugate of the composition isomorphism of the pushforwards, which is
monoidal for their lax monoidal structures.

## Main results

- `AlgebraicGeometry.Etale.isMonoidal_lowerStarComp_hom'`: the composition isomorphism
  `h₁_* ⋙ h₂_* ≅ (h₁ ≫ h₂)_*` of pushforwards is monoidal.
- `AlgebraicGeometry.Etale.upperStarComp_hom_app_tensor_comp_δ`: the composition isomorphism
  of pullbacks commutes with the comparison maps `δ`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
  [(R.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(S.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(T.smallEtaleTopology.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The composition isomorphism `h₁_* ⋙ h₂_* ≅ (h₁ ≫ h₂)_*` of pushforwards of étale sheaves is
monoidal. -/
instance Etale.isMonoidal_lowerStarComp_hom' (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (Etale.lowerStarComp A h₁ h₂ h₁₂ hh).hom := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ h₁).IsContinuous
      S.smallEtaleTopology T.smallEtaleTopology := Etale.isContinuous_overPullback h₁
  have : (MorphismProperty.Over.pullback @Etale ⊤ h₂).IsContinuous
      R.smallEtaleTopology S.smallEtaleTopology := Etale.isContinuous_overPullback h₂
  have : (MorphismProperty.Over.pullback @Etale ⊤ h₁₂).IsContinuous
      R.smallEtaleTopology T.smallEtaleTopology := Etale.isContinuous_overPullback h₁₂
  exact Functor.isMonoidal_sheafPushforwardContinuousComp'_hom
    (A := A) (J := R.smallEtaleTopology) (K := S.smallEtaleTopology)
    (L := T.smallEtaleTopology) (MorphismProperty.Over.pullbackComp h₁ h₂ h₁₂ hh).symm

/-- The inverse of the composition isomorphism of pushforwards of étale sheaves is monoidal. -/
instance Etale.isMonoidal_lowerStarComp_inv' (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (Etale.lowerStarComp A h₁ h₂ h₁₂ hh).inv :=
  inferInstance

/-- The composition isomorphism `h₂^* ⋙ h₁^* ≅ (h₁ ≫ h₂)^*` of pullbacks commutes with the
comparison maps `δ` of the oplax monoidal pullbacks:
```
  h₁^* h₂^* (X ⊗ Y) ──────────────────▶ (h₁ ≫ h₂)^* (X ⊗ Y)
        │ h₁^* δ ≫ δ                         │ δ
        ▼                                    ▼
  h₁^* h₂^* X ⊗ h₁^* h₂^* Y ─────▶ (h₁ ≫ h₂)^* X ⊗ (h₁ ≫ h₂)^* Y
```
-/
@[reassoc]
lemma Etale.upperStarComp_inv_app_tensor_comp_δ (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (X Y : Sheaf R.smallEtaleTopology A) :
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh).inv.app (X ⊗ Y) ≫ δ (h₁₂)^*[A] X Y =
      (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ ≫
        ((Etale.upperStarComp A h₁ h₂ h₁₂ hh).inv.app X ⊗ₘ
          (Etale.upperStarComp A h₁ h₂ h₁₂ hh).inv.app Y) := by
  have := conjugateEquiv_symm_app_tensor_comp_δ (Etale.upperStarLowerStarAdjunction A h₁₂)
    ((Etale.upperStarLowerStarAdjunction A h₂).comp (Etale.upperStarLowerStarAdjunction A h₁))
    (Etale.lowerStarComp A h₁ h₂ h₁₂ hh).inv X Y
  rw [comp_δ] at this
  simp only [Category.assoc] at this
  exact this

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks commutes with the
comparison maps `δ` of the oplax monoidal pullbacks. -/
@[reassoc]
lemma Etale.upperStarComp_hom_app_tensor_comp_δ (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (X Y : Sheaf R.smallEtaleTopology A) :
    δ (h₁₂)^*[A] X Y ≫ ((Etale.upperStarComp A h₁ h₂ h₁₂ hh).hom.app X ⊗ₘ
        (Etale.upperStarComp A h₁ h₂ h₁₂ hh).hom.app Y) =
      (Etale.upperStarComp A h₁ h₂ h₁₂ hh).hom.app (X ⊗ Y) ≫
        (h₁)^*[A].map (δ (h₂)^*[A] X Y) ≫ δ (h₁)^*[A] _ _ := by
  rw [← cancel_epi ((Etale.upperStarComp A h₁ h₂ h₁₂ hh).inv.app (X ⊗ Y)),
    upperStarComp_inv_app_tensor_comp_δ_assoc, Iso.inv_hom_id_app_assoc, tensorHom_comp_tensorHom,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

end AlgebraicGeometry
