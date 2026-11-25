/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Pullbacks of pro-étale sheaves and underlying abelian sheaves

For a commutative ring `Λ`, taking underlying abelian sheaves of sheaves of `Λ`-modules commutes
with the pullbacks of pro-étale sheaves, being the left adjoint of a coefficient adjunction while
the direct images commute with it on the nose:

- `AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso`: `g^* ∘ forget₂ ≅ forget₂ ∘ g^*`
  for an arbitrary morphism of schemes `g`;
- `AlgebraicGeometry.ProEtale.sheafComposeForget₂CompComparisonUpperStarIso`:
  `ν^* ∘ forget₂ ≅ forget₂ ∘ ν^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

instance isLeftAdjoint_forget₂_moduleCat_ab :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  infer_instance

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **Pullback commutes with underlying abelian sheaves**: `g^* (forget₂ F) ≅ forget₂ (g^* F)`
for pro-étale sheaves of `Λ`-modules, the conjugate of the identity of direct images. -/
noncomputable def sheafComposeForget₂CompUpperStarIso :
    sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        (g)^*[AddCommGrpCat.{u + 1}] ≅
      (g)^*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction _ g).comp (sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))))
    ((sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).comp
        (upperStarLowerStarAdjunction _ g))).symm
    (Iso.refl _)

variable (X) in
/-- **The comparison pullback commutes with underlying abelian sheaves**:
`ν^* (forget₂ F) ≅ forget₂ (ν^* F)` for étale sheaves of `Λ`-modules. -/
noncomputable def sheafComposeForget₂CompComparisonUpperStarIso :
    sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        comparisonUpperStar AddCommGrpCat.{u + 1} X ≅
      comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  (conjugateIsoEquiv
    ((comparisonAdjunction _ X).comp (sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))))
    ((sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).comp (comparisonAdjunction _ X))).symm
    (Iso.refl _)

end AlgebraicGeometry.ProEtale
