/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismMonoidal
public import WeilConjectures.PoincareDuality.ProperProjectionComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-!

# The exceptional projection morphism of a compactification is a module structure

The derived exceptional projection morphism
`PF^!_{f,K,B} : Rf_!(c) K ⊗ᴸ B ⟶ Rf_!(c) (K ⊗ᴸ Lf^* B)` of a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` (`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification`)
is compatible with the unit and the tensor structure of `Lf^*` in its second variable. This is
`CategoryTheory.Adjunction.projection_comp_unit` and
`CategoryTheory.Adjunction.projection_comp_tensor`, the identification
`leftDerivedUpperStarCompactificationIso : Lf^* ≅ Lg^* ⋙ Li^*` being monoidal by
`leftDerivedUpperStarComp_δ` and `leftDerivedUpperStarComp_hom_app_unit`.

## Main statements

- `ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_unit`,
  `ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_tensor`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The identification `Lf^* ≅ Lg^* ⋙ Li^*` is monoidal -/

section CompactificationIso

/-- The counit of the derived pullback is the unit comparison `Lf^* Λ_Y ≅ Λ_X`. -/
lemma η_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    η L((f)^*⟦Λ⟧) = (leftDerivedUpperStarUnitIso Λ f).hom :=
  rfl

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The identification `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification is compatible with the units. -/
lemma ε_comp_map_ε_comp_leftDerivedUpperStarCompactificationIso_inv_app :
    ε L((c.i)^*⟦Λ⟧) ≫ L((c.i)^*⟦Λ⟧).map (ε L((c.g)^*⟦Λ⟧)) ≫
        (leftDerivedUpperStarCompactificationIso Λ c).inv.app (𝟙_ _) =
      ε L((f)^*⟦Λ⟧) :=
  NatIso.ε_comp_map_ε_comp_inv_app_of_eq_eqToIso_trans (F := fun h : X ⟶ Y ↦ L((h)^*⟦Λ⟧))
    (e := leftDerivedUpperStarComp Λ c.i c.g) c.comm _ _ rfl (η_leftDerivedUpperStar Λ c.g)
    (η_leftDerivedUpperStar Λ c.i) (η_leftDerivedUpperStar Λ (c.i ≫ c.g))
    (leftDerivedUpperStarComp_hom_app_unit Λ c.i c.g)

/-- The identification `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification is compatible with the
multiplications. -/
lemma μ_comp_map_μ_comp_leftDerivedUpperStarCompactificationIso_inv_app
    (B C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    μ L((c.i)^*⟦Λ⟧) ((L((c.g)^*⟦Λ⟧)).obj B) ((L((c.g)^*⟦Λ⟧)).obj C) ≫
        L((c.i)^*⟦Λ⟧).map (μ L((c.g)^*⟦Λ⟧) B C) ≫
        (leftDerivedUpperStarCompactificationIso Λ c).inv.app (B ⊗ C) =
      ((leftDerivedUpperStarCompactificationIso Λ c).inv.app B ⊗ₘ
          (leftDerivedUpperStarCompactificationIso Λ c).inv.app C) ≫ μ L((f)^*⟦Λ⟧) B C := by
  -- elaborating the instance without the expected type avoids a costly unification
  have h := NatIso.μ_comp_map_μ_comp_inv_app_of_eq_eqToIso_trans
    (F := fun h : X ⟶ Y ↦ L((h)^*⟦Λ⟧)) (e := leftDerivedUpperStarComp Λ c.i c.g) c.comm
    (congrArg (fun h : X ⟶ Y ↦ L((h)^*⟦Λ⟧)) c.comm) (leftDerivedUpperStarCompactificationIso Λ c)
    rfl B C (leftDerivedUpperStarComp_δ Λ c.i c.g B C)
  exact h

end CompactificationIso
/-! ### The module axioms on the unbounded derived categories -/

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- **Unitality of the exceptional projection morphism**:
`PF^!_{f,K,Λ} = Rf_! K ⊗ᴸ Λ ≅ Rf_! K ≅ Rf_! (K ⊗ᴸ Λ) ⟶ Rf_! (K ⊗ᴸ Lf^* Λ)`. -/
lemma exceptionalProjectionMorphismOfCompactification_unit
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    exceptionalProjectionMorphismOfCompactification Λ c K (𝟙_ _) =
      (ρ_ _).hom ≫ (Rf_!(c)⟦Λ⟧).map ((ρ_ K).inv ≫ K ◁ ε L((f)^*⟦Λ⟧)) :=
  Adjunction.projection_comp_unit D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧)
    (leftDerivedUpperStarCompactificationIso Λ c) (properProjectionMorphism Λ c.g)
    (fun K N ↦ inv (openImmersionProjectionComparison Λ c.i K N))
    (fun A ↦ (derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism_unit A)
    (fun K ↦ by
      have : IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
          c.i).projectionComparison K (𝟙_ _)) :=
        isIso_openImmersionProjectionComparison Λ c.i K _
      exact Adjunction.inv_projectionComparison_unit _ K)
    (fun K _ _ h ↦ inv_openImmersionProjectionComparison_natural_right Λ c.i K h)
    (ε_comp_map_ε_comp_leftDerivedUpperStarCompactificationIso_inv_app Λ c) K

/-- **Associativity of the exceptional projection morphism**: `PF^!_{f,K,B ⊗ᴸ C}` is
`PF^!_{f,K,B} ⊗ᴸ C` followed by `PF^!_{f,K ⊗ᴸ Lf^* B,C}` and the multiplication of `Lf^*`. -/
lemma exceptionalProjectionMorphismOfCompactification_tensor
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    exceptionalProjectionMorphismOfCompactification Λ c K (B ⊗ C) =
      (α_ _ _ _).inv ≫ exceptionalProjectionMorphismOfCompactification Λ c K B ▷ C ≫
        exceptionalProjectionMorphismOfCompactification Λ c (K ⊗ (L((f)^*⟦Λ⟧)).obj B) C ≫
        (Rf_!(c)⟦Λ⟧).map ((α_ _ _ _).hom ≫ K ◁ μ L((f)^*⟦Λ⟧) B C) :=
  Adjunction.projection_comp_tensor D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧)
    (leftDerivedUpperStarCompactificationIso Λ c) (properProjectionMorphism Λ c.g)
    (fun K N ↦ inv (openImmersionProjectionComparison Λ c.i K N))
    (fun A B C ↦ (derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism_tensor A B C)
    (fun φ B ↦ (derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism_natural_left φ B)
    (fun K B C ↦ by
      have : IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
          c.i).projectionComparison K (B ⊗ C)) :=
        isIso_openImmersionProjectionComparison Λ c.i K _
      have : IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
          c.i).projectionComparison K B) :=
        isIso_openImmersionProjectionComparison Λ c.i K _
      have : IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
          c.i).projectionComparison (K ⊗ (L((c.i)^*⟦Λ⟧)).obj B) C) :=
        isIso_openImmersionProjectionComparison Λ c.i _ _
      exact Adjunction.inv_projectionComparison_tensor _ K B C)
    (fun {K K'} φ N ↦
      @Adjunction.inv_projectionComparison_natural_left _ _ _ _ _ _ _ _
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i) _ _ _ φ N
        (isIso_openImmersionProjectionComparison Λ c.i K N)
        (isIso_openImmersionProjectionComparison Λ c.i K' N))
    (fun K _ _ h ↦ inv_openImmersionProjectionComparison_natural_right Λ c.i K h)
    (μ_comp_map_μ_comp_leftDerivedUpperStarCompactificationIso_inv_app Λ c) K B C

end OfCompactification

end AlgebraicGeometry.ProEtale.CondensedRing
