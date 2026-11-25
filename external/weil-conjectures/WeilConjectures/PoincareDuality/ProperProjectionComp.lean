/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionCoherence
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!

# The derived proper projection morphism of a composite

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of schemes, the derived projection morphism
`PF^*_{f ≫ g}` of `L(f ≫ g)^* ⊣ R(f ≫ g)_*` is the composite of `PF^*_g` and `Rg_* PF^*_f`, read
through the composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` and its conjugate
(`ProEtale.CondensedRing.properProjectionMorphism_comp`). This is the proper part of the
composition clause of the coherence of the projection formula (blueprint `prop-sf-pf-coherence`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace CategoryTheory.Adjunction

/-- Transport the projection morphism to a composite adjunction and expand its two factors. -/
private lemma projectionMorphism_eq_of_iso_comp
    {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
    {F : C₃ ⥤ C₁} {G : C₁ ⥤ C₃} {F₁ : C₂ ⥤ C₁} {G₁ : C₁ ⥤ C₂}
    {F₂ : C₃ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
    [F.OplaxMonoidal] [F₁.OplaxMonoidal] [F₂.OplaxMonoidal]
    (a : F ⊣ G) (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (e : F ≅ F₂ ⋙ F₁)
    (he : ∀ K M, δ F K M ≫ (e.hom.app K ⊗ₘ e.hom.app M) =
      e.hom.app (K ⊗ M) ≫ δ (F₂ ⋙ F₁) K M) (A : C₁) (B : C₃) :
    a.projectionMorphism A B =
      (conjugateIsoEquiv (a₂.comp a₁) a e).inv.app A ▷ B ≫
        a₂.projectionMorphism (G₁.obj A) B ≫
        G₂.map (a₁.projectionMorphism A (F₂.obj B)) ≫
        (conjugateIsoEquiv (a₂.comp a₁) a e).hom.app _ ≫ G.map (A ◁ e.inv.app B) := by
  rw [projectionMorphism_eq_of_iso a (a₂.comp a₁) e he, projectionMorphism_comp]
  simp only [Category.assoc, Functor.comp_obj]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma δ_leftDerivedUpperStar {W V : Scheme.{u}} (h : W ⟶ V)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    δ L((h)^*⟦Λ⟧) K M = ((leftDerivedUpperStarTensor Λ h).app K).app M :=
  rfl

/-- The composition isomorphism of the derived pullbacks is compatible with the comultiplications,
in the form used by `CategoryTheory.Adjunction.projectionMorphism_eq_of_iso`. -/
lemma leftDerivedUpperStarComp_δ
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    δ L((f ≫ g)^*⟦Λ⟧) K M ≫
        ((leftDerivedUpperStarComp Λ f g).hom.app K ⊗ₘ (leftDerivedUpperStarComp Λ f g).hom.app M) =
      (leftDerivedUpperStarComp Λ f g).hom.app (K ⊗ M) ≫
        δ (L((g)^*⟦Λ⟧) ⋙ L((f)^*⟦Λ⟧)) K M := by
  simp only [Functor.OplaxMonoidal.comp_δ, δ_leftDerivedUpperStar]
  exact leftDerivedUpperStarTensor_comp Λ f g K M

/-- **The proper projection morphism of a composite** (blueprint `prop-sf-pf-coherence`,
composition clause, for the pullback–pushforward adjunctions). -/
lemma properProjectionMorphism_comp
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    properProjectionMorphism Λ (f ≫ g) A B =
      (rightDerivedLowerStarComp Λ f g).inv.app A ▷ B ≫
        properProjectionMorphism Λ g ((R((f)_*⟦Λ⟧)).obj A) B ≫
        (R((g)_*⟦Λ⟧)).map (properProjectionMorphism Λ f A ((L((g)^*⟦Λ⟧)).obj B)) ≫
        (rightDerivedLowerStarComp Λ f g).hom.app _ ≫
        (R((f ≫ g)_*⟦Λ⟧)).map (A ◁ (leftDerivedUpperStarComp Λ f g).inv.app B) :=
  Adjunction.projectionMorphism_eq_of_iso_comp (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ g)
    (leftDerivedUpperStarComp Λ f g) (leftDerivedUpperStarComp_δ Λ f g) A B

section Open

variable {U V : Scheme.{u}} (i : U ⟶ V) (i' : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion i']

-- instantiating the abstract statement in the derived categories of module objects
/-- **The open projection comparison of a composite** (blueprint `prop-sf-pf-coherence`,
composition clause, for the extensions by zero along open immersions). -/
lemma openImmersionProjectionComparison_comp
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    openImmersionProjectionComparison Λ (i ≫ i') M N =
      ((conjugateIsoEquiv
          (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (i ≫ i'))
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ i).comp
            (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ i'))).symm
          (leftDerivedUpperStarComp Λ i i')).inv.app _ ≫
        (D((i')_!open⟦Λ⟧)).map ((D((i)_!open⟦Λ⟧)).map
          (M ◁ (leftDerivedUpperStarComp Λ i i').hom.app N)) ≫
        (D((i')_!open⟦Λ⟧)).map (openImmersionProjectionComparison Λ i M ((L((i')^*⟦Λ⟧)).obj N)) ≫
        openImmersionProjectionComparison Λ i' ((D((i)_!open⟦Λ⟧)).obj M) N ≫
        ((conjugateIsoEquiv
          (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (i ≫ i'))
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ i).comp
            (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ i'))).symm
          (leftDerivedUpperStarComp Λ i i')).hom.app M ▷ N :=
  Adjunction.projectionComparison_eq_of_iso_comp _ _ _ (leftDerivedUpperStarComp Λ i i')
    (leftDerivedUpperStarComp_δ Λ i i') M N

end Open

end AlgebraicGeometry.ProEtale.CondensedRing
