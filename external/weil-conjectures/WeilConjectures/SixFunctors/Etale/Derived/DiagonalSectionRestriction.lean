/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Restriction along the sections `x ↦ (x, y)` of `X ×_S X`

Let `a : X ⟶ S` be proper, `P = X ×_S X` with projections `p₁`, `p₂`, and let `y` be a section
of `a`. Then `j_y = (𝟙, a ≫ y) : X ⟶ P` is a section of `p₁` with `j_y ≫ p₂ = a ≫ y`, and
restricting along `j_y` turns a morphism `α : Lp₁^* N ⟶ Lp₂^* La^* Q` into a morphism
`N ⟶ La^* Q` (`AlgebraicGeometry.Etale.pullbackLiftSectionRestrict`). Classically, for
`N = Λ_X` and `Q = Λ_S`, this is the restriction `H^*(X ×_S X) ⟶ H^*(X)` to the fibre
`X × {y}` of the second projection.

The restriction is independent of the section `y` as soon as the unit `Q ⟶ Ra_* La^* Q` is an
epimorphism onto `Q` in the weak sense that `h ↦ η_Q ≫ h` is injective on `Hom(Ra_* La^* Q, Q)`
(`AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_eq`). By proper base change
`La^* Ra_* ≅ Rp₁_* Lp₂^*`, every `α` is `Lp₁^* φ` followed by `Lp₂^*` of the counit of
`La^* ⊣ Ra_*`, and its restriction along `j_y` is `φ ≫ La^*(ψ_y)` for the restriction
`ψ_y : Ra_* La^* Q ⟶ Q` of global sections to the point `y`. Each `ψ_y` is a retraction of the
unit `η_Q`, so the `ψ_y` all agree.

## Main definitions

- `AlgebraicGeometry.Etale.pullbackLiftSection`: the section `j_y = (𝟙, a ≫ y)` of `p₁`.
- `AlgebraicGeometry.Etale.pullbackLiftSectionRestrict`: restriction along `j_y`.

## Main statements

- `AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_eq`: independence of the section.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- The section `x ↦ (x, y(a(x)))` of the first projection `X ×_S X ⟶ X` attached to a section
`y` of `a : X ⟶ S`. -/
noncomputable def pullbackLiftSection (y : S ⟶ X) (hy : y ≫ a = 𝟙 S) : X ⟶ pullback a a :=
  pullback.lift (𝟙 X) (a ≫ y) (by rw [Category.id_comp, Category.assoc, hy, Category.comp_id])

@[reassoc (attr := simp)]
lemma pullbackLiftSection_fst (y : S ⟶ X) (hy : y ≫ a = 𝟙 S) :
    pullbackLiftSection a y hy ≫ pullback.fst a a = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackLiftSection_snd (y : S ⟶ X) (hy : y ≫ a = 𝟙 S) :
    pullbackLiftSection a y hy ≫ pullback.snd a a = a ≫ y :=
  pullback.lift_snd _ _ _

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- *Restriction along the section `j_y = (𝟙, a ≫ y)`* of `p₁ : X ×_S X ⟶ X`: a morphism
`α : Lp₁^* N ⟶ Lp₂^* La^* Q` is pulled back along `j_y` and read through
`Lj_y^* Lp₁^* ≅ 𝟭` and `Lj_y^* Lp₂^* La^* ≅ La^* Ly^* La^* ≅ La^*`. -/
noncomputable def pullbackLiftSectionRestrict (y : S ⟶ X) (hy : y ≫ a = 𝟙 S)
    {N : DerivedCategoryModule Λ X} {Q : DerivedCategoryModule Λ S}
    (α : (L((pullback.fst a a)^*[ModuleCat.{u + 1} Λ])).obj N ⟶
      (L((pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q)) :
    N ⟶ (L((a)^*[ModuleCat.{u + 1} Λ])).obj Q :=
  (leftDerivedUpperStarCompSectionIso _ (pullbackLiftSection a y hy) (pullback.fst a a)
      (pullbackLiftSection_fst a y hy)).inv.app N ≫
    (L((pullbackLiftSection a y hy)^*[ModuleCat.{u + 1} Λ])).map α ≫
      ((leftDerivedUpperStarComp _ (pullbackLiftSection a y hy) (pullback.snd a a)).inv.app _ ≫
        (leftDerivedUpperStarComp _ a y (pullbackLiftSection a y hy ≫ pullback.snd a a)
          (pullbackLiftSection_snd a y hy)).hom.app _) ≫
      (L((a)^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarCompSectionIso _ y a hy).hom.app Q)

/-- The restriction `ψ_y : Ra_* La^* Q ⟶ Q` of global sections to the point `y` of `a`: pull
back the counit of `La^* ⊣ Ra_*` along `y`, through `Ly^* La^* ≅ 𝟭`. -/
noncomputable def sectionEvaluation (y : S ⟶ X) (hy : y ≫ a = 𝟙 S)
    (Q : DerivedCategoryModule Λ S) :
    (R((a)_*[ModuleCat.{u + 1} Λ])).obj ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q) ⟶ Q :=
  (leftDerivedUpperStarCompSectionIso _ y a hy).inv.app _ ≫
    (L((y)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction _ a).counit.app _) ≫
    (leftDerivedUpperStarCompSectionIso _ y a hy).hom.app Q

/-- The restriction to a point is a retraction of the unit `Q ⟶ Ra_* La^* Q`. -/
@[reassoc (attr := simp)]
lemma unit_app_sectionEvaluation (y : S ⟶ X) (hy : y ≫ a = 𝟙 S)
    (Q : DerivedCategoryModule Λ S) :
    (derivedUpperStarLowerStarAdjunction _ a).unit.app Q ≫ sectionEvaluation a Λ y hy Q = 𝟙 _ := by
  have h := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) y a hy).inv.naturality
    ((derivedUpperStarLowerStarAdjunction _ a).unit.app Q)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h
  rw [sectionEvaluation, reassoc_of% h, ← Functor.map_comp_assoc,
    Adjunction.left_triangle_components, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]

/-- The restriction to a point does not depend on the point, as soon as precomposition with the
unit `Q ⟶ Ra_* La^* Q` is injective. -/
lemma sectionEvaluation_eq (x y : S ⟶ X) (hx : x ≫ a = 𝟙 S) (hy : y ≫ a = 𝟙 S)
    (Q : DerivedCategoryModule Λ S)
    (hQ : Function.Injective (fun h : (R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q) ⟶ Q ↦
      (derivedUpperStarLowerStarAdjunction _ a).unit.app Q ≫ h)) :
    sectionEvaluation a Λ x hx Q = sectionEvaluation a Λ y hy Q :=
  hQ (by simp only [unit_app_sectionEvaluation a Λ])

/-- The coherence behind `AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_map_comp`: on
objects pulled back from `S`, the identification `Lj_y^* Lp₁^* La^* ≅ La^*` through the section
`j_y` of `p₁` and the one through `j_y ≫ p₂ = a ≫ y` and the section `y` of `a` agree. -/
lemma pullbackLiftSection_coherence (y : S ⟶ X) (hy : y ≫ a = 𝟙 S)
    (W : DerivedCategoryModule Λ S) :
    (leftDerivedUpperStarCompSectionIso _ (pullbackLiftSection a y hy) (pullback.fst a a)
        (pullbackLiftSection_fst a y hy)).inv.app _ ≫
      (L((pullbackLiftSection a y hy)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback a a).flip.toCommSq).hom.app W) ≫
      (leftDerivedUpperStarComp _ (pullbackLiftSection a y hy) (pullback.snd a a)).inv.app _ ≫
        (leftDerivedUpperStarComp _ a y (pullbackLiftSection a y hy ≫ pullback.snd a a)
          (pullbackLiftSection_snd a y hy)).hom.app _ =
    (L((a)^*[ModuleCat.{u + 1} Λ])).map
      ((leftDerivedUpperStarCompSectionIso _ y a hy).inv.app W) := by
  have H := leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} Λ) a a
    (pullback.fst a a) (pullback.snd a a) y (pullbackLiftSection a y hy)
    pullback.condition.symm (pullbackLiftSection_snd a y hy) hy
    (pullbackLiftSection_fst a y hy) W
  have e : (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback a a).flip.toCommSq).inv.app W =
      (leftDerivedUpperStarComp _ (pullback.snd a a) a).inv.app W ≫
        (leftDerivedUpperStarComp _ (pullback.fst a a) a (pullback.snd a a ≫ a)
          pullback.condition.symm).hom.app W := rfl
  rw [← e] at H
  simp only [Category.assoc] at H
  rw [← cancel_mono ((L((a)^*[ModuleCat.{u + 1} Λ])).map
    ((leftDerivedUpperStarCompSectionIso _ y a hy).hom.app W)), ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [← H, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp

/-- **Restriction along `j_y` of a morphism pulled back from `X`**: for
`φ : N ⟶ La^* Ra_* La^* Q`, the restriction along `j_y` of
`Lp₁^* φ ≫ (Lp₁^* La^* ≅ Lp₂^* La^*) ≫ Lp₂^*(ε)`, with `ε` the counit of `La^* ⊣ Ra_*`, is
`φ ≫ La^*(ψ_y)` for the restriction `ψ_y` of global sections to `y`
(`AlgebraicGeometry.Etale.sectionEvaluation`). -/
lemma pullbackLiftSectionRestrict_map_comp (y : S ⟶ X) (hy : y ≫ a = 𝟙 S)
    {N : DerivedCategoryModule Λ X} {Q : DerivedCategoryModule Λ S}
    (φ : N ⟶ (L((a)^*[ModuleCat.{u + 1} Λ])).obj ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q))) :
    pullbackLiftSectionRestrict a Λ y hy ((L((pullback.fst a a)^*[ModuleCat.{u + 1} Λ])).map φ ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback a a).flip.toCommSq).hom.app _ ≫
      (L((pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction _ a).counit.app _)) =
    φ ≫ (L((a)^*[ModuleCat.{u + 1} Λ])).map (sectionEvaluation a Λ y hy Q) := by
  have n₁ := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
    (pullbackLiftSection a y hy) (pullback.fst a a) (pullbackLiftSection_fst a y hy)).inv.naturality
      φ
  have n₂ := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (pullbackLiftSection a y hy)
    (pullback.snd a a)).inv ≫ (leftDerivedUpperStarComp _ a y _
      (pullbackLiftSection_snd a y hy)).hom).naturality
        ((derivedUpperStarLowerStarAdjunction _ a).counit.app
          ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
    NatTrans.comp_app, Category.assoc] at n₁ n₂
  have hc := pullbackLiftSection_coherence a Λ y hy ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
    ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q))
  simp only [pullbackLiftSectionRestrict, sectionEvaluation, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n₁, reassoc_of% n₂, reassoc_of% hc]

variable [Finite Λ] [IsProper a]

/-- **Restriction along `j_y` through proper base change**: for `α : Lp₁^* N ⟶ Lp₂^* La^* Q`,
let `φ : N ⟶ La^* Ra_* La^* Q` be the adjoint of `α` under `Lp₁^* ⊣ Rp₁_*` read through the
proper base change isomorphism `La^* Ra_* ≅ Rp₁_* Lp₂^*`. Then the restriction of `α` along
`j_y` is `φ ≫ La^*(ψ_y)` for the restriction `ψ_y` of global sections to `y`
(`AlgebraicGeometry.Etale.sectionEvaluation`). -/
lemma pullbackLiftSectionRestrict_eq_comp (y : S ⟶ X) (hy : y ≫ a = 𝟙 S)
    {N : DerivedCategoryModule Λ X} {Q : DerivedCategoryModule Λ S}
    (α : (L((pullback.fst a a)^*[ModuleCat.{u + 1} Λ])).obj N ⟶
      (L((pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q)) :
    haveI := Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
      isAddTorsion_of_finite (IsPullback.of_hasPullback a a).flip
    pullbackLiftSectionRestrict a Λ y hy α =
      ((derivedUpperStarLowerStarAdjunction _ (pullback.fst a a)).homEquiv _ _ α ≫
        inv ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback a a).flip.toCommSq).app
            ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q))) ≫
        (L((a)^*[ModuleCat.{u + 1} Λ])).map (sectionEvaluation a Λ y hy Q) := by
  have := Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite (IsPullback.of_hasPullback a a).flip
  have hα : α = (L((pullback.fst a a)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction _ (pullback.fst a a)).homEquiv _ _ α ≫
        inv ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback a a).flip.toCommSq).app
            ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q))) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback a a).flip.toCommSq).hom.app _ ≫
      (L((pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction _ a).counit.app _) := by
    rw [← derivedUpperStar_map_derivedBaseChangeMap_app_counit, ← Functor.map_comp_assoc,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have h₀ := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (pullback.fst a a)).homEquiv_counit (g := (derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) (pullback.fst a a)).homEquiv _ _ α)
    rw [Equiv.symm_apply_apply] at h₀
    exact h₀
  conv_lhs => rw [hα]
  exact pullbackLiftSectionRestrict_map_comp a Λ y hy _

/-- **Independence of the section.** For proper `a : X ⟶ S` and `Q ∈ D(S)` such that
`h ↦ η_Q ≫ h` is injective on `Hom(Ra_* La^* Q, Q)`, restriction along the sections
`j_x = (𝟙, a ≫ x)` and `j_y = (𝟙, a ≫ y)` of `X ×_S X ⟶ X` agree: both are
`φ ≫ La^*(ψ)` for the restriction `ψ` of global sections to a point
(`AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_eq_comp`), and these restrictions are
retractions of `η_Q`. -/
theorem pullbackLiftSectionRestrict_eq (x y : S ⟶ X) (hx : x ≫ a = 𝟙 S) (hy : y ≫ a = 𝟙 S)
    {N : DerivedCategoryModule Λ X} {Q : DerivedCategoryModule Λ S}
    (hQ : Function.Injective (fun h : (R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q) ⟶ Q ↦
      (derivedUpperStarLowerStarAdjunction _ a).unit.app Q ≫ h))
    (α : (L((pullback.fst a a)^*[ModuleCat.{u + 1} Λ])).obj N ⟶
      (L((pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj Q)) :
    pullbackLiftSectionRestrict a Λ x hx α = pullbackLiftSectionRestrict a Λ y hy α := by
  rw [pullbackLiftSectionRestrict_eq_comp, pullbackLiftSectionRestrict_eq_comp,
    sectionEvaluation_eq a Λ x y hx hy Q hQ]

end Etale

end AlgebraicGeometry
