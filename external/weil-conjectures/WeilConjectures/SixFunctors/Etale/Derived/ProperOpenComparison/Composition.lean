/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs

/-!
# Composition of proper-open comparison maps

For proper maps `u : T₁ ⟶ T₂`, `v : T₂ ⟶ T₃` and open immersions `jᵢ : X ⟶ Tᵢ` with
`j₁ ≫ u = j₂` and `j₂ ≫ v = j₃`, the comparison maps of
`WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs` satisfy

`α_{u ≫ v, K} = Rv_* (α_{u,K}) ∘ α_{v,K}`

modulo `R(u ≫ v)_* ≅ Rv_* Ru_*`, and the comparison map of the identity is the identity
(blueprint `proposition-construction-independence-rf-shriek--7`).

Both statements follow from the characterisation `Ru_* (ι_{j₁}) ∘ α_u = ι_{j₂}` of `α_u`
(`AlgebraicGeometry.ProperOpenDatum.eq_comparison`), together with the associativity and the
right unit law of the composition isomorphisms of the derived pushforwards. In particular they do
not use proper base change.

## Main statements

- the right unit law for the composition isomorphisms of derived pushforwards:
  `Etale.whiskerLeft_lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso'`.
- `AlgebraicGeometry.ProperOpenDatum.comparison_comp`: the composition law.
- `AlgebraicGeometry.ProperOpenDatum.comparison_id`: the identity law.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

/-- **The right unit law** for the composition isomorphisms of the bounded below derived
pushforwards: `R⁺g_* ≅ R⁺g_* ⋙ R⁺(𝟙)_* ≅ R⁺(g ≫ 𝟙)_* = R⁺g_*` is the identity. -/
lemma whiskerLeft_lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso'
    {V Y : Scheme.{u}} (g : V ⟶ Y) :
    Functor.whiskerLeft ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y).inv ≫
      (Functor.rightDerivedFunctorPlusCompIso' ((g)_*[ModuleCat.{u + 1} Λ])
        ((𝟙 Y)_*[ModuleCat.{u + 1} Λ])
        (Etale.lowerStarComp _ g (𝟙 Y) g (Category.comp_id g).symm)).hom =
      𝟙 _ := by
  refine Functor.rightDerived_ext (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus)
    (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith)
    (HomotopyCategory.Plus.quasiIso _) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app,
    Functor.comp_obj]
  have hnat := (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y).inv.naturality
    (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.id_map, Functor.id_obj] at hnat
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac
    ((g)_*[ModuleCat.{u + 1} Λ]) ((𝟙 Y)_*[ModuleCat.{u + 1} Λ])
    (Etale.lowerStarComp _ g (𝟙 Y) g (Category.comp_id g).symm)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightDerivedFunctorPlusCompUnit_app, assoc] at hfac
  have hcomp :
      (NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y).inv).app
        (((g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K) ≫
      (NatTrans.mapHomotopyCategoryPlus
        (Etale.lowerStarComp _ g (𝟙 Y) g (Category.comp_id g).symm).hom).app K = 𝟙 _ := by
    have : Functor.whiskerLeft ((g)_*[ModuleCat.{u + 1} Λ])
        (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y).inv ≫
        (Etale.lowerStarComp _ g (𝟙 Y) g (Category.comp_id g).symm).hom = 𝟙 _ := by
      rw [Etale.lowerStarComp_id_right]
      ext F : 2
      simp
    have h' := NatTrans.congr_app (congrArg NatTrans.mapHomotopyCategoryPlus this) K
    rw [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_id] at h'
    exact h'
  have hQ : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y).inv).app
          (((g)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
        (Etale.lowerStarComp _ g (𝟙 Y) g (Category.comp_id g).symm).hom).app K) = 𝟙 _ := by
    rw [← DerivedCategory.Plus.Qh.map_comp, hcomp, DerivedCategory.Plus.Qh.map_id]
  simp only [Functor.comp_obj] at hnat
  rw [reassoc_of% hnat, lowerStarIdDerivedPlus_inv_app, assoc, hfac, reassoc_of% hQ]
  exact (comp_id _).symm

end Etale

namespace ProperOpenDatum

private theorem comparison_comp_of_squares
    {C : Type*} [Category C] {A B C₁ D E F G H : C}
    {a : A ⟶ B} {b : B ⟶ C₁} {c : C₁ ⟶ D} {d : D ⟶ E} {e : E ⟶ F}
    {f : C₁ ⟶ G} {g : G ⟶ E} {h : G ⟶ H} {i : H ⟶ F} {j : B ⟶ H} {k : A ⟶ F}
    (hnat : f ≫ g = c ≫ d) (hassoc : h ≫ i = g ≫ e)
    (h₁ : b ≫ f ≫ h = j) (h₂ : a ≫ j ≫ i = k) :
    a ≫ b ≫ c ≫ d ≫ e = k := by
  rw [← reassoc_of% hnat, ← hassoc, reassoc_of% h₁, h₂]

variable {X T₁ T₂ T₃ : Scheme.{u}} (u : T₁ ⟶ T₂) (v : T₂ ⟶ T₃) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
  (j₃ : X ⟶ T₃) [IsProper u] [IsProper v] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
  [IsOpenImmersion j₃] (h₁ : j₁ ≫ u = j₂) (h₂ : j₂ ≫ v = j₃)

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: Composition of proper-open
comparison maps. For proper `u : T₁ ⟶ T₂`, `v : T₂ ⟶ T₃` and open immersions `jᵢ : X ⟶ Tᵢ` with
`j₁ ≫ u = j₂`, `j₂ ≫ v = j₃`,

`α_{u ≫ v} = α_v ≫ Rv_* (α_u) ≫ (Rv_* Ru_* ≅ R(u ≫ v)_*)`.

The identity law is `comparison_id`. -/
theorem comparison_comp :
    (⟨T₁, T₃, u ≫ v, j₁, j₃, by rw [reassoc_of% h₁, h₂], inferInstance, inferInstance,
        inferInstance⟩ : ProperOpenDatum X).comparison Λ =
      (⟨T₂, T₃, v, j₂, j₃, h₂, inferInstance, inferInstance, inferInstance⟩ :
          ProperOpenDatum X).comparison Λ ≫
        Functor.whiskerRight
          ((⟨T₁, T₂, u, j₁, j₂, h₁, inferInstance, inferInstance, inferInstance⟩ :
            ProperOpenDatum X).comparison Λ)
          ((v)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ≫
        Functor.whiskerLeft D+((j₁)_!open[ModuleCat.{u + 1} Λ])
          (Functor.rightDerivedFunctorPlusCompIso' ((u)_*[ModuleCat.{u + 1} Λ])
            ((v)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ u v (u ≫ v) rfl)).hom := by
  symm
  refine ProperOpenDatum.eq_comparison Λ
    (⟨T₁, T₃, u ≫ v, j₁, j₃, by rw [reassoc_of% h₁, h₂], inferInstance, inferInstance,
        inferInstance⟩ : ProperOpenDatum X) _ ?_
  ext K : 2
  have h₁' := comparison_app_toLowerStar_app Λ
    (⟨T₁, T₂, u, j₁, j₂, h₁, inferInstance, inferInstance, inferInstance⟩ : ProperOpenDatum X) K
  have h₂' := comparison_app_toLowerStar_app Λ
    (⟨T₂, T₃, v, j₂, j₃, h₂, inferInstance, inferInstance, inferInstance⟩ : ProperOpenDatum X) K
  have hassoc := NatTrans.congr_app (rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc
    (ModuleCat.{u + 1} Λ) j₁ u v j₂ (u ≫ v) j₃ h₁.symm rfl h₂.symm) K
  have hnat := (Functor.rightDerivedFunctorPlusCompIso' ((u)_*[ModuleCat.{u + 1} Λ])
    ((v)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ u v (u ≫ v) rfl)).hom.naturality
    ((openImmersionLowerShriekToLowerStarPlus Λ j₁).app K)
  rw [toLowerStar_app] at h₁' h₂'
  dsimp only at h₁' h₂'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map] at hassoc hnat
  rw [NatTrans.comp_app, NatTrans.comp_app, toLowerStar_app]
  dsimp only
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Category.assoc]
  have h₁'' := congrArg ((v)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map h₁'
  simp only [Functor.map_comp] at h₁''
  exact comparison_comp_of_squares hnat hassoc h₁'' h₂'


/-- The identity law of blueprint `proposition-construction-independence-rf-shriek--7`: for the
identity of `T` (and `j₁ = j₂ = j`), the comparison map is the inverse of the identity
isomorphism `R(𝟙)_* ≅ 𝟭`. -/
theorem comparison_id {T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
    (⟨T, T, 𝟙 T, j, j, Category.comp_id j, inferInstance, inferInstance, inferInstance⟩ :
        ProperOpenDatum X).comparison Λ =
      Functor.whiskerLeft D+((j)_!open[ModuleCat.{u + 1} Λ])
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) T).inv := by
  symm
  refine ProperOpenDatum.eq_comparison Λ
    (⟨T, T, 𝟙 T, j, j, Category.comp_id j, inferInstance, inferInstance, inferInstance⟩ :
      ProperOpenDatum X) _ ?_
  ext K : 2
  have hnat := (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) T).inv.naturality
    ((openImmersionLowerShriekToLowerStarPlus Λ j).app K)
  have hunit := NatTrans.congr_app
    (whiskerLeft_lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso' Λ j) K
  simp only [Functor.id_map, Functor.id_obj] at hnat
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hunit
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, toLowerStar_app]
  dsimp only
  rw [← reassoc_of% hnat]
  erw [hunit]
  exact comp_id _

end ProperOpenDatum

end AlgebraicGeometry
