/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenCover
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage

/-!
# Constructibility of direct images is local on the target

For a morphism `f : X ⟶ S` with `S` Noetherian and an open cover `(Uᵢ)` of `S`, the property
`𝒞(f)` holds as soon as `𝒞(f ∣_ Uᵢ)` holds for the restrictions `f ∣_ Uᵢ : f⁻¹ Uᵢ ⟶ Uᵢ`
(`AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_iSup_eq_top`). Indeed restriction to
an open commutes with the higher direct images, by étale base change for the derived direct
image (`AlgebraicGeometry.Etale.upperStarHomologyRightDerivedLowerStarIso`), and
constructibility is local on open covers
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_iSup_eq_top`). This is the target
localisation of the blueprint proof of `proposition-proper-direct-image-finite-coefficients`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Étale restriction of higher direct images.** For a cartesian square
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` with `g` étale, the restriction along
`g` of `Rᵠf_* F` is `Rᵠf'_*(g'^* F)`, by étale base change for the derived direct image
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`). -/
noncomputable def upperStarHomologyRightDerivedLowerStarIso {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [Etale g]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
    (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f')_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((g')^*[ModuleCat.{u + 1} Λ].obj F))) :=
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  (g)^*[ModuleCat.{u + 1} Λ].mapIso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
    ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
        (((g')^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _)

/-- **`𝒞` is local on the target.** Let `f : X ⟶ S` be a morphism to a Noetherian scheme and
`(Uᵢ)` an open cover of `S`. If `𝒞(f ∣_ Uᵢ)` holds for every `i`, then `𝒞(f)` holds. -/
theorem HasConstructibleDirectImages.of_iSup_eq_top {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) {ι : Type*} (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, HasConstructibleDirectImages Λ (f ∣_ U i)) : HasConstructibleDirectImages Λ f := by
  intro F hF q
  refine IsConstructibleSheaf.of_iSup_eq_top U hU _ fun i ↦ ?_
  have := h i _ (IsConstructibleSheaf.upperStar (f ⁻¹ᵁ U i).ι F) q
  exact IsConstructibleSheaf.of_iso
    (upperStarHomologyRightDerivedLowerStarIso (isPullback_morphismRestrict f (U i)).flip F q).symm

end Etale

end AlgebraicGeometry
