/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs

/-!
# Direct image from an open and closed section

Let `s : X ⟶ V` be an open immersion with closed range. Then the canonical map
`ι_s : s_! ⟶ Rs_*` of `D⁺(X_ét, Λ)`
(`AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStarPlus`) is an isomorphism: `V` is
the disjoint union of the two open subschemes `s(X)` and `V \ s(X)`, on the first `ι_s`
restricts to an isomorphism, and on the second both sides vanish.

Consequently, if moreover `s` is a section of a morphism `p : V ⟶ X`, then

`Rp_* s_! K ≅ Rp_* Rs_* K ≅ R(s ≫ p)_* K = R(𝟙)_* K ≅ K`

(blueprint `proposition-construction-independence-rf-shriek--7`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStarPlus_app_of_isClosed_range`
- `AlgebraicGeometry.Etale.clopenSectionDirectImageIso`
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

variable {X V : Scheme.{u}} (s : X ⟶ V) [IsOpenImmersion s]

/-- For an open immersion `s` with closed range, the canonical map `ι_s : s_! K ⟶ Rs_* K` is an
isomorphism. On the open complement `W` of the range of `s` both sides vanish (`Rs_* K` by
étale base change, the fibre product `X ×_V W` being empty); on the closed complement of `W`,
which lies inside the range of `s`, it is `s^*` of `ι_s`. -/
theorem isIso_openImmersionLowerShriekToLowerStarPlus_app_of_isClosed_range
    (hs : IsClosed (Set.range s.base))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((openImmersionLowerShriekToLowerStarPlus Λ s).app K) := by
  set ψ := (openImmersionLowerShriekToLowerStarPlus Λ s).app K
  let W : V.Opens := ⟨(Set.range s.base)ᶜ, hs.isOpen_compl⟩
  have hW : Set.range W.ι.base = (Set.range s.base)ᶜ := W.range_ι
  set i := W.ι.closedComplement
  have hi : Set.range i.base ⊆ Set.range s.base := by
    rw [Scheme.Hom.range_closedComplement, hW, compl_compl]
  set l := IsOpenImmersion.lift s i hi
  have hl : l ≫ s = i := IsOpenImmersion.lift_fac _ _ _
  have hdisj : Disjoint (Set.range W.ι.base) (Set.range s.base) := by
    rw [hW]
    exact disjoint_compl_left
  have hempty : IsEmpty ↥(pullback s W.ι) := ⟨fun x ↦ by
    have h₁ : (pullback.fst s W.ι ≫ s).base x ∈ Set.range s.base :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    have h₂ : (pullback.snd s W.ι ≫ W.ι).base x ∈ Set.range W.ι.base :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [pullback.condition] at h₁
    rw [hW] at h₂
    exact h₂ h₁⟩
  suffices IsIso (DerivedCategory.Plus.ι.map ψ) from
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map _ W.ι i
    W.ι.range_closedComplement _ ?_ ?_
  · -- on `W`, source and target vanish
    have hs : IsZero (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).obj
        (D+((s)_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
      IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _
        (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ s
          W.ι hdisj (DerivedCategory.Plus.ι.obj K))
    have ht : IsZero (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).obj
        (((s)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K)) := by
      let sq := IsPullback.of_hasPullback s W.ι
      have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
      exact IsZero.of_iso
        ((((pullback.snd s W.ι)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus).map_isZero
          (isZero_derivedCategoryPlus_of_isEmpty Λ _ _))
        (asIso ((Etale.derivedBaseChangeMapPlus _ sq.toCommSq).app K))
    have := isIso_of_source_target_iso_zero (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).map ψ)
      hs.isoZero ht.isoZero
    exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).map ψ)))
  · -- on the closed complement of `W`, which lies in the range of `s`, it is `s^*` of `ι_s`
    have h : IsIso (D+((i)^*[ModuleCat.{u + 1} Λ]).map ψ) := by
      rw [NatIso.isIso_map_iff (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ)
        l s i hl.symm)]
      exact (inferInstance : IsIso (D+((l)^*[ModuleCat.{u + 1} Λ]).map
        (D+((s)^*[ModuleCat.{u + 1} Λ]).map ψ)))
    exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((i)^*[ModuleCat.{u + 1} Λ]).map ψ)))

/-- For an open immersion `s` with closed range, `ι_s : D⁺s_! ⟶ R⁺s_*` is an isomorphism. -/
lemma isIso_openImmersionLowerShriekToLowerStarPlus_of_isClosed_range
    (hs : IsClosed (Set.range s.base)) :
    IsIso (openImmersionLowerShriekToLowerStarPlus Λ s) :=
  have := isIso_openImmersionLowerShriekToLowerStarPlus_app_of_isClosed_range Λ s hs
  NatIso.isIso_of_isIso_app _

variable {X V : Scheme.{u}} (p : V ⟶ X) (s : X ⟶ V) [IsOpenImmersion s]

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: Direct image from an open and
closed section. Let `p : V ⟶ X` be a morphism and `s : X ⟶ V` an open immersion with closed range
and `s ≫ p = 𝟙 X`. Restriction to the component `s(X)` gives a canonical isomorphism

`Rp_* s_! K ≅ K`

on `D⁺(X_ét, Λ)`: the inverse of `ι_s : s_! K ≅ Rs_* K`
(`isIso_openImmersionLowerShriekToLowerStarPlus_app_of_isClosed_range`) followed by the
composition isomorphism `Rp_* Rs_* ≅ R(s ≫ p)_* = R(𝟙)_*` and `R(𝟙)_* ≅ 𝟭`. -/
noncomputable def clopenSectionDirectImageIso (hs : IsClosed (Set.range s.base))
    (h : s ≫ p = 𝟙 X) :
    D+((s)_!open[ModuleCat.{u + 1} Λ]) ⋙ ((p)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ≅
      𝟭 _ :=
  haveI := isIso_openImmersionLowerShriekToLowerStarPlus_of_isClosed_range Λ s hs
  Functor.isoWhiskerRight (asIso (openImmersionLowerShriekToLowerStarPlus Λ s))
      ((p)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ≪≫
    Functor.rightDerivedFunctorPlusCompIso' ((s)_*[ModuleCat.{u + 1} Λ])
      ((p)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ s p (𝟙 X) h.symm) ≪≫
    lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X

lemma clopenSectionDirectImageIso_hom_app (hs : IsClosed (Set.range s.base))
    (h : s ≫ p = 𝟙 X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (clopenSectionDirectImageIso Λ p s hs h).hom.app K =
      ((p)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((openImmersionLowerShriekToLowerStarPlus Λ s).app K) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((s)_*[ModuleCat.{u + 1} Λ])
          ((p)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ s p (𝟙 X) h.symm)).hom.app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app K :=
  rfl

end Etale

end AlgebraicGeometry
