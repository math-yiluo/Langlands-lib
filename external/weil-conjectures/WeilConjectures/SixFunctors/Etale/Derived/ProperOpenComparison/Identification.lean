/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Counit
public import WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.ClopenSection

/-!
# The restriction isomorphism of the proper-open comparison

Let `u : T₁ ⟶ T₂` be proper and `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` open immersions with
`j₁ ≫ u = j₂` (`AlgebraicGeometry.ProperOpenDatum`), with `V = T₁ ×_{T₂} X`, projections
`b : V ⟶ T₁`, `p : V ⟶ X` and section `s : X ⟶ V`. This file identifies the restriction
isomorphism `θ_u : j₂^* Ru_* j₁! K ≅ K` of
`WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs`, to which the comparison
map `α_u` is adjoint, with the composite

`j₂^* Ru_* j₁! K ≅ Rp_* b^* j₁! K ≅ Rp_* s_! K ≅ K`

of the restriction of the derived direct image to the open `X ⊆ T₂`
(blueprint `proposition-construction-independence-rf-shriek--7`), the restriction of the extension
by zero to `V` and the direct image from the open and closed section `s`
(blueprint `proposition-construction-independence-rf-shriek--7`).

## Main definitions

- `AlgebraicGeometry.Etale.derivedOpenRestrictionIso`: `a^* Rf_* ≅ Rf_{U*} b^*` for an open
  immersion `a : U ⟶ S`.
- `AlgebraicGeometry.ProperOpenDatum.upperStarBLowerShriekIso`: `b^* j₁! ≅ s_!`.

## Main statements

- `AlgebraicGeometry.ProperOpenDatum.restrictionIso_hom_app_eq`: the identification of `θ_u`.
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

variable {T S U V : Scheme.{u}} {f : T ⟶ S} {a : U ⟶ S} [IsOpenImmersion a] {b : V ⟶ T}
  {fU : V ⟶ U}

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: Derived direct image restricted
to an open. For a morphism `f : T ⟶ S`, an open immersion `a : U ⟶ S` and the cartesian square
`V = T ×_S U` with projections `b : V ⟶ T` and `f_U : V ⟶ U`, restriction gives a natural
isomorphism

`a^* Rf_* L ≅ Rf_{U,*} b^* L`

on `D⁺(T_ét, Λ)`: the derived base change map
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`), which is an isomorphism by étale base
change (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`). -/
noncomputable def derivedOpenRestrictionIso (sq : IsPullback b fU f a) :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⋙ D+((a)^*[ModuleCat.{u + 1} Λ]) ≅
      D+((b)^*[ModuleCat.{u + 1} Λ]) ⋙ ((fU)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  asIso (Etale.derivedBaseChangeMapPlus _ sq.toCommSq)

@[simp]
lemma derivedOpenRestrictionIso_hom (sq : IsPullback b fU f a) :
    (derivedOpenRestrictionIso Λ sq).hom =
      Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq :=
  rfl

end Etale

namespace ProperOpenDatum

variable {X : Scheme.{u}} (D : ProperOpenDatum X)

/-- The square `𝟙 ≫ j₁ = s ≫ b` is cartesian, `b` being a monomorphism. -/
lemma isPullback_section : IsPullback (𝟙 X) D.section D.j₁ D.b :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp : 𝟙 X ≫ D.j₁ = D.section ≫ D.b)
    (fun c ↦ c.fst) (fun c ↦ comp_id _)
    (fun c ↦ by
      rw [← cancel_mono D.b]
      simp [c.condition])
    (fun c m h₁ _ ↦ by simpa using h₁))

/-- The map `b^* j₁! K ⟶ Rs_* K`: `b^*` of `ι_{j₁} : j₁! K ⟶ Rj₁_* K`, followed by the base
change isomorphism `b^* Rj₁_* K ≅ Rs_* K` of the cartesian square `𝟙 ≫ j₁ = s ≫ b`. -/
noncomputable def upperStarBToLowerStar :
    D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙ D+((D.b)^*[ModuleCat.{u + 1} Λ]) ⟶
      ((D.section)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  Functor.whiskerRight (openImmersionLowerShriekToLowerStarPlus Λ D.j₁)
      D+((D.b)^*[ModuleCat.{u + 1} Λ]) ≫
    Etale.derivedBaseChangeMapPlus _ D.isPullback_section.toCommSq ≫
    Functor.whiskerRight (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom
      ((D.section)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ≫
    (Functor.leftUnitor _).hom

lemma upperStarBToLowerStar_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.upperStarBToLowerStar Λ).app K =
      D+((D.b)^*[ModuleCat.{u + 1} Λ]).map
          ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K) ≫
        (Etale.derivedBaseChangeMapPlus _ D.isPullback_section.toCommSq).app K ≫
        ((D.section)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app K) := by
  simp [upperStarBToLowerStar]

instance isIso_upperStarBToLowerStar : IsIso (D.upperStarBToLowerStar Λ) := by
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ D.isPullback_section
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [upperStarBToLowerStar_app]
  infer_instance

instance isIso_openImmersionLowerShriekToLowerStarPlus_section :
    IsIso (openImmersionLowerShriekToLowerStarPlus Λ D.section) :=
  isIso_openImmersionLowerShriekToLowerStarPlus_of_isClosed_range Λ D.section
    D.isClopen_range_section.isClosed

/-- The restriction of the extension by zero along the clopen section: `b^* j₁! K ≅ s_! K`,
the map `b^* j₁! K ⟶ Rs_* K` of `upperStarBToLowerStar` followed by the inverse of the
isomorphism `ι_s : s_! K ≅ Rs_* K` (the range of `s` is closed). -/
noncomputable def upperStarBLowerShriekIso :
    D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙ D+((D.b)^*[ModuleCat.{u + 1} Λ]) ≅
      D+((D.section)_!open[ModuleCat.{u + 1} Λ]) :=
  asIso (D.upperStarBToLowerStar Λ) ≪≫
    (asIso (openImmersionLowerShriekToLowerStarPlus Λ D.section)).symm

@[reassoc]
lemma upperStarBLowerShriekIso_hom_app_comp
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.upperStarBLowerShriekIso Λ).hom.app K ≫
        (openImmersionLowerShriekToLowerStarPlus Λ D.section).app K =
      (D.upperStarBToLowerStar Λ).app K := by
  simp [upperStarBLowerShriekIso]

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: The specified comparison
isomorphism. The restriction isomorphism `θ_{u,K} : j₂^* Ru_* j₁! K ≅ K` of
`AlgebraicGeometry.ProperOpenDatum.restrictionIso`, to which the comparison map `α_u` is adjoint
(`AlgebraicGeometry.ProperOpenDatum.homEquiv_comparison_app`), is the composite of

* the restriction of the derived direct image to the open `X ⊆ T₂`,
  `j₂^* Ru_* j₁! K ≅ Rp_* b^* j₁! K` (`AlgebraicGeometry.Etale.derivedOpenRestrictionIso`),
* `Rp_*` of the restriction of the extension by zero, `b^* j₁! K ≅ s_! K`
  (`AlgebraicGeometry.ProperOpenDatum.upperStarBLowerShriekIso`), and
* the direct image from the clopen section, `Rp_* s_! K ≅ K`
  (`AlgebraicGeometry.Etale.clopenSectionDirectImageIso`). -/
theorem restrictionIso_hom_app_eq
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.restrictionIso Λ).hom.app K =
      (Etale.derivedOpenRestrictionIso Λ D.isPullback).hom.app
          (D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
        ((D.p)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((D.upperStarBLowerShriekIso Λ).hom.app K) ≫
        (clopenSectionDirectImageIso Λ D.p D.section D.isClopen_range_section.isClosed
          D.section_p).hom.app K := by
  have hcounit := Etale.derivedBaseChangeMapPlus_app_comp_lowerStarIdDerivedPlus
    (ModuleCat.{u + 1} Λ) D.j₂ ⟨rfl⟩ K
  have hpaste := NatTrans.congr_app (Etale.derivedBaseChangeMapPlus_paste_vert_of_eq
    (ModuleCat.{u + 1} Λ) D.isPullback_section.toCommSq D.isPullback.toCommSq D.comm
    D.section_p ⟨rfl⟩) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, id_comp] at hpaste
  have hnatBC := (Etale.derivedBaseChangeMapPlus _ D.isPullback.toCommSq).naturality
    ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K)
  have hnatC := (Functor.rightDerivedFunctorPlusCompIso' ((D.section)_*[ModuleCat.{u + 1} Λ])
    ((D.p)_*[ModuleCat.{u + 1} Λ])
    (Etale.lowerStarComp _ D.section D.p (𝟙 X) D.section_p.symm)).hom.naturality
      ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatBC hnatC
  have hcancel : D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map
      ((Functor.rightDerivedFunctorPlusCompIso' ((D.j₁)_*[ModuleCat.{u + 1} Λ])
        ((D.u)_*[ModuleCat.{u + 1} Λ])
        (Etale.lowerStarComp _ D.j₁ D.u D.j₂ D.comm.symm)).hom.app K) ≫
      D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map
      ((Functor.rightDerivedFunctorPlusCompIso' ((D.j₁)_*[ModuleCat.{u + 1} Λ])
        ((D.u)_*[ModuleCat.{u + 1} Λ])
        (Etale.lowerStarComp _ D.j₁ D.u D.j₂ D.comm.symm)).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [restrictionIso_hom_app, toLowerStar_app, ← hcounit, hpaste,
    clopenSectionDirectImageIso_hom_app, ← Functor.map_comp_assoc,
    upperStarBLowerShriekIso_hom_app_comp, upperStarBToLowerStar_app]
  simp only [Functor.map_comp, assoc]
  rw [reassoc_of% hcancel, reassoc_of% hnatBC, reassoc_of% hnatC]
  rfl

end ProperOpenDatum

end AlgebraicGeometry
