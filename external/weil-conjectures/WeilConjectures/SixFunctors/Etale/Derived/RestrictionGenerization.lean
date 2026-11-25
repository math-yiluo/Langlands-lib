/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.ExactSectionsRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.StrictLocalizationPoints
public import WeilConjectures.SixFunctors.Etale.Derived.StrictlyHenselianConstantSections
public import WeilConjectures.SixFunctors.Etale.Derived.UnitCompVanishing

/-!
# Vanishing of restriction maps by generization

Let `Y` be an irreducible scheme, `z` a closed point of `Y` and `N ∈ D(Y_ét, Λ)` a complex whose
stalks at the geometric points over `z` vanish and whose restriction to `Y - z` has locally
constant cohomology sheaves. Then for every geometric point `s̄` of `Y` not over `z`, the
restriction map `RΓ(Y, N) ⟶ N_s̄` is zero in `D(Λ)`.

Choose a geometric point `η̄` over the generic point of `Y` and specializations of `η̄` to `s̄` and
to a geometric point `z̄` over `z`, i.e. lifts of `η̄` to the strict localizations `Y_(s̄)` and
`Y_(z̄)`. Naturality of restriction gives the commutative square

```
RΓ(Y, N) ──▶ N_s̄
   │          │ ≅
   ▼          ▼
  N_z̄ = 0 ──▶ N_η̄
```

whose right arrow, the specialization map, is an isomorphism because the cohomology sheaves of
`N` are locally constant on the strictly local scheme `Y_(s̄)`, which lies over `Y - z`. Hence the
upper arrow is zero (blueprint `lemma-cohomology-near-two-transverse-divisors`, last step).

## Main statements

- `AlgebraicGeometry.Etale.derivedGlobalSectionsRestriction_eq_zero_of_isZero_of_isLocallyConstant`

## Implementation notes

Instead of the square above we work with the derived global sections `RΓ(Y, η_t(N))` of the
units `η_t(N) : N ⟶ Rt_* t^* N`, whose vanishing implies that of the restriction map along `t`.
Along a composite these units compose
(`AlgebraicGeometry.Etale.rightDerivedGlobalSections_map_unit_comp_eq_zero`,
`AlgebraicGeometry.Etale.rightDerivedGlobalSections_map_unit_eq_zero_of_comp`). The geometric
points `η̄` through `Y_(s̄)` and through `Y_(z̄)` need not be the same: they only need to have
the same image point, the generic point of `Y`
(`AlgebraicGeometry.Etale.rightDerivedGlobalSections_map_unit_eq_zero_of_apply_eq`). The
boundedness of `N` is not used.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The restriction map along `f` vanishes as soon as the derived global sections of the unit of
`f^* ⊣ Rf_*` vanish. -/
lemma derivedGlobalSectionsRestriction_eq_zero_of_map_unit_eq_zero {X X' : Scheme.{u}}
    (f : X' ⟶ X) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : (rightDerivedGlobalSections _ X).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K) = 0) :
    derivedGlobalSectionsRestriction Λ f K = 0 := by
  rw [derivedGlobalSectionsRestriction, derivedUpperStarLowerStarAdjunction_eq,
    Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.map_comp, h, zero_comp, zero_comp]

/-- **Vanishing on the strict localization at a point where the stalks vanish.** Let
`s : Spec Ω ⟶ S` be a geometric point and `N ∈ D(S_ét, Λ)` whose pullback to every geometric
point with the same image as `s` vanishes. Then the derived global sections of the unit
`N ⟶ Rg_* g^* N` along the strict localization `g : S_(s) ⟶ S` vanish: its target is
`RΓ(S_(s), g^* N) = 0`. -/
theorem rightDerivedGlobalSections_map_unit_strictLocalizationToBase_eq_zero {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : ∀ (κ : Type u) [Field κ] [IsSepClosed κ] (t : Spec (.of κ) ⟶ S),
      (∀ x, t x = s (IsLocalRing.closedPoint Ω)) →
        IsZero ((D((t)^*[ModuleCat.{u + 1} Λ])).obj N)) :
    (rightDerivedGlobalSections _ S).map ((mapDerivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) (strictLocalizationToBase s)).unit.app N) = 0 := by
  let π := strictLocalizationToBase s
  let r := closedGeometricPoint (strictHenselization s)
  have : PreservesFiniteColimits
      (Sheaf.Γ (strictLocalization s).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    preservesFiniteColimits_Γ_of_isStrictlyHenselianLocalRing (strictHenselization s)
  have hZ : IsZero ((rightDerivedGlobalSections _ (strictLocalization s)).obj
      ((D((π)^*[ModuleCat.{u + 1} Λ])).obj N)) := by
    refine isZero_rightDerivedGlobalSections_obj _ _ fun n ↦ ?_
    let G := (DerivedCategory.homologyFunctor _ n).obj ((D((π)^*[ModuleCat.{u + 1} Λ])).obj N)
    have : IsIso (globalSectionsUpperStarMap _ r G) :=
      Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ
        (IsLocalRing.maximalIdeal (strictHenselization s)) (𝟙 _) _ (𝟙 _)
        (IsPullback.id_vert _) G
    refine IsZero.of_iso (Functor.map_isZero _ ?_) (asIso (globalSectionsUpperStarMap _ r G))
    refine IsZero.of_iso (Functor.map_isZero (DerivedCategory.homologyFunctor _ n) ?_)
      (((r)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso n).app
        ((D((π)^*[ModuleCat.{u + 1} Λ])).obj N))
    refine IsZero.of_iso (hN _ (r ≫ π) fun x ↦ ?_)
      ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp _ r π) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).app N).symm
    rw [Scheme.Hom.comp_apply, closedGeometricPoint_apply]
    exact strictLocalizationToBase_apply_closedPoint s
  exact (hZ.of_iso ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ π).app _)).eq_of_tgt
    _ _

/-- **The vanishing of a restriction map only depends on the image point.** Let `t₁`, `t₂` be
geometric points of `Y` with the same image. If the derived global sections of the unit
`N ⟶ Rt₂_* t₂^* N` vanish, then so do those of `N ⟶ Rt₁_* t₁^* N`: both geometric points
become equal after restriction to a common algebraically closed field, and the restriction
along a morphism of spectra of separably closed fields is an isomorphism. -/
theorem rightDerivedGlobalSections_map_unit_eq_zero_of_apply_eq {Y : Scheme.{u}}
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {K₁ K₂ : Type u} [Field K₁] [IsSepClosed K₁] [Field K₂] [IsSepClosed K₂]
    (t₁ : Spec (.of K₁) ⟶ Y) (t₂ : Spec (.of K₂) ⟶ Y)
    (h : t₁ (IsLocalRing.closedPoint K₁) = t₂ (IsLocalRing.closedPoint K₂))
    (h₂ : (rightDerivedGlobalSections _ Y).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₂).unit.app N) = 0) :
    (rightDerivedGlobalSections _ Y).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₁).unit.app N) = 0 := by
  obtain ⟨Ω, _, _, a, b, hab⟩ := exists_comp_eq_comp_of_apply_closedPoint_eq t₁ t₂ h
  refine rightDerivedGlobalSections_map_unit_eq_zero_of_comp _ t₁ a N ?_ ?_
  · rw [hab]
    exact rightDerivedGlobalSections_map_unit_comp_eq_zero _ t₂ b N h₂
  · exact isIso_rightDerivedGlobalSections_map_unit_of_isIso _ a _ fun n ↦
      isIso_globalSectionsUpperStarMap_of_isSepClosed a _

/-- **Vanishing of restriction maps by generization** (blueprint
`lemma-cohomology-near-two-transverse-divisors`, the generization square): let `Y` be an irreducible
scheme, `z` a closed point of `Y` and `N ∈ D(Y_ét, Λ)` such that `N_z̄ = 0` for the geometric points
`z̄` over `z` and the restriction of `N` to `Y - z` has locally constant cohomology sheaves. Then
for every geometric point `s̄` of `Y` not over `z`, the restriction map `RΓ(Y, N) ⟶ N_s̄` is
zero. -/
theorem derivedGlobalSectionsRestriction_eq_zero_of_isZero_of_isLocallyConstant
    {Y : Scheme.{u}} [IrreducibleSpace Y] (z : Y) (hz : IsClosed ({z} : Set Y))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hNz : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (zbar : Spec (.of Ω) ⟶ Y),
      Set.range zbar = {z} → IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj N))
    (hNloc : ∀ n : ℤ, IsLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((L((Opens.ι ⟨({z} : Set Y)ᶜ, hz.isOpen_compl⟩)^*[ModuleCat.{u + 1} Λ])).obj N)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (sbar : Spec (.of Ω) ⟶ Y)
    (hs : z ∉ Set.range sbar) :
    derivedGlobalSectionsRestriction Λ sbar N = 0 := by
  apply derivedGlobalSectionsRestriction_eq_zero_of_map_unit_eq_zero
  let U : Y.Opens := ⟨({z} : Set Y)ᶜ, hz.isOpen_compl⟩
  -- the strict localization `Y_(s̄)` at `s̄`, through its closed point
  let π := strictLocalizationToBase sbar
  rw [← spec_map_strictHenselizationEval_comp_strictLocalizationToBase sbar]
  refine rightDerivedGlobalSections_map_unit_comp_eq_zero _ π _ N ?_
  -- a geometric point `e` of `Y_(s̄)` over the generic point of `Y`
  obtain ⟨p, hp⟩ := exists_strictLocalizationToBase_apply_eq sbar
    (genericPoint_specializes (sbar (IsLocalRing.closedPoint Ω)))
  obtain ⟨K, _, _, e, he⟩ := exists_isAlgClosed_apply_closedPoint_eq p
  refine rightDerivedGlobalSections_map_unit_eq_zero_of_comp _ π e N ?_ ?_
  · -- the strict localization `Y_(z̄)` at a geometric point `z̄` over `z`
    obtain ⟨Kz, _, _, zbar, hzbar⟩ := exists_isAlgClosed_apply_closedPoint_eq z
    obtain ⟨p', hp'⟩ := exists_strictLocalizationToBase_apply_eq zbar
      (genericPoint_specializes (zbar (IsLocalRing.closedPoint _)))
    obtain ⟨K', _, _, e', he'⟩ := exists_isAlgClosed_apply_closedPoint_eq p'
    refine rightDerivedGlobalSections_map_unit_eq_zero_of_apply_eq Λ N (e ≫ π)
      (e' ≫ strictLocalizationToBase zbar) ?_ ?_
    · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he, he']
      exact hp.trans hp'.symm
    refine rightDerivedGlobalSections_map_unit_comp_eq_zero _ _ _ N ?_
    refine rightDerivedGlobalSections_map_unit_strictLocalizationToBase_eq_zero Λ zbar N
      fun κ _ _ t ht ↦ ?_
    refine (hNz κ t ?_).of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) t).app N).symm
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint κ, ?_⟩, ?_⟩
    · rw [ht, hzbar]
    · rintro _ ⟨x, rfl⟩
      rw [ht, hzbar]
  · -- the restriction from `Y_(s̄)` to `e` is an isomorphism
    have : PreservesFiniteColimits
        (Sheaf.Γ (strictLocalization sbar).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      preservesFiniteColimits_Γ_of_isStrictlyHenselianLocalRing (strictHenselization sbar)
    refine isIso_rightDerivedGlobalSections_map_unit_of_isIso _ e _ fun n ↦ ?_
    -- `Y_(s̄)` maps to `Y - z`
    have hπ : Set.range π ⊆ Set.range U.ι := by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      intro hq
      have hq' : π q = z := hq
      have hs' := strictLocalizationToBase_specializes sbar q
      rw [hq'] at hs'
      exact hs ⟨IsLocalRing.closedPoint Ω, hs'.mem_closed hz rfl⟩
    let πU := IsOpenImmersion.lift U.ι π hπ
    have hπU : πU ≫ U.ι = π := IsOpenImmersion.lift_fac _ _ _
    have h₁ : IsLocallyConstantSheaf ((L((U.ι)^*[ModuleCat.{u + 1} Λ]) ⋙
        DerivedCategory.homologyFunctor _ n).obj N) := hNloc n
    have h₂ := IsLocallyConstantSheaf.upperStar πU ((L((U.ι)^*[ModuleCat.{u + 1} Λ]) ⋙
        DerivedCategory.homologyFunctor _ n).obj N)
    have : IsLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
        ((D((π)^*[ModuleCat.{u + 1} Λ])).obj N)) :=
      IsLocallyConstantSheaf.of_iso
        ((πU)^*[ModuleCat.{u + 1} Λ].mapIso
          ((leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} Λ) U.ι n).app N).symm ≪≫
        ((Etale.upperStarComp _ πU U.ι π hπU.symm).app _).symm ≪≫
        (((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app N)
    exact isIso_globalSectionsUpperStarMap_of_isLocallyConstantSheaf
      (R := ↥(strictHenselization sbar)) e _

end AlgebraicGeometry.Etale
