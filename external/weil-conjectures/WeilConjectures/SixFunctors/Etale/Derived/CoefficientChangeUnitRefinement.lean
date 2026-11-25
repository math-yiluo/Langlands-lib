/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement

/-!
# The comparison of derived lower shrieks along a refinement and restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of finite coefficient rings and `r : c.Refinement d` a
refinement of compactifications of `f : X ⟶ Y` whose square over `X` is cartesian. The
comparison `Rf_!(d) ⟶ Rf_!(c)` of the unbounded derived lower shrieks
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`) is compatible
with the coefficient comparisons of `Rf_!(c)` and `Rf_!(d)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison_app_restrictScalars`).
This is used for the compatible systems of Frobenius coefficient morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The base change comparison `(c.i)_! ⟶ (d.i)_! ⋙ (r.hom)^*` of a refinement is compatible
with the coefficient comparisons of the extensions by zero and of the pullback. -/
lemma refinementOpenImmersionLowerShriekBaseChange_app_restrictScalars
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (openImmersionLowerShriekRestrictScalarsIso ρ c.i).hom.app N ≫
        (Sheaf.restrictScalars c.Z.smallEtaleTopology ρ).map
          ((r.openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ')).app N) =
      (r.openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ)).app
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj N) ≫
        (r.hom)^*[ModuleCat.{u + 1} Λ].map
          ((openImmersionLowerShriekRestrictScalarsIso ρ d.i).hom.app N) ≫
        (upperStarRestrictScalarsIso ρ r.hom).hom.app
          ((d.i)_!open[ModuleCat.{u + 1} Λ'].obj N) := by
  have hs := openImmersionLowerShriekBaseChangeMap_app_restrictScalars ρ
    (⟨by simp [r.i_hom]⟩ : CommSq (𝟙 X) c.i d.i r.hom) N
  rw [Etale.openImmersionLowerShriekBaseChangeMap_id_left (ModuleCat.{u + 1} Λ') c.i r.hom d.i
    r.i_hom, Etale.openImmersionLowerShriekBaseChangeMap_id_left (ModuleCat.{u + 1} Λ) c.i r.hom
    d.i r.i_hom] at hs
  have hid := congr_app (upperStarRestrictScalarsIso_id_hom ρ X) N
  have hn := (openImmersionLowerShriekRestrictScalarsIso ρ c.i).hom.naturality
    ((upperStarId (ModuleCat.{u + 1} Λ') X).hom.app N)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id, Category.id_comp,
    Functor.map_comp, Category.assoc, Functor.comp_map] at hs hid hn
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, hid] at hs
  exact (cancel_epi _).1 hs

/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*` of a refinement with
cartesian square over `X` is compatible with the coefficient comparisons. -/
lemma refinementLowerShriekBaseChangeDerivedIso_hom_app_restrictScalars
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i).hom.app K ≫
        (Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology ρ).map
          ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} Λ') r hcart).hom.app K) =
      (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} Λ) r hcart).hom.app
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K) ≫
        D((r.hom)^*[ModuleCat.{u + 1} Λ]).map
          ((derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ d.i).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ r.hom)).hom.app
          (D((d.i)_!open[ModuleCat.{u + 1} Λ']).obj K) := by
  have := r.isIso_openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ) hcart
  have := r.isIso_openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ') hcart
  exact Functor.mapDerivedCategorySquareIso_hom_app_comp
    (openImmersionLowerShriekRestrictScalarsIso ρ d.i) (upperStarRestrictScalarsIso ρ r.hom)
    (openImmersionLowerShriekRestrictScalarsIso ρ c.i)
    (asIso (r.openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ)))
    (asIso (r.openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ')))
    (refinementOpenImmersionLowerShriekBaseChange_app_restrictScalars ρ r) K

variable (dq ddg dcg : ℕ)
  (hdq : ∀ (F : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), dq < q →
    IsZero ((((r.hom)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
  (hddg : ∀ (F : Sheaf d.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), ddg < q →
    IsZero ((((d.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
  (hdcg : ∀ (F : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), dcg < q →
    IsZero ((((c.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))

/-- The composition isomorphism `R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*` of a refinement is
compatible with the coefficient comparisons of the derived direct images. -/
lemma rightDerivedFunctorCompIso'_refinementLowerStarComp_hom_app_restrictScalars
    (M : DerivedCategory (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    R((d.g)_*[ModuleCat.{u + 1} Λ]).map
        ((derivedRestrictScalarsCompRightDerivedLowerStarIso ρ r.hom dq hdq).hom.app M) ≫
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ d.g ddg hddg).hom.app
        (R((r.hom)_*[ModuleCat.{u + 1} Λ']).obj M) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
        ((Functor.rightDerivedFunctorCompIso' (r.hom)_*[ModuleCat.{u + 1} Λ']
          (d.g)_*[ModuleCat.{u + 1} Λ'] (refinementLowerStarComp _ r)).hom.app M) =
    (Functor.rightDerivedFunctorCompIso' (r.hom)_*[ModuleCat.{u + 1} Λ]
          (d.g)_*[ModuleCat.{u + 1} Λ] (refinementLowerStarComp _ r)).hom.app
        ((Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology ρ).obj M) ≫
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g dcg hdcg).hom.app M := by
  rw [rightDerivedFunctorCompIso'_refinementLowerStarComp_hom,
    rightDerivedFunctorCompIso'_refinementLowerStarComp_hom]
  exact Adjunction.conjugateEquiv_comp_restrict
    (mapDerivedUpperStarLowerStarAdjunction _ r.hom)
    (mapDerivedUpperStarLowerStarAdjunction _ d.g) (mapDerivedUpperStarLowerStarAdjunction _ c.g)
    (mapDerivedUpperStarLowerStarAdjunction _ r.hom)
    (mapDerivedUpperStarLowerStarAdjunction _ d.g) (mapDerivedUpperStarLowerStarAdjunction _ c.g)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ r.hom))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ r.hom dq hdq)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ d.g))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ d.g ddg hddg)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ c.g))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g dcg hdcg)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ r.hom dq hdq)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ d.g ddg hddg)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ c.g dcg hdcg) _ _
    (Functor.mapDerivedCategorySquareIso_hom_app_comp (upperStarRestrictScalarsIso ρ d.g)
      (upperStarRestrictScalarsIso ρ r.hom) (upperStarRestrictScalarsIso ρ c.g)
      (upperStarComp _ r.hom d.g c.g r.hom_g.symm) (upperStarComp _ r.hom d.g c.g r.hom_g.symm)
      (upperStarRestrictScalarsIso_hom_app_comp_upperStarComp ρ r.hom d.g c.g r.hom_g.symm))
    M

/-- **The comparison of derived lower shrieks along a refinement is compatible with restriction
of scalars** (statement (C)): for a refinement `r : c.Refinement d` of compactifications of
`f : X ⟶ Y` over a quasi-compact base whose square over `X` is cartesian, and finite
coefficients `Λ`, the comparisons `Rf_!(d) ⟶ Rf_!(c)` over `Λ` and over `Λ'` are related by the
coefficient comparisons of `Rf_!(c)` and `Rf_!(d)`, built from bounds `dc` and `dd` for the
higher direct images along `c.g` and `d.g`. -/
lemma rightDerivedLowerShriekOfCompactificationComparison_app_restrictScalars [Finite Λ]
    [CompactSpace Y] (hcart : IsPullback c.i (𝟙 X) r.hom d.i) (dc dd : ℕ)
    (hdc : ∀ (F : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), dc < q →
      IsZero ((((c.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hdd : ∀ (F : Sheaf d.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), dd < q →
      IsZero ((((d.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ d.i)
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ d.g dd hdd)).hom.app K ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
        ((rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ') r
          hcart).app K) =
    (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ) r hcart).app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K) ≫
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g dc hdc)).hom.app K := by
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  obtain ⟨dq, hdq⟩ :=
    exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ isAddTorsion_of_finite r.hom
  rw [pasteTwoSquaresIso_hom_app, pasteTwoSquaresIso_hom_app]
  exact Adjunction.comparison_restrict (mapDerivedUpperStarLowerStarAdjunction _ r.hom)
    (mapDerivedUpperStarLowerStarAdjunction _ r.hom)
    (refinementLowerShriekBaseChangeDerivedIso _ r hcart)
    (refinementLowerShriekBaseChangeDerivedIso _ r hcart)
    (Functor.rightDerivedFunctorCompIso' _ _ (refinementLowerStarComp _ r))
    (Functor.rightDerivedFunctorCompIso' _ _ (refinementLowerStarComp _ r))
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ d.i)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ r.hom))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ r.hom dq hdq)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ d.g dd hdd)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g dc hdc)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ r.hom dq hdq)
    (refinementLowerShriekBaseChangeDerivedIso_hom_app_restrictScalars ρ r hcart)
    (rightDerivedFunctorCompIso'_refinementLowerStarComp_hom_app_restrictScalars ρ r dq dd dc hdq
      hdd hdc) K

end AlgebraicGeometry.Etale
