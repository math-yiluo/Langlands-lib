/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnitComplex
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonCounit

/-!
# The site comparison and the units of the direct image adjunctions

Let `f : U ⟶ V` be a quasi-compact quasi-separated morphism of schemes and `ν^*` the comparison
from the étale to the pro-étale site. On bounded below complexes, `ν^*` commutes with the derived
pullbacks (`ProEtale.leftDerivedUpperStarComparisonIso`) and with the derived direct images
(`ProEtale.rightDerivedLowerStarComparisonIso'`), compatibly with the counits of the adjunctions
`f^* ⊣ Rf_*` (`ProEtale.ComparisonCore.comparison_counit`). Hence the two comparisons are also
compatible with the units (`ProEtale.comparison_unit`): `ν^*` of the étale unit
`G ⟶ Rf_* f^* G`, followed by the comparisons, is the pro-étale unit at `ν^* G`. For an arbitrary
morphism `f` the same holds on `D⁺` for the canonical base change morphism
`ν^* R⁺f_* ⟶ R⁺f_* ν^*` of right derived functors (`ProEtale.comparison_unit_plus`).

As an application, the pro-étale nearby cycles of a constant complex on a strictly henselian local
ring are trivial: for a strictly henselian local ring `R`, a morphism `t : Spec Ω ⟶ Spec R` from
the spectrum of a separably closed field, a map `b : R ⟶ κ` to a field with kernel the maximal
ideal and a bounded below complex `G` of étale sheaves on `Spec R` with constant cohomology
sheaves, the pullback along `Spec b` of the pro-étale unit `ν^* G ⟶ Rt_* Lt^* ν^* G` is an
isomorphism (`ProEtale.isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology`). This is
the étale statement
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_app_of_isConstant_homology`) transported along
`ν^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

/-- **Transport of units along comparison functors.** Let `e : l ⊣ r` and `d : p ⊣ s` be
adjunctions, `A₀`, `A₁` comparison functors with an isomorphism `a : l ⋙ A₁ ≅ A₀ ⋙ p` of left
adjoints and a map `b : r ⋙ A₀ ⟶ A₁ ⋙ s` of right adjoints compatible with the counits (`hb`).
Then `A₀` of the unit of `e`, followed by `b` and `s` of `a`, is the unit of `d`. -/
theorem CategoryTheory.Adjunction.map_unit_comp_eq_unit {E₀ E₁ P₀ P₁ : Type*}
    [Category E₀] [Category E₁] [Category P₀] [Category P₁]
    {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} (e : l ⊣ r) (d : p ⊣ s)
    {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} (a : l ⋙ A₁ ≅ A₀ ⋙ p) (b : r ⋙ A₀ ⟶ A₁ ⋙ s)
    (hb : ∀ K, a.hom.app (r.obj K) ≫ p.map (b.app K) ≫ d.counit.app (A₁.obj K) =
      A₁.map (e.counit.app K)) (G : E₀) :
    A₀.map (e.unit.app G) ≫ b.app (l.obj G) ≫ s.map (a.hom.app G) = d.unit.app (A₀.obj G) := by
  apply (d.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [d.counit_naturality, reassoc_of% ((Iso.eq_inv_comp (a.app _)).2 (hb (l.obj G)))]
  have hn := a.inv.naturality (e.unit.app G)
  simp only [Functor.comp_map] at hn
  rw [Iso.app_inv, reassoc_of% hn, ← A₁.map_comp_assoc, e.left_triangle_components,
    A₁.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact (d.left_triangle_components _).symm

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The site comparison and the units**: for a quasi-compact quasi-separated `f : U ⟶ V` and
`G ∈ D⁺(V_ét)`, `ν^*` of the étale unit `G ⟶ Rf_* f^* G`, followed by the comparisons
`ν^* Rf_* ≅ Rf_* ν^*` and `ν^* f^* ≅ Lf^* ν^*`, is the pro-étale unit
`ν^* G ⟶ Rf_* Lf^* ν^* G`. -/
theorem comparison_unit {U V : Scheme.{u}} (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f]
    (G : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ])).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app G) ≫
      (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map
        ((leftDerivedUpperStarComparisonIso f Λ).hom.app G) =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ])).obj G) :=
  Adjunction.map_unit_comp_eq_unit
    (A₀ := DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
    (A₁ := DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ]))
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (leftDerivedUpperStarComparisonIso f Λ)
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom
    (ComparisonCore.comparison_counit Λ f) G

/-- **The canonical comparison of direct images and the units**, on bounded below derived
categories and for an arbitrary morphism `f : U ⟶ V`: `ν_V^*` of the étale unit
`G ⟶ R⁺f_* f^* G`, followed by the canonical base change morphism
`ν_V^* R⁺f_* f^* G ⟶ R⁺f_* ν_U^* f^* G` of right derived functors
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusBaseChange`) and `R⁺f_*` of the
pullback comparison `ν_U^* f^* G ≅ f^* ν_V^* G`, is the pro-étale unit
`ν_V^* G ⟶ R⁺f_* f^* ν_V^* G`. No hypothesis on `f` is needed: this is the unit form of the
counit compatibility `AlgebraicGeometry.ProEtale.ComparisonCore.comparison_counit_plus`. -/
theorem comparison_unit_plus {U V : Scheme.{u}} (f : U ⟶ V)
    (G : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let a := (Functor.mapDerivedCategoryPlusCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
      (upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
    D+(ν^*(V)[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app G) ≫
      (rightDerivedLowerStarComparisonPlusBaseChange f (ModuleCat.{u + 1} Λ)).app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
      R+(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map (a.inv.app G) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
      (D+(ν^*(V)[ModuleCat.{u + 1} Λ]).obj G) := by
  intro a
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  exact Adjunction.map_unit_comp_eq_unit
    (A₀ := D+(ν^*(V)[ModuleCat.{u + 1} Λ]))
    (A₁ := D+(ν^*(U)[ModuleCat.{u + 1} Λ]))
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
    a.symm
    (rightDerivedLowerStarComparisonPlusBaseChange f (ModuleCat.{u + 1} Λ))
    (ComparisonCore.comparison_counit_plus Λ f) G

/-- **Pro-étale nearby cycles of constant complexes over a strictly henselian local ring**: let
`R` be a strictly henselian local ring, `t : Spec Ω ⟶ Spec R` a morphism from the spectrum of a
separably closed field and `b : R ⟶ κ` a map to a field with kernel the maximal ideal. For a
bounded below complex `G` of étale sheaves of `Λ`-modules on `Spec R` with constant cohomology
sheaves, the pullback along `Spec b` of the pro-étale unit `ν^* G ⟶ Rt_* Lt^* ν^* G` is an
isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
    {κ : Type u} [Field κ] (b : R →+* κ) (hb : RingHom.ker b = IsLocalRing.maximalIdeal R)
    (G : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : ∀ q, Sheaf.IsConstant (Spec (.of R)).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj G)) :
    IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b))).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Spec (.of R))[ModuleCat.{u + 1} Λ])).obj G))) := by
  have : IsLocalHom b := ⟨fun x hx ↦ by
    by_contra h
    have hx0 : b x = 0 := (RingHom.mem_ker).1 (hb ▸ (IsLocalRing.mem_maximalIdeal x).2 h)
    rw [hx0] at hx
    exact not_isUnit_zero hx⟩
  have hs : Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.lift b)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.lift_comp_residue]
  have hη : IsIso (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b))).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app G)) := by
    have := Etale.isIso_upperStar_map_unit_app_of_isConstant_homology Λ R t G hG
    rw [hs, NatIso.isIso_map_iff (Etale.upperStarPlusComp _ _ _), Functor.comp_map]
    infer_instance
  have hν : IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b))).map
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(Spec (.of R))[ModuleCat.{u + 1} Λ])).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app G))) :=
    (NatIso.isIso_map_iff
      (leftDerivedUpperStarComparisonIso (Spec.map (CommRingCat.ofHom b)) Λ)
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app G)).1
      (by
        rw [Functor.comp_map]
        infer_instance)
  rw [← comparison_unit Λ t G, Functor.map_comp, Functor.map_comp]
  infer_instance

end AlgebraicGeometry.ProEtale
