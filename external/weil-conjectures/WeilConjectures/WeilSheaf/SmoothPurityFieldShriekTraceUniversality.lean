/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldShriekCoordinates

/-! # The actual geometric smooth trace is universal under unit base change -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (c' : Compactification f'.left)
  {πZ : c'.Z ⟶ (compactificationOverField f).Z}
  (hi : IsPullback c'.i πX πZ (compactificationOverField f).i)
  (hg : IsPullback πZ c'.g (compactificationOverField f).g πY)
  [WeaklyEtale πZ] [WeaklyEtale πY]
  (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ≅ 𝟙_ _)
  (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- Unit base change proves universality in the ambient left-derived coordinates. -/
theorem baseChangedSmoothTrace_ambient_universal
    [IsIso (smoothUnitBaseChange l f f'
      (purityFieldLowerShriekExchange l f f' (compactificationOverField f) c' hi hg) e.hom)]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c').TraceUniversalAt
      K.obj
      ((purityFieldCompactificationAmbientExchange l f f' (compactificationOverField f) c' hi
        hg).inv.app
          (boundedConstructibleTateTwist l X d (2 * d)).obj ≫
        (upperStar (Profinite.padicAlgClRingObj l) πY).leftDerivedFunctor.map
          ((boundedConstructibleLowerShriekOfCompactificationCompatibility l
            (compactificationOverField f)).inv.app (boundedConstructibleTateTwist l X d (2 * d)) ≫
            (smoothTrace l f d).hom)) := by
  have ht := baseChangedSmoothTrace_compactification_universal l f f' c' hi hg e d K
  rw [purityFieldCompactificationTrace_coordinates] at ht
  refine Functor.traceUniversalAt_of_coordinates
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c')
    ((purityFieldPullbackCompatibility l (πY := πX)).app
      (boundedConstructibleTateTwist l X d (2 * d)))
    ((purityFieldPullbackCompatibility l (πY := πY)).app (𝟙_ _)) _ ?_
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using ht

/-- Pass from left-derived to levelwise pullback coordinates, as used by the
specified geometric descent comparison. -/
theorem baseChangedSmoothTrace_levelwise_universal
    [IsIso (smoothUnitBaseChange l f f'
      (purityFieldLowerShriekExchange l f f' (compactificationOverField f) c' hi hg) e.hom)]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c').TraceUniversalAt
      K.obj
      ((rightDerivedLowerShriekOfCompactificationBaseChangeIso (Profinite.padicAlgClRingObj l)
          (compactificationOverField f) c' hi hg).inv.app
          (boundedConstructibleTateTwist l X d (2 * d)).obj ≫
        (upperStar (Profinite.padicAlgClRingObj l) πY).mapDerivedCategory.map
          ((boundedConstructibleLowerShriekOfCompactificationCompatibility l
            (compactificationOverField f)).inv.app (boundedConstructibleTateTwist l X d (2 * d)) ≫
            (smoothTrace l f d).hom)) := by
  have : WeaklyEtale πX := MorphismProperty.of_isPullback hi ‹WeaklyEtale πZ›
  have ht := Functor.bijective_map_comp_iso_trace
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c')
    ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πX).symm.app
      (boundedConstructibleTateTwist l X d (2 * d)).obj)
    ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πY).app
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧)).obj) _
    (baseChangedSmoothTrace_ambient_universal l f f' c' hi hg e d K)
  simp only [purityFieldCompactificationAmbientExchange, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Iso.app_hom, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at ht
  rw [(leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πY).hom.naturality,
    Iso.inv_hom_id_app_assoc] at ht
  exact ht

end AlgebraicGeometry.ProEtale.CondensedRing
