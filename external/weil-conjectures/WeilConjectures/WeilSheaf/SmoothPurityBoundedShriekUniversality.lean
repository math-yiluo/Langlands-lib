/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothPurityTraceUniversalityTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-! # Universality on the compactification used by geometric descent -/

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

/-- Removing the unit identification from a trace does not affect universality. -/
theorem baseChangedSmoothTrace_without_unit_universal
    [IsIso (smoothUnitBaseChange l f f'
      (purityFieldLowerShriekExchange l f f' (compactificationOverField f) c' hi hg) e.hom)]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    (boundedConstructibleLowerShriekOfCompactification l c').TraceUniversalAt K
      ((purityFieldCompactificationExchange l f f' (compactificationOverField f) c' hi hg).inv.app
          (boundedConstructibleTateTwist l X d (2 * d)) ≫
        (boundedConstructibleUpperStarOfMap l πY).map (smoothTrace l f d)) := by
  let a := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
    c' (compactificationOverField f')
  have hb := Functor.traceUniversalAt_of_iso a
    (baseChangedSmoothTrace l f f'
      (purityFieldLowerShriekExchange l f f' (compactificationOverField f) c' hi hg) e.hom d)
    (bijective_map_comp_baseChangedSmoothTrace l f f'
      (purityFieldLowerShriekExchange l f f' (compactificationOverField f) c' hi hg) e.hom d K)
  have ht := Functor.bijective_map_comp_iso_trace
    (boundedConstructibleLowerShriekOfCompactification l c') (Iso.refl _) e.symm _ hb
  simpa only [Functor.TraceUniversalAt, baseChangedSmoothTrace,
    purityFieldLowerShriekExchange,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id, Category.id_comp, Category.comp_id, a] using ht

/-- The chosen compactification trace is universal on the ambient geometric hom
sets when C9's unit base-change component is invertible. -/
theorem baseChangedSmoothTrace_compactification_universal
    [IsIso (smoothUnitBaseChange l f f'
      (purityFieldLowerShriekExchange l f f' (compactificationOverField f) c' hi hg) e.hom)]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c').TraceUniversalAt
      K.obj
      ((boundedConstructibleLowerShriekOfCompactificationCompatibility l c').inv.app
          ((boundedConstructibleUpperStarOfMap l πX).obj
            (boundedConstructibleTateTwist l X d (2 * d))) ≫
        ((purityFieldCompactificationExchange l f f' (compactificationOverField f) c' hi hg).inv.app
          (boundedConstructibleTateTwist l X d (2 * d))).hom ≫
        ((boundedConstructibleUpperStarOfMap l πY).map (smoothTrace l f d)).hom) := by
  exact Functor.traceUniversalAt_of_fullyFaithful (boundedConstructible _).ι
    (boundedConstructible _).ι (boundedConstructibleLowerShriekOfCompactificationCompatibility l c')
    _ K (baseChangedSmoothTrace_without_unit_universal l f f' c' hi hg e d K)

end AlgebraicGeometry.ProEtale.CondensedRing
