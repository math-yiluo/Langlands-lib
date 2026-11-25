/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

/-! # Compact-support base change between different fields

Restrict the ambient weakly étale compactification exchange through the fully faithful
bounded constructible inclusions. The resulting square uses the actual chosen compactifications.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}



/-- The bounded cross-field pullback agrees with the ambient left-derived pullback. -/
noncomputable def purityFieldPullbackCompatibility :
    boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') πY ⋙
        (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((πY)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

section Compactification

variable (c : Compactification f.left) (c' : Compactification f'.left)
  {πZ : c'.Z ⟶ c.Z} (hi : IsPullback c'.i πX πZ c.i)
  (hg : IsPullback πZ c'.g c.g πY) [WeaklyEtale πZ] [WeaklyEtale πY]

/-- The ambient compactification exchange in left-derived coordinates. -/
noncomputable def purityFieldCompactificationAmbientExchange :
    Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ L((πY)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((πX)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ Rf_!(c')⟦Profinite.padicAlgClRingObj ℓ⟧ := by
  have : WeaklyEtale πX := MorphismProperty.of_isPullback hi ‹WeaklyEtale πZ›
  exact Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ πY) ≪≫
    rightDerivedLowerShriekOfCompactificationBaseChangeIso _ c c' hi hg ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ πX).symm _

/-- Restriction of compactification base change to the bounded constructible categories. -/
noncomputable def purityFieldCompactificationExchange :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
        boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c' :=
  ObjectProperty.preimageIso_liftSquareWithComparisons
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c')
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (purityFieldCompactificationAmbientExchange ℓ f f' c c' hi hg)

/-- Forgetting the bounded restriction gives the specified ambient exchange, with
the two lower-shriek inclusion comparisons made explicit. -/
lemma purityFieldCompactificationExchange_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((purityFieldCompactificationExchange ℓ f f' c c' hi hg).hom.app K).hom =
      L((πY)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).hom.app K) ≫
      (purityFieldCompactificationAmbientExchange ℓ f f' c c' hi hg).hom.app K.obj ≫
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c').inv.app
        ((boundedConstructibleUpperStarOfMap ℓ πX).obj K) := by
  have he := ObjectProperty.preimageIso_liftSquareWithComparisons_hom_app_hom
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c')
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (purityFieldCompactificationAmbientExchange ℓ f f' c c' hi hg) K
  dsimp only [purityFieldCompactificationExchange]
  exact_mod_proofs he

/-- The same cross-field exchange for the lower-shriek functors chosen by Nagata. -/
noncomputable def purityFieldLowerShriekExchange :
    boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerShriek ℓ f' :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField f) c) _ ≪≫
    purityFieldCompactificationExchange ℓ f f' c c' hi hg ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        c' (compactificationOverField f'))

end Compactification

/-- Compact-support base change for an arbitrary cartesian cross-field square along
weakly étale base change, with both lower-shriek functors chosen by Nagata. -/
noncomputable def purityFieldLowerShriekBaseChange
    (sq : IsPullback πX f'.left f.left πY) [WeaklyEtale πY] :
    boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerShriek ℓ f' :=
  purityFieldLowerShriekExchange ℓ f f' (compactificationOverField f)
    ((compactificationOverField f).ofIsPullback sq)
    ((compactificationOverField f).isPullback_i_ofIsPullback sq).flip
    ((compactificationOverField f).isPullback_g_ofIsPullback sq).flip

end AlgebraicGeometry.ProEtale.CondensedRing
