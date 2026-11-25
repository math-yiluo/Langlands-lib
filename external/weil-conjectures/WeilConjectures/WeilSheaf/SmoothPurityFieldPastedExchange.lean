/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquarePasting

/-! # The bounded compactification exchange is the paste of its two restrictions -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

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
  (c : Compactification f.left) (c' : Compactification f'.left)
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left} {πZ : c'.Z ⟶ c.Z}
  (hi : IsPullback c'.i πX πZ c.i) (hg : IsPullback πZ c'.g c.g πY)
  [WeaklyEtale πZ] [WeaklyEtale πY]

/-- The open exchange in the left-derived pullback coordinates used by `Dᵇc`. -/
noncomputable def purityFieldOpenAmbientExchange :
    D((c.i)_!open⟦Profinite.padicAlgClRingObj l⟧) ⋙
        L((πZ)^*⟦Profinite.padicAlgClRingObj l⟧) ≅
      L((πX)^*⟦Profinite.padicAlgClRingObj l⟧) ⋙
        D((c'.i)_!open⟦Profinite.padicAlgClRingObj l⟧) := by
  have : WeaklyEtale πX := MorphismProperty.of_isPullback hi ‹WeaklyEtale πZ›
  exact Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ πZ) ≪≫
    openImmersionLowerShriekMapDerivedCategoryBaseChangeIso _ hi ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ πX).symm _

/-- The proper exchange in the same left-derived pullback coordinates. -/
noncomputable def purityFieldProperAmbientExchange :
    R((c.g)_*⟦Profinite.padicAlgClRingObj l⟧) ⋙
        L((πY)^*⟦Profinite.padicAlgClRingObj l⟧) ≅
      L((πZ)^*⟦Profinite.padicAlgClRingObj l⟧) ⋙
        R((c'.g)_*⟦Profinite.padicAlgClRingObj l⟧) :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ πY) ≪≫
    rightDerivedLowerStarBaseChangeIso _ hg ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ πZ).symm _

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The ambient compactification exchange pastes the open and proper exchanges; the
left-derived/levelwise comparison at the compactifying scheme cancels. -/
lemma purityFieldCompactificationAmbientExchange_eq_paste :
    purityFieldCompactificationAmbientExchange l f f' c c' hi hg =
      Adjunction.compForgetIso
        (purityFieldOpenAmbientExchange l f f' c c' hi)
        (purityFieldProperAmbientExchange l f f' c c' hg) := by
  have : WeaklyEtale πX := MorphismProperty.of_isPullback hi ‹WeaklyEtale πZ›
  exact (Adjunction.compForgetIso_conjugate
    (leftDerivedUpperStarIsoMapDerivedCategory _ πX)
    (leftDerivedUpperStarIsoMapDerivedCategory _ πZ)
    (leftDerivedUpperStarIsoMapDerivedCategory _ πY)
    (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso _ hi)
    (rightDerivedLowerStarBaseChangeIso _ hg)).symm

/-- The specified open exchange restricted to bounded constructible complexes. -/
noncomputable def purityFieldOpenRestrictedExchange :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj l) l c.overI ⋙
        boundedConstructibleUpperStarOfMap l (X := c.overObj) (Y := c'.overObj) πZ ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := X') πX ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj l) l c'.overI :=
  ObjectProperty.preimageIso_liftSquareWithComparisons
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ l c.overI)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ l c'.overI)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj K.property)
    (purityFieldOpenAmbientExchange l f f' c c' hi)

/-- The specified proper exchange restricted to bounded constructible complexes. -/
noncomputable def purityFieldProperRestrictedExchange :
    boundedConstructibleLowerStar l c.overG ⋙
        boundedConstructibleUpperStarOfMap l (X := Y) (Y := Y') πY ≅
      boundedConstructibleUpperStarOfMap l (X := c.overObj) (Y := c'.overObj) πZ ⋙
        boundedConstructibleLowerStar l c'.overG :=
  ObjectProperty.preimageIso_liftSquareWithComparisons
    (boundedConstructibleLowerStarCompatibility l c.overG)
    (boundedConstructibleLowerStarCompatibility l c'.overG)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (purityFieldProperAmbientExchange l f f' c c' hg)

/-- Restriction of the specified ambient compactification exchange is exactly the
paste of the restrictions of its two factors. -/
lemma purityFieldCompactificationExchange_eq_paste :
    purityFieldCompactificationExchange l f f' c c' hi hg =
      Adjunction.compForgetIso
        (purityFieldOpenRestrictedExchange l f f' c c' hi)
        (purityFieldProperRestrictedExchange l f f' c c' hg) := by
  rw [purityFieldCompactificationExchange,
    purityFieldCompactificationAmbientExchange_eq_paste]
  have he := ObjectProperty.preimageIso_liftSquareWithComparisons_comp
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ l c.overI)
    (boundedConstructibleLowerStarCompatibility l c.overG)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ l c'.overI)
    (boundedConstructibleLowerStarCompatibility l c'.overG)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (purityFieldOpenAmbientExchange l f f' c c' hi)
    (purityFieldProperAmbientExchange l f f' c c' hg)
  exact he

/-- The exchange for the chosen lower shrieks is the same paste, transported through
the two specified compactification-independence isomorphisms. -/
lemma purityFieldLowerShriekExchange_eq_paste :
    purityFieldLowerShriekExchange l f f' c c' hi hg =
      Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
            (compactificationOverField f) c) _ ≪≫
        Adjunction.compForgetIso
          (purityFieldOpenRestrictedExchange l f f' c c' hi)
          (purityFieldProperRestrictedExchange l f f' c c' hg) ≪≫
        Functor.isoWhiskerLeft _
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
            c' (compactificationOverField f')) := by
  rw [purityFieldLowerShriekExchange, purityFieldCompactificationExchange_eq_paste]

end AlgebraicGeometry.ProEtale.CondensedRing
