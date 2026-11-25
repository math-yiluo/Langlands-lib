/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedExchange
public import WeilConjectures.WeilSheaf.SmoothPurityReflectedLiftExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic

/-! # The proper factor of the compactification paste is proper base change -/

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
  {πY : Y'.left ⟶ Y.left} {πZ : c'.Z ⟶ c.Z}
  (hg : IsPullback πZ c'.g c.g πY) [WeaklyEtale πZ] [WeaklyEtale πY]

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The left-derived proper exchange is the usual derived base change map. -/
lemma purityFieldProperAmbientExchange_hom :
    (purityFieldProperAmbientExchange l f f' c c' hg).hom =
      baseChangeMap (Profinite.padicAlgClRingObj l) hg.toCommSq := by
  have := isIso_baseChangeMap_of_weaklyEtale (Profinite.padicAlgClRingObj l) hg
  have he := Functor.isoWhisker_conjugate_cancel
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πY)
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l) πZ)
    (asIso (baseChangeMap (Profinite.padicAlgClRingObj l) hg.toCommSq))
  exact congrArg Iso.hom he

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The restricted proper factor is precisely the proper base change used in the
exceptional base change theorem. -/
lemma purityFieldProperRestrictedExchange_hom :
    (purityFieldProperRestrictedExchange l f f' c c' hg).hom =
      boundedConstructibleBaseChangeOfMap l
        (f := c.overG) (f' := c'.overG) hg.toCommSq := by
  have he := ObjectProperty.preimageIso_liftSquareWithComparisons_lift_hom
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj l c.overG K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj l c'.overG K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (purityFieldProperAmbientExchange l f f' c c' hg)
  rw [purityFieldProperAmbientExchange_hom] at he
  exact he

end AlgebraicGeometry.ProEtale.CondensedRing
