/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldTrace
public import WeilConjectures.WeilSheaf.SmoothPurityTraceDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection

/-!
# Base change of the trace for a smooth proper map

The finite-base trace remains universal after weakly étale base change, including
pullback to the geometric fibre. This uses the specified exceptional base-change
map and works for relative smooth proper maps.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

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
  (f : X ⟶ Y) (f' : X' ⟶ Y') [IsProper f.left] [IsProper f'.left]
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (sq : IsPullback πX f'.left f.left πY)
  {P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N' : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj l⟧}
  (γ : P ⟶ (boundedConstructibleUpperShriek l f).obj N)
  (v : (boundedConstructibleUpperStarOfMap l πY).obj N ⟶ N')

/-- Pull back the counit trace defined by `γ` across proper base change. -/
noncomputable def baseChangedProperTrace :
    (boundedConstructibleLowerStar l f').obj
      ((boundedConstructibleUpperStarOfMap l πX).obj P) ⟶ N' :=
  have := isIso_boundedConstructibleBaseChangeOfMap l sq
  (asIso (boundedConstructibleBaseChangeOfMap l sq.toCommSq)).inv.app P ≫
    (boundedConstructibleUpperStarOfMap l πY).map
      ((boundedConstructibleLowerStar l f).map γ ≫
        (lowerStarUpperShriekAdjunction l f).counit.app N) ≫ v

/-- The adjoint of the pulled-back trace is the pulled-back orientation followed by
the specified exceptional base-change map. -/
lemma homEquiv_baseChangedProperTrace :
    (lowerStarUpperShriekAdjunction l f').homEquiv _ _
        (baseChangedProperTrace l f f' sq γ v) =
      (boundedConstructibleUpperStarOfMap l πX).map γ ≫
        (upperShriekBaseChangeOfMap l sq).app N ≫
        (boundedConstructibleUpperShriek l f').map v := by
  have := isIso_boundedConstructibleBaseChangeOfMap l sq
  simpa only [baseChangedProperTrace, Adjunction.unitBaseChange, asIso_hom,
    upperShriekBaseChangeOfMap, Category.assoc] using
    Adjunction.homEquiv_baseChangedTrace (lowerStarUpperShriekAdjunction l f)
      (lowerStarUpperShriekAdjunction l f')
      (asIso (boundedConstructibleBaseChangeOfMap l sq.toCommSq)) v γ

/-- For a smooth proper map, weakly étale base change preserves the universal
property of a trace whose adjoint is invertible. -/
theorem isIso_homEquiv_baseChangedProperTrace [IsIso γ] [IsIso v] [WeaklyEtale πY]
    (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    IsIso ((lowerStarUpperShriekAdjunction l f').homEquiv _ _
      (baseChangedProperTrace l f f' sq γ v)) := by
  rw [homEquiv_baseChangedProperTrace]
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale l d sq N
  infer_instance

/-- An invertible exceptional base-change component suffices for universality of
the pulled-back trace. -/
theorem isIso_homEquiv_baseChangedProperTrace_of_isIso [IsIso γ] [IsIso v]
    [IsIso ((upperShriekBaseChangeOfMap l sq).app N)] :
    IsIso ((lowerStarUpperShriekAdjunction l f').homEquiv _ _
      (baseChangedProperTrace l f f' sq γ v)) := by
  rw [homEquiv_baseChangedProperTrace]
  infer_instance

/-- Ambient morphism version of universality for an invertible exceptional
base-change component. -/
theorem bijective_map_comp_baseChangedProperTrace_of_isIso [IsIso γ] [IsIso v]
    [IsIso ((upperShriekBaseChangeOfMap l sq).app N)]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    Function.Bijective fun φ : K.obj ⟶
        ((boundedConstructibleUpperStarOfMap l πX).obj P).obj ↦
      (lowerStar (Profinite.padicAlgClRingObj l) f'.left).rightDerivedFunctor.map φ ≫
        (baseChangedProperTrace l f f' sq γ v).hom := by
  have := isIso_homEquiv_baseChangedProperTrace_of_isIso l f f' sq γ v
  exact ObjectProperty.bijective_map_comp_hom_of_isIso_homEquiv _ _
    (lowerStar (Profinite.padicAlgClRingObj l) f'.left).rightDerivedFunctor
    (fun M hM ↦ boundedConstructible_rightDerivedLowerStar_obj l f' ⟨M, hM⟩)
    (lowerStarUpperShriekAdjunction l f')
    (baseChangedProperTrace l f f' sq γ v) K.obj K.property

/-- The same universal property, on ambient derived morphisms from a constructible
complex. This is the form needed by the free Weil resolution. -/
theorem bijective_map_comp_baseChangedProperTrace [IsIso γ] [IsIso v] [WeaklyEtale πY]
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧) :
    Function.Bijective fun φ : K.obj ⟶
        ((boundedConstructibleUpperStarOfMap l πX).obj P).obj ↦
      (lowerStar (Profinite.padicAlgClRingObj l) f'.left).rightDerivedFunctor.map φ ≫
        (baseChangedProperTrace l f f' sq γ v).hom := by
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale l d sq N
  exact bijective_map_comp_baseChangedProperTrace_of_isIso l f f' sq γ v K

end AlgebraicGeometry.ProEtale.CondensedRing
