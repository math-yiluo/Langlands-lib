/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrictionOfHomEq
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper
public import WeilConjectures.TraceFormula.SupportedRestrictionCoefficientChange
public import WeilConjectures.TraceFormula.SupportedRestrictionE

/-!

# The supported restriction with `E`-coefficients and its extension to `ℚ̄_ℓ`

For a finite subextension `E ⊆ ℚ̄_ℓ` and a fixed locus `F` of a correspondence, the supported
restriction can be formed with `E`-coefficients from the compact-support base change of the fixed
square (`FixedLocus.supportedRestrictionE`). Under the extension of scalars `T : E ⟶ ℚ̄_ℓ` it
becomes the `ℚ̄_ℓ`-supported restriction of `T P`
(`FixedLocus.map_supportedRestrictionE_comp`), given the compatibility of base change with the
coefficient comparisons (blueprint `sk-thm-sf-compatibility`, (7):
`boundedConstructibleLowerShriekBaseChange_toPadicAlgCl`). With the `f^!` clause of blueprint
`proposition-six-operations-change-coefficients`
(`isIso_boundedConstructibleUpperShriekToPadicAlgCl`) this transports the vanishing of a stalk of
the supported restriction from `E` to `ℚ̄_ℓ`
(`FixedLocus.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE`).

-/

@[expose] public section


universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K}

namespace Correspondence.FixedLocus

variable (F : c.FixedLocus) (E : FiniteIntermediateField ℓ)

/-- **The supported restriction under `E ⟶ ℚ̄_ℓ`**: the extension of scalars `T` of the
`E`-supported restriction of `P`, followed by the `f^!`-exchange for `d` and the pullback
comparison for `Δ`, is the pullback comparison for `ι`, then `Lι^*` of the `f^!`-exchange for `c`,
then the `ℚ̄_ℓ`-supported restriction of `T P`. -/
theorem map_supportedRestrictionE_comp
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleToPadicAlgCl F.F.left ℓ E).map (F.supportedRestrictionE E P) ≫
        (boundedConstructibleUpperShriekToPadicAlgCl ℓ E F.d).app _ ≫
        (boundedConstructibleUpperShriek ℓ F.d).map
          ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E (diag X)).hom.app P) =
      (boundedConstructibleUpperStarToPadicAlgClIso ℓ E F.ι).hom.app _ ≫
        (boundedConstructibleUpperStar _ ℓ F.ι).map
          ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E c.support).app P) ≫
        F.supportedRestriction ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P) := by
  -- The compatibility is stated for the named base changes; matching it against `σ.hom.app M`
  -- (or matching the composite against `h` at default transparency) makes the elaborator unfold
  -- the full-subcategory compositions, so pass `σ.hom = s` and compare reducibly.
  have e₁ : (F.lowerShriekBaseChangeIsoE E).hom =
      boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E F.isPullback := asIso_hom _
  have e₂ : F.lowerShriekBaseChangeIso.hom =
      boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback :=
    @asIso_hom _ _ _ _ _ (isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback)
  have hσ := boundedConstructibleLowerShriekBaseChange_toPadicAlgCl ℓ E F.isPullback
  have h := Adjunction.map_mateEquiv_app_comp_of_hom_eq
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E c.support)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E F.d)
    (boundedConstructibleUpperStar _ ℓ F.ι) (boundedConstructibleUpperStar _ ℓ (diag X))
    (F.lowerShriekBaseChangeIsoE E)
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ F.d)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X))
    F.lowerShriekBaseChangeIso
    (boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E)
    (boundedConstructibleToPadicAlgCl c.C.left ℓ E)
    (boundedConstructibleToPadicAlgCl F.F.left ℓ E)
    (boundedConstructibleToPadicAlgCl X.left ℓ E)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E c.support)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E F.d)
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E F.ι)
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E (diag X)) e₁ e₂
    (by with_reducible exact hσ) P
  have e := F.supportedRestriction_eq_mateEquiv
    ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P)
  unfold supportedRestrictionE boundedConstructibleUpperShriekToPadicAlgCl
  with_reducible exact h.trans (congrArg (_ ≫ _ ≫ ·) e.symm)

/-- **Transport of the vanishing of the supported restriction from `E` to `ℚ̄_ℓ`**: if the stalk
along `z : T ⟶ Fix(c)` of the extension of scalars to `ℚ̄_ℓ` of the `E`-supported restriction of
`P` vanishes, so does the stalk of the `ℚ̄_ℓ`-supported restriction of `ℚ̄_ℓ ⊗ P`. This uses the
`f^!` clause of blueprint `proposition-six-operations-change-coefficients`
(`isIso_boundedConstructibleUpperShriekToPadicAlgCl`) for the support `c`. -/
theorem upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧)
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      ((boundedConstructibleToPadicAlgCl F.F.left ℓ E).map (F.supportedRestrictionE E P)) = 0) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P)) = 0 := by
  have := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E c.support
  have h1 := congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
    (F.map_supportedRestrictionE_comp E P)
  simp only [Functor.map_comp, h, Limits.zero_comp] at h1
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).1
    ((Preadditive.IsIso.comp_left_eq_zero _ _).1 h1.symm)

/-- **Transport of the vanishing of a stalk of the supported restriction from `E` to `ℚ̄_ℓ`**: if
the stalk along `z : T ⟶ Fix(c)` of the `E`-supported restriction of `P` vanishes, so does the
stalk of the `ℚ̄_ℓ`-supported restriction of `ℚ̄_ℓ ⊗ P`. -/
theorem upperStar_map_supportedRestriction_eq_zero_of_upperStar_map_supportedRestrictionE
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧)
    (h : (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      (F.supportedRestrictionE E P) = 0) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction ((boundedConstructibleToPadicAlgCl (X ⨯ X).left ℓ E).obj P)) = 0 := by
  refine F.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE E z P ?_
  have h1 := NatIso.map_eq_zero_of_map_eq_zero (boundedConstructibleUpperStarToPadicAlgClIso ℓ E z)
    (f := F.supportedRestrictionE E P) (by
      dsimp only [Functor.comp_map]
      refine (congrArg (boundedConstructibleToPadicAlgCl T.left ℓ E).map ?_).trans
        (Functor.map_zero _ _ _)
      with_reducible exact h)
  dsimp only [Functor.comp_map] at h1
  with_reducible exact h1

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
