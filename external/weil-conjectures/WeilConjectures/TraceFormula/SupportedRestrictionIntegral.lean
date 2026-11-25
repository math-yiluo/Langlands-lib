/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrictionOfHomEq
public import WeilConjectures.TraceFormula.SupportedRestrictionE
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizing
public import WeilConjectures.AlgebraicGeometry.OverPullbackFiniteType
public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!

# The supported restriction with `𝒪_E`-coefficients and its rationalization

For a finite subextension `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E` and a fixed locus `F` of a
correspondence, the supported restriction can be formed with `𝒪_E`-coefficients from the
compact-support base change of the fixed square (`FixedLocus.supportedRestrictionIntegral`).
Under the extension of scalars `T : 𝒪_E ⟶ E` it becomes the `E`-supported restriction of `T P`
(`FixedLocus.map_supportedRestrictionIntegral_comp`), given the compatibility of base change with
the coefficient comparisons (blueprint `sk-thm-sf-compatibility`, (7):
`boundedConstructibleLowerShriekBaseChange_extendScalars`). With the `f^!` clause of blueprint
`proposition-six-operations-change-coefficients`
(`isIso_boundedConstructibleUpperShriekExtendScalars`) this transports the vanishing of a stalk of
the supported restriction from `𝒪_E` to `E`
(`FixedLocus.upperStar_map_supportedRestrictionE_eq_zero_of_supportedRestrictionIntegral`).

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

/-- Compact-support base change `Rc_! ⋙ LΔ^* ≅ Lι^* ⋙ Rd_!` in the fixed square, with
`𝒪_E`-coefficients. -/
noncomputable def lowerShriekBaseChangeIsoIntegral :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 c.support ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ F.ι ⋙
        PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 F.d :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 F.isPullback
  asIso (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 F.isPullback)

/-- The supported restriction `Lι^* Rc^! P ⟶ Rd^! LΔ^* P` with `𝒪_E`-coefficients: the mate
`Rc^! ⋙ Lι^* ⟶ LΔ^* ⋙ Rd^!` of the inverse of compact-support base change in the fixed square. -/
noncomputable def supportedRestrictionIntegral
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 c.support).obj P) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 F.d).obj
        ((boundedConstructibleUpperStar _ ℓ (diag X)).obj P) :=
  (CategoryTheory.mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1
      c.support)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 F.d)
    (TwoSquare.mk _ _ _ _ (F.lowerShriekBaseChangeIsoIntegral E).inv)).app P

/-- **The supported restriction under `𝒪_E ⟶ E`**: the extension of scalars `T` of the
`𝒪_E`-supported restriction of `P`, followed by the `f^!`-exchange for `d` and the pullback
comparison for `Δ`, is the pullback comparison for `ι`, then `Lι^*` of the `f^!`-exchange for `c`,
then the `E`-supported restriction of `T P`. -/
theorem map_supportedRestrictionIntegral_comp
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleExtendScalars F.F.left ℓ E).map (F.supportedRestrictionIntegral E P) ≫
        (boundedConstructibleUpperShriekExtendScalars ℓ E F.d).app _ ≫
        (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E F.d).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E (diag X)).hom.app P) =
      (boundedConstructibleUpperStarExtendScalarsIso ℓ E F.ι).hom.app _ ≫
        (boundedConstructibleUpperStar _ ℓ F.ι).map
          ((boundedConstructibleUpperShriekExtendScalars ℓ E c.support).app P) ≫
        F.supportedRestrictionE E ((boundedConstructibleExtendScalars (X ⨯ X).left ℓ E).obj P) := by
  -- The compatibility is stated for the named base changes; matching it against `σ.hom.app M`
  -- (or matching the composite against `h` at default transparency) makes the elaborator unfold
  -- the full-subcategory compositions, so pass `σ.hom = s` and compare reducibly.
  have e : (F.lowerShriekBaseChangeIsoIntegral E).hom =
      boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 F.isPullback :=
    @asIso_hom _ _ _ _ _
      (isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E.1 F.isPullback)
  have e' : (F.lowerShriekBaseChangeIsoE E).hom =
      boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E F.isPullback := asIso_hom _
  have h := Adjunction.map_mateEquiv_app_comp_of_hom_eq
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 c.support)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 F.d)
    (boundedConstructibleUpperStar _ ℓ F.ι) (boundedConstructibleUpperStar _ ℓ (diag X))
    (F.lowerShriekBaseChangeIsoIntegral E)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E c.support)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E F.d)
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ F.ι)
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (diag X))
    (F.lowerShriekBaseChangeIsoE E)
    (boundedConstructibleExtendScalars (X ⨯ X).left ℓ E)
    (boundedConstructibleExtendScalars c.C.left ℓ E)
    (boundedConstructibleExtendScalars F.F.left ℓ E)
    (boundedConstructibleExtendScalars X.left ℓ E)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E c.support)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E F.d)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E F.ι)
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E (diag X)) e e'
    (by with_reducible
      exact boundedConstructibleLowerShriekBaseChange_extendScalars ℓ E F.isPullback) P
  unfold supportedRestrictionIntegral supportedRestrictionE
    boundedConstructibleUpperShriekExtendScalars
  with_reducible exact h

/-- **Transport of the vanishing of the supported restriction from `𝒪_E` to `E`**: if the stalk
along `z : T ⟶ Fix(c)` of the extension of scalars to `E` of the `𝒪_E`-supported restriction of
`P` vanishes, so does the stalk of the `E`-supported restriction of `E ⊗ P`. This uses the `f^!`
clause of blueprint `proposition-six-operations-change-coefficients`
(`isIso_boundedConstructibleUpperShriekExtendScalars`) for the support `c`. -/
theorem upperStar_map_supportedRestrictionE_eq_zero_of_supportedRestrictionIntegral
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (h : (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      ((boundedConstructibleExtendScalars F.F.left ℓ E).map
        (F.supportedRestrictionIntegral E P)) = 0) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      (F.supportedRestrictionE E ((boundedConstructibleExtendScalars (X ⨯ X).left ℓ E).obj P)) =
        0 := by
  have := isIso_boundedConstructibleUpperShriekExtendScalars ℓ E c.support
  have h1 := congrArg (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
    (F.map_supportedRestrictionIntegral_comp E P)
  simp only [Functor.map_comp, h, Limits.zero_comp] at h1
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).1
    ((Preadditive.IsIso.comp_left_eq_zero _ _).1 h1.symm)

/-- **Transport of the vanishing of a stalk of the supported restriction from `𝒪_E` to `E`**: if
the stalk along `z : T ⟶ Fix(c)` of the `𝒪_E`-supported restriction of `P` vanishes, so does the
stalk of the `E`-supported restriction of `E ⊗ P`. -/
theorem upperStar_map_supportedRestrictionE_eq_zero_of_upperStar_map_supportedRestrictionIntegral
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (h : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).map
      (F.supportedRestrictionIntegral E P) = 0) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ z).map
      (F.supportedRestrictionE E ((boundedConstructibleExtendScalars (X ⨯ X).left ℓ E).obj P)) =
        0 := by
  refine F.upperStar_map_supportedRestrictionE_eq_zero_of_supportedRestrictionIntegral E z P ?_
  have h1 := NatIso.map_eq_zero_of_map_eq_zero (boundedConstructibleUpperStarExtendScalarsIso ℓ E z)
    (f := F.supportedRestrictionIntegral E P) (by
      dsimp only [Functor.comp_map]
      refine (congrArg (boundedConstructibleExtendScalars T.left ℓ E).map ?_).trans
        (Functor.map_zero _ _ _)
      with_reducible exact h)
  dsimp only [Functor.comp_map] at h1
  with_reducible exact h1

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
