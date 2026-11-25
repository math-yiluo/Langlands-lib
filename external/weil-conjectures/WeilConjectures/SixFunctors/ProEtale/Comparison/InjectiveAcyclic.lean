/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineCechCriterion
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CechComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.SectionsFunctor

/-!
# Acyclicity of pulled-back injective étale sheaves

Let `A` be a Grothendieck abelian category and `I` an injective `A`-valued sheaf on the small
étale site of a scheme `X`. The comparison pullback `ν^* I` to the small pro-étale site is
acyclic for the restriction `ν_*`: `R^q ν_* (ν^* I) = 0` for `q > 0`.

The proof follows [Stacks, Tag 099U] and the blueprint
(`lemma-acyclicity-pulled-back-injectives`, `prop-weil-pbc-site-comparison-finite-level`).
On an affine scheme `W`, the higher cohomology of `ν^* I` on `W_proét` is computed on the affine
pro-étale site, and vanishes by the Čech criterion
(`AlgebraicGeometry.Scheme.AffineProEt.isZero_rightDerived_of_exactAt_overCechComplex`): the
Čech complex of `ν^* I` for a surjection of affine pro-étale `W`-schemes is the filtered colimit
of the Čech complexes of `I` for étale morphisms of affine schemes presenting it, which are
exact since `I` is injective
(`AlgebraicGeometry.ProEtale.exactAt_overCechComplex_comparisonUpperStar`). Testing the higher
direct images on affine étale `X`-schemes reduces the general case to the affine one.

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar`:
  `H^q(W_proét, ν^* I) = 0` for `q > 0` and `W` affine.
- `AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`:
  `R^q ν_* (ν^* I) = 0` for `q > 0`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Higher cohomology of pulled-back injectives on affine schemes.** Let `W` be affine and `I`
an injective étale sheaf on `W`. Then `H^q(W_proét, ν^* I) = 0` for `q > 0`: on the affine
pro-étale site, the Čech complexes of `ν^* I` for surjections are exact in positive degrees
(`exactAt_overCechComplex_comparisonUpperStar`), so the Čech criterion applies.
(blueprint: `lemma-acyclicity-pulled-back-injectives`) -/
theorem isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar {W : Scheme.{u}}
    [IsAffine W] (I : Sheaf W.smallEtaleTopology A) [Injective I] (q : ℕ) :
    IsZero (((globalSectionsFunctor A W).rightDerived (q + 1)).obj
      ((comparisonUpperStar A W).obj I)) := by
  have : LocallySmall.{u + 1} W.AffineProEt :=
    ⟨fun _ _ ↦ ⟨ULift.{u + 1} _, ⟨Equiv.ulift.symm⟩⟩⟩
  have : EssentiallySmall.{u + 1} W.AffineProEt := essentiallySmall_of_small_of_locallySmall _
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  have : HasSheafify (AffineProEt.topology W) A :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall A _
  let Φ := (AffineProEt.toProEt W).sheafPushforwardContinuous A (AffineProEt.topology W)
    (ProEt.topology W)
  have : Φ.Additive := ⟨rfl⟩
  let G := (comparisonUpperStar A W).obj I
  -- the Čech criterion on the affine pro-étale site
  have h₁ := AffineProEt.isZero_rightDerived_of_exactAt_overCechComplex (Φ.obj G)
    (fun f _ q ↦ exactAt_overCechComplex_comparisonUpperStar I f q) q
  -- transport along the equivalence between sheaves on the two sites
  let e : globalSectionsFunctor A W ≅
      Φ ⋙ sheafToPresheaf _ A ⋙ (evaluation _ A).obj (op (AffineProEt.top W)) :=
    Iso.refl _
  have : Φ.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      Φ.asEquivalence.symm.toAdjunction
  exact h₁.of_iso ((NatIso.rightDerived e (q + 1)).app G ≪≫
    (Functor.rightDerivedCompIsoOfExact Φ _ (q + 1)).app G)

/-- A short complex of étale sheaves is exact if the short complexes of sections over all affine
étale schemes are exact. -/
lemma _root_.AlgebraicGeometry.Etale.exact_of_exact_affineEtale_sections
    {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology A))
    (h : ∀ U : X.AffineEtale, (S.map (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj (op ((AffineEtale.Spec X).obj U)))).Exact) :
    S.Exact := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let Φ := (AffineEtale.Spec X).sheafPushforwardContinuous A
    (AffineEtale.topology X) X.smallEtaleTopology
  have : Φ.Additive := ⟨rfl⟩
  have : Φ.PreservesHomology := {}
  rw [← S.exact_map_iff_of_faithful Φ]
  -- the presheaves underlying the restriction to the affine site form an exact short complex
  let T := (S.map Φ).map (sheafToPresheaf (AffineEtale.topology X) A)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    exact fun U ↦ h U.unop
  -- sheafifying it gives back the restriction, sheafification being exact
  have : (presheafToSheaf (AffineEtale.topology X) A).PreservesHomology := {}
  have hT' := hT.map (presheafToSheaf (AffineEtale.topology X) A)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hT'
  exact (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm

/-- Blueprint `lemma-acyclicity-pulled-back-injectives--1`: Exactness and full faithfulness at
finite level

*Acyclicity.* For every injective étale sheaf `I` the pro-étale sheaf `ν^* I` is acyclic for
`ν_*`: `R^q ν_* (ν^* I) = 0` for `q > 0`. The higher direct images are computed on affine étale
`X`-schemes `U`, where they are the higher cohomology groups of `ν^* (I|_U)` on `U_proét`, which
vanish (`isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar`). The other two clauses
of the node, exactness of `ν^*` and invertibility of the unit `F ⟶ ν_* ν^* F`, are
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar`,
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_comparisonUpperStar` and
`AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`. -/
theorem rightAcyclic_comparisonUpperStar_obj_of_injective (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology A) [Injective I] :
    ν_*(X)[A].rightAcyclic (ν^*(X)[A].obj I) := by
  intro q
  let G := (comparisonUpperStar A X).obj I
  let R : InjectiveResolution G := injectiveResolution G
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj _ (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology]
  refine Etale.exact_of_exact_affineEtale_sections A _ fun U ↦ ?_
  let T : X.ProEt := (toProEt X).obj ((AffineEtale.Spec X).obj U)
  have hT : IsZero (((sectionsFunctor A T).rightDerived (q + 1)).obj G) := by
    refine isZero_rightDerived_sectionsFunctor_of_upperStar A T G (q + 1) ?_
    refine IsZero.of_iso ?_ (((globalSectionsFunctor A T.left).rightDerived (q + 1)).mapIso
      ((comparisonUpperStarCompUpperStarIso A T.hom).app I))
    have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
    have : Etale T.hom := ((AffineEtale.Spec X).obj U).prop
    have : Injective ((Etale.upperStar A T.hom).obj I) :=
      Etale.injective_upperStar_obj_of_etale' A T.hom I
    exact isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar A _ q
  have h' := hT.of_iso (R.isoRightDerivedObj _ (q + 1)).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology] at h'
  exact h'

end AlgebraicGeometry.ProEtale
