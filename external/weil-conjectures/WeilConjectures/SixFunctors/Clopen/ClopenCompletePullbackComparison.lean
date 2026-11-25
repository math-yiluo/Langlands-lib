/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
import all WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import WeilConjectures.SixFunctors.Clopen.ClopenIntegralCompletionRestriction
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Completed pullback versus normalized clopen restriction

Source: Stacks Project, proetale.tex, Tag 09C3; derived.tex, Tag 08TC.
(blueprint: lem-sf-clopen-complete-pullback-comparison).
-/

@[expose] public section
set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
-- This instance has a free universe and leaves universe constraints stuck here.
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local instance 5000] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private noncomputable instance (priority := 10000) residueBasesAbSheafify
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

private instance (priority := 10000) residueBasesAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

/-- On a complete input, the completed clopen pullback is ordinary restriction.

Source: Stacks Project, proetale.tex, Tag 09C3, restriction to the disjoint affine
opens; derived.tex, Tag 08TC. This is the comparison needed in step 3 of
lem-sf-residue-lisse-clopen-bases.
(blueprint: lem-sf-clopen-complete-pullback-comparison).

Proof: the finite coefficient identifications in d are fixed by their values on
constant sections. Sheafification uniqueness identifies them with the normalized
open coefficient identifications. The equations with every quotient projection
then identify the completed coefficient maps, by the inverse-limit universal
property. Consequently their module restrictions, and their exact termwise
derived descents, are naturally isomorphic. Apply
clopenIntegralCompletionRestriction to identify the specified completed pullback
with ordinary restriction of quotient completion. The canonical completion unit
of K is invertible by canonicalCompletionUnitCriterion. Applying ordinary
restriction to that unit and composing with the preceding comparisons gives the
asserted isomorphism. This argument imposes no constructibility or Tor condition;
it includes the empty open and the zero complex. -/
theorem sf_clopen_complete_pullback_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (U : S.Opens) (hU : IsClosed (U : Set S))
    (d : SfClopenCoefficientRestriction.{u, u} l E S U)
    (K : IntegralOnSlice.D.{u, u} l E S none)
    (hK : IsDerivedCompleteUnrestricted.{u, u} l E S K) :
    Nonempty ((integralDerivedPullback.{u, u} l E U.ι).obj K ≅
      (sfClopenDerivedRestriction.{u, u} (l := l) (E := E) d).obj K)  := by
  let H := sheafCompose (ProEt.topology U.toScheme)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let ff := fullyFaithfulSheafCompose (ProEt.topology U.toScheme)
    CommRingCat.fullyFaithfulForget₂ToRingCat.{u + 1}
  let finite (n : ℕ) : integralCoefficientCommRingSheaf l E U.toScheme n ≅
      (OpenCompletedRestriction.ringRestriction.{u, u} U.ι).obj
        (integralCoefficientCommRingSheaf l E S n) := ff.preimageIso (d.finite n)
  let completed : completedIntegralCommRingSheafUnrestricted.{u, u} l E U.toScheme ≅
      (OpenCompletedRestriction.ringRestriction.{u, u} U.ι).obj
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E S) :=
    ff.preimageIso d.completion
  have hf (n : ℕ) : H.map (finite n).hom = (d.finite n).hom := ff.map_preimage _
  have hc : H.map completed.hom = d.completion.hom := ff.map_preimage _
  let c : OpenCompletedRestriction.Coefficients.{u, u} l E U.ι :=
    { finite := finite
      constants := by
        intro n V
        apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
        rw [Functor.map_comp]
        change _ ≫ (H.map (finite n).hom).hom.app (op V) = _
        rw [hf]
        ext x
        exact d.finite_constant n V x
      completed := completed
      projections := by
        intro n
        apply H.map_injective
        rw [Functor.map_comp, Functor.map_comp, hc, hf]
        exact d.projection n }
  have he : c = OpenCompletedRestriction.coefficients.{u, u} l E U.ι :=
    OpenCompletedRestriction.coefficients_subsingleton l E U.ι c _
  have hnormalized : H.map
      (OpenCompletedRestriction.coefficients.{u, u} l E U.ι).completed.hom =
      d.completion.hom := by
    rw [← he]
    exact hc
  let F : scalarReductionSource.{u, u} l E S ⥤
      scalarReductionSource.{u, u} l E U.toScheme :=
    sfClopenModuleRestriction U _ _ d.completion
  let : F.Additive := d.additive
  let : PreservesFiniteLimits F := d.limits
  let : PreservesFiniteColimits F := d.colimits
  let e : OpenCompletedRestriction.ordinary.{u, u} l E U.ι ≅ F :=
    SheafOfModules.pushforwardCongr (F := sfClopenSiteInclusion U)
      (J := ProEt.topology U.toScheme) (K := ProEt.topology S) hnormalized ≪≫ Iso.refl _
  let : (OpenCompletedRestriction.ordinary.{u, u} l E U.ι).Additive :=
    OpenCompletedRestriction.ordinaryAdditive.{u, u} l E U.ι
  let : PreservesFiniteLimits (OpenCompletedRestriction.ordinary.{u, u} l E U.ι) :=
    OpenCompletedRestriction.ordinaryLimits.{u, u} l E U.ι
  let : PreservesFiniteColimits (OpenCompletedRestriction.ordinary.{u, u} l E U.ι) :=
    OpenCompletedRestriction.ordinaryColimits.{u, u} l E U.ι
  let ed := Functor.mapDerivedCategoryNatIso
    (C := scalarReductionSource.{u, u} l E S)
    (D := scalarReductionSource.{u, u} l E U.toScheme) e
  obtain ⟨ep⟩ := clopenIntegralCompletionRestriction l E S U hU
  have hu : IsIso ((IntegralOnSlice.completionUnit.{u, u} l E S none).app K) :=
    (IntegralOnSlice.canonicalCompletionUnitCriterion.{u, u} l E S K).mpr hK
  let := hu
  exact ⟨(ep.app K).symm ≪≫
    (OpenCompletedRestriction.derivedRestriction.{u, u} l E U.ι).mapIso
      (asIso ((IntegralOnSlice.completionUnit.{u, u} l E S none).app K)).symm ≪≫
    ed.app K⟩

end WeilConjectures
