/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonDefinitions
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLinePowerComparisons
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineDerivedComparisons
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineRestrictions
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonIso
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Assembly of signed integral line reduction and restriction

Source: Stacks 07A4; Bhatt--Scholze, Definitions 3.4.10 and 3.5.2.
(blueprint: lem-pur-integral-line-reduction-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem comparison_isIso
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : D.{u, u} l E X none) (hK : IsComplete l E X none K) :
    IsIso ((comparison l E X L m).app K) := by
  have : (power l E X L m).IsFiniteLocallyFreeOfRank 1 := by
    rw [power_eq_coefficient]
    exact (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L m).1
  apply integralLineTensorComparison_iso l E X ?_ K hK (power l E X L m)
  intro x
  let := hl x
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
  simpa using (isUnit_of_invertible (l : X.residueField x)).ne_zero

/-- Signed lines commute with all positive derived reductions, preserve derived completeness
and the integral constructible category with each given uniform cohomological interval,
and induce inverse ordinary and completed tensor equivalences on that full category.

Source: Bhatt--Scholze, Definitions 3.4.10 and 3.5.2, Lemma 3.4.12,
Proposition 3.5.1, pp. 22--24; Stacks 07A4; blueprint
`sk-def-sp-tate-twist-locally-free.proof.md`, (3), final sentence
(blueprint: lem-pur-integral-line-reduction-restriction).

Proof:
1. Trivialize L. Its signed powers have bases e tensor ... tensor e, 1, or
   the functional taking the positive basis to 1. Pair opposite bases by
   multiplication; the inverse sends a to ap tensor q. The factors change by
   u^m and u^(-m), so the evaluations glue and satisfy both triangle identities.
   Use localizedSiteTensorRestriction and the sheaf tensor-Hom adjunction.
2. Positive scalar comparison balances tensor factors. For negative powers send
   phi tensor a to the functional x tensor c mapped to residue(phi(x))ac.
   Each comparison is the identity on the local quotient basis. These maps
   commute with every quotient and preserve evaluation (PowerFormula).
3. By lem-pur-line-unbounded-derived-tensor the lines in degree zero are K-flat.
   Apply the ringed-topoi derived-tensor pullback theorem to the identity topos
   and R to R_n. Its representative is the balancing map in ChainFormula.
   This commutes with both strict quotient transitions (DerivedFormula).
4. Tensor by the line has tensor by its opposite as both adjoints, by the
   dual-tensor adjunction theorem. Hence it preserves products with projections.
   It is exact; pro-etale countable products are exact and represent derived
   products by derived-limit-existence (2). Thus the same comparison works on
   arbitrary complexes, without asserting that localization at a cover preserves products.
5. Apply this triangulated product-preserving equivalence to the canonical
   augmented reduction-unit Roos triangle. The balancing comparison takes its
   first map to the new reduction units and 1-s to the new quotient shift.
   This proves completeness of ordinary tensor with the signed line.
6. Compute completed tensor on flat-term K-flat representatives, using
   integralOperationsWellDefined. The levelwise balancing maps identify its
   finite-tensor tower with tensor by the line of the original reduction tower.
   On Roos coordinates (v,u), apply the product comparison on both summands;
   it respects d(v,u)=(dv,-du-(1-s)v), by roos_cone_calculus.
7. The identity-field case of finiteFreeCompletedScalarComparison identifies
   the original complete object with this Roos model by its (c,0) unit.
   Tensoring that unit and using step 6 gives exactly integralLineComparison,
   with zero shifted-product component. It is invertible and natural in K.
8. The reduction comparison identifies cohomology with H^i(K_n) tensor P_n.
   Exact line tensor preserves every zero cohomology degree, hence the very
   same interval [a,b], without assuming K itself bounded.
9. On each constructible stratum, exact finite-coefficient pullback commutes
   with tensor. Refine with a finite-model trivializing cover of L_n. Tensor
   with its rank-one finite value takes M to M tensor A_n, isomorphic to M.
   This preserves finite local values on the same finite constructible partition.
   Steps 5, 7 and 8 then give both integral membership claims.
10. The ordinary evaluations restrict through the full inclusion. Conjugate
   them by the actual completion comparisons c to obtain the two completed
   evaluations in CompletedRestriction. Naturality cancels adjacent comparisons
   in the triangle composites, leaving the ordinary triangle identities.
-/
theorem integral_line_reduction_restriction
    (_hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (_hfinite : FiniteReductions l E X L) :
    ∃ (b : PowerComparisons l E X L) (d : DerivedComparisons l E X L)
      (e : Evaluations l E X L),
      PowerFormula l E X L b ∧ DerivedFormula l E X L b d ∧ EvaluationFormula l E X L e ∧
      (∀ (m : ℤ) (K : D.{u, u} l E X none), IsComplete l E X none K →
        IsIso ((comparison l E X L m).app K) ∧
          IsComplete l E X none ((ordinary l E X L m).obj K)) ∧
      (∀ (m : ℤ) (K : D.{u, u} l E X none) (a z : ℤ),
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ⊆ Set.Icc a z) →
        ∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj
            ((ordinary l E X L m).obj K)) ⊆ Set.Icc a z) ∧
      Restrictions l E X L e := by
  obtain ⟨b, e, hb, he⟩ := integral_line_power_comparisons l E X L
  obtain ⟨d, hd, hs⟩ := integral_line_derived_comparisons l E X L b hb
  obtain ⟨hc, hr⟩ := integral_line_restrictions l E X _hl L _hfinite e he
  refine ⟨b, d, e, hb, hd, he, ?_, hs, hr⟩
  intro m K hK
  exact ⟨comparison_isIso l E X _hl L m K hK, hc m K hK⟩

end WeilConjectures.IntegralLineReduction
