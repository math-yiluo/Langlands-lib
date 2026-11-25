/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.TraceFormula.Supporting.SimultaneousIntegralPullbackComparisons

/-!
# Realization of integral pullback comparisons

Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: lem-trf-integral-pullback-comparison-realization).

The sequence site retains the whole quotient diagram. Its pullback is the left
adjoint of the actual sectionwise direct image. Scalar change is the universal
derived change of rings for the actual map of quotient coefficient sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The strict-system realization of integral pullback comparisons, including
the normalized counit construction, finite reductions, and all coherence laws.
Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: lem-trf-integral-pullback-comparison-realization).

Proof (the DAG proof plan):

1. Choose a flat-term K-flat representative P→K by [lem-pc-kflat-resolution]. Form the quotient
   complexes P_{F,n}=P⊗_{R_{E,V}}(A_{F,n})_V and their actual quotient transitions, and pull them
   back termwise to define Q_{f,F}(P) and Q_{h,k,E}(P). The definitions of completed pullback and
   scalar extension in [def-pur-integral-derived-operations] and [def-weil-integral-scalar-
   extension], together with [lem-pur-derived-change-of-rings], identify these with the required
   finite-level derived constructions. The reduction isomorphisms in [lem-pur-integral-operations-
   preserve-constructible] (1) and the coherent quotient-system model in [lem-pur-coefficient-
   extension-reduction-model] show that these are strict normalized towers, including the scalar
   tower, with transitions induced by the actual quotient maps.

2. For a strict tower C_• take a K-injective tower resolution C_•→I_• and use the ordinary limit-
   cone map Δ lim I_•→I_•. The strict-tower homotopy-limit theorem [lem-weil-pbc-ringed-strict-
   tower-homotopy-limit] says that this construction is the total derived inverse limit, is
   functorial on tower maps, and has the Roos triangle. Thus ε_C is a morphism in the derived
   category of the whole tower, rather than a collection of unrelated maps after reduction.

3. Towers of modules over the completed coefficient sheaf (resp. over the quotient rings A_{F,•})
   are the modules over the corresponding sheaf of rings on the product of the site with the poset
   N^op, so [lem-pur-derived-change-of-rings] applies to the levelwise change of rings R→A_{F,•}
   on tower derived categories; a constant tower of a K-flat complex is K-flat there, since tensor
   products and acyclicity are levelwise. Apply ε to the reduction tower of F_{k,E}K and then
   apply h^*, with the levelwise change-of-rings counits and tensor associators; this gives
   η_{h,k,K}. Apply the same construction to the L-coefficient tower of F_{f,E}K and to the tower
   of T_VK after f^*; these give λ_{f,K} and μ_{f,K}. The finite pullback comparison is the
   canonical termwise map on K-flat reductions by [lem-weil-pbc-proetale-derived-pullback-
   composition]. Its levelwise reduction maps are the canonical isomorphisms supplied by [lem-pur-
   integral-operations-preserve-constructible] (1), while [lem-pur-coefficient-extension-
   reduction-model] identifies the scalarized reductions with the L-coefficient quotient tower and
   supplies their coherent counit. Hence η, λ and μ are maps of the whole strict towers with
   levelwise isomorphisms; functoriality and exactness of Rlim from [lem-weil-pbc-ringed-strict-
   tower-homotopy-limit] make them isomorphisms after realization.

4. The maps just constructed are independent of P, of the tower resolution, and of common
   refinements. [lem-pur-integral-operations-well-defined] gives the unique comparison for
   completed pullback realizations from two K-flat resolutions, and [lem-weil-integral-scalar-
   extension-well-defined] gives the analogous comparison for scalar-extension towers. The
   comparison maps commute with the quotient maps by the tensor formulas in [lem-pur-coefficient-
   extension-reduction-model] and [lem-pur-scalar-extension-tower-coherence]. Functoriality of
   Rlim then transports ε, η, λ and μ across these comparisons, proving independence before the
   families are fixed.

5. Define c^E_{h,k,K}=η_{h,k,K}^{-1}∘Rlim(c_{h,k,•}) and a_{f,K}=μ_{f,K}^{-1}∘λ_{f,K}, and define
   c^L similarly. The source of c^E is identified with Rlim Q_{kh,E}(P) by the defining pullback
   tower. Each c_{h,k,n} is the finite canonical composition map, and [lem-weil-pbc-proetale-
   derived-pullback-composition] identifies its strict termwise realization; [lem-pur-integral-
   operations-preserve-constructible] (1) supplies the reduction isomorphisms used in η, while
   [lem-pur-coefficient-extension-reduction-model] and [lem-pur-scalar-extension-tower-coherence]
   supply the scalar-association and quotient-transition maps used in λ and μ. Thus the displayed
   formulas are valid choices of the comparison families and are natural isomorphisms by Step 3
   and functoriality of Rlim. The formula for c^L is applied to T_VK, which lies in D^b_c(V,O_L)
   by [lem-weil-integral-scalar-extension-constructible]; likewise T_W F_{k,E}K and T_Z F_{kh,E}K
   are constructible, so the L-level reduction isomorphisms of [lem-pur-integral-operations-
   preserve-constructible] (1) apply to all the L-level factors, and the rationalized equations
   below take place in the rationalized constructible categories.

6. Before realization, expand the scalar/composition equation using the strict representatives
   just fixed. First, the counit ε_C of Step 2 is natural in strict tower maps φ:C→C′: lift φ to
   the K-injective tower resolutions (possible and unique up to homotopy because I′ is K-injective
   [def-pur-kinjective-complex]); the ordinary limit-cone maps then commute strictly with the
   lift. Since levelwise change of rings, the action counits and the termwise pullback h^* are
   functors on the tower derived categories, the comparison F_{h,L}(R lim C)→R lim h^*C built from
   ε_C exactly as η is natural in φ, i.e. F_{h,L}(R lim φ) corresponds to R lim(h^*φ). This is
   what is used below for F_{h,L}(a_{k,K}). The factor a_{k,K} is represented by the strict
   scalar-association map κ_{k,n}; applying F_{h,L} means applying the termwise pullback h^* to
   that same tower map, and a_{h,F_{k,E}K} is represented by κ_{h,n}. The factor T_Z(c^E_{h,k,K})
   is represented by scalar extension of the finite map c_{h,k,n}, while the right-hand
   c^L_{h,k,T_VK} and a_{kh,K} use the corresponding L-level composition map and κ_{kh,n}. The
   strict tower coherence identity [lem-pur-scalar-extension-tower-coherence] and naturality of
   the finite pullback maps [lem-weil-pbc-proetale-derived-pullback-composition] identify the two
   composites term by term; [lem-pur-derived-change-of-rings] identifies the tensor
   reassociations. Applying the functor Rlim from [lem-weil-pbc-ringed-strict-tower-homotopy-
   limit] gives the displayed equality.

7. The same strict-system calculation with three composable maps gives the two associativity
   composites of c^E as the same reassociation of (j∘h∘k)^*P_n, and the identity map gives the
   unit comparison. Equality of scheme morphisms and finite iterations are respected because the
   finite inverse-image and coefficient maps are functorial, and Rlim preserves these equalities.
   For E=L, [lem-pur-coefficient-extension-reduction-model] says that the coherent reduction
   comparison is the usual reduction counit, while [lem-weil-finite-free-completed-scalar-
   comparison] identifies χ_{E/E,K} with the derived-completeness map K→Rlim_n(K⊗^L A_{E,n}) after
   K⊗^L R≅K. Both maps are induced by the same quotient component and zero shifted component, so
   the specified scalar comparison is the identity under multiplication and completeness.

8. For E⊂L⊂M, [lem-pur-coefficient-extension-reduction-model] identifies each scalar reduction
   comparison with the coherent quotient-system counit, and [lem-pur-scalar-extension-tower-
   coherence] states that the successive scalar-association maps agree with the direct E⊂M map as
   strict-system equations. Conjugating the ordinary derived tensor associator by the completion
   maps χ of [lem-weil-finite-free-completed-scalar-comparison] therefore gives the asserted
   integral scalar associator and its compatibility with all comparisons above. Finally, the
   scalar-localization functor of [def-weil-rationalization-karoubi] sends equal strict tower maps
   to equal rationalized maps, with no finite Tor-amplitude assumption. -/
theorem integralPullbackComparisonRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) :
    ∃ D : IntegralComparisonSystem l,
      IntegralComparisonRealizationCoherence l E L ι D := by
  obtain ⟨D, hD⟩ := integralPullbackComparisonRealization_simultaneous.{u} l
  exact ⟨D, hD E L ι⟩

end WeilConjectures
