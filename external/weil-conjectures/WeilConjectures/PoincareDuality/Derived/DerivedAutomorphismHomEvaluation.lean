/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage

import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationB

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

Source: Stacks Project, Modules on Sites, Tag 0GMX; the derived and completed
normalization is the enhancement in the node's sixteen proof steps, supplying
main-20261015 theorem-poincare-duality-frobenius--2 Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Finite inputs are unbounded. Integral inputs have exactly the recorded
Hom-constructibility condition. Completed inverse image is constructed from
all coefficient projections; its comparison with tower pullback uses the
actual completion unit and a resolution-normalized total-limit comparison.
System maps and their identities are stated before evaluation or realization.
Rational maps are localized; algebraically closed maps use every common stage.

## Main definitions

* `podFiniteHomComparison`: transpose of pullback of finite evaluation.
* `podPartialHomComparison`: the same construction on permitted Hom pairs.
* `podCompletedRingMap`: completed coefficient transport from all projections.
* `podCompletedToTower`: the completion-unit comparison with tower pullback.

## Main statements

* `derivedAutomorphismHomEvaluation`: the four evaluation-defined natural isomorphisms.
* The `*_laws`, `*_shift`, `*_comp` declarations give all coherent identities.
* `podHomReductionSquare`: the actual system-level reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall

/-- Evaluation-defined natural isomorphisms at all four coefficient stages,
with actual system evaluation and transposition. The signed shift, composition,
completion-unit, reduction and argument-first clauses are the companion
statements in this module, all listed in the owning node's declaration record.
Source: Stacks 0GMX and the agent-formulated derived/completed enhancement in
main-20261015 theorem-poincare-duality-frobenius--2 Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Proof, following the node's complete sixteen-step construction:

1. Put $F=g^{-1}$, using the covering-preserving equivalence $(U\to X)\mapsto(U\to X\xrightarrow
gY)$. Its quasi-inverse is inverse image along $g^{-1}$. Thus $F$ is exact, preserves products
and coproducts, and identifies constant finite coefficient sheaves, compatibly with every
quotient map. Also $F\widehat{\mathcal
O}_{E,Y}=F\lim_n(A_{E,n})_Y\cong\lim_n(A_{E,n})_X=\widehat{\mathcal O}_{E,X}$. This is the
actual comparison induced by all the projections. Reindexing sheaves and their module actions
gives mutually inverse module equivalences for these completed ring sheaves as well: the inverse
coefficient map is obtained by the same construction for $g^{-1}$ and their composites are
identities on every projection. The tensor and sheaf-Hom comparisons are those on local
sections, $s\otimes t\mapsto Fs\otimes Ft$ and $f\mapsto Ff$.
Uses: lem-weil-proetale-isomorphism-inverse-image, lem-pur-isomorphism-inverse-image-tensor-hom.

2. These equivalences preserve the resolution classes directly. If $I$ is K-injective and $A$ is
acyclic, a chain map $A\to FI$ corresponds under the inverse exact equivalence to a map
$F^{-1}A\to I$; its null homotopy transports back. If $Q$ is K-flat, then $A\otimes FQ\cong
F(F^{-1}A\otimes Q)$ is acyclic. Flat terms are preserved by the same argument on short exact
sequences. Exactness carries quasi-isomorphisms to quasi-isomorphisms, and termwise application
descends to the derived categories with the specified shift comparison. The termwise unit and
counit still give inverse derived equivalences. At finite coefficients this derived functor is
exactly $P=Lg^*$ in the question.
Uses: def-pur-kinjective-complex, def-pc-kflat-complex,
lem-pur-isomorphism-inverse-image-tensor-hom, situation-conventions.

3. For finite coefficients, and separately in the ambient completed-ring module category, choose
a representative $K$ of $M$ and a K-injective representative $I$ of $N$. In Hom degree $r$ the
sheaf comparisons of Step 1 give $F\prod_p\mathcal Hom(K^p,I^{p+r})\cong\prod_p\mathcal
Hom(FK^p,FI^{p+r})$. They commute with $d(f)=d_I f-(-1)^r f d_K$, so define an isomorphism of
Hom complexes. Step 2 makes $FI$ an admissible K-injective representative. Consequently
localization gives an isomorphism $c:FH(M,N)\cong H(FM,FN)$. Naturality holds on maps of
complexes, and independence of representatives and descent in both variables follow from the
cited quasi-isomorphism invariance of Hom complexes. In particular this covers arbitrary
unbounded finite-coefficient inputs.
Uses: def-pur-derived-internal-hom, def-pur-hom-complex, lem-pur-rhom-well-defined.

4. The cited internal currying isomorphism, followed by global-Hom recovery, gives the
tensor-Hom transposition bijection. Use flat-term K-flat representatives for the tensor inputs.
The canonical tensor comparison $\mu$ is induced by the ordinary comparison on their total
tensor complexes. Evaluation is ordinary Hom-complex evaluation followed by the inverse
localized augmentation of the target. Reindexing the pure-tensor evaluation $f\otimes x\mapsto
f(x)$ gives the same chain map on either side. When evaluation is written in the order $x\otimes
f$, both sides use the same Koszul symmetry. Thus $\operatorname{ev}_{FM,FN}(1\otimes
c)\mu=F(\operatorname{ev}_{M,N})$. The closed adjunction and its representative normalization
identify this $c$ with the evaluation-defined comparison; the transposition bijection makes it
the unique map satisfying this equation.
Uses: lem-pc-kflat-resolution, lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-pur-rhom-global-sections, lem-sfb-ringed-derived-monoidal-comparisons,
def-coef-ringed-tensor-hom-model.

5. For $b:M\otimes^L L\to N$ write $b=\operatorname{ev}_{M,N}(1\otimes b^\sharp)$. Apply $F$ and
the naturality of $\mu$. Step 4 gives
$F(b)\mu_{M,L}^{-1}=\operatorname{ev}_{FM,FN}(1\otimes(cF(b^\sharp)))$. Applying the inverse of
the transposition bijection proves the displayed transposition formula. It also proves
naturality in $M,N$: after uncurrying either side of the naturality square one obtains the same
composite of evaluation with the two input maps.
Uses: def-coef-ringed-tensor-hom-model.

6. The shift comparison for $F$ is identity in each degree. The Hom-complex identifications for
$H(M[a],N[b])$ reindex the factors and multiply by the usual signs coming from $d_{K[a]}=(-1)^a
d_K$. Step 3 applies $F$ to the same factors and the same integer signs, so its square with each
of these identifications commutes as a square of complexes. It therefore commutes in the derived
category. This checks shifts in both Hom inputs, rather than only a shift of the output.
Uses: situation-conventions, def-pur-hom-complex.

7. For a second scheme isomorphism $h:Z\to X$, identify $P_{gh}$ with $P_hP_g$ by the canonical
derived pullback-composition map. The two candidate internal-Hom comparisons become equal after
uncurrying: both give $P_hP_g(\operatorname{ev})$, since the tensor-composition square in the
cited statement commutes. Injectivity of transposition proves the composition identity for $c$.
For the identity scheme map it similarly gives the identity comparison. This is also visible
before localization: two successive reindexings send a local homomorphism $f$ to $h^{-1}g^{-1}f$
in either construction.
Uses: lem-sfb-ringed-derived-monoidal-comparisons, def-coef-ringed-tensor-hom-model.

8. Now work integrally. For a derived-complete input $K$, the canonical quotient-tower unit
$u_K:K\to\mathcal L_Y\mathcal R_YK$ is an isomorphism: apply the finite-free completed-scalar
comparison with $L=E$. In particular this is the canonical unit, not an arbitrarily chosen
isomorphism with a Roos triangle. Reindexing takes each reduction to the corresponding reduction
of $FK$ and commutes with its quotient maps. It commutes with total derived inverse limit: apply
it termwise to a K-injective resolution in the abelian tower category; Step 2's null-homotopy
argument applies to tower maps, and the ordinary limit commutes with this equivalence. Hence
$F\mathcal L_Y\mathcal R_YK\cong\mathcal L_X F_\bullet\mathcal R_YK=Lg^*K$. Composing with
$F(u_K)$ gives the claimed natural identification $FK\cong Lg^*K$, with all its reduction
projections fixed.
Uses: lem-weil-finite-free-completed-scalar-comparison,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-coef-derived-system-evaluation-calculus,
prose-03-02.

9. The same calculation applied to the actual strict tensor-reduction complexes identifies
$F(M\widehat\otimes^L N)$ with $FM\widehat\otimes^L FN$. On a flat-term K-flat model it
reindexes each total-tensor summand, and on the Roos realization it reindexes both product
coordinates and $1-s$. This is the specified completed tensor comparison, since that comparison
is fixed by precisely these representative and Roos-coordinate equations. Coefficient
transitions commute before taking the limit. The comparison is invertible, with inverse given by
inverse reindexing. Substitution of normalized tensor/pullback systems shows that composition,
symmetry, and shift comparisons have the same normalization after realization.
Uses: def-pur-completed-pullback-tensor-comparison,
lem-pur-completed-operation-tower-substitution.

10. To check integral evaluation against completed tensor, use the completion reflector. The
constant-completion comparison identifies quotient-tower completion with Koszul completion,
respecting its unit. The reflector then gives, for a complete target $N$,
$\operatorname{Hom}(\widehat{M\otimes^LL},N)\cong\operatorname{Hom}(M\otimes^LL,N)$
and $\operatorname{Hom}(M\otimes^LL,N)\cong\operatorname{Hom}(L,H(M,N))$.
Here the hat is the functorial completion of the ordinary tensor; its quotient tower is exactly
the defining tower of completed tensor. Thus evaluation for completed tensor is the unique
extension of ordinary evaluation along the completion unit. This establishes transposition on
the complete full subcategory without assuming that ordinary tensor is already complete or that
$M$ is perfect.
Uses: lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-koszul-completion-reflector, def-coef-ringed-tensor-hom-model.

11. Use the ambient completed-ring Hom comparison of Step 3. Under Step 8 it is the required
integral $c$. Its source is constructible by the hypothesis on $H(M,N)$ and preservation of the
integral category by pullback; hence its target is constructible as well. Precompose its
completed evaluation equation with the ordinary-to-completed tensor unit. By Steps 4 and 9 this
becomes the already proved ordinary evaluation equation. The reflector's bijection in Step 10
proves equality of the completed maps. Step 5 now proves the integral transposition formula;
Steps 6 and 7 prove the shift and composition identities, since completion units and both Roos
coordinates commute with reindexing. The hypothesis on the internal Hom is used here to stay on
the stated constructible domain, not to obtain its ambient comparison.
Uses: lem-pur-integral-operations-preserve-constructible,
lem-weil-pbc-ringed-koszul-completion-reflector.

12. For the system assertion, reindex the underlying site while keeping the inverse-sequence
index and all coefficient quotient arrows. This defines an exact equivalence of the two abelian
categories of strict module systems, with an explicit inverse. Step 2 therefore applies to their
unbounded derived categories. On their ringed sequence topoi, the product-Hom-complex
construction of Step 3 gives an actual internal-Hom comparison and Step 4 gives an actual
equality of evaluation maps. For cartesian first inputs its evaluations are the finite-level
comparisons, by the fiberwise-Hom identification in the cited semilinear-system statement. In
the transition formula of that statement, reindexing commutes with scalar extension, $t^M$, its
inverse, $t^N$, and evaluation; consequently it gives the same transpose. Thus the maps respect
the specified system transitions, before evaluation at any level.
Uses: lem-coef-semilinear-derived-sections, lem-coef-derived-system-evaluation-calculus.

13. The comparison with integral reduction is the square having top $\mathcal
R_X(FH(M,N))\to\mathcal R_XH(FM,FN)$ and bottom $F_\bullet\mathcal I_Y(\mathcal R_YM,\mathcal
R_YN)\to\mathcal I_X(\mathcal R_XFM,\mathcal R_XFN)$, with vertical maps the specified $\beta$
and the canonical reduction/reindexing identifications. This square commutes as a system square:
$\beta$ is defined by the same evaluation, and Step 12's reindexing carries that evaluation
chain map and its transpose to themselves. Its unit/counit comparisons are the reduction/limit
adjunction's actual unit and counit, so applying the functorial $\mathcal L$ preserves this
square and all the evaluation and transposition identities. This proves the demanded realization
normalization. It uses neither equality detection by finite evaluations nor invertibility of
$\beta$ for arbitrary inputs; the integral Hom comparison is the ambient one already
constructed.
Uses: lem-coef-derived-system-evaluation-calculus, lem-coef-semilinear-derived-sections.

14. Rationalize the integral maps and their inverses. For arbitrary arrows $a=\sum_i
a_i\otimes\lambda_i$ and $b=\sum_j b_j\otimes\nu_j$ in localized Hom groups, each naturality or
evaluation equation expands by bilinearity to the integral equation for $(a_i,b_j)$ multiplied
by $\lambda_i\nu_j$; similarly the transpose identity is linear in its input. The inverse
identities and shift/composition identities localize as well. This proves the assertion for
arbitrary rational morphisms, rather than just arrows which are integral. These are exactly the
localized operations specified in the question.
Uses: def-weil-rationalization-karoubi, prose-03-02.

15. For a finite coefficient extension $E\subset L$, its completed coefficient sheaf is finite
free over the original completed coefficient sheaf, and ordinary scalar extension agrees
canonically with the specified completed one. The evaluation-normalized derived scalar
adjunction identifies the restriction of $H_S(S\otimes_R^LM,S\otimes_R^LN)$ with
$H_R(M,N\otimes_R^LS)$. On choosing a finite free basis for $S$, the latter is a finite direct
sum of copies of $H_R(M,N)$: internal Hom preserves finite biproducts, either by its Hom-complex
formula or by the transposition bijection. Therefore the scalar comparison is the direct sum of
copies of Step 3's comparison, with evaluation $(f\otimes s)(x\otimes t)=f(x)\otimes st$.
Reindexing fixes the coefficient scalars and hence commutes with this map. This argument uses
finite direct sums only, so imposes no perfectness condition on the inputs. The formula is basis
independent because it is the transpose of evaluation. It commutes with a further extension by
associativity of scalar multiplication and tensor reassociation. The existing operation/scalar
comparisons therefore carry $c$ to the comparison at the larger field, with its evaluation and
shifts.
Uses: lem-weil-finite-free-completed-scalar-comparison,
lem-pur-integral-operations-scalar-extension, lem-sfb-dc-hom-scalar-adjunction.

16. Represent all objects, arrows and the comparisons over one common finite coefficient field
in $\overline{\mathbf Q}_\ell$. Step 15 makes the class of $c$ independent of enlarging that
field. If two arrow representatives become equal at a further field, their naturality equations
and images under $c$ agree there, hence define equal classes. Evaluation, transposition,
inverses, composition and shifts can each be checked at that common field using Steps 11 and 14;
their classes have the required identities. This is precisely the common-stage operation
construction, and completes all coefficient stages.
Uses: def-weil-algebraically-closed-coefficients, prose-03-02.
-/
theorem derivedAutomorphismHomEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    (∃ e : finiteIntrinsicDerivedInternalHom l E Y n ⋙ finiteDerivedPullback l E n g ≅
        ((finiteDerivedPullback l E n g).op.prod (finiteDerivedPullback l E n g)) ⋙
          finiteIntrinsicDerivedInternalHom l E X n,
      ∀ M N, e.hom.app (op M, N) = podFiniteHomComparison l E g n M N) ∧
    (∃ e : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
        podPairPullback (constructibleIntegralPullback l E g) _ _
          (podIntegralPairs_pullback l E g) ⋙ constructibleIntegralHom l E X,
      ∀ P, e.hom.app P = podIntegralHomComparison l E g P) ∧
    (∃ e : rationalDerivedInternalHom l E Y ⋙ rationalDerivedPullback l E g ≅
        podPairPullback (rationalDerivedPullback l E g) _ _
          (podRationalPairs_pullback l E g) ⋙ rationalDerivedInternalHom l E X,
      ∀ P, e.hom.app P = podRationalHomComparison l E g P) ∧
    (∃ e : commonStageDerivedInternalHom l Ω Y ⋙ commonStageDerivedPullback l Ω g ≅
        podPairPullback (commonStageDerivedPullback l Ω g) _ _
          (podCommonPairs_pullback l Ω g) ⋙ commonStageDerivedInternalHom l Ω X,
      ∀ P, e.hom.app P = podCommonHomComparison l Ω g P) ∧
    PodPartialHomCompatibility (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g) ∧
    PodPartialHomCompatibility (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g) ∧
    PodPartialHomCompatibility (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g) ∧
    (∀ M N, IsIso (podSystemHomComparison l E g M N)) ∧
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
      (pullbackTensorSystemComparison l E g) := by
  have hf := podFiniteHomComparison_laws l E g n
  have hi := podIntegralHomComparison_laws l E g
  have hr := (podRationalHomComparison_laws l E g).1
  have hc := podCommonHomComparison_laws l Ω g
  refine ⟨?_, ?_, ?_, ?_, hi, hr, hc, podSystemHomComparison_laws l E g⟩
  · let e : finiteIntrinsicDerivedInternalHom l E Y n ⋙ finiteDerivedPullback l E n g ≅
        ((finiteDerivedPullback l E n g).op.prod (finiteDerivedPullback l E n g)) ⋙
          finiteIntrinsicDerivedInternalHom l E X n :=
      NatIso.ofComponents (fun P ↦ @asIso _ _ _ _
        (podFiniteHomComparison l E g n P.1.unop P.2) (hf.1 _ _))
        (fun f ↦ hf.2.1 _ _ _ _ f.1.unop f.2)
    exact ⟨e, fun _ _ ↦ rfl⟩
  · let e : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
        podPairPullback (constructibleIntegralPullback l E g) _ _
          (podIntegralPairs_pullback l E g) ⋙ constructibleIntegralHom l E X :=
      NatIso.ofComponents (fun P ↦ @asIso _ _ _ _
        (podIntegralHomComparison l E g P) (hi.isIso P))
        (fun f ↦ hi.naturality _ _ f)
    exact ⟨e, fun _ ↦ rfl⟩
  · let e : rationalDerivedInternalHom l E Y ⋙ rationalDerivedPullback l E g ≅
        podPairPullback (rationalDerivedPullback l E g) _ _
          (podRationalPairs_pullback l E g) ⋙ rationalDerivedInternalHom l E X :=
      NatIso.ofComponents (fun P ↦ @asIso _ _ _ _
        (podRationalHomComparison l E g P) (hr.isIso P))
        (fun f ↦ hr.naturality _ _ f)
    exact ⟨e, fun _ ↦ rfl⟩
  · let e : commonStageDerivedInternalHom l Ω Y ⋙ commonStageDerivedPullback l Ω g ≅
        podPairPullback (commonStageDerivedPullback l Ω g) _ _
          (podCommonPairs_pullback l Ω g) ⋙ commonStageDerivedInternalHom l Ω X :=
      NatIso.ofComponents (fun P ↦ @asIso _ _ _ _
        (podCommonHomComparison l Ω g P) (hc.isIso P))
        (fun f ↦ hc.naturality _ _ f)
    exact ⟨e, fun _ ↦ rfl⟩

end WeilConjectures
