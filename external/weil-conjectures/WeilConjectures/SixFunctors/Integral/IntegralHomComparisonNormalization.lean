/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.Integral.IntegralHomComparisonUncurry

/-! # Independence of the normalized integral Hom reduction presentation

Source: Stacks Tags 06YY and 08J7; the universal-property and evaluation normalization
in the integral Hom reduction construction
(blueprint: lem-sfb-integral-hom-comparison-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe d u
open CategoryTheory Opposite
namespace WeilConjectures

/-- The two normalized presentations give the same evaluation-transpose morphism.
Their tensor orders differ by the signed exchange, so equality of maps, rather than
an arbitrary isomorphism between their endpoints, is essential here.

Source: Stacks Tags 06YY and 08J7; the normalization paragraphs of the integral
Hom reduction construction
(blueprint: lem-sfb-integral-hom-comparison-normalization).

Proof: on K-flat pairs the representative comparisons identify both tensors with the
ordinary signed total tensor. Exchange the factors using the Koszul symmetry; its
sectionwise factor is (-1)^(ij). The two evaluation normalizations then agree on
homogeneous generators: the sign in TensorPresentation.evaluation cancels this exchange.
Their adjunction Hom equivalences therefore agree on K-flat sources and K-injective
targets. Every derived source has a K-flat representative and every derived target a
K-injective representative. Naturality and the localization universal property extend
these identifications to all objects. The two scalar comparisons also agree there:
the ordinary units both send x to 1 tensor x, and their counit normalization squares
identify them on every K-flat pair. Apply the target adjunction's injectivity to the
two reduced-evaluation transposes. The preceding equalities identify their uncurried
maps, giving the asserted equality. This includes n=0, zero complexes, and unbounded
inputs; no finite-field hypothesis on the base scheme is used. -/
theorem integralHomComparison_normalization
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (K L : completedIntegralDerivedCategory l E X D hl) :
    integralHomReductionComparison D l hl E X n K L =
      IntegralHom.comparison l E X D hl m K L := by
  apply ((m.target.adjunction
    ((integralDerivedReduction l E X D hl n).obj K)).homEquiv _ _).symm.injective
  rw [integralHomComparison_uncurry_eq D l hl E X n a m K L]
  simp [IntegralHom.comparison]

end WeilConjectures
