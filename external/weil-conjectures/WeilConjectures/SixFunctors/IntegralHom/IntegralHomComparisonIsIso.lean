/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomComparisonRepresentative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Invertibility of the normalized integral Hom comparison

Source: blueprint order 2478, proof steps 1 and 4-7; Stacks Tags 093M,
06YQ, 08J7, 0A8X and 07A6
(blueprint: lem-sf-integral-hom-comparison-is-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

-- Use the existing sheafification at the coefficient universe for this declaration.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The specified transpose of reduced evaluation is invertible for arbitrary
inputs. The presentation hypotheses only specify the normalized tensor models.

Source: blueprint order 2478, steps 1 and 4-7; Stacks Tags 093M, 06YQ,
08J7, 0A8X and 07A6
(blueprint: lem-sf-integral-hom-comparison-is-iso).

Proof: The coefficient valuation ring is a DVR, hence Noetherian. Completion
identifies the restricted quotient with Q_n=[B --t^(n+1)--> B] in degrees -1,0,
with its degree-zero unit. This bounded free complex is K-flat. The coefficient
extension/restriction adjunction and tensor-Hom adjunction identify the restricted
finite internal Hom with Hom_B(K,Res_n N), naturally in N, by Yoneda. Resolve K
by K-flat P and L by K-injective I. The bounded split-free tensor lemma makes
Tot(I tensor Q_n) K-injective. The restriction of the displayed comparison is
therefore modeled by Hom(P,I) tensor Q_n to Hom(P,Tot(I tensor Q_n)). On a
homogeneous f tensor q it is x maps to (-1)^(degree(q)*degree(x)) f(x) tensor q.
In each total degree, the two finite coefficient degrees commute with the product
over degrees of P, making this a degreewise isomorphism even when P is unbounded.
The differential terms involving d_I,d_P,d_Q have signs respectively bp,
a+1+bp,a+bp+p on x of degree p, on both sides. Thus it is a chain isomorphism.
The evaluation and scalar-unit normalizations identify it with the restriction
of comparison, rather than just an unspecified isomorphism of its endpoints.
Restriction is conservative: it preserves the underlying cohomology sheaves.
Hence the comparison itself is an isomorphism over the finite quotient. The
argument includes zero inputs and n=0, which denotes the first positive power. -/
theorem comparison_isIso
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    IsIso (comparison l E Y D hl m K L) := by
  let U := scalarReductionRestriction l E Y n
  have : PreservesFiniteLimits U := scalarReductionRestrictionLimits l E Y n
  have : PreservesFiniteColimits U := scalarReductionRestrictionColimits l E Y n
  let V := SheafOfModules.toSheaf (completedIntegralCoefficientSheaf l E Y D hl)
  have : (U ⋙ V).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf
      (integralCoefficientSheaf l E Y n)).ReflectsIsomorphisms
  have : U.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp U V
  obtain ⟨P, I, Q, _, _, _, _, hzero, eNeg, eZero, f, hf, s, t, h⟩ :=
    comparison_representative l E Y D hl a n m K L
  have (j : ℤ) : IsIso (f.f j) :=
    twoTermFreeHomTensor_component_isIso Y _ P I Q hzero eNeg eZero f hf j
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  have hmap : IsIso ((scalarReductionDerivedRestriction l E Y n).map
      (comparison l E Y D hl m K L)) := by
    have : IsIso ((scalarReductionDerivedRestriction l E Y n).map
        (comparison l E Y D hl m K L) ≫ t.hom) := by
      rw [h]
      infer_instance
    exact (isIso_comp_right_iff _ t.hom).mp this
  rw [DerivedCategory.isIso_iff]
  intro j
  have : IsIso (U.map ((DerivedCategory.homologyFunctor _ j).map
      (comparison l E Y D hl m K L))) :=
    (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso j) _).2
      (by change IsIso ((DerivedCategory.homologyFunctor _ j).map
            ((scalarReductionDerivedRestriction l E Y n).map
              (comparison l E Y D hl m K L)))
          infer_instance)
  exact isIso_of_reflects_iso _ U

end WeilConjectures.IntegralHom
