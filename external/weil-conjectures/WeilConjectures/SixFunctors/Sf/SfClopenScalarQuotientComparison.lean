/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenScalarModuleComparison
import WeilConjectures.SixFunctors.Sf.SfClopenScalarComparisonDescent
import WeilConjectures.SixFunctors.Sf.SfClopenScalarChainComparison

/-! # Scalar extension and actual quotient complexes on a clopen

Source: Stacks Project, Tag 06YY.
(blueprint: lem-sf-clopen-scalar-quotient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Normalized scalar and chain-level quotient comparisons on a clopen component.
This assertion concerns scalar extension and chain maps only: it does not assert
naturality of a derived tower, preservation of completeness, or a Tor bound.

Source: Stacks Project, sites-cohomology.tex, Lemma derived-base-change (Tag 06YY),
Lemma pullback-K-flat, and Lemma pullback-tensor-product; sites.tex, restriction to
an object. Extracted from the scalar-extension and tensor-formula paragraphs of
lem-sf-clopen-derived-compatibility
(blueprint: lem-sf-clopen-scalar-quotient-comparison).

Proof: write T as the disjoint union of U and its open complement, including an
empty component. The finite-clopen module equivalence identifies restriction with
projection. Use d.projection to identify the completed-to-finite coefficient map
with its local counterpart. On presheaf tensor products send s tensor x to
s tensor x after the coefficient identification d.finite; the balanced relations
hold by the projection square. The inverse uses the inverse coefficient comparison.
Continuous restriction commutes with sheafification on the localized site, so these
maps induce inverse module-sheaf maps and are natural in the module. Apply them
degreewise to obtain finite_quotient. Restrict scalars along the completed-to-finite
maps, using the same projection square, to obtain quotient. Their formulas on
sheafified pure tensors are the two asserted normalization equalities.

Projection in a finite product preserves K-flat complexes and flat terms. The
ordinary tensor comparison therefore descends through K-flat localization to the
natural derived comparison reduction. Its square with the universal comparison
is the derived base-change square. To obtain that square for arbitrary P, first
check it on K-flat resolutions; naturality of both universal counits and the
ordinary comparison then gives it after the resolution map, which is inverted
in the source derived category. Thus no K-flat hypothesis on P is needed.

The two chain coherence equations follow from these pure-tensor formulas and the
existing formulas for units and transitions; they are proved by the consumer. The
constructions also apply to an empty component, whose module category is zero. -/
theorem sf_clopen_scalar_quotient_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    ∃ (reduction : ∀ n : ℕ,
    scalarReductionDerivedExtension l E T n ⋙ sfClopenFiniteDerivedRestriction d n ≅
      sfClopenDerivedRestriction d ⋙ scalarReductionDerivedExtension l E U.toScheme n)
       (finite_quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteComplexRestriction d n).obj (unrestrictedTowerFiniteComplex l E T n P) ≅
      unrestrictedTowerFiniteComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P))
       (quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenComplexRestriction d).obj (unrestrictedTowerComplex l E T n P) ≅
      unrestrictedTowerComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)),
    (∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((finite_quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x) ∧
    (∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteDerivedRestriction d n).map (sfClopenReductionCounit T n P) ≫
        (sfClopenFiniteLocalizationIso d n (unrestrictedTowerFiniteComplex l E T n P)).hom ≫
        DerivedCategory.Q.map (finite_quotient P n).hom =
      (reduction n).hom.app (DerivedCategory.Q.obj P) ≫
        (scalarReductionDerivedExtension l E U.toScheme n).map
          (sfClopenLocalizationIso d P).hom ≫
        sfClopenReductionCounit U.toScheme n ((sfClopenComplexRestriction d).obj P)) ∧
    (∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x) := by
  classical
  let := fun n ↦ scalarReductionExtensionAdditive l E T n
  let := fun n ↦ scalarReductionExtensionAdditive l E U.toScheme n
  let := d.additive
  let := d.finite_additive
  choose c hc using sf_clopen_scalar_module_comparison l E T U d
  obtain ⟨quotient, hquot⟩ := sf_clopen_scalar_chain_comparison l E T U d
  choose reduction hred using fun n ↦
    sf_clopen_scalar_comparison_descent l E T U hU d n (c n)
  let finiteQuotient (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenFiniteComplexRestriction d n).obj (unrestrictedTowerFiniteComplex l E T n P) ≅
        unrestrictedTowerFiniteComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P) :=
    (NatIso.mapHomologicalComplex (c n) (.up ℤ)).app P
  refine ⟨reduction, finiteQuotient, quotient, ?_, fun P n ↦ hred n P, ?_⟩
  · intro P n q V s x
    exact hc n (P.X q) V s x
  · exact hquot

end WeilConjectures
