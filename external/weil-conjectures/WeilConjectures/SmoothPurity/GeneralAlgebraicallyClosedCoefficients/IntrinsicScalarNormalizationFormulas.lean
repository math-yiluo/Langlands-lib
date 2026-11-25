/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Intrinsic scalar normalization formulas

Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact derived scalar
composition; `SfScalarExtensionComposition.lean`, intrinsic normalization, and
`GeneralAlgebraicallyClosedCoefficientStages.lean`, normalized shifts and associators
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).

The coefficient models and all three comparisons are the published constructions.
`integralOrdinaryDerivedScalar` is the exact termwise induced functor, and
`integralOrdinaryDerivedScalarComp` is the inverse exact-derived composition comparison
followed by the derived image of `integralOrdinaryScalarComp`. The latter's section
normalization is stated below. The integral compositor b is written inline as
`sfIntegralScalarComp` followed by `eqToIso` of the coefficient-inclusion composition law
(the construction `SfStrictDirectImageScalar.integralAssociator` names; it is not
redefined here). Heterogeneous equalities retain the actual coefficient composition
transport, including repeated indices. No idempotent completion is used.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
set_option Elab.async false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  integralScalarExtension integralOrdinaryScalar integralCompletedScalarMap
  sfIntegralOrdinaryComparison integralOrdinaryDerivedScalarComp

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

private theorem index_rational_transport
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (κ : Coefficient.{u} l Ω E →ₐ[Padic l] Coefficient.{u} l Ω M)
    (e : (coefficientInclusion l Ω L M k).comp (coefficientInclusion l Ω E L h) = κ)
    (a : transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
      sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M) κ)
    (ha : HEq a (scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
      (coefficientInclusion l Ω L M k) κ e Y))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      (a.hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω M) Y).map
        ((sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
          eqToIso (congrArg
            (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω M) i Y)
            e)).hom.app K)) := by
  obtain rfl := eq_of_heq ha
  subst κ
  simpa only [scalarAssociator, eqToIso_refl, Iso.trans_refl, sfRationalScalarComp,
    sfRationalConstructibleLocalization, ScalarLocalization.localization] using
    (sfRationalScalarComp_existsUnique l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k)).exists.choose_spec
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K)

/-- The actual rational associator is the rationalization image of the integral one.
HEq retains the specified endpoint equalities of the rational scalar functors.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, rational scalar composition
(blueprint: lem-pur-intrinsic-scalar-normalization-formulas).
Proof: rationalization has unchanged objects. Localize the integral compositor and its
inverse componentwise. On a pure tensor arrow, naturality is integral naturality tensored
with the image of the coefficient. Bilinearity extends this to every arrow
(`def-weil-linear-scalar-localization`, `def-weil-rationalization-karoubi`). Localization
preserves the inverse equations. Every rational object is an integral representative,
so this component prescription uniquely determines `sfRationalScalarComp`. The stage
associator follows it by the coefficient-inclusion equality, hence has the stated image
(`lem-general-algebraically-closed-coefficient-stages`). Equality elimination applies
the same endpoint transport on both sides. Repeated indices need no strict identity
of tensor functors, and primality alone supplies the proof parameter l ≠ 0. -/
theorem intrinsicRationalScalarAssociator_image
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq
      ((associator l Ω Y E L M h k).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω M) Y).map
        ((sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
          eqToIso (congrArg
            (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω M) i Y)
            ((coefficientInclusion_laws l Ω).2 E L M h k))).hom.app K)) := by
  exact index_rational_transport l Ω Y E L M h k
    (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k) (associator l Ω Y E L M h k)
    ((associator_existsUnique l Ω Y E L M h k).exists.choose_spec) K

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures
