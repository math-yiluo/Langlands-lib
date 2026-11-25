/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Compactification.RefinementCategory

/-!
# The specified integral compact-support tower

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0GL0
(blueprint: def-sf-integral-compact-support-tower).

The finite terms use the chosen compactification. The quotient transitions are the
scalar-extension adjuncts of the reduction units followed by the normalized
compact-support coefficient comparisons. Derived limits are properties of arbitrary
objects, expressed by their Roos triangles.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Positive coefficient levels are finite. Source: blueprint coefficient extension;
Bhatt--Scholze, Section 6.7 (blueprint: def-sf-integral-compact-support-tower). -/
noncomputable instance sfCompactSupportCoefficientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Restriction from exponent n+2 to exponent n+1 along the specified quotient map.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable abbrev sfCompactSupportFiniteRestriction (T : Scheme.{u}) (n : ℕ) :
    scalarReductionTarget.{u, u} l E T n ⥤ scalarReductionTarget.{u, u} l E T (n + 1) :=
  proEtaleCoefficientRestrictScalars T (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finite quotient restriction is left exact. Source: Stacks Tag 03DA
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable instance sfCompactSupportFiniteRestrictionLimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (sfCompactSupportFiniteRestriction l E T n) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits T
    (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finite quotient restriction is right exact. Source: Stacks Tag 03DA
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable instance sfCompactSupportFiniteRestrictionColimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (sfCompactSupportFiniteRestriction l E T n) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits T
    (Padic.coefficientExtensionTransition l E (n + 1))

/-- The completion projections commute with the specified finite quotient transition.
Source: Stacks Tag 03CO; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-sf-integral-compact-support-tower).
Proof: the completed sheaf is the inverse limit of the finite quotient tower.
Its cone condition identifies the higher projection followed by the quotient map
with the lower projection. Forgetting commutativity gives exactly this condition
for ring sheaves; faithfulness lifts it back to commutative ring sheaves. -/
theorem sfCompactSupportProjection_transition (T : Scheme.{u}) (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E T (n + 1) ≫
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift) =
      completedIntegralCommRingProjectionUnrestricted l E T n := by
  apply (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  change limit.π (integralCoefficientSheafSystem l E T) (Opposite.op (n + 1)) ≫
      integralCoefficientSheafTransition l E T n =
    limit.π (integralCoefficientSheafSystem l E T) (Opposite.op n)
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    using limit.w (integralCoefficientSheafSystem l E T)
      (homOfLE (Nat.le_succ n)).op

/-- The sectionwise identity composite restriction comparison, supplied by the shared
commutative ring-sheaf restriction interface. Source: Stacks Tags 03DA and 03CO
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable def sfCompactSupportRestrictionComp (T : Scheme.{u}) (n : ℕ) :
    sfCompactSupportFiniteRestriction l E T n ⋙
        scalarReductionRestriction.{u, u} l E T (n + 1) ≅
      scalarReductionRestriction.{u, u} l E T n :=
  pbcRestrictComp (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift))
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (sfCompactSupportProjection_transition l E T n)

/-- Exact restriction composition on derived categories. Source: Stacks Tag 015F
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable def sfCompactSupportDerivedRestrictionComp (T : Scheme.{u}) (n : ℕ) :
    (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory ⋙
        scalarReductionDerivedRestriction.{u, u} l E T (n + 1) ≅
      scalarReductionDerivedRestriction.{u, u} l E T n :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (sfCompactSupportRestrictionComp l E T n)

/-- The canonical reduction map at the finite coefficient level. It is the adjunct
of the lower reduction unit under the higher reduction/restriction adjunction.
On a K-flat representative it is precisely x tensor a ↦ x tensor rho(a), since that
adjunction's unit is x ↦ x tensor 1 and the restriction comparison is identity on
sections. Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tags 03EK and 07A6
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable def sfCompactSupportReductionTransition (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E T (n + 1)).obj K ⟶
      (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory.obj
        ((scalarReductionDerivedExtension.{u, u} l E T n).obj K) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E T (n + 1)).choose.homEquiv
    K _).symm
    ((sfDerivedReductionUnit l E T n).app K ≫
      (sfCompactSupportDerivedRestrictionComp l E T n).inv.app
        ((scalarReductionDerivedExtension.{u, u} l E T n).obj K))

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The actual term Res_n R(c.g)_* c.i_! (K tensor^L A_n), where the natural index
n denotes exponent n+1. Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable def sfCompactSupportTerm
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E Y) :=
  (scalarReductionDerivedRestriction.{u, u} l E Y n).obj
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))

/-- The specified quotient transition: apply compact support at the higher level to
the reduction map, apply the compact-support restriction comparison, and restrict to
completed coefficients. The final identity-on-sections comparison identifies the two
composite restrictions. Source: Bhatt--Scholze, Sections 6.5 and 6.7
(blueprint: def-sf-integral-compact-support-tower). -/
noncomputable def sfCompactSupportTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    sfCompactSupportTerm l E c K (n + 1) ⟶ sfCompactSupportTerm l E c K n :=
  (scalarReductionDerivedRestriction.{u, u} l E Y (n + 1)).map
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (sfCompactSupportReductionTransition l E X K n) ≫
      (sfCompactSupportRestriction c
        (Padic.coefficientExtensionTransition l E (n + 1))).hom.app
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
    (sfCompactSupportDerivedRestrictionComp l E Y n).hom.app
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))

end WeilConjectures
