/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportConstructible
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-!
# Integral, rational, and algebraically closed compact-support functors

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/
def-weil-integral-rational-qbar-compact-support.md, node
def-weil-integral-rational-qbar-compact-support
(blueprint: def-weil-integral-rational-qbar-compact-support).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The integral compact-support value obtained from the specified derived-limit tower.
The natural index n denotes the positive exponent n+1, with the same compactification
at every level. The terms and transitions are sfCompactSupportTerm and
sfCompactSupportTransition, including the quotient-induced reduction map and the
normalized compact-support and composite-restriction comparisons. Exact countable
products of completed-coefficient module sheaves supply derived-category products.
Choose a vertex of the resulting Roos triangle; any two such vertices are isomorphic.
The recorded constructibility theorem supplies membership in the integral category.
Source: blueprint order 1490; Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support).
-/
noncomputable def sfIntegralCompactSupportValue
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructibleCategory l E Y := by
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  let h := (exists_isDerivedLimit_and_iso
      (fun n : ℕ ↦ sfCompactSupportTerm l E c K.obj n)
      (fun n : ℕ ↦ sfCompactSupportTransition l E c K.obj n)).1
  let M : DerivedCategory (scalarReductionSource.{u, u} l E Y) := Classical.choose h
  have hM : IsDerivedLimit
      (fun n : ℕ ↦ sfCompactSupportTransition l E c K.obj n) M := Classical.choose_spec h
  exact ⟨M, sfIntegralCompactSupport_constructible l E c K₀ _hl K.obj K.property M hM⟩

/-- The rational compact-support value in the localized stage category.
K is the integral representative of the rational input; raw scalar localization has
exactly the same objects. Apply the integral value and regard it in that localization.
Source: blueprint order 1490; Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support).
-/
noncomputable def sfRationalCompactSupportValue
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : sfIntegralConstructibleCategory l E X) :
    sfRationalConstructibleCategory l E Y :=
  (sfRationalConstructibleLocalization l E Y).obj
    (sfIntegralCompactSupportValue l E K₀ _hl c K)

/-- The algebraically closed compact-support value is the literal finite-stage pair.
K represents the rational object at E₀, using the canonical small coefficient model.
Keep E₀ as the stage and apply the rational value there. Independence of the integral
representative, finite stage and compactification remains a separate assertion.
Source: blueprint order 1490; Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support).
-/
noncomputable def sfQbarCompactSupportValue
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c : Compactification f) (E₀ : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) X) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y := by
  exact ⟨E₀, sfRationalCompactSupportValue l (Coefficient.{u} l Ω E₀) K₀ _hl c K⟩

end WeilConjectures
