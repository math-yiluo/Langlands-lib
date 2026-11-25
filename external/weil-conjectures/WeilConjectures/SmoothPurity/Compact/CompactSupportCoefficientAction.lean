/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SmoothPurity.Supporting.MixedReductionUnit
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Normalized finite-stage compact-support action

Source: blueprint definition order 1490 and the coefficient comparisons in
proposition-six-operations-change-coefficients, compact-support paragraph
(blueprint: def-weil-compact-support-coefficient-action).

The finite action is fixed to the already normalized integral/Roos construction.
The coefficient comparison is required to be the tensor-unit mate at finite levels.
The finite-field-independence statement asserts existence of this normalized package.

## Main definitions

- `sfCompactSupportFiniteFunctor`: actual tensor extension of the normalized integral action.
- `SfCompactSupportIntegralBetaSpec`: the prescribed finite tensor-unit mate equation.
- `SfCompactSupportCoefficientAction`: coherent normalized action on coefficient stages.
- `SfCompactSupportCoefficientAction.representative`: the specified common-stage map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

section FiniteMate
variable {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
  (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The finite-coefficient comparison is the unique tensor-linear lift of compact
support of the input tensor unit, followed by the fixed restriction comparison.
Source: proposition-six-operations-change-coefficients and lemma-sp-reduction--1
(blueprint: def-weil-compact-support-coefficient-action). -/
def sfCompactSupportFiniteMate
    (K : proEtaleDerivedCategory X A)
    (M : proEtaleDerivedCategory X B)
    (ηM : K ⟶ (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory.obj M)
    (N : proEtaleDerivedCategory Y B)
    (ηN : (sfAmbientCompactSupportCandidate A c).obj K ⟶
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.obj N)
    (hN : ∀ Z : proEtaleDerivedCategory Y B,
      Function.Bijective (fun a : N ⟶ Z ↦ ηN ≫
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map a)) :
    N ⟶ (sfAmbientCompactSupportCandidate B c).obj M :=
  (Equiv.ofBijective _ (hN _)).symm
    ((sfAmbientCompactSupportCandidate A c).map ηM ≫
      (sfCompactSupportRestriction c φ).hom.app M)
end FiniteMate

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The integral coefficient comparison is the finite tensor-unit mate on every
quotient. All units are the prescribed mixed tensor/diagonal Roos units. The output
unit is transported through the fixed reduction isomorphism of the integral action.
The existential variable is only a proof of a universal property, not comparison data.
Source: proposition-six-operations-change-coefficients, completed compact-support and associativity
paragraphs (blueprint: def-weil-compact-support-coefficient-action). -/
def SfCompactSupportIntegralBetaSpec
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (b : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ⋙
          sfCompactSupportFiniteIntegralFunctor l K₀ hl c L) : Prop :=
  let FX := sfCompactSupportFiniteIntegralFunctor l K₀ hl c E
  let TX := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
  let TY := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    let φ := integralScalarQuotientMap l E L ι n
    let R := (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory
    let A := (scalarReductionDerivedExtension l E X n).obj K.obj
    let M := (scalarReductionDerivedExtension l L X n).obj (TX.obj K).obj
    let N := (scalarReductionDerivedExtension l L Y n).obj (TY.obj (FX.obj K)).obj
    let ηM := sfMixedCompletedReductionUnit l E L ι X n K.obj
    let ηN := (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).inv ≫
      sfMixedCompletedReductionUnit l E L ι Y n (FX.obj K).obj
    ∃ hN : ∀ Z : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l L (n + 1)),
      Function.Bijective (fun a : N ⟶ Z ↦ ηN ≫ R.map a),
      (scalarReductionDerivedExtension l L Y n).map (b.hom.app K).hom ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c L (TX.obj K) n).hom =
          sfCompactSupportFiniteMate φ c A M ηM N ηN hN

end FiniteAction

section Action
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (c : Compactification f)

/-- A coefficient action with both its finite maps and its beta fixed to the actual
compact-support construction. The finite equality retains the complete previously
normalized strict-tower action, including all rational pure tensors. The integral
beta is the tensor-unit mate above, and rational beta is its raw localization.
Source: definition order 1490 and proposition-six-operations-change-coefficients
(blueprint: def-weil-compact-support-coefficient-action). -/
structure SfCompactSupportCoefficientAction where
  /-- The compatible action on the recorded stage systems. -/
  system : (stageSystem l Ω X).Morphism (stageSystem l Ω Y)
  /-- All maps, not just objects, are the fixed finite compact-support functors. -/
  finite_eq : ∀ E, system.Φ E = sfCompactSupportFiniteFunctor l K₀ hl c
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E)
  /-- The literal output pairs are the previously defined values. -/
  value_eq : ∀ A : Pair l Ω X, system.functor.obj A =
    sfQbarCompactSupportValue l K₀ hl Ω c A.stage A.obj.obj
  /-- The integral coefficient comparisons on the actual completed scalar extensions. -/
  integralBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙ integralTransition l Ω Y E L h ≅
      integralTransition l Ω X E L h ⋙ sfCompactSupportFiniteIntegralFunctor l K₀ hl c
      (AlgebraicallyClosedCoefficients.Coefficient l Ω L)
  /-- The comparison is the prescribed tensor-unit mate, not an arbitrary natural iso. -/
  integralBeta_spec : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    SfCompactSupportIntegralBetaSpec l K₀ hl c
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E)
      (AlgebraicallyClosedCoefficients.Coefficient l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (integralBeta h)
  /-- The rational comparison is exactly the localization of this integral map. -/
  rationalBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : Stage l Ω X E), HEq ((system.β h).hom.app K)
      ((sfRationalConstructibleLocalization l (AlgebraicallyClosedCoefficients.Coefficient
        l Ω L) Y).map ((integralBeta h).hom.app K.obj))

namespace SfCompactSupportCoefficientAction
variable {l K₀ hl Ω c} (S : SfCompactSupportCoefficientAction l K₀ hl Ω c)

/-- The recorded output pair, retained without a new coefficient-category definition.
Source: definition order 1490
(blueprint: def-weil-compact-support-coefficient-action). -/
abbrev value (_S : SfCompactSupportCoefficientAction l K₀ hl Ω c) (A : Pair l Ω X) :=
  sfQbarCompactSupportValue l K₀ hl Ω c A.stage A.obj.obj

/-- The specified common-stage comparison is the image of alpha followed by alpha'
inverse, transported to the literal output values.
Source: definition order 1490, finite-field-independence proof step 3
(blueprint: def-weil-compact-support-coefficient-action). -/
def comparison {A B P : Pair l Ω X} (α : A ≅ P) (α' : B ≅ P) :
    S.value A ≅ S.value B :=
  (eqToIso (S.value_eq A)).symm ≪≫ S.system.functor.mapIso (α ≪≫ α'.symm) ≪≫
    eqToIso (S.value_eq B)

/-- The literal class [M, beta inverse F_M(u) beta], in diagrammatic order.
Source: definition order 1490, finite-field-independence proof step 3
(blueprint: def-weil-compact-support-coefficient-action). -/
def representative (A B : Pair l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
    (hA : A.stage ≤ M) (hB : B.stage ≤ M) (u : StageHom A B ⟨M, hA, hB⟩) :
    S.value A ⟶ S.value B :=
  eqToHom (S.value_eq A).symm ≫
    ofHom (S.system.functor.obj A) (S.system.functor.obj B) M hA hB
      ((S.system.β hA).hom.app A.obj ≫ (S.system.Φ M).map u ≫
        (S.system.β hB).inv.app B.obj) ≫ eqToHom (S.value_eq B)
end SfCompactSupportCoefficientAction

end Action
end WeilConjectures
