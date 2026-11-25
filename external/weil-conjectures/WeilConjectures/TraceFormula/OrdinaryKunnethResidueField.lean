/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OrdinaryKunnethCriterion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaResidueFieldEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.FieldBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness
import WeilConjectures.Tactic.TransportExact

/-!
# The ordinary Künneth formula for global sections with coefficients `𝔽_E`

For a cartesian square `P = X ×_k Y` of `k`-schemes of finite type over a separably closed field
`k` in which `ℓ` is invertible, and complexes `A` on `X`, `B` on `Y` of module objects over
`𝔽̲_E` which are bounded below of étale origin, the ordinary Künneth map
`RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(P, Lp₁^* A ⊗ Lp₂^* B)` (`ProEtale.CondensedRing.lowerStarKunnethMap'`
of the two squares over `Spec k`) is an isomorphism
(`ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback_residueField`; blueprint
`lemma-kunneth-one-identity-factor--1`, torsion case).

By `ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isIso` it suffices that generic base
change along `Y ⟶ Spec k`, the relative Künneth formula for `p₂` and the projection formula over
`Spec k` hold; these are the étale statements (`Etale.isIso_derivedBaseChangeMap_of_field`,
`Etale.isIso_rightDerivedLowerStarProjectionMap_leftDerivedUpperStar`, Stacks 0F1I, 0F12, 0F1N)
read on module objects through the comparisons of the étale, pro-étale and condensed finite
coefficient categories.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

variable {k : Type u} [Field k] [IsSepClosed k] [Fact (ringChar k ≠ ℓ)]
  {X Y P : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (integersResidueField ℓ E.1)

/-- **The ordinary Künneth formula for global sections with coefficients `𝔽_E`** (blueprint
`lemma-kunneth-one-identity-factor--1`, torsion case; SGA 4½, [Th. finitude], Cor. 1.11): for a
cartesian square `P = X ×_k Y` of `k`-schemes of finite type over a separably closed field `k` with
`ℓ ≠ char k`, and complexes `A`, `B` of module objects over `𝔽̲_E` bounded below of étale
origin, the Künneth map `RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(X ×_k Y, Lp₁^* A ⊗ Lp₂^* B)` is an
isomorphism. -/
theorem isIso_lowerStarKunnethMap'_of_isPullback_residueField (p₁ : P.left ⟶ X.left)
    (p₂ : P.left ⟶ Y.left) (w₁ : p₁ ≫ X.hom = P.hom ≫ 𝟙 _) (w₂ : p₂ ≫ Y.hom = P.hom ≫ 𝟙 _)
    (h : IsPullback p₁ p₂ X.hom Y.hom)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj 𝔽 X.left)))
    (hA : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) X.left
      ((finiteCoefficientDerivedEquivalence X.left (integersResidueField ℓ E.1)).functor.obj A))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj 𝔽 Y.left)))
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) Y.left
      ((finiteCoefficientDerivedEquivalence Y.left (integersResidueField ℓ E.1)).functor.obj B)) :
    IsIso (lowerStarKunnethMap' 𝔽
      (⟨w₁⟩ : CommSq p₁ P.hom X.hom (𝟙 _)) (⟨w₂⟩ : CommSq p₂ P.hom Y.hom (𝟙 _)) A B) := by
  have := quasiSeparated_of_locallyOfFiniteType_spec_field X.hom
  have := hasInvertibleExponent_residueFieldCoeff ℓ E (𝟙 (Spec (.of k)))
  have h₁ := isIso_baseChangeMap_app_of_field_residueField ℓ E.1 h A hA
  have h₂ := isIso_projectionMorphism_residueField_leftDerivedUpperStar ℓ E.1 X.hom Y.hom h hA hB
  have h₃ := isIso_projectionMorphism_residueField_rightDerivedLowerStar ℓ E.1 X.hom Y.hom hA hB
  refine isIso_lowerStarKunnethMap'_of_isIso 𝔽 ⟨w₁⟩ ⟨w₂⟩ (CommSq.mk h.w) A B ?_ ?_ ?_
  · transport_exact h₁
  · transport_exact h₂
  · transport_exact h₃

end AlgebraicGeometry.ProEtale.CondensedRing
