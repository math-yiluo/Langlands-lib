/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullCompatible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionRestrictConstructibleProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleDictionary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionAdjoint

/-!
# Reduction modulo `ℓⁿ` commutes with `Rf_!` and `Rf^!` along proper morphisms

For a proper morphism `f`, the reduction modulo `ℓⁿ` read on the small étale site
(`ProEtale.CondensedRing.etaleReduction`) commutes with `Rf_!` through an isomorphism `γ` whose
transpose under `Rf_! ⊣ Rf^!` is an isomorphism
(`ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso`). This assembles
`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_isProper_of_comparisons` with its
inputs: the compatibilities of the pullback comparison with the natural reduction triangle,
the constructibility of restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, and the dictionary
between condensed and étale bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image` (with the compact-support
comparison `γ^!` of `lemma-change-coefficients-compact-support`), for the coefficient map
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site (`definition-constructible-sheaves`), for a proper morphism
`f`. **Reduction modulo `ℓⁿ` commutes with `Rf_!` and with `Rf^!`**: there is an isomorphism
`γ^! : (Rf_! K)_{𝒪_E ⧸ ℓⁿ} ≅ Rf_! (K_{𝒪_E ⧸ ℓⁿ})` whose transpose
`β : (Rf^! K)_{𝒪_E ⧸ ℓⁿ} ⟶ Rf^! (K_{𝒪_E ⧸ ℓⁿ})` under `Rf_! ⊣ Rf^!` is an isomorphism.

This is weaker than the blueprint node, and enough for its use in the trace formula: it covers
only proper `f`, and it only asserts that some isomorphism `γ` with invertible transpose exists,
without identifying `γ` with the canonical `γ^!` of the blueprint (nor `β` with its canonical
comparison). -/
theorem exists_etaleReductionLowerShriekIso (f : Z ⟶ Y) [IsProper f.left] :
    ∃ γ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n Z ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left,
      IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
        (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γ.inv)) := by
  have hη := integersModPowPullUnitCompatible ℓ E n f.left
  have hδ := integersModPowPullδCompatible ℓ E n f.left
  have hZ := restrictScalarsIntegersModPowBoundedConstructible ℓ E n Z.left
  have hY := restrictScalarsIntegersModPowBoundedConstructible ℓ E n Y.left
  have hZo := etaleOriginReading ℓ E n Z
  have hYo := etaleOriginReading ℓ E n Y
  have hZc := boundedConstructibleOfEtale ℓ E n Z
  exact hasEtaleReductionLowerShriekIso_of_isProper_of_comparisons f hη hδ hZ hY hZo hYo hZc

end AlgebraicGeometry.ProEtale.CondensedRing
