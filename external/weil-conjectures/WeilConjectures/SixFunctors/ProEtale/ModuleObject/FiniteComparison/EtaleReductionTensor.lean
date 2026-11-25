/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonTensorEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Monoidal

/-!
# Reduction modulo `ℓⁿ`, read on the étale site, commutes with `⊗ᴸ`

For bounded constructible `𝒪_E`-complexes `K` and `M` on `X_proét`, the reduction modulo `ℓⁿ`
read on the small étale site, `K ↦ Rν_* Φ (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`, commutes with the derived tensor
products (`ProEtale.CondensedRing.nonempty_etaleReductionTensorIso_of_components`; this is
`ProEtale.CondensedRing.nonempty_etaleReductionTensorIso`, stated before the composite functor is
named):

* the reduction `K ↦ K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` commutes with `⊗ᴸ`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReductionTensorIso`);
* the comparison `Φ` of the two finite-coefficient models commutes with `⊗ᴸ`
  (`ProEtale.finiteCoefficientDerivedEquivalenceTensorIso`);
* the images under `Φ` of bounded constructible complexes are bounded below of étale origin
  (`ProEtale.isEtaleOrigin_of_isConstructible`), and `Rν_*`
  commutes with `⊗ᴸ` on these when the tensor product is bounded below
  (`ProEtale.nonempty_rightDerivedComparisonLowerStarTensorIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with the tensor product**, stated
for the composite `Rν_* ∘ Φ ∘ ι ∘ red` (see `nonempty_etaleReductionTensorIso`). -/
theorem nonempty_etaleReductionTensorIso_of_components
    (K M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Nonempty ((R(ν_*(Y.left)[ModuleCat.{u + 1}
        (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))])).obj
        ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj (K ⊗ M)))) ≅
      ((Etale.derivedTensor
          (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))) Y.left).obj
        ((R(ν_*(Y.left)[ModuleCat.{u + 1}
            (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))])).obj
          ((finiteCoefficientDerivedEquivalence Y.left
              (PadicAlgCl.integersModPow ℓ E n)).functor.obj
            ((boundedConstructible _).ι.obj
              ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj K))))).obj
        ((R(ν_*(Y.left)[ModuleCat.{u + 1}
            (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))])).obj
          ((finiteCoefficientDerivedEquivalence Y.left
              (PadicAlgCl.integersModPow ℓ E n)).functor.obj
            ((boundedConstructible _).ι.obj
              ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M))))) := by
  let red := boundedConstructibleIntegersModPowReduction Y.left ℓ E n
  let Φ := (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor
  let e := Φ.mapIso (boundedConstructibleIntegersModPowReductionTensorIso ℓ E n K M) ≪≫
    finiteCoefficientDerivedEquivalenceTensorIso Y.left (PadicAlgCl.integersModPow ℓ E n) _ _
  have hKM :=
    (isEtaleOrigin_of_isConstructible _ (red.obj (K ⊗ M)).property).plusEtaleOrigin
  have hK := (isEtaleOrigin_of_isConstructible _ (red.obj K).property).plusEtaleOrigin
  have hM := (isEtaleOrigin_of_isConstructible _ (red.obj M).property).plusEtaleOrigin
  obtain ⟨e'⟩ := nonempty_rightDerivedComparisonLowerStarTensorIso hK hM
    (DerivedCategory.TStructure.t.plus.prop_of_iso e hKM.plus)
  exact ⟨(R(ν_*(Y.left)[ModuleCat.{u + 1}
    (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))])).mapIso e ≪≫ e'⟩

end AlgebraicGeometry.ProEtale.CondensedRing
