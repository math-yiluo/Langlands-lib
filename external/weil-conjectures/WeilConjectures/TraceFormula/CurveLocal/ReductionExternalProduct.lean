/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.TraceFormula.CurveLocal.SwapProduct

/-!

# Reduction modulo `ℓⁿ` of an integral external product

For bounded constructible `𝒪_E`-complexes `M`, `N` on `X`, the reduction modulo `ℓⁿ`, read on
the étale site (`ProEtale.CondensedRing.etaleReduction`), of the external product
`M ⊠ N = Lp₁^* M ⊗ Lp₂^* N` on `X ⨯ X` is, through the identification `X ×_k X ≅ X ⨯ X`
interchanging the factors (`ProEtale.CondensedRing.swapPullbackToProd`), the classical external
product `N_{𝒪_E ⧸ ℓⁿ} ⊠ M_{𝒪_E ⧸ ℓⁿ}` of the reductions.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **Reduction of an integral external product**: the reduction modulo `ℓⁿ` of
`Lp₁^* M ⊗ Lp₂^* N` on `X ⨯ X`, pulled back along `X ×_k X ≅ X ⨯ X` (interchanging the
factors), is the classical external product of the reductions of `N` and `M`. -/
theorem nonempty_etaleReduction_externalProduct_iso
    (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Nonempty ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        (swapPullbackToProd X))).obj ((etaleReduction ℓ E n (X ⨯ X)).obj
          ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
              (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
            (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
              (prod.snd : X ⨯ X ⟶ X)).obj N)) ≅
      Etale.externalProduct (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X.hom X.hom
        ((etaleReduction ℓ E n X).obj N) ((etaleReduction ℓ E n X).obj M)) := by
  obtain ⟨eT⟩ := nonempty_etaleReductionTensorIso ℓ E n
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
      (prod.fst : X ⨯ X ⟶ X)).obj M)
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
      (prod.snd : X ⨯ X ⟶ X)).obj N)
  obtain ⟨eB⟩ := Etale.nonempty_iso_derivedTensor_flip
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) (pullback X.hom X.hom)
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)
  let φ := swapPullbackToProd X
  exact ⟨(L(Etale.upperStar A φ)).mapIso (eT ≪≫
      ((Etale.derivedTensor A (X ⨯ X).left).mapIso
          ((etaleReductionUpperStarIso ℓ E n (prod.fst : X ⨯ X ⟶ X)).app M)).app _ ≪≫
      ((Etale.derivedTensor A (X ⨯ X).left).obj _).mapIso
          ((etaleReductionUpperStarIso ℓ E n (prod.snd : X ⨯ X ⟶ X)).app N)) ≪≫
    Etale.leftDerivedUpperStarTensorIso A φ _ _ ≪≫
    ((Etale.derivedTensor A (pullback X.hom X.hom)).mapIso
        ((Etale.leftDerivedUpperStarComp A φ (prod.fst : X ⨯ X ⟶ X).left
          (pullback.snd X.hom X.hom) (by simp [φ])).app _).symm).app _ ≪≫
    ((Etale.derivedTensor A (pullback X.hom X.hom)).obj _).mapIso
        ((Etale.leftDerivedUpperStarComp A φ (prod.snd : X ⨯ X ⟶ X).left
          (pullback.fst X.hom X.hom) (by simp [φ])).app _).symm ≪≫
    (eB.app _).app _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
