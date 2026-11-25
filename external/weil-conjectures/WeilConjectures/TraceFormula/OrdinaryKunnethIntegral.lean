/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ExternalProductCoefficients
public import WeilConjectures.TraceFormula.OrdinaryKunnethFinite
public import WeilConjectures.TraceFormula.OrdinaryKunnethReduction

/-!
# Vanishing on the boundary for the ordinary Künneth formula, integral coefficients

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. For morphisms
`i : Z ⟶ X` and `f : U ⟶ Y` of separated `k`-schemes of finite type, a bounded constructible
`𝒪_E`-complex `N` on `X` with `Li^* N = 0` and any `B` on `U`, the complex
`R(𝟙 × f)_* (N ⊠ B)` vanishes on `Z ⨯ Y`:
`CondensedRing.PadicIntegersRingObj.isZero_upperStar_prodMap_lowerStar_prodMap_externalProduct`.

Following the proof of blueprint `lemma-kunneth-one-identity-factor--1` (coefficient transport from
finite coefficients), it is checked after the reduction modulo `ℓ` read on the étale site, which
detects zero objects (`ProEtale.CondensedRing.isZero_of_isZero_etaleReduction`) and commutes with
the pullbacks, the tensor product and the pushforward
(`ProEtale.CondensedRing.etaleReductionUpperStarIso`,
`ProEtale.CondensedRing.nonempty_etaleReductionTensorIso`,
`ProEtale.CondensedRing.etaleReductionLowerStarIso`). This identifies the reduction with the
finite-coefficient complex of `Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor`
over the finite ring `𝒪_E ⧸ ℓ`, which vanishes by the ordinary Künneth formula with finite
coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

/-- The reduction modulo `ℓⁿ`, read on the étale site, sends zero objects to zero objects: the
derived extension of scalars is a left adjoint. -/
lemma isZero_etaleReduction_obj_of_isZero (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {P : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧} (hP : IsZero P) :
    IsZero ((etaleReduction ℓ E n X).obj P) := by
  have := ((Mod.extendRestrictAdjunction
    (integersModPowReduction X.left ℓ E n)).derivedAdjunction).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (L(Mod.extendScalars (integersModPowReduction X.left ℓ E n)))
  exact Functor.map_isZero ((boundedConstructible _).ι ⋙
    L(Mod.extendScalars (integersModPowReduction X.left ℓ E n)) ⋙
      (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])) hP

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **Reduction of the boundary complex**: the reduction modulo `ℓⁿ`, read on the étale site, of
the pullback to `Z ⨯ Y` of `R(𝟙 × f)_* (N ⊠ B)` is the corresponding complex
`L(i × 𝟙)^* R(𝟙 × f)_* (Lp_X^* red N ⊗ᴸ Lp_U^* red B)` built from the reductions of `N` and `B`:
reduction commutes with pullbacks, pushforwards and tensor products. -/
theorem nonempty_etaleReduction_upperStar_lowerStar_externalProduct_iso (n : ℕ) (i : Z ⟶ X)
    (f : U ⟶ Y) (N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    Nonempty ((etaleReduction ℓ E.1 n (Z ⨯ Y)).obj
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
          (prod.map i (𝟙 Y))).obj
          ((boundedConstructibleLowerStar ℓ E.1 (prod.map (𝟙 X) f)).obj
            (boundedConstructibleExternalProduct ℓ E.1 N B))) ≅
      (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
          (prod.map i (𝟙 Y)).left)).obj
        ((R(Etale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
          (prod.map (𝟙 X) f).left)).obj
          (((Etale.derivedTensor (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
              (X ⨯ U).left).obj
            ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
              (prod.fst : X ⨯ U ⟶ X).left)).obj ((etaleReduction ℓ E.1 n X).obj N))).obj
            ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
              (prod.snd : X ⨯ U ⟶ U).left)).obj ((etaleReduction ℓ E.1 n U).obj B))))) := by
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)
  refine (nonempty_etaleReductionTensorIso ℓ E.1 n
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (prod.fst : X ⨯ U ⟶ X)).obj N)
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (prod.snd : X ⨯ U ⟶ U)).obj B)).map fun eT ↦ ?_
  exact (etaleReductionUpperStarIso ℓ E.1 n (prod.map i (𝟙 Y))).app _ ≪≫
    (L(Etale.upperStar A (prod.map i (𝟙 Y)).left)).mapIso
      ((etaleReductionLowerStarIso ℓ E.1 n (prod.map (𝟙 X) f)).app _ ≪≫
        (R(Etale.lowerStar A (prod.map (𝟙 X) f).left)).mapIso
          (eT ≪≫
            ((Etale.derivedTensor A (X ⨯ U).left).mapIso
              ((etaleReductionUpperStarIso ℓ E.1 n (prod.fst : X ⨯ U ⟶ X)).app N)).app _ ≪≫
            ((Etale.derivedTensor A (X ⨯ U).left).obj _).mapIso
              ((etaleReductionUpperStarIso ℓ E.1 n (prod.snd : X ⨯ U ⟶ U)).app B)))

/-- **Vanishing on the boundary, integral coefficients**: for morphisms `i : Z ⟶ X` and
`f : U ⟶ Y` of separated `k`-schemes of finite type, a bounded constructible `𝒪_E`-complex `N` on
`X` with `Li^* N = 0` and any `B` on `U`, the pullback to `Z ⨯ Y` of `R(𝟙 × f)_* (N ⊠ B)` vanishes.
Its reduction modulo `ℓ`, read on the étale site, is the finite-coefficient complex of
`Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor` for the reductions of `N` and `B`
(blueprint `lemma-kunneth-one-identity-factor--1`, coefficient transport). -/
theorem isZero_upperStar_prodMap_lowerStar_prodMap_externalProduct (i : Z ⟶ X) (f : U ⟶ Y)
    {N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    (hN : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ i).obj N))
    (B : Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (prod.map i (𝟙 Y))).obj
      ((boundedConstructibleLowerStar ℓ E.1 (prod.map (𝟙 X) f)).obj
        (boundedConstructibleExternalProduct ℓ E.1 N B))) := by
  refine isZero_of_isZero_etaleReduction ℓ E.1 one_ne_zero ?_
  refine (nonempty_etaleReduction_upperStar_lowerStar_externalProduct_iso ℓ E 1 i f N B).elim
    fun e ↦ ?_
  refine (Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor
    (integersModPowCoeff.{u} ℓ E.1 1) f i _ ?_ _).of_iso e
  exact (isZero_etaleReduction_obj_of_isZero ℓ E.1 1 Z hN).of_iso
    ((etaleReductionUpperStarIso ℓ E.1 1 i).app N).symm

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
