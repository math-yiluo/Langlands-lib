/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusGraphSquare
public import WeilConjectures.TraceFormula.CurveLocal.ReductionExternalProduct

/-!

# The classical coefficient datum of an integral external product modulo `ℓⁿ`

Let `X` be a smooth curve over the algebraically closed field `k` with the model Frobenius `Φ`,
`m ≥ 1`, `F` the fixed locus of the graph correspondence `(𝟙, Φ_m)` and `z` a point of `F` over
`x`. For bounded constructible `𝒪_E`-complexes `M`, `N` on `X` with `M_x = 0` and `n : ℕ`, this
file builds the classical coefficient datum
(`Etale.CurveLocalModel.CoefficientDatum`) of the reduction modulo `ℓⁿ` of `M ⊠ N` on the
strictly local model at `x` (`ProEtale.CondensedRing.Correspondence.reductionCoefficientDatum`):
the coefficient ring `𝒪_E ⧸ ℓⁿ`, the reductions `N_{𝒪_E ⧸ ℓⁿ}` and `M_{𝒪_E ⧸ ℓⁿ}`, and the
restriction to the strict localization of the reduction of `Lp₁^* M ⊗ Lp₂^* N`, pulled back to
`X ×_k X`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The reduction modulo `ℓⁿ`, read on the étale site, sends zero objects to zero objects: the
derived extension of scalars is a left adjoint. -/
lemma isZero_etaleReduction_obj (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧} (hP : IsZero P) :
    IsZero ((etaleReduction ℓ E n Y).obj P) := by
  have := ((Mod.extendRestrictAdjunction
    (integersModPowReduction Y.left ℓ E n)).derivedAdjunction).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (L(Mod.extendScalars (integersModPowReduction Y.left ℓ E n)))
  exact Functor.map_isZero ((boundedConstructible _).ι ⋙
    L(Mod.extendScalars (integersModPowReduction Y.left ℓ E n)) ⋙
      (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])) hP

/-- If `Lf^* P` vanishes, so does the pullback `Lf^* (P_{𝒪_E ⧸ ℓⁿ})` of the reduction. -/
lemma isZero_upperStar_etaleReduction_obj {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : Z ⟶ Y) {P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (hP : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj P)) :
    IsZero ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)).obj
      ((etaleReduction ℓ E n Y).obj P)) :=
  (isZero_etaleReduction_obj ℓ E n Z hP).of_iso ((etaleReductionUpperStarIso ℓ E n f).app P).symm

/-- The pullback `Lφ^* (P_{𝒪_E ⧸ ℓⁿ})` of the reduction modulo `ℓⁿ` of `P`, as a bounded below
complex: the reduction is bounded (`boundedConstructibleFiniteTor_etaleReduction`). -/
noncomputable def upperStarEtaleReductionPlus (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] {W : Scheme.{u}} (φ : W ⟶ Y.left)
    (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    DerivedCategory.Plus
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  ⟨(L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)).obj
      ((etaleReduction ℓ E n Y).obj P),
    DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ φ).app _).symm
      ((Functor.mapDerivedCategoryPlus
        (Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)).obj
          ⟨_, (boundedConstructibleFiniteTor_etaleReduction ℓ E n P).1.1.1⟩).property⟩
end Reduction

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

open PadicAlgCl

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- In `𝒪_E ⧸ ℓⁿ`, lifted to the universe of étale sheaves, `ℓⁿ = 0`. -/
lemma natCast_pow_eq_zero_integersModPowCoeff (E : FiniteIntermediateField ℓ) (n : ℕ) :
    (ℓ : integersModPowCoeff.{u} ℓ E.1 n) ^ n = 0 :=
  ULift.down_injective (by simp [PadicAlgCl.natCast_pow_eq_zero_integersModPow])

variable (ℓ) in
/-- **The classical coefficient datum of `M ⊠ N` modulo `ℓⁿ`** on the strictly local model at
the fixed point `x = ι(z)`: the coefficient ring `𝒪_E ⧸ ℓⁿ`, the reductions `N_{𝒪_E ⧸ ℓⁿ}` and
`M_{𝒪_E ⧸ ℓⁿ}` (with `(M_{𝒪_E ⧸ ℓⁿ})_x = 0` as `M_x = 0`), and the restriction to the strict
localization of the reduction of `Lp₁^* M ⊗ Lp₂^* N`, pulled back to `X ×_k X`, identified with
`(N_{𝒪_E ⧸ ℓⁿ} ⊠ M_{𝒪_E ⧸ ℓⁿ})|_T` by `nonempty_etaleReduction_externalProduct_iso`. -/
noncomputable def reductionCoefficientDatum [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (E : FiniteIntermediateField ℓ) (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hM : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (z ≫ F.ι)).obj M)) (n : ℕ) :
    (frobeniusLocalModel hΦ hm v F z).CoefficientDatum ℓ where
  Λ := integersModPowCoeff.{u} ℓ E.1 n
  isNilpotent_natCast := ⟨n, natCast_pow_eq_zero_integersModPowCoeff E n⟩
  L := (etaleReduction ℓ E.1 n X).obj N
  K := (etaleReduction ℓ E.1 n X).obj M
  boundedConstructibleFiniteTor_L := boundedConstructibleFiniteTor_etaleReduction ℓ E.1 n N
  boundedConstructibleFiniteTor_K := boundedConstructibleFiniteTor_etaleReduction ℓ E.1 n M
  isZero_upperStar_y := isZero_upperStar_etaleReduction_obj ℓ E.1 n (z ≫ F.ι) hM
  P := (Functor.mapDerivedCategoryPlus (Etale.upperStar
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) (frobeniusLocalModel hΦ hm v F z).τ)).obj
      (upperStarEtaleReductionPlus ℓ E.1 n (X ⨯ X) (swapPullbackToProd X)
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
            (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
            (prod.snd : X ⨯ X ⟶ X)).obj N))
  iso := ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
    (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
      (frobeniusLocalModel hΦ hm v F z).τ)).mapIso
        (nonempty_etaleReduction_externalProduct_iso ℓ E.1 n M N).some

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
