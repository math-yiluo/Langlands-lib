/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ReductionCoefficientDatum
public import WeilConjectures.TraceFormula.CurveLocal.ReductionExchangeRestriction
public import WeilConjectures.TraceFormula.CurveLocal.StalkExchangeRestriction

/-!

# The stalk of the integral supported restriction modulo `ℓⁿ`

Let `X` be a smooth curve over the algebraically closed field `k` with the model Frobenius `Φ`,
`m ≥ 1`, `F` the fixed locus of the graph correspondence `(𝟙, Φ_m)` and `z` a point of `F` over
`x`. For bounded constructible `𝒪_E`-complexes `M`, `N` on `X` with `M_x = 0`, let
`ρ = ρ_{M ⊠ N}` be the integral supported restriction. This file proves that
`RΓ(s, (z^* ρ)_{𝒪_E ⧸ ℓⁿ})`, followed by an isomorphism, factors through the classical supported
restriction `ρ_{a,b}` of the coefficient datum
`ProEtale.CondensedRing.Correspondence.reductionCoefficientDatum` on the strictly local model at
`x` (`ProEtale.CondensedRing.Correspondence.exists_reduction_stalk_integralSupportedRestriction`).

The reduction modulo `ℓⁿ` carries `ρ` to the étale exchange restriction of the fixed square of
the model (`ProEtale.CondensedRing.exists_etaleReduction_map_exchangeRestriction_comp_eq`,
`ProEtale.CondensedRing.Correspondence.isPullback_frobeniusLocalModel_graph`), commutes with the
pullback along `z` (`ProEtale.CondensedRing.etaleReductionUpperStarIso`), and the geometric stalk
of the étale exchange restriction factors through `ρ_{a,b}`
(`Etale.CurveLocalModel.exists_geometricStalk_map_exchangeRestriction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **Bookkeeping for a stalk of a factorization.** Let `ζ : U ≅ T ⋙ G` and `x : A ⟶ B`. If
`T(x)` followed by an isomorphism `β` factors as `s ≫ ρ`, and `G(ρ)` followed by an isomorphism
`e` factors as `s' ≫ ρ'`, then `U(x)` followed by an isomorphism factors through `ρ'`. -/
lemma exists_map_comp_eq_of_iso_of_factorization {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* ℰ] {U : 𝒞 ⥤ ℰ} {T : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ ℰ} (ζ : U ≅ T ⋙ G) {A B : 𝒞} (x : A ⟶ B)
    {D₁ D₂ : 𝒟} {s : T.obj A ⟶ D₁} {β : T.obj B ⟶ D₂} (hβ : IsIso β) {ρ : D₁ ⟶ D₂}
    (h₁ : T.map x ≫ β = s ≫ ρ) {E₁ E₂ : ℰ} {e : G.obj D₂ ≅ E₂} {s' : G.obj D₁ ⟶ E₁}
    {ρ' : E₁ ⟶ E₂} (h₂ : G.map ρ ≫ e.hom = s' ≫ ρ') :
    ∃ (e' : U.obj B ≅ E₂) (s'' : U.obj A ⟶ E₁), U.map x ≫ e'.hom = s'' ≫ ρ' := by
  refine ⟨ζ.app B ≪≫ G.mapIso (asIso β) ≪≫ e, ζ.hom.app A ≫ G.map s ≫ s', ?_⟩
  have hn := ζ.hom.naturality x
  rw [Functor.comp_map] at hn
  rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    reassoc_of% hn, ← G.map_comp_assoc, h₁, G.map_comp_assoc, h₂]
  simp only [Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

variable (ℓ) in
/-- The geometric stalk at a rational point `z` of the reduction modulo `ℓⁿ` is the reduction of
the pullback along `z`: `RΓ(s, (z^* -)_{𝒪_E ⧸ ℓⁿ}) ≅ RΓ(s, Lz^* (-)_{𝒪_E ⧸ ℓⁿ})`. -/
noncomputable def etaleReductionGeometricStalkIso {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (z : RationalPoint Y)
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ z ⋙
        etaleReduction ℓ E n (point k)) ⋙
      Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        (point k).left ≅
      etaleReduction ℓ E n Y ⋙ Etale.geometricStalk (integersModPowCoeff.{u} ℓ E n) z.left :=
  Functor.isoWhiskerRight (etaleReductionUpperStarIso ℓ E n z) _ ≪≫ Functor.associator _ _ _

namespace Correspondence

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- **The stalk of the integral supported restriction modulo `ℓⁿ`**: for `M_x = 0`, the map
`RΓ(s, (z^* ρ_{M ⊠ N})_{𝒪_E ⧸ ℓⁿ})`, followed by an isomorphism with `RΓ_y(B, b^* P)`, factors
through the classical supported restriction `ρ_{a,b}` of the coefficient datum
`reductionCoefficientDatum` on the strictly local model at `x`. -/
theorem exists_reduction_stalk_integralSupportedRestriction [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (E : FiniteIntermediateField ℓ) (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hM : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (z ≫ F.ι)).obj M)) (n : ℕ) :
    ∃ (e : (Etale.rightDerivedGlobalSections
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) (point k).left).obj
          ((etaleReduction ℓ E.1 n (point k)).obj
            ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).obj
              ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 F.d).obj
                ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                  (diag X)).obj
                  ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                      (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
                    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                      (prod.snd : X ⨯ X ⟶ X)).obj N))))) ≅
        (reductionCoefficientDatum ℓ hΦ hm v F z E M N hM n).target)
      (s : (Etale.rightDerivedGlobalSections
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) (point k).left).obj
          ((etaleReduction ℓ E.1 n (point k)).obj
            ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).obj
              ((boundedConstructibleUpperStar _ ℓ F.ι).obj
                ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1
                  (ofGraph K (frobeniusIterate Φ m) v).support).obj
                  ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                      (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
                    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                      (prod.snd : X ⨯ X ⟶ X)).obj N))))) ⟶
        (reductionCoefficientDatum ℓ hΦ hm v F z E M N hM n).source),
      (Etale.rightDerivedGlobalSections
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) (point k).left).map
          ((etaleReduction ℓ E.1 n (point k)).map
            ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).map
              (F.supportedRestrictionIntegral E
                ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                    (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
                  (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
                    (prod.snd : X ⨯ X ⟶ X)).obj N)))) ≫ e.hom =
        s ≫ (reductionCoefficientDatum ℓ hΦ hm v F z E M N hM n).supportedRestriction := by
  have hsq := isPullback_frobeniusLocalModel_graph hΦ hm v F z
  have h₁ := exists_etaleReduction_map_exchangeRestriction_comp_eq ℓ E.1 n
    (F.lowerShriekBaseChangeIsoIntegral E) (frobeniusLocalModel hΦ hm v F z).graph
    (pullback.diagonal (frobeniusLocalModel hΦ hm v F z).f) (swapPullbackToProd X)
    (frobeniusLocalModel_graph_swapPullbackToProd hΦ hm v F z) (diagonal_swapPullbackToProd X)
    hsq ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
        (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
      (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
        (prod.snd : X ⨯ X ⟶ X)).obj N)
  have h₂ := Etale.CurveLocalModel.exists_geometricStalk_map_exchangeRestriction
    (integersModPowCoeff.{u} ℓ E.1 n) (frobeniusLocalModel hΦ hm v F z) hsq z.left
    (left_comp_ofGraph_d_left _ v F z)
    (upperStarEtaleReductionPlus ℓ E.1 n (X ⨯ X) (swapPullbackToProd X)
      ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
          (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
          (prod.snd : X ⨯ X ⟶ X)).obj N))
  exact exists_map_comp_eq_of_iso_of_factorization (etaleReductionGeometricStalkIso ℓ z E.1 n)
    _ h₁.choose_spec.choose_spec.1 h₁.choose_spec.choose_spec.2 h₂.choose_spec.choose_spec

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
