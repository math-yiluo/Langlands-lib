/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ReductionStalkRestriction
public import WeilConjectures.TraceFormula.PointFiberReduction

/-!

# The integral supported restriction modulo `ℓⁿ` on the strictly local model

Let `X` be a smooth curve over the algebraically closed field `k` with the model Frobenius `Φ`,
`m ≥ 1`, `F` the fixed locus of the graph correspondence `(𝟙, Φ_m)` and `z` a point of `F`
over `x`. For bounded constructible `𝒪_E`-complexes `M`, `N` on `X` with `M_x = 0`, let
`ρ = ρ_{M ⊠ N}` be the integral supported restriction
(`ProEtale.CondensedRing.Correspondence.FixedLocus.supportedRestrictionIntegral`) and
`f₀ = Fib_s(z^* ρ)` its point fibre, a morphism in `D(𝒪_E)`. This file proves that the
reductions of `f₀` modulo every `ℓⁿ` factor through classical supported restrictions `ρ_{a,b}`
on the strictly local model `M_x` at `x` (`Correspondence.frobeniusLocalModel`), with the
coefficient datum `(𝒪_E ⧸ ℓⁿ, N_{𝒪_E ⧸ ℓⁿ}, M_{𝒪_E ⧸ ℓⁿ})`: this is the reduction clause of
`Correspondence.HasIntegralReductionModel` (blueprint `lemma-vanishing-local-term-zero-stalk`, the
passage from the classical finite-coefficient computation to `𝒪_E`).

The proof transports `ρ` to the étale site by the reduction modulo `ℓⁿ`
(`CategoryTheory.Adjunction.exists_map_mateEquiv_app_comp_eq`, with the coefficient
comparisons of `proposition-six-operations-change-coefficients` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`), identifies
`X ⨯ X` with the fibre product of the model (interchanging the factors), compares the stalk of the
étale exchange restriction with `ρ_{a,b}`
(`Etale.CurveLocalModel.exists_geometricStalk_map_exchangeRestriction`), and reduces the point
fibre (`ProEtale.CondensedRing.exists_pointFiberFunctorIntegral_reduction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Pretriangulated

/-- **Transporting a reduction triangle along an isomorphism.** Let `Res : 𝒰 ⥤ 𝒯` with `𝒯`
pretriangulated, `B₀ --N--> B₀ --π_B--> Res X_B ⟶` a distinguished triangle and
`f₀ ≫ π_B = π_A ≫ Res(r)`. If `r` followed by an isomorphism `e : X_B ≅ T` factors as `s ≫ ρ`,
then `f₀` followed by the reduction `B₀ ⟶ Res T` of a distinguished triangle on `N` factors
through `Res(ρ)`. -/
lemma exists_distinguished_comp_eq_of_iso {𝒯 𝒰 : Type*} [Category* 𝒯] [Preadditive 𝒯]
    [HasZeroObject 𝒯] [HasShift 𝒯 ℤ] [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]
    [Category* 𝒰] (Res : 𝒰 ⥤ 𝒯) {A₀ B₀ : 𝒯} (f₀ : A₀ ⟶ B₀) (N : ℤ) {XA XB S T : 𝒰}
    {r : XA ⟶ XB} {πA : A₀ ⟶ Res.obj XA} {πB : B₀ ⟶ Res.obj XB} (hπ : f₀ ≫ πB = πA ≫ Res.map r)
    {δ : Res.obj XB ⟶ B₀⟦(1 : ℤ)⟧} (hT : Triangle.mk (N • 𝟙 B₀) πB δ ∈ distTriang 𝒯)
    (e : XB ≅ T) (s : XA ⟶ S) {ρ : S ⟶ T} (h : r ≫ e.hom = s ≫ ρ) :
    ∃ (πA' : A₀ ⟶ Res.obj S) (πB' : B₀ ⟶ Res.obj T) (δ' : Res.obj T ⟶ B₀⟦(1 : ℤ)⟧),
      Triangle.mk (N • 𝟙 B₀) πB' δ' ∈ distTriang 𝒯 ∧ πA' ≫ Res.map ρ = f₀ ≫ πB' := by
  refine ⟨πA ≫ Res.map s, πB ≫ Res.map e.hom, Res.map e.inv ≫ δ,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (Res.mapIso e).symm (by simp) (by simp [← Functor.map_comp]) (by simp)), ?_⟩
  rw [Category.assoc, ← Res.map_comp, ← h, Res.map_comp, reassoc_of% hπ]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

variable (ℓ) in
/-- The point fibre `Fib_s(z^* ρ_{M ⊠ N})` of the integral supported restriction of `M ⊠ N` at a
point `z` of the fixed locus, as an arrow of `D(𝒪_E)`. -/
noncomputable def pointIntegralSupportedRestriction [IsSepClosed k] {c : Correspondence ℓ K}
    (F : c.FixedLocus) (z : RationalPoint F.F) (E : FiniteIntermediateField ℓ)
    (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    Arrow (DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (integers ℓ E.1)))) :=
  Arrow.mk ((pointFiberFunctorIntegral ℓ k E).map
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).map
      (F.supportedRestrictionIntegral E
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
            (prod.fst : X ⨯ X ⟶ X)).obj M ⊗
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
            (prod.snd : X ⨯ X ⟶ X)).obj N))))

/-- **The integral supported restriction reduces to classical supported restrictions**: for
bounded constructible `𝒪_E`-complexes `M`, `N` on the curve `X` with `M_x = 0` at the point
`x = ι(z)`, every reduction modulo `ℓⁿ` of the point fibre `f₀ : A₀ ⟶ B₀` of the integral
supported restriction of `M ⊠ N` at `z` factors through a classical supported restriction
`ρ_{a,b}` on the strictly local model at `x`: there are a classical coefficient datum `D` with
coefficients under `𝒪_E`, a map `π_A : A₀ ⟶ RΓ_a(T, P)` and a distinguished triangle
`B₀ --ℓⁿ--> B₀ --π_B--> RΓ_y(B, b^* P) ⟶` with `π_A ≫ ρ_{a,b} = f₀ ≫ π_B`. -/
theorem exists_reduction_pointIntegralSupportedRestriction [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (E : FiniteIntermediateField ℓ) (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hM : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (z ≫ F.ι)).obj M)) (n : ℕ) :
    ∃ (D : (frobeniusLocalModel hΦ hm v F z).CoefficientDatum ℓ)
      (φ : Shrink.{u + 1} (integers ℓ E.1) →+* D.Λ)
      (πA : (pointIntegralSupportedRestriction ℓ F z E M N).left ⟶
        (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.source)
      (πB : (pointIntegralSupportedRestriction ℓ F z E M N).right ⟶
        (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target)
      (δ : (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target ⟶
        (pointIntegralSupportedRestriction ℓ F z E M N).right⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk
        (((ℓ : ℤ) ^ n) • 𝟙 (pointIntegralSupportedRestriction ℓ F z E M N).right) πB δ ∈
          distTriang _ ∧
      πA ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map D.supportedRestriction =
        (pointIntegralSupportedRestriction ℓ F z E M N).hom ≫ πB := by
  have hπ := exists_pointFiberFunctorIntegral_reduction ℓ k E n
  have hst := exists_reduction_stalk_integralSupportedRestriction hΦ hm v F z E M N hM n
  refine ⟨reductionCoefficientDatum ℓ hΦ hm v F z E M N hM n, integersModPowCoeffHom ℓ E n, ?_⟩
  exact Pretriangulated.exists_distinguished_comp_eq_of_iso
    (ModuleCat.restrictScalars (integersModPowCoeffHom ℓ E n)).mapDerivedCategory
    (pointIntegralSupportedRestriction ℓ F z E M N).hom _ (hπ.choose.naturality _)
    (hπ.choose_spec _).choose_spec hst.choose hst.choose_spec.choose hst.choose_spec.choose_spec

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
