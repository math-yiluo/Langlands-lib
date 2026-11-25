/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.TraceZigzag
public import WeilConjectures.CategoryTheory.Monoidal.ZigzagTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStarBraided
public import WeilConjectures.TraceFormula.PointNormalizationBaseChange
public import WeilConjectures.TraceFormula.PointNormalizationTau

/-!

# Point normalization of the trace class

Over the base point `s = Spec k`, the trace class of the diagonal correspondence of an
endomorphism `v` of a dualizable object integrates to the categorical trace of `v` (blueprint
`lemma-local-terms-point--1`, `lemma-local-terms-point`).

## Strategy

By the description of the trace class as an exceptional adjoint along the fixed locus
(`Correspondence.traceClass_eq_homEquiv`) and of the supported class of the diagonal
correspondence (`supportedClass_ofEnd`), the integral `∫_s Tr(v)` is
`P ∘ (v ⊗ D_s K) ∘ σ` (`Correspondence.integral_traceClass_ofEnd_eq`) for a morphism
`σ : ℚ̄_ℓ ⟶ K ⊗ D_s K` built from the class of the identity and a pairing
`P : K ⊗ D_s K ⟶ ℚ̄_ℓ` built from the evaluation. The pair `(σ, P)` satisfies the zigzag identity
of a duality, and the trace through such a pair is the categorical trace
(`MonoidalCategory.trace_eq_of_zigzag`), the Koszul braiding being symmetric
(`boundedConstructible_braiding_hom_braiding_hom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace Correspondence

variable {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- **The zigzag identity of the coevaluation and the pairing over the base point**: `σ` and `P`
satisfy the zigzag identity of a duality. -/
theorem pointCoev_zigzag (v : K ⟶ K) :
    (ρ_ K).inv ≫ K ◁ pointCoev v ≫ (α_ K K _).inv ≫ (β_ K K).hom ▷ _ ≫ (α_ K K _).hom ≫
      K ◁ pointPairing v ≫ (ρ_ K).hom = 𝟙 K := by
  rw [pointCoev_eq, pointPairing_eq]
  let χ : (boundedConstructibleUpperStar _ ℓ (diag (point k))).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj K) ⟶ K :=
    Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
      ((boundedConstructibleUpperShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj K) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).counit.app K
  let τ' : (boundedConstructibleUpperStar _ ℓ (diag (point k))).obj
      ((boundedConstructibleLowerShriek ℓ (diag (point k))).obj (𝟙_ _)) ⟶ 𝟙_ _ :=
    (pointDiagAdj ℓ k).counit.app (𝟙_ _)
  refine zigzag_of_transport (boundedConstructibleUpperStar _ ℓ (diag (point k)))
    (diagUnitClass ℓ (K := K) diag_point_snd diag_point_fst.symm ≫
      inv (kunnethVerdierMap ℓ K K))
    (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ prod.snd) K _)
    ((boundedConstructibleUpperStar _ ℓ prod.snd).map
      ((ihom.ev K).app (dualizingComplex' ℓ (point k))))
    (exceptionalKunnethMap ℓ K)
    (uncurry (diagUnitClass ℓ (K := K) diag_point_snd diag_point_fst.symm))
    (Verdier.whiskerLeft_comp_inv_curry _ (kunnethVerdierPairing ℓ K K)
      (isIso_kunnethVerdierMap ℓ K K))
    (diagUpperStarProjIso ℓ prod.snd (by simp) K)
    (diagUpperStarProjIso ℓ prod.fst (by simp) K).hom
    (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom
    (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom
    _ _ χ (pointTau v) τ' ?hτ ?hbraid
    (diagUpperStarProjIso_μ_map ℓ prod.snd (by simp) K _ _ ((ihom.ev K).app _)) ?hK ?hC
  case hτ => exact pointTau_comp_counit v
  case hbraid => exact boundedConstructibleUpperStar_μ_map_braiding_hom ℓ (diag (point k)) _ _
  case hK =>
    exact pointKunneth_transport K
      (boundedConstructibleUpperStar_μ_map_braiding_hom ℓ (diag (point k)) _ _)
      (pointKunneth_baseChange ℓ rfl)
  case hC =>
    exact pointClass_transport K
      (boundedConstructibleUpperStar_μ_map_braiding_hom ℓ (diag (point k)) _ _)

/-- **Point normalization of the pairing** (blueprint `lemma-local-terms-point--1`,
`lemma-local-terms-point`): over the base point, the trace class of the diagonal correspondence of
an endomorphism `v` of a perfect complex integrates to the categorical trace of `v`,
`∫_s Tr(v) = tr(v)`. -/
theorem integral_traceClass_ofEnd [HasRightDual K] (v : K ⟶ K) :
    ((ofEnd K v).traceClass (fixedLocusOfEnd v)).integral = .of (trace v) :=
  (integral_traceClass_ofEnd_eq v).trans (congrArg End.of (trace_eq_of_zigzag
    (fun A B ↦ boundedConstructible_braiding_hom_braiding_hom A B) _ _ (pointCoev_zigzag v) v))

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
