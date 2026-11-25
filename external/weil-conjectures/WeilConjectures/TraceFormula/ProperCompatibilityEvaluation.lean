/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KernelPushforwardCoherence

/-!

# Exchange of the evaluation kernels along a proper map

For a proper morphism `f : X ⟶ Y`, `q = f × f` and `K' = Rf_* K`, the kernel pushforward
`ρ_f : Rq_* (K ⊠ D_X K) ⟶ K' ⊠ D_Y K'` exchanges the evaluation kernels:
`e_{K'} ∘ ρ_f = RΔ_{Y*} τ_f ∘ Rq_* e_K`
(`ProEtale.CondensedRing.kernelPushforward_comp_evaluationKernel_lowerStar`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (1)). The proof passes to the `LΔ_Y^* ⊣ RΔ_{Y*}`
and `Lf^* ⊣ Rf_*` adjoints, where it reduces to the coherence of the composition isomorphisms of the
derived pullbacks (`ProEtale.CondensedRing.upperStarComp_inv_app_comp_prodUpperStarCounit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

section EvaluationExchange

variable (ℓ) {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- **Exchange of the evaluation kernels** along a proper morphism `f` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (1)): with `q = f × f` and `K' = Rf_* K`,
`e_{K'} ∘ ρ_f = RΔ_{Y*} τ_f ∘ Rq_* e_K`, read through `Rq_* RΔ_{X*} ≅ RΔ_{Y*} Rf_*`. -/
theorem kernelPushforward_comp_evaluationKernel_lowerStar (f : X ⟶ Y) [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hΔ : diag X ≫ prod.map f f = f ≫ diag Y) :
    kernelPushforward ℓ f K ≫ evaluationKernel ℓ ((boundedConstructibleLowerStar ℓ f).obj K) =
      (boundedConstructibleLowerStar ℓ (prod.map f f)).map (evaluationKernel ℓ K) ≫
        (boundedConstructibleLowerStarComp ℓ (diag X) (prod.map f f)).hom.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerStar ℓ r).obj
          (dualizingComplex' ℓ X)) hΔ) ≫
        (boundedConstructibleLowerStarComp ℓ f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ f) := by
  -- Keep the derived functors folded while transporting both adjoints.
  simp only [kernelPushforward, Category.assoc]
  rewrite [IsIso.inv_comp_eq]
  simp only [prodLowerStarExternalProduct, evaluationKernel]
  simp only [Adjunction.homEquiv_comp_map_comp
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map f f))]
  conv_lhs =>
    simp only [← Adjunction.homEquiv_naturality_left
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag Y))]
  conv_rhs =>
    simp only [← Adjunction.homEquiv_naturality_left
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))]
  simp only [homEquiv_comp_lowerStarComp_hom_app_assoc ℓ (diag X) (prod.map f f),
    homEquiv_comp_eqToHom_of_eq_assoc ℓ hΔ,
    homEquiv_comp_lowerStarComp_inv_app_assoc ℓ f (diag Y),
    ← Adjunction.homEquiv_naturality_right
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag Y))]
  have hu : (boundedConstructibleLowerStar ℓ f).obj K ◁ lowerStarVerdierDualMap ℓ f K ≫
      (ihom.ev ((boundedConstructibleLowerStar ℓ f).obj K)).app (dualizingComplex' ℓ Y) =
      lowerStarTensorMap ℓ f K (verdierDual ℓ K) ≫
        (boundedConstructibleLowerStar ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)) ≫
        lowerStarDualizingComplexTrace ℓ f :=
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app _ _ _
  simp only [diagUpperStarExternalProductIso_hom_naturality_right_assoc]
  refine (congrArg (fun t ↦ (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag Y)).homEquiv
    _ _ ((diagUpperStarExternalProductIso ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
      ((boundedConstructibleLowerStar ℓ f).obj (verdierDual ℓ K))).hom ≫ t))
        hu).trans ?_
  simp only [upperStarComp_inv_app_comp_prodUpperStarCounit_assoc ℓ f K (verdierDual ℓ K)
    hΔ]
  apply congrArg ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag Y)).homEquiv _
    (dualizingComplex' ℓ Y))
  exact Adjunction.comp_homEquiv_comp_map _ _ _ _ _ _

end EvaluationExchange

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

/-- **Exchange of the evaluation kernels** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (1)): `δ_{K'} ∘ ρ_f = RΔ_{Y*} τ_f ∘ Rq_* δ_K`,
read through `Rq_* RΔ_{X*} ≅ RΔ_{Y*} Rf_*`. -/
theorem kernelPushforward_comp_evaluationKernel :
    kernelPushforward ℓ P.f K ≫ evaluationKernel ℓ P.coeff =
      (boundedConstructibleLowerStar ℓ (prod.map P.f P.f)).map (evaluationKernel ℓ K) ≫
        (boundedConstructibleLowerStarComp ℓ (diag X) (prod.map P.f P.f)).hom.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (by rw [P.diag_comp_prodMap]) ≫
        (boundedConstructibleLowerStarComp ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f) :=
  kernelPushforward_comp_evaluationKernel_lowerStar ℓ P.f K P.diag_comp_prodMap

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
