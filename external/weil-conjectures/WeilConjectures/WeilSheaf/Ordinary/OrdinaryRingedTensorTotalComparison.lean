/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! Totalization of a termwise ordinary tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
attribute [local instance] Mod.monoidalCategoryCochainComplex

/-- A natural binary comparison induces the standard sum-total comparison.
Source: Stacks 0FPQ.
(blueprint: new-sf-ordinary-ringed-tensor-total-comparison).

Proof: curry the binary comparison and apply `HomologicalComplex.mapBifunctorComparison`.
The equivalence preserves the coproducts indexed by a fixed
sum, so every component is invertible. The defining coproduct equation is exactly
the displayed summand formula.
-/
theorem ordinary_ringed_tensor_total_comparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u + 1})
    (E : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
    [E.functor.Additive]
    (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ E.functor ≅
      E.functor.prod E.functor ⋙ MonoidalCategory.tensor
        (RingedTensorModules.{u + 1, u + 1, u + 1} J R)) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    ∃ (τ : MonoidalCategory.tensor (CochainComplex (ProEtale.AdicSheaf l Y) ℤ) ⋙
          E.functor.mapHomologicalComplex (.up ℤ) ≅
        (E.functor.mapHomologicalComplex (.up ℤ)).prod
          (E.functor.mapHomologicalComplex (.up ℤ)) ⋙ MonoidalCategory.tensor _),
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (p q n : ℤ) (h : p + q = n),
        E.functor.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
            (τ.hom.app (P, Q)).f n =
          ν.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιTensorObj
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let μ : (Functor.postcompose₂.obj E.functor).obj
      (MonoidalCategory.curriedTensor (ProEtale.AdicSheaf l Y)) ≅
    (((Functor.whiskeringLeft₂ _).obj E.functor).obj E.functor).obj
      (MonoidalCategory.curriedTensor (RingedTensorModules.{u + 1, u + 1, u + 1} J R)) :=
    NatIso.ofComponents (fun P ↦ NatIso.ofComponents
      (fun Q ↦ ν.app (P, Q)) (by
        intro Q Q' q
        simpa using ν.hom.naturality (show (P, Q) ⟶ (P, Q') from (𝟙 P, q)))) (by
      intro P P' p
      apply NatTrans.ext
      funext Q
      simpa using ν.hom.naturality (show (P, Q) ⟶ (P', Q) from (p, 𝟙 Q)))
  refine ⟨NatIso.ofComponents
    (fun PQ ↦ asIso (HomologicalComplex.mapBifunctorComparison μ.hom (.up ℤ) PQ.1 PQ.2))
    ?_, ?_⟩
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨p, q⟩
    exact HomologicalComplex.mapBifunctorComparison_naturality μ.hom (.up ℤ) p q
  · intro P Q p q n h
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      μ.hom (.up ℤ) P Q p q n h

end AlgebraicGeometry.ProEtaleWeilSheaf
