/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-! # The tensor family associated to an orientation has its scalar trace normalization -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical tensor extension of an orientation is a natural family normalized by
its scalar counit. Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md paragraph 2, transposition of integration.

Proof: transpose the natural transformation consisting of inverse projection, tensoring
with the scalar trace, and the left unitor. Its counit is that transformation by the
adjunction triangle identity. To identify each component with the orientation followed by
the dualizing tensor map, transpose again. Naturality of the projection in its first
variable moves the orientation through the inverse projection; functoriality of tensor
combines it with the unit counit to give the specified scalar trace.
(blueprint: lem-pur-normalized-integration-tensor). -/
theorem normalizedIntegration_tensor
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R)
    (π : ∀ M : C, tensorLeft (L.obj M) ⟶ (P ⋙ tensorLeft M) ⋙ L)
    [∀ M, IsIso (π M)]
    (np : ∀ {M M' : C} (f : M ⟶ M') (K : D),
      L.map f ▷ K ≫ (π M').app K = (π M).app K ≫ L.map (f ▷ P.obj K))
    (W : C) (ω : W ⟶ R.obj (𝟙_ D)) :
    ∃ σ : P ⋙ tensorLeft W ⟶ R,
      (∀ K, σ.app K = (ω ▷ P.obj K) ≫
        adj.projectionTensorMap (fun M K ↦ (π M).app K) (𝟙_ D) K ≫
          R.map (λ_ K).hom) ∧
      ∀ K, L.map (σ.app K) ≫ adj.counit.app K =
        inv ((π W).app K) ≫ (L.map ω ≫ adj.counit.app (𝟙_ D)) ▷ K ≫
          (λ_ K).hom := by
  let t := L.map ω ≫ adj.counit.app (𝟙_ D)
  let c : ((P ⋙ tensorLeft W) ⋙ L) ⟶ 𝟭 D :=
    inv (π W) ≫ (curriedTensor D).map t ≫ (leftUnitorNatIso D).hom
  let σ : P ⋙ tensorLeft W ⟶ R :=
    { app := fun K ↦ adj.homEquiv _ K (c.app K)
      naturality := by
        intro K K' f
        apply adj.homEquiv_naturality_left_square
        exact c.naturality f }
  have hc (K : D) : L.map (σ.app K) ≫ adj.counit.app K =
      inv ((π W).app K) ≫ t ▷ K ≫ (λ_ K).hom := by
    change (adj.homEquiv _ K).symm (adj.homEquiv _ K (c.app K)) = _
    simp only [Equiv.symm_apply_apply, c, NatTrans.comp_app, NatIso.isIso_inv_app,
      curriedTensor_map_app, leftUnitorNatIso_hom_app]
  refine ⟨σ, ?_, hc⟩
  intro K
  apply adj.ext_of_comp_counit
  rw [hc]
  have hn : L.map (ω ▷ P.obj K) ≫ inv ((π (R.obj (𝟙_ D))).app K) =
      inv ((π W).app K) ≫ L.map ω ▷ K := by
    apply (cancel_epi ((π W).app K)).1
    rw [← Category.assoc, ← np, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, IsIso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hε := adj.counit.naturality (λ_ K).hom
  change L.map (R.map (λ_ K).hom) ≫ adj.counit.app K =
    adj.counit.app (𝟙_ D ⊗ K) ≫ (λ_ K).hom at hε
  rw [hε, adj.map_projectionTensorMap_comp_counit_assoc, reassoc_of% hn]
  simp only [t, comp_whiskerRight, Category.assoc]

end WeilConjectures.PurityFiniteSetting
