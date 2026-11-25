/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorAdjunctionExchange
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # First-variable naturality of the normalized tensor exchange

Source: Stacks 06YU and 08J7, signed tensor symmetry and normalized evaluation.
(blueprint: lem-sfb-integral-hom-tensor-exchange-naturality)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite
namespace WeilConjectures.IntegralHom

/-- The adjunction-defined exchange is natural in the first tensor factor.

Source: Stacks Tags 06YU and 08J7, tensor symmetry and evaluation on representatives;
the representative-comparison part of the integral Hom normalization proof.
(blueprint: lem-sfb-integral-hom-tensor-exchange-naturality).

Proof: write inverse transposition as tensoring the supplied map followed by the
counit. The public evaluation naturality theorem moves a morphism in K across
that counit. Naturality of the model's curry equivalence identifies the resulting
transpose with its tensor map. Naturality in the remaining tensor argument was
already proved directly from the two adjunction equivalences. -/
theorem tensorAdjunctionExchange_naturality_first
    {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) (b : HomReductionTensorModel R)
    (K K' A : Derived.{u, u} X R) (f : K ⟶ K') :
    a.tensor.map (Prod.mkHom (f) (𝟙 A)) ≫ tensorAdjunctionExchange.{u} R a b K' A =
      tensorAdjunctionExchange.{u} R a b K A ≫ b.tensor.map (Prod.mkHom (𝟙 A) (f)) := by
  let T := b.tensor.obj (A, K')
  let eta := (b.curry A K' T).symm (𝟙 T)
  let hmap := (homReductionHom R).map (Prod.mkHom f.op (𝟙 T))
  have hc : b.curry A K T (eta ≫ hmap) =
      b.tensor.map (Prod.mkHom (𝟙 A) f) := by
    have h := b.natural A A K' K T T (𝟙 A) f (𝟙 T) eta
    dsimp only [eta] at h
    rw [Category.id_comp, Category.comp_id, Equiv.apply_symm_apply,
      Category.comp_id] at h
    exact h
  have he : a.tensor.map (Prod.mkHom f (𝟙 A)) ≫
      tensorAdjunctionExchange R a b K' A =
      ((a.adjunction K).homEquiv A T).symm (eta ≫ hmap) := by
    change a.tensor.map (Prod.mkHom f (𝟙 A)) ≫
      ((a.adjunction K').homEquiv A T).symm eta = _
    rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
    simp only [Functor.curry_obj_obj_map]
    have hn := evaluation_naturality X R a K' K T f
    change a.tensor.map (Prod.mkHom (𝟙 K) hmap) ≫ _ =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ _ at hn
    have hp : Prod.mkHom f (𝟙 A) ≫ Prod.mkHom (𝟙 K') eta =
        Prod.mkHom (𝟙 K) eta ≫ Prod.mkHom f (𝟙 _) := by
      ext <;> simp
    rw [← Category.assoc, ← Functor.map_comp, hp, Functor.map_comp,
      Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
    congr 1
  rw [he, tensorAdjunctionExchange_uncurry, hc]

end WeilConjectures.IntegralHom
