/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels

/-! # The exchange determined by the two tensor-Hom adjunctions

The map from the presentation tensor in order `(K,A)` to the tensor model in
order `(A,K)` is constructed by transposing the unit. No choice of a tensor
comparison is made here.
(blueprint: def-sfb-integral-hom-tensor-adjunction-exchange)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite
namespace WeilConjectures.IntegralHom

variable {X : AlgebraicGeometry.Scheme.{u}}
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (a : TensorPresentation.{u, u} X R) (b : HomReductionTensorModel R)

/-- Exchange tensor order by the canonical comparison of left adjoints to the
same internal Hom. It is the inverse `a` adjunction applied to the unit of `b`.
Source: Stacks 06YU, 08J7, tensor symmetry and the tensor-Hom adjunction.
(blueprint: def-sfb-integral-hom-tensor-adjunction-exchange). -/
noncomputable def tensorAdjunctionExchange (K A : Derived.{u, u} X R) :
    a.tensor.obj (K, A) ⟶ b.tensor.obj (A, K) :=
  ((a.adjunction K).homEquiv A (b.tensor.obj (A, K))).symm
    ((b.curry A K (b.tensor.obj (A, K))).symm (𝟙 _))

/-- Transposition through the exchange is the original presentation transposition.
Source: naturality of the two adjunction equivalences, Stacks 08J7.
(blueprint: def-sfb-integral-hom-tensor-adjunction-exchange). -/
theorem tensorAdjunctionExchange_uncurry (K A L : Derived.{u, u} X R)
    (f : A ⟶ (homReductionHom R).obj (op K, L)) :
    ((a.adjunction K).homEquiv A L).symm f =
      tensorAdjunctionExchange R a b K A ≫ b.curry A K L f := by
  apply ((a.adjunction K).homEquiv A L).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  dsimp only [tensorAdjunctionExchange]
  rw [Equiv.apply_symm_apply]
  apply (b.curry A K L).injective
  have h := b.natural A A K K (b.tensor.obj (A, K)) L
    (𝟙 A) (𝟙 K) (b.curry A K L f)
    ((b.curry A K (b.tensor.obj (A, K))).symm (𝟙 _))
  have hid : b.tensor.map (Prod.mkHom (𝟙 A) (𝟙 K)) = 𝟙 _ := b.tensor.map_id (A, K)
  simpa only [Category.id_comp, Equiv.apply_symm_apply, hid,
    Category.comp_id, Functor.curry_obj_obj_map, op_id] using h.symm

/-- Naturality in the argument represented by the left adjoints is formal.
Source: naturality of adjunction equivalences, Stacks 08J7.
(blueprint: def-sfb-integral-hom-tensor-adjunction-exchange). -/
theorem tensorAdjunctionExchange_naturality_second
    (K A A' : Derived.{u, u} X R) (g : A ⟶ A') :
    a.tensor.map (Prod.mkHom (𝟙 K) (g)) ≫ tensorAdjunctionExchange R a b K A' =
      tensorAdjunctionExchange R a b K A ≫ b.tensor.map (Prod.mkHom (g) (𝟙 K)) := by
  let T := b.tensor.obj (A', K)
  let eta := (b.curry A' K T).symm (𝟙 T)
  have h := b.natural A' A K K T T g (𝟙 K) (𝟙 T) eta
  have hi : (homReductionHom R).map (Prod.mkHom ((𝟙 K).op) (𝟙 T)) = 𝟙 _ :=
    (homReductionHom R).map_id (op K, T)
  have hc : b.curry A K T (g ≫ eta) = b.tensor.map (Prod.mkHom (g) (𝟙 K)) := by
    dsimp only [eta] at h
    rw [hi, Category.comp_id, Equiv.apply_symm_apply, Category.comp_id] at h
    simpa only [T, eta, Category.comp_id] using h
  calc
    a.tensor.map (Prod.mkHom (𝟙 K) (g)) ≫ tensorAdjunctionExchange R a b K A' =
        ((a.adjunction K).homEquiv A T).symm (g ≫ eta) := by
      exact ((a.adjunction K).homEquiv_naturality_left_symm g eta).symm
    _ = tensorAdjunctionExchange R a b K A ≫ b.curry A K T (g ≫ eta) :=
      tensorAdjunctionExchange_uncurry R a b K A T (g ≫ eta)
    _ = _ := by rw [hc]

/-- In particular the exchange carries evaluation to the presentation counit.
Source: Stacks 08J7, evaluation as the transpose of the identity.
(blueprint: def-sfb-integral-hom-tensor-adjunction-exchange). -/
theorem tensorAdjunctionExchange_evaluation (K L : Derived.{u, u} X R) :
    tensorAdjunctionExchange R a b K ((homReductionHom R).obj (op K, L)) ≫
      b.curry ((homReductionHom R).obj (op K, L)) K L (𝟙 _) =
        (a.adjunction K).counit.app L := by
  rw [← tensorAdjunctionExchange_uncurry]
  exact (a.adjunction K).homEquiv_symm_id L

end WeilConjectures.IntegralHom
