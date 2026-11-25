/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Realization of an intertwining tensor map

Source: the explicit calculation in Step 6 of
`lem-pod-condensed-point-sections-transport`.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A natural realization transport compatible with the tensor cup sends an
intertwining tensor map to an intertwining scalar map.
Source: blueprint `theorem-poincare-duality-frobenius`, naturality of the cup, and Step 6 of the
point-section transport argument.
Proof: move the transport past the realized arrow by naturality, use the
intertwining equation, use tensor compatibility, then the naturality of the cup.
(blueprint: lem-pod-point-transport-intertwining) -/
theorem realized_tensor_intertwining
    {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B]
    (P : A ⥤ A) (G : A ⥤ B)
    (μ : ∀ C H : A, G.obj C ⊗ G.obj H ⟶ G.obj (C ⊗ H))
    (hμ : ∀ {C C' H H' : A} (f : C ⟶ C') (g : H ⟶ H'),
      (G.map f ⊗ₘ G.map g) ≫ μ C' H' = μ C H ≫ G.map (f ⊗ₘ g))
    (r : G ⟶ P ⋙ G)
    (δ : ∀ C H : A, P.obj (C ⊗ H) ⟶ P.obj C ⊗ P.obj H)
    (hr : ∀ C H : A,
      μ C H ≫ r.app (C ⊗ H) ≫ G.map (δ C H) =
        (r.app C ⊗ₘ r.app H) ≫ μ (P.obj C) (P.obj H))
    (C H E : A) (φC : P.obj C ⟶ C) (φH : P.obj H ⟶ H) (φE : P.obj E ⟶ E)
    (v : C ⊗ H ⟶ E)
    (hv : δ C H ≫ (φC ⊗ₘ φH) ≫ v = P.map v ≫ φE) :
    (μ C H ≫ G.map v) ≫ r.app E ≫ G.map φE =
      ((r.app C ≫ G.map φC) ⊗ₘ (r.app H ≫ G.map φH)) ≫
        μ C H ≫ G.map v := by
  calc
    _ = μ C H ≫ r.app (C ⊗ H) ≫
        G.map (P.map v ≫ φE) := by
      simp only [Functor.map_comp, Category.assoc]
      have hn : G.map v ≫ r.app E = r.app (C ⊗ H) ≫ G.map (P.map v) :=
        r.naturality v
      rw [reassoc_of% hn]
    _ = μ C H ≫ r.app (C ⊗ H) ≫
        G.map (δ C H) ≫ G.map (φC ⊗ₘ φH) ≫ G.map v := by
      rw [← hv]
      simp only [Functor.map_comp]
    _ = (r.app C ⊗ₘ r.app H) ≫ μ (P.obj C) (P.obj H) ≫
        G.map (φC ⊗ₘ φH) ≫ G.map v := by rw [reassoc_of% hr C H]
    _ = _ := by
      rw [← reassoc_of% hμ φC φH]
      simp only [tensorHom_comp_tensorHom_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
