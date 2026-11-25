/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData

/-!
# The zeroth module of formal glueing data

Source: Stacks Project, More on Algebra, Remark 05EL
(blueprint: def-weil-pbc-formal-glueing-H0).
-/

@[expose] public section

universe u v w

namespace FormalGlueing

open scoped TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The module of compatible sections, as the intersection of kernels of the
compatibility differences. Tensor factors are in Mathlib's order `S ⊗[R] M`.
Source: Stacks Project, More on Algebra, Remark 05EL, displayed definition of
`H^0` (blueprint: def-weil-pbc-formal-glueing-H0). -/
noncomputable def h0 {t : ℕ} (φ : R →+* S) (f : Fin t → R) (X : Data.{u, v, w} φ f) :
    Submodule R (restrict φ X.M' × ∀ i : Fin t, piece (f i) (X.M i)) :=
  letI : Algebra R S := φ.toAlgebra
  let pr : ∀ i : Fin t,
      (restrict φ X.M' × ∀ j : Fin t, piece (f j) (X.M j)) →ₗ[R]
        piece (f i) (X.M i) :=
    fun i ↦ (LinearMap.proj i).comp (LinearMap.snd R _ _)
  (⨅ i : Fin t, LinearMap.ker
    (((X.alpha i).toLinearMap.comp
        (LocalizedModule.mkLinearMap _ (restrict φ X.M'))).comp
          (LinearMap.fst R _ _) -
      (TensorProduct.mk R S (piece (f i) (X.M i)) 1).comp (pr i))) ⊓
    ⨅ i : Fin t, ⨅ j : Fin t, LinearMap.ker
      (((X.alpha_overlap i j).toLinearMap.comp
          (LocalizedModule.mkLinearMap _ (piece (f i) (X.M i)))).comp (pr i) -
        (LocalizedModule.mkLinearMap _ (piece (f j) (X.M j))).comp (pr j))

end FormalGlueing
