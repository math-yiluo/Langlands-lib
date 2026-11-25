/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.ProEtaleCoefficients.FiniteProductWContractible
/-! Finite disjoint unions of w-contractible spectra.
(blueprint: det-pe-hypercover-finite-coproduct-spectrum) -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v
/-- Finite disjoint unions of w-contractible spectra are spectra of w-contractible rings.
Source: Stacks Project, Tag 09A1 (2); Mathlib `sigmaSpec`.
(blueprint: det-pe-hypercover-finite-coproduct-spectrum)

Proof: reindex the finite family by `Fin (Nat.card I)`, so the product of its coordinate
rings remains in the scheme universe. The finite-product theorem proves w-contractibility.
The canonical finite coproduct-to-product-spectrum isomorphism and the componentwise
isomorphisms identify its spectrum with the original coproduct. Empty families yield the
zero ring and empty spectrum, with no nonempty-index assumption.
-/
theorem finite_coproduct_wContractible_spectrum (I : Type v) [Finite I] (A : I → Scheme.{u})
    (h : ∀ i, ∃ D : CommRingCat.{u}, IsWContractibleRing D ∧ Nonempty (Spec D ≅ A i)) :
    ∃ D : CommRingCat.{u}, IsWContractibleRing D ∧ Nonempty (Spec D ≅ ∐ A) := by
  classical
  let e : ULift.{u} (Fin (Nat.card I)) ≃ I :=
    Equiv.ulift.trans (Finite.equivFin I).symm
  choose D hD he using fun i : ULift.{u} (Fin (Nat.card I)) ↦ h (e i)
  let := hD
  have hw : IsWContractibleRing (∀ i, D i) :=
    isWContractibleRing_pi_of_finite (ULift.{u} (Fin (Nat.card I))) (fun i ↦ D i)
  refine ⟨.of (∀ i, D i), hw, ⟨?_⟩⟩
  exact (asIso (sigmaSpec D)).symm ≪≫
    Sigma.mapIso (fun i ↦ (he i).some) ≪≫ Sigma.reindex e A
