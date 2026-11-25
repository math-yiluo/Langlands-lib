/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Geometric regularity of the closed fibre of a local completion

Source: Stacks Project, More on Algebra, Proposition Tag 07PX
(blueprint: lem-weil-pbc-completion-closed-fiber).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AdicCompletion

/-- The closed fibre of a Noetherian local ring's completion is geometrically regular.

Proof: The residue field at the maximal ideal is canonically A/m since localization
at the maximal ideal of a local ring inverts only units. Tensoring the completion
with A/m is canonically the quotient by the extended maximal ideal. The completion
map induces an isomorphism A/m to this quotient, by its evaluation at level one.
These identifications respect the residue-field algebra structures, so the closed
fibre is the residue field as an algebra over itself. It is thus Noetherian. For any
finite purely inseparable extension k'/k, tensoring this algebra with k' gives k'
itself, a field and hence a regular ring. No characteristic hypothesis is required.

Source: Stacks Project, More on Algebra, Proposition Tag 07PX
(blueprint: lem-weil-pbc-completion-closed-fiber). -/
theorem isGeometricallyRegular_closedFiber
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    Algebra.IsGeometricallyRegular (IsLocalRing.maximalIdeal A).ResidueField
      ((IsLocalRing.maximalIdeal A).Fiber (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  classical
  let m := IsLocalRing.maximalIdeal A
  let B := AdicCompletion m A
  let k := m.ResidueField
  let qk : (A ⧸ m) ≃ₐ[A] k := AlgEquiv.ofBijective (IsScalarTower.toAlgHom A (A ⧸ m) k)
    m.bijective_algebraMap_quotient_residueField
  let eq : (B ⧸ m.map (algebraMap A B)) ≃ₐ[A] (A ⧸ m) :=
    (Ideal.quotientEquivAlgOfEq A
      (AdicCompletion.ker_evalOneₐ_eq_map m m.fg_of_isNoetherianRing).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.evalOneₐ_surjective m))
  let eA : (k ⊗[A] B) ≃ₐ[A] k :=
    (Algebra.TensorProduct.congr qk.symm (AlgEquiv.refl : B ≃ₐ[A] B)).trans
      (((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m).symm.restrictScalars A).trans
        (eq.trans qk))
  let e : (k ⊗[A] B) ≃ₐ[k] k :=
    AlgEquiv.extendScalarsOfSurjective m.algebraMap_residueField_surjective eA
  have : IsNoetherianRing (k ⊗[A] B) := isNoetherianRing_of_ringEquiv k e.symm.toRingEquiv
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  let e' : k' ⊗[k] (k ⊗[A] B) ≃ₐ[k] k' :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k' ≃ₐ[k] k') e).trans
      ((Algebra.TensorProduct.rid k k' k').restrictScalars k)
  exact IsRegularRing.of_ringEquiv e'.symm.toRingEquiv

end AdicCompletion
