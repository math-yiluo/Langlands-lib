/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change of essentially smooth algebras

Source: Stacks Project, Algebra, Tags 00DK and 00T4; Smoothing Ring Maps, proof of 07FJ.
-/

@[expose] public section
universe u v
open scoped TensorProduct
namespace Algebra

/-- Essential smoothness is preserved by extension of scalars.
Source: Stacks Project, Algebra, Tags 00DK and 00T4, used in Smoothing Ring Maps,
proof of Lemma 07FJ, item-eighth-resolve.
(blueprint: lem-weil-pbc-essentially-smooth-base-change).

Proof: Present E as a localization S⁻¹P of a smooth R-algebra P. Transport the
P-algebra structure to E through this presentation. Smoothness of Q⊗_R P over Q
follows by smooth base change. Localization base change identifies Q⊗_R E as the
localization of Q⊗_R P at the image of S. The localization algebra equivalence,
restricted to Q, is the required essentially smooth presentation. -/
theorem essentiallySmooth_baseChange
    {R Q : Type u} {E : Type v}
    [CommRing R] [CommRing Q] [CommRing E] [Algebra R Q] [Algebra R E]
    (hE : EssentiallySmooth R E) : EssentiallySmooth Q (Q ⊗[R] E) := by
  rcases hE with ⟨P, ringP, algP, hP, S, ⟨e⟩⟩
  let := ringP
  let := algP
  have : Smooth R P := hP
  let : Algebra P E := (e.symm.toRingHom.comp (algebraMap P (Localization S))).toAlgebra
  have : IsScalarTower R P E := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R E r = e.symm (algebraMap P (Localization S) (algebraMap R P r))
    rw [← IsScalarTower.algebraMap_apply R P (Localization S), e.symm.commutes]
  have : IsLocalization S E :=
    (IsLocalization.isLocalization_iff_of_ringEquiv S e.symm.toRingEquiv).mp inferInstance
  let P' := Q ⊗[R] P
  let D := Q ⊗[R] E
  let : Algebra P' D :=
    (Algebra.TensorProduct.map (AlgHom.id R Q) (IsScalarTower.toAlgHom R P E)).toAlgebra
  have : IsScalarTower Q P' D := IsScalarTower.of_algebraMap_eq fun q ↦ by
    simp [P', D, RingHom.algebraMap_toAlgebra]
  have hloc : IsLocalization
      (S.map (Algebra.TensorProduct.includeRight (R := R) (A := Q))) D :=
    IsLocalization.tensorProduct_tensorProduct_right R Q S E
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  exact ⟨P', inferInstance, inferInstance, inferInstance,
    S.map (Algebra.TensorProduct.includeRight (R := R) (A := Q)),
    ⟨(IsLocalization.algEquiv
      (S.map (Algebra.TensorProduct.includeRight (R := R) (A := Q)))
      D (Localization _)).restrictScalars Q⟩⟩

end Algebra
