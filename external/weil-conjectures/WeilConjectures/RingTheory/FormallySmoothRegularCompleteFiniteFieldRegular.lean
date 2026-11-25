/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.FormallySmoothAdicClosedFiber
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import WeilConjectures.RingTheory.FormallySmoothRegularCompletePurelyInseparableRegular
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule

/-!
# Finite field base changes of a formally smooth complete algebra

Source: Stacks Project, More on Algebra, Proposition 07PM, last two paragraphs,
and Algebra, Lemma 0381.
(blueprint: lem-weil-pbc-fs-regular-complete-finite-field-regular)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- A formally smooth complete local algebra over a regular complete local domain
becomes regular after every finite extension of the base fraction field.
Source: Stacks Project, More on Algebra, Proposition 07PM, final two paragraphs,
and Algebra, Lemma 0381.
(blueprint: lem-weil-pbc-fs-regular-complete-finite-field-regular)

Proof: Apply 07NQ for flatness and geometric regularity of the closed fibre.
Taking the trivial field extension in 0381 makes the closed fibre regular;
as it is local, it is regular local. Apply regular local ascent 031E to obtain
regular locality of C, then 0AFS to make C regular. Its generic fibre is
Noetherian by localization base change. For each finite purely inseparable
extension of K use the characteristic-zero argument and degree induction in
lem-weil-pbc-fs-regular-complete-purely-inseparable-regular. Tensor cancellation
identifies the result with the field base change of the generic fibre, proving
geometric regularity. Finally 0381 makes the base change along any finite L/K
regular. Tensor cancellation identifies this ring with L tensor_A C. -/
theorem isRegularRing_tensorProduct_of_formallySmoothAdic_regular_complete
    (A : Type u) (C : Type v) (K : Type u) (L : Type w)
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [Module.Finite K L]
    [IsLocalHom (algebraMap A C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (hfs : FormallySmoothAdic A C (IsLocalRing.maximalIdeal C)) :
    IsRegularRing (TensorProduct A L C)  := by
  have halg : (algebraMap A C).toAlgebra = (inferInstance : Algebra A C) :=
    toAlgebra_algebraMap
  have hfs' : letI : Algebra A C := (algebraMap A C).toAlgebra
      FormallySmoothAdic A C (IsLocalRing.maximalIdeal C) := halg.symm ▸ hfs
  obtain ⟨hflat, hclosed⟩ :=
    RingHom.flat_and_isGeometricallyRegular_closedFiber_of_formallySmoothAdic
      (algebraMap A C) hfs'
  let k := A ⧸ IsLocalRing.maximalIdeal A
  let I := (IsLocalRing.maximalIdeal A).map (algebraMap A C)
  let F := C ⧸ I
  let : Field k := Ideal.Quotient.field _
  let : Algebra k F := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal C).ne_top
    (IsLocalRing.map_maximalIdeal_le (algebraMap A C))
  have : Nontrivial F := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing F :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hclosed' : IsGeometricallyRegular k F := by
    convert hclosed using 1
    apply algebra_ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have : IsRegularRing (TensorProduct k k F) :=
    isRegularRing_tensorProduct_of_isGeometricallyRegular hclosed' k
      (IntermediateField.fg_top k k)
  have : IsRegularRing F := IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k F).toRingEquiv
  have : IsRegularLocalRing F := IsRegularLocalRing.of_isRegularRing_of_isLocalRing F
  have : IsRegularLocalRing C :=
    IsRegularLocalRing.of_flat_of_regular_closedFiber (algebraMap A C) hflat inferInstance
  have : IsRegularRing C :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal C)).2
  have hgeom : IsGeometricallyRegular K (TensorProduct A K C) := by
    refine ⟨?_, ?_⟩
    · let : Algebra C (TensorProduct A C K) := Algebra.TensorProduct.leftAlgebra
      have : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))
          (TensorProduct A C K) := IsLocalization.tensor (S := C) (A := K) _
      have := IsLocalization.isNoetherianRing
        (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) (TensorProduct A C K)
        (inferInstance : IsNoetherianRing C)
      exact isNoetherianRing_of_ringEquiv (TensorProduct A C K)
        (Algebra.TensorProduct.comm A C K).toRingEquiv
    · intro E _ _ _ _
      let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
      have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
      have : IsRegularRing (TensorProduct A E C) :=
        isRegularRing_tensorProduct_of_formallySmoothAdic_regular_complete_purelyInseparable
          A C K E hfs
      exact IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.cancelBaseChange A K E E C).symm.toRingEquiv
  have : IsRegularRing (TensorProduct K L (TensorProduct A K C)) :=
    isRegularRing_tensorProduct_of_isGeometricallyRegular hgeom L
      (IntermediateField.fg_top K L)
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A K L L C).toRingEquiv

end Algebra
