/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FormallySmoothAdicBaseChange
import WeilConjectures.RingTheory.PurelyInseparableBaseChangeLocalRing
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalOfFormallySmoothAdic

/-! Intermediate regularity assertion for a purely inseparable base change.
(blueprint: lem-weil-pbc-fs-adic-field-geometrically-regular-regular-base-change) -/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

/-- A finite purely inseparable base change of a formally smooth adic local algebra is regular.
The proof follows Steps 1--4 of Tag 07EL: base-change formal smoothness, upgrade the adic
topology from the extended maximal ideal to the unique maximal ideal, apply Tag 07EI, and
localize at primes. The tensor-factor swap is handled by `Algebra.TensorProduct.comm`.
(blueprint: lem-weil-pbc-fs-adic-field-geometrically-regular-regular-base-change) -/
theorem isRegularRing_tensorProduct_of_formallySmoothAdic
    (k : Type u) (C : Type v) (k' : Type (max u v))
    [Field k] [CommRing C] [Algebra k C] [IsNoetherianRing C] [IsLocalRing C]
    [Field k'] [Algebra k k'] [Module.Finite k k'] [IsPurelyInseparable k k']
    (h : FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)) :
    IsRegularRing (k' ⊗[k] C) := by
  let D := C ⊗[k] k'
  let _ : Algebra k D := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra k' D := Algebra.TensorProduct.rightAlgebra
  obtain ⟨_, _, _, _, hnoeth, hlocal, hmax, _⟩ :=
    Algebra.TensorProduct.purelyInseparable_baseChange_localRing k k' C
  let _ : IsNoetherianRing D := hnoeth
  let _ : IsLocalRing D := hlocal
  have hfsI : FormallySmoothAdic k' D
      ((IsLocalRing.maximalIdeal C).map
        (algebraMap C D)) := by
    simpa [D] using formallySmoothAdic_tensorProduct k C k'
      (IsLocalRing.maximalIdeal C) h
  have hle : (IsLocalRing.maximalIdeal C).map
      (algebraMap C D) ≤ IsLocalRing.maximalIdeal D :=
    IsLocalRing.map_maximalIdeal_le _
  have hfs : FormallySmoothAdic k' D (IsLocalRing.maximalIdeal D) := by
    intro E _ _ J hJ g hg
    obtain ⟨n, hn, hgn⟩ := hg
    obtain ⟨f, hf⟩ := hfsI J hJ g ⟨n, hn, fun x hx =>
      hgn x ((Ideal.pow_right_mono hle n) hx)⟩
    exact ⟨f, hf⟩
  have hreglocal : IsRegularLocalRing D :=
    isRegularLocalRing_of_formallySmoothAdic k' D hfs
  have hreg : IsRegularRing D := by
    apply isRegularRing_iff.mpr
    intro p hp
    let _ : p.IsPrime := hp
    exact (IsRegularLocalRing.localization_at_prime_and_isRegularRing p).1
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.commRight k k' C).symm.toRingEquiv

end Algebra
