/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.FormallySmoothCompleteDegreePRegular
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule

/-!
# Purely inseparable base changes of a regular complete algebra

Source: Stacks Project, More on Algebra, Proposition 07PM, last two paragraphs.
(blueprint: lem-weil-pbc-fs-regular-complete-purely-inseparable-regular)
-/

@[expose] public section

universe u v w

namespace Algebra
attribute [-instance] IntermediateField.module' in
/-- Finite purely inseparable fraction-field base changes of a regular formally
smooth complete algebra are regular.
Source: Stacks Project, More on Algebra, Proposition 07PM, final two paragraphs.
(blueprint: lem-weil-pbc-fs-regular-complete-purely-inseparable-regular)

Proof: Localize the regular ring C at the images of the nonzero elements of A;
localization base change and localization of regular rings make K tensor_A C
regular. If K has characteristic zero, a purely inseparable extension is
separable and therefore trivial. Transport the localized regular ring along
the induced tensor equivalence. In characteristic p, use strong induction on
the finite degree [L:K]. If the bottom intermediate field is the top, the
structure map K -> L is surjective and the same tensor equivalence applies.
Otherwise Fields 09HI supplies an intermediate M with [M:K] < [L:K] and
[L:M] = p. Apply the induction hypothesis to M/K. The degree-p ascent lemma
lem-weil-pbc-fs-complete-degree-p-regular then gives regularity over L.
This treats degree one, p = 2, and a zero generic fibre without exceptions. -/
theorem isRegularRing_tensorProduct_of_formallySmoothAdic_regular_complete_purelyInseparable
    (A : Type u) (C : Type v) (K : Type u) (L : Type w)
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [CommRing C] [IsLocalRing C] [IsRegularRing C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [Module.Finite K L]
    [IsPurelyInseparable K L]
    [IsLocalHom (algebraMap A C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (hfs : FormallySmoothAdic A C (IsLocalRing.maximalIdeal C)) :
    IsRegularRing (TensorProduct A L C)  := by
  let R := TensorProduct A C K
  let : Algebra C R := Algebra.TensorProduct.leftAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) R :=
    IsLocalization.tensor (S := C) (A := K) _
  have hbase : IsRegularRing (TensorProduct A K C) := by
    have : IsRegularRing R := by
      let S := Algebra.algebraMapSubmonoid C (nonZeroDivisors A)
      apply RingTheory.isRegularRing_of_localization C R S (algebraMap C R)
      · exact IsLocalization.map_units R
      · intro y
        obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj S y
        obtain ⟨z, hz⟩ := IsLocalization.map_units R s
        refine ⟨r, s, ↑z⁻¹, z⁻¹.isUnit, ?_, ?_⟩
        · rw [← hz]
          exact z.mul_inv
        · calc
            y = (y * algebraMap C R s) * ↑z⁻¹ := by rw [← hz]; simp
            _ = algebraMap C R r * ↑z⁻¹ := by rw [hy]
      · intro r hr
        exact (IsLocalization.map_eq_zero_iff S R r).mp hr
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm A C K).toRingEquiv
  have trivial_extension (E : Type w) [Field E] [Algebra K E] [Algebra A E]
      [IsScalarTower A K E] (hsurj : Function.Surjective (algebraMap K E)) :
      IsRegularRing (TensorProduct A E C) := by
    have := hbase
    let e : K ≃ₐ[A] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom A K E)
      ⟨(algebraMap K E).injective, hsurj⟩
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : C ≃ₐ[A] C)).toRingEquiv
  rcases CharP.exists' K with hzero | ⟨p, hp, hchar⟩
  · have := hzero
    exact trivial_extension L (IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L)
  · have := hp
    have := hchar
    generalize hn : Module.finrank K L = n
    induction n using Nat.strong_induction_on generalizing L with
    | h n ih =>
      by_cases htriv : (⊥ : IntermediateField K L) = ⊤
      · apply trivial_extension L
        intro x
        have hx : x ∈ (⊥ : IntermediateField K L) := by rw [htriv]; trivial
        exact hx
      · obtain ⟨_, _, _, _, _, _, hlast⟩ := IsPurelyInseparable.exists_pth_root_tower K L p
        obtain ⟨M, β, _, _, _, _, hfinite, hpure, hlt, _, hdegree, _⟩ := hlast htriv
        have := hfinite
        have := hpure
        let : Algebra A M := ((algebraMap K M).comp (algebraMap A K)).toAlgebra
        have : IsScalarTower A K M := IsScalarTower.of_algebraMap_eq' rfl
        have hregular : IsRegularRing (TensorProduct A M C) :=
          ih (Module.finrank K M) (hn ▸ hlt) M rfl
        exact isRegularRing_tensorProduct_of_formallySmoothAdic_degree_p
          A C K L p M hdegree hregular hfs

end Algebra
