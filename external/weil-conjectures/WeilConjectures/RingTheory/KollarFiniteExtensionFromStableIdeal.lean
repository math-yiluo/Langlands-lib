/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Finite extension from a stable maximal ideal

Source: Stacks Project, Algebra, Tag 0BHZ, fourth proof paragraph.
-/

@[expose] public section
universe u v
namespace IsLocalRing
/-- Source: Stacks Project, Algebra, Tag 0BHZ, fourth proof paragraph.
(blueprint: new-kollar-finite-extension-stable-ideal).

Proof: Let i be the injective localization map R to L = R localized at x.
Construct S as the subalgebra of elements z of L satisfying z i(m) ⊆ i(m).
The image i(m) is a finite R-submodule N of L. Since x belongs to m and i(x) is
invertible in L, multiplication by i(x) gives an injective R-linear map S to N.
Therefore S is finite as an R-module. The stability hypothesis implies y/x lies
in S. The map R to S is injective and S is nonzero. It cannot be surjective:
if y/x = i(r), multiplication by i(x) and injectivity of i give y = xr,
contradicting y outside xR. By its construction S preserves i(m), so the image
of m is already an ideal of S and mS lies in the image of R. Thus the kernel
and cokernel conditions hold for n = 1. Finally i(x) is invertible in L, hence
x acts injectively on S. An element annihilated by m must be zero, whereas
zero has annihilator R rather than the proper ideal m. Transport the explicit
subalgebra to ULift to meet the requested universe. -/
theorem kollar_finite_extension_of_stable_ideal (R : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hr : IsSMulRegular R x)
    (y : R) (hy : y ∉ Ideal.span ({x} : Set R))
    (hstable : ∀ a ∈ maximalIdeal R, ∃ b ∈ maximalIdeal R, x * b = a * y) :
    let extension : Prop := ∃ (S : Type (max u v)) (sRing : CommRing S),
      letI := sRing
      ∃ φ : R →+* S,
        letI := φ.toAlgebra
        Nontrivial S ∧ Module.Finite R S ∧ ¬ Function.Bijective φ ∧
          (∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n * RingHom.ker φ = ⊥ ∧
            ∀ z ∈ Ideal.map φ ((maximalIdeal R) ^ n), z ∈ φ.range) ∧
          ¬ ∃ z : S, ∀ a : R, φ a * z = 0 ↔ a ∈ maximalIdeal R
    extension := by
  classical
  let L := Localization.Away x
  let i : R →+* L := algebraMap R L
  have hi : Function.Injective i := by
    apply IsLocalization.injective L (M := Submonoid.powers x)
    apply Submonoid.powers_le.mpr
    apply mem_nonZeroDivisors_iff_left.mpr
    intro a ha
    apply hr.right_eq_zero_of_smul
    simpa [mul_comm] using ha
  let S₀ : Subalgebra R L :=
    { carrier := {z | ∀ a ∈ maximalIdeal R, ∃ b ∈ maximalIdeal R, z * i a = i b}
      zero_mem' := by intro a _; exact ⟨0, Ideal.zero_mem _, by simp⟩
      one_mem' := by intro a ha; exact ⟨a, ha, by simp⟩
      add_mem' := by
        intro z w hz hw a ha
        obtain ⟨b, hb, hzb⟩ := hz a ha
        obtain ⟨c, hc, hwc⟩ := hw a ha
        exact ⟨b + c, Ideal.add_mem _ hb hc, by rw [add_mul, hzb, hwc, map_add]⟩
      mul_mem' := by
        intro z w hz hw a ha
        obtain ⟨b, hb, hwb⟩ := hw a ha
        obtain ⟨c, hc, hzc⟩ := hz b hb
        exact ⟨c, hc, by rw [mul_assoc, hwb, hzc]⟩
      algebraMap_mem' := by
        intro r a ha
        exact ⟨r * a, Ideal.mul_mem_left _ _ ha, (map_mul i r a).symm⟩ }
  let s : L := i y * IsLocalization.Away.invSelf x
  have hs : s ∈ S₀ := by
    intro a ha
    obtain ⟨b, hb, heq⟩ := hstable a ha
    refine ⟨b, hb, ?_⟩
    dsimp [s]
    calc
      i y * IsLocalization.Away.invSelf x * i a =
          i (a * y) * IsLocalization.Away.invSelf x := by rw [map_mul]; ring
      _ = i (x * b) * IsLocalization.Away.invSelf x := by rw [heq]
      _ = i b := by
        rw [map_mul]
        simpa [i, mul_assoc, mul_comm, mul_left_comm] using
          congrArg (· * i b) (IsLocalization.Away.mul_invSelf (S := L) x)
  let N : Submodule R L := Submodule.map (Algebra.linearMap R L) (maximalIdeal R)
  have hN : N.FG := Submodule.FG.map _ ((maximalIdeal R).fg_of_isNoetherianRing)
  have : Module.Finite R N := Module.Finite.of_fg hN
  let f : S₀ →ₗ[R] N :=
    { toFun := fun z ↦ ⟨i x * z.1, by
        obtain ⟨b, hb, heq⟩ := z.2 x hx
        exact ⟨b, hb, by simpa [mul_comm] using heq.symm⟩⟩
      map_add' := by intro z w; apply Subtype.ext; simp [mul_add]
      map_smul' := by
        intro r z
        apply Subtype.ext
        simp [Algebra.smul_def, mul_left_comm] }
  have hf : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    have h' : i x * z.1 = i x * w.1 := congrArg Subtype.val h
    have hu : IsUnit (i x) := IsLocalization.map_units L ⟨x, Submonoid.mem_powers x⟩
    exact hu.mul_left_cancel h'
  have : Module.Finite R S₀ := Module.Finite.of_injective f hf
  have hinj₀ : Function.Injective (algebraMap R S₀) := by
    intro a b h
    exact hi (congrArg Subtype.val h)
  have hnonsurj₀ : ¬ Function.Surjective (algebraMap R S₀) := by
    intro hsurj
    obtain ⟨r, heq⟩ := hsurj ⟨s, hs⟩
    have heq' : i r = s := congrArg Subtype.val heq
    have hmul := congrArg (i x * ·) heq'
    have hxr : x * r = y := by
      apply hi
      rw [map_mul]
      have hu := IsLocalization.Away.mul_invSelf (S := L) x
      simpa only [s, i, ← mul_assoc, mul_left_comm (algebraMap R L x), hu,
        one_mul, mul_one] using hmul
    exact hy (Ideal.mem_span_singleton.mpr ⟨r, hxr.symm⟩)
  let S := ULift.{v} S₀
  let eRing : S ≃+* S₀ := ULift.ringEquiv
  let φ : R →+* S := eRing.symm.toRingHom.comp (algebraMap R S₀)
  let := φ.toAlgebra
  let : Module R S := φ.toAlgebra.toModule
  let e : S ≃ₐ[R] S₀ :=
    { __ := eRing
      commutes' := by intro r; exact eRing.apply_symm_apply _ }
  have : Nontrivial S₀ := Function.Injective.nontrivial hinj₀
  have : Nontrivial S := e.toEquiv.nontrivial
  have : Module.Finite R S := Module.Finite.equiv e.symm.toLinearEquiv
  have hinj : Function.Injective φ := by
    intro a b h
    exact hinj₀ (by simpa [φ, e, eRing] using congrArg e h)
  have hker : RingHom.ker φ = ⊥ := (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  let J : Ideal S :=
    { carrier := {z | ∃ a ∈ maximalIdeal R, φ a = z}
      zero_mem' := ⟨0, Ideal.zero_mem _, map_zero φ⟩
      add_mem' := by
        rintro z w ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, Ideal.add_mem _ ha hb, map_add φ a b⟩
      smul_mem' := by
        rintro z w ⟨a, ha, rfl⟩
        obtain ⟨b, hb, heq⟩ := (e z).2 a ha
        refine ⟨b, hb, ?_⟩
        apply e.injective
        apply Subtype.ext
        simpa [φ, e, eRing] using heq.symm }
  have hmap : Ideal.map φ (maximalIdeal R) ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact ⟨a, ha, rfl⟩
  refine ⟨S, inferInstance, φ, ?_⟩
  change Nontrivial S ∧ Module.Finite R S ∧ _
  refine ⟨inferInstance, inferInstance, ?_, ⟨1, le_rfl, ?_, ?_⟩, ?_⟩
  · intro hb
    apply hnonsurj₀
    intro z
    obtain ⟨a, ha⟩ := hb.2 (e.symm z)
    exact ⟨a, by simpa [φ, e, eRing] using congrArg e ha⟩
  · simp [hker]
  · intro z hz
    obtain ⟨a, _, ha⟩ := hmap (by simpa using hz)
    exact ⟨a, ha⟩
  · rintro ⟨z, hz⟩
    have hzero := (hz x).mpr hx
    have hzero' : i x * (e z).1 = 0 := by
      simpa [φ, e, eRing] using congrArg (fun w ↦ (e w).1) hzero
    have hz0 : z = 0 := by
      apply e.injective
      apply Subtype.ext
      have hu : IsUnit (i x) := IsLocalization.map_units L ⟨x, Submonoid.mem_powers x⟩
      exact hu.mul_left_cancel (by simpa using hzero')
    have h1 := (hz 1).mp (by simp [hz0])
    exact h1 isUnit_one
end IsLocalRing
