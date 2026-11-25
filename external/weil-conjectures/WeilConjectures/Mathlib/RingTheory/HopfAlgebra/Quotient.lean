/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Convolution products of algebra homomorphisms killing a Hopf ideal

If two algebra homomorphisms out of a Hopf algebra `A` vanish on a Hopf ideal `I`, then so does
their convolution product: both factor through the quotient Hopf algebra `A ⧸ I`, and the
quotient map is a bialgebra homomorphism.

## Blueprint

- `det-d-geometry`: the points of a closed subgroup scheme `V(I)` of an affine group scheme form a
  subgroup.
-/

@[expose] public section

open WithConv

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Algebra R B]

namespace Ideal.IsHopfIdeal

/-- The zero ideal is a Hopf ideal. -/
instance bot : (⊥ : Ideal A).IsHopfIdeal R where
  counit_eq_zero x hx := by simp_all
  map_mkQ_comul_eq_zero x hx := by
    rw [Submodule.restrictScalars_mem, Ideal.mem_bot] at hx
    rw [hx, map_zero, map_zero]
  antipode_mem x hx := by simp_all

/-- The convolution product of two algebra homomorphisms vanishing on a Hopf ideal vanishes on
it. (blueprint: `det-d-geometry`) -/
theorem convMul_apply_eq_zero {I : Ideal A} [I.IsHopfIdeal R] {f g : A →ₐ[R] B}
    (hf : ∀ a ∈ I, f a = 0) (hg : ∀ a ∈ I, g a = 0) {a : A} (ha : a ∈ I) :
    (toConv f * toConv g) a = 0 := by
  let q : A →ₐc[R] A ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hf' : f = (Ideal.Quotient.liftₐ I f hf).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  have hg' : g = (Ideal.Quotient.liftₐ I g hg).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  rw [hf', hg', ← AlgHom.convMul_comp_bialgHom_distrib]
  have : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
  simp [this]

/-- The supremum of a family of Hopf ideals is a Hopf ideal: the counit, coideal and antipode
conditions are additive. -/
theorem _root_.Ideal.isHopfIdeal_sSup {S : Set (Ideal A)} (hS : ∀ J ∈ S, J.IsHopfIdeal R) :
    (SupSet.sSup S).IsHopfIdeal R := by
  set T := SupSet.sSup S
  have key : ∀ x ∈ T, Coalgebra.counit (R := R) x = 0 ∧
      Coalgebra.comul (R := R) x ∈ LinearMap.range (LinearMap.lTensor A
        (T.restrictScalars R).subtype) ⊔ LinearMap.range (LinearMap.rTensor A
          (T.restrictScalars R).subtype) ∧ HopfAlgebra.antipode R x ∈ T := by
    intro x hx
    change x ∈ SupSet.sSup S at hx
    rw [sSup_eq_iSup'] at hx
    refine Submodule.iSup_induction _ (motive := fun x ↦ Coalgebra.counit (R := R) x = 0 ∧
      Coalgebra.comul (R := R) x ∈ LinearMap.range (LinearMap.lTensor A
        (T.restrictScalars R).subtype) ⊔ LinearMap.range (LinearMap.rTensor A
          (T.restrictScalars R).subtype) ∧ HopfAlgebra.antipode R x ∈ T) hx ?_ ?_ ?_
    · intro J y hy
      have hJ := hS J.1 J.2
      have hle : J.1 ≤ T := le_sSup J.2
      have hle' : J.1.restrictScalars R ≤ T.restrictScalars R := hle
      refine ⟨hJ.counit_eq_zero hy, ?_, hle (hJ.antipode_mem hy)⟩
      have hc := ((Submodule.isCoideal_iff_comul_mem _).1 hJ.toIsCoideal).2 y hy
      refine IsConcreteLE.le_iff.1 (sup_le_sup ?_ ?_) hc
      · rintro _ ⟨z, rfl⟩
        refine ⟨LinearMap.lTensor A (Submodule.inclusion hle') z, ?_⟩
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        rfl
      · rintro _ ⟨z, rfl⟩
        refine ⟨LinearMap.rTensor A (Submodule.inclusion hle') z, ?_⟩
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
        rfl
    · simp
    · intro y z hy hz
      refine ⟨by rw [map_add, hy.1, hz.1, add_zero], ?_, ?_⟩
      · rw [map_add]
        exact add_mem hy.2.1 hz.2.1
      · rw [map_add]
        exact add_mem hy.2.2 hz.2.2
  have : (T.restrictScalars R).IsCoideal := (Submodule.isCoideal_iff_comul_mem _).2
    ⟨fun x hx ↦ (key x hx).1, fun x hx ↦ (key x hx).2.1⟩
  exact ⟨fun x hx ↦ (key x hx).2.2⟩

end Ideal.IsHopfIdeal
