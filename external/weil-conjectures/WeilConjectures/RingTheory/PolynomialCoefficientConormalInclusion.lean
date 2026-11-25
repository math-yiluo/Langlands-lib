/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import WeilConjectures.RingTheory.PolynomialCoefficientTensorQuotient

/-! # The conormal inclusion for polynomial coefficient reduction

Source: Stacks Project, Algebra, Tag 00S2, proof of lemma-exact-sequence-NL;
Smoothing Ring Maps, Tag 07CE, equation-sequence.
(blueprint: lem-weil-pbc-polynomial-coefficient-conormal-inclusion)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Coefficient expansion identifies the source of the conormal inclusion, its image,
and its injectivity criterion, without any projectivity assumption.
Source: Stacks Project, Algebra, Tag 00S2, proof of lemma-exact-sequence-NL;
Smoothing Ring Maps, Tag 07CE, equation-sequence.
(blueprint: lem-weil-pbc-polynomial-coefficient-conormal-inclusion)

Proof. Put Q = P[y], H = ker(Q → (P/I)[y]), J = ker φ, and A = P/I.
Compatibility gives H ≤ J. Coefficient expansion identifies the P-module H with
Q ⊗_P I: a polynomial in H has all coefficients in I, and its inverse sums the
monomial tensors of those coefficients. Reducing modulo HJ identifies H/HJ with
C ⊗_P I, because Q/J = C. Since I acts as zero on C, tensoring the quotient
I → I/I² identifies C ⊗_P I with C ⊗_A (I/I²). These identifications send
c ⊗ [x] to the class of a lift of c times the constant polynomial x.
Inclusion H ≤ J followed by J → J/J² kills HJ, hence descends to the required
C-linear map i. Its image is exactly the image of H in J/J², which is the stated
submodule equality after restriction to Q. Its kernel, under the identifications,
is (H ∩ J²)/HJ: the class of h vanishes in J/J² exactly when h lies in J².
Thus i is injective exactly when H ∩ J² = HJ. The representative formula is the
formula for the composite, and is independent of the chosen lifts since their
differences lie in J. The argument also applies to an empty variable set and to
I = P, when C and the tensor module are zero. -/
theorem polynomial_coefficient_conormal_inclusion
    (P : Type u) [CommRing P] (I : Ideal P) (m : ℕ)
    (C : Type v) [CommRing C] [Algebra (P ⧸ I) C]
    (α : MvPolynomial (Fin m) (P ⧸ I) →ₐ[P ⧸ I] C)
    (φ : MvPolynomial (Fin m) P →+* C)
    (hφeq : φ = α.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I)))
    (hφ : Function.Surjective φ) :
    ∃ (i : C ⊗[P ⧸ I] I.Cotangent →ₗ[C]
        (Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent),
      (∀ (c : C) (x : I) (y : (Extension.ofSurjective φ.toIntAlgHom hφ).ker),
        y.1 = MvPolynomial.C x.1 →
          i (c ⊗ₜ I.toCotangent x) = c • Extension.Cotangent.mk y) ∧
      i.range.restrictScalars (Extension.ofSurjective φ.toIntAlgHom hφ).Ring =
        (Submodule.comap (Extension.ofSurjective φ.toIntAlgHom hφ).ker.subtype
          (RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)))).map
            Extension.Cotangent.mk ∧
      (Function.Injective i ↔
        RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)) ⊓
            (RingHom.ker φ) ^ 2 =
          RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)) *
            RingHom.ker φ) := by
  classical
  let E := Extension.ofSurjective φ.toIntAlgHom hφ
  let H : Ideal E.Ring := RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m))
  have hHJ : H ≤ E.ker := by
    intro q hq
    change φ q = 0
    rw [hφeq]
    change α (MvPolynomial.map (Ideal.Quotient.mk I) q) = 0
    rw [show MvPolynomial.map (Ideal.Quotient.mk I) q = 0 from hq, map_zero]
  let j : H →ₗ[E.Ring] E.ker := Submodule.inclusion hHJ
  let f : H →ₗ[E.Ring] E.Cotangent := Extension.Cotangent.mk.comp j
  let N : Submodule E.Ring H := E.ker • ⊤
  have hN : N ≤ f.ker := by
    intro x hx
    apply (Extension.Cotangent.mk_eq_zero_iff _).mpr
    have hx' : x.1 ∈ E.ker * H :=
      (Submodule.mem_smul_top_iff E.ker H x).mp hx
    change x.1 ∈ E.ker ^ 2
    simpa only [pow_two] using (Ideal.mul_mono_right hHJ) hx'
  let g : H ⧸ N →ₗ[E.Ring] E.Cotangent := N.liftQ f hN
  obtain ⟨e, he⟩ := polynomial_coefficient_tensor_quotient P I m C α φ hφeq hφ
  let t : C ⊗[P ⧸ I] I.Cotangent →ₗ[E.Ring] E.Cotangent := g.comp e.toLinearMap
  let i : C ⊗[P ⧸ I] I.Cotangent →ₗ[C] E.Cotangent :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := fun c z ↦ by
        obtain ⟨q, rfl⟩ := E.algebraMap_surjective c
        simpa only [RingHom.id_apply, algebraMap_smul] using t.map_smul q z }
  refine ⟨i, ?_, ?_, ?_⟩
  · intro c x y hy
    have hx : MvPolynomial.C x.1 ∈ H := by
      change MvPolynomial.map (Ideal.Quotient.mk I) (MvPolynomial.C x.1) = 0
      rw [MvPolynomial.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr x.2, map_zero]
    let z : H := ⟨MvPolynomial.C x.1, hx⟩
    change g (e (c ⊗ₜ I.toCotangent x)) = c • Extension.Cotangent.mk y
    rw [he c x z rfl]
    change f (E.σ c • z) = c • Extension.Cotangent.mk y
    rw [f.map_smul]
    have hz : j z = y := Subtype.ext hy.symm
    change E.σ c • Extension.Cotangent.mk (j z) = c • Extension.Cotangent.mk y
    rw [hz, ← algebraMap_smul C, E.algebraMap_σ]
  · change t.range = _
    rw [LinearMap.range_comp, e.range, Submodule.map_top, Submodule.range_liftQ]
    change (Extension.Cotangent.mk.comp j).range = _
    rw [LinearMap.range_comp]
    congr 1
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_comap]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  · have hg : Function.Injective i ↔ Function.Injective g := by
      change Function.Injective (g ∘ e) ↔ Function.Injective g
      constructor
      · intro hi a b hab
        have := hi (show g (e (e.symm a)) = g (e (e.symm b)) by simpa using hab)
        exact e.symm.injective this
      · exact fun hg ↦ hg.comp e.injective
    rw [hg]
    change Function.Injective g ↔ H ⊓ E.ker ^ 2 = H * E.ker
    constructor
    · intro hg
      apply le_antisymm
      · intro x hx
        have hxH : x ∈ H := hx.1
        let y : H := ⟨x, hxH⟩
        have hfy : f y = 0 := (Extension.Cotangent.mk_eq_zero_iff _).mpr hx.2
        have hgy : g (Submodule.Quotient.mk y) = g 0 := by
          simpa [g] using hfy
        have hyN : y ∈ N := (Submodule.Quotient.mk_eq_zero N).mp (hg hgy)
        have := (Submodule.mem_smul_top_iff E.ker H y).mp hyN
        simpa [Ideal.mul_comm] using this
      · exact le_inf Ideal.mul_le_left
          (by simpa [pow_two] using Ideal.mul_mono_left hHJ)
    · intro hprod
      apply (injective_iff_map_eq_zero g).mpr
      intro z hz
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
      have hx : x.1 ∈ E.ker ^ 2 := by
        exact (Extension.Cotangent.mk_eq_zero_iff (P := E) (j x)).mp hz
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      apply (Submodule.mem_smul_top_iff E.ker H x).mpr
      have : x.1 ∈ H * E.ker := hprod ▸ (show x.1 ∈ H ⊓ E.ker ^ 2 from ⟨x.2, hx⟩)
      simpa [Ideal.mul_comm] using this

end Algebra
