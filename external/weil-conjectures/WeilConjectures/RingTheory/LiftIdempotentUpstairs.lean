/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.EtaleLiftCoprimeFactorization
import WeilConjectures.RingTheory.IntegralIdempotentAnnihilatingPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Coprime.Lemmas
import WeilConjectures.RingTheory.EtaleMakeTensorPairCoprime

/-!
# Lifting an idempotent upstairs after an étale neighbourhood

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07M4
(blueprint: lem-weil-pbc-lift-idempotent-upstairs).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

private theorem tensor_quotient_equiv
    {A : Type u} {B : Type v} {C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A)
    (α : A ⧸ I ≃+* C ⧸ I.map (algebraMap A C))
    (hα : ∀ a : A, α (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk _ (algebraMap A C a)) :
    ∃ β : B ⧸ I.map (algebraMap A B) ≃+*
        (TensorProduct A B C) ⧸ I.map (algebraMap A (TensorProduct A B C)),
      ∀ b : B, β (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (B := C) b) := by
  let αA : (A ⧸ I) ≃ₐ[A] (C ⧸ I.map (algebraMap A C)) :=
    { α with commutes' := hα }
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) αA
  let e₃ := Algebra.TensorProduct.tensorQuotientEquiv (R := A) A C B
    (I.map (algebraMap A C))
  have hI : (I.map (algebraMap A C)).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B)) =
      I.map (algebraMap A (TensorProduct A B C)) := by
    change (I.map (algebraMap A C)).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom = _
    rw [Ideal.map_map]
    congr 1
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap).symm
  let e₄ := Ideal.quotEquivOfEq hI
  refine ⟨e₁.toRingEquiv.trans (e₂.toRingEquiv.trans (e₃.toRingEquiv.trans e₄)), ?_⟩
  intro b
  change e₄ (e₃ (e₂ (e₁ (Ideal.Quotient.mk _ b)))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  simp only [e₂, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.refl_toAlgHom, AlgHom.id_apply, map_one]
  change e₄ (e₃ (b ⊗ₜ[A] (Ideal.Quotient.mk _ (1 : C)))) = _
  dsimp only [e₃, e₄]
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotEquivOfEq_mk]
  rfl

/-- An idempotent modulo an ideal lifts after an étale base change preserving the
quotient.  The equivalence `β` records the canonical tensor--quotient
identification induced by `α`; the final equality is precisely the lifting
condition under that identification.
Source: Stacks Project, More on Algebra, Lemma Tag 07M4
(blueprint: lem-weil-pbc-lift-idempotent-upstairs).

Proof:
1. Lift `ebar` to `y`. The integral annihilator lemma gives a monic `f`
   with `f(y) = 0` reducing to `X^d * (X - 1)^d`, with `d ≥ 1`.
2. The identity `1*X + (-1)*(X - 1) = 1` and Mathlib's coprime-power
   lemma show the factors are coprime. Lift this factorization over an étale
   `A`-algebra `C` inducing an isomorphism modulo `I`.
3. In `T = B ⊗[A] C`, evaluate the lifted factors at `y ⊗ 1` to obtain
   `x,z` with `x*z = 0`. Their reductions are coprime by evaluating the
   coprime polynomial factors. The reduction of `x` equals that of `y ⊗ 1`
   because this is an idempotent and `d` is positive. The private tensor
   quotient equivalence checks this identification on representatives.
4. Apply `exists_etale_isCoprime_tensor_of_isCoprime_quotient`: separation
   of the closed integral image and principal localization give a further
   étale `C → D`, preserving `C/IC`, in which the images of `x,z` are coprime.
5. Write `1 = u*x + v*z` in `B ⊗[A] D`, and set `e = u*x`. Since `x*z = 0`,
   `e² = e*(u*x + v*z) = e`. In the quotient let `t` be the transported
   `ebar`. Then `x mod I = t` and `t² = t`; multiplying the reduced Bézout
   identity by `t` gives `u*t = t`, because `z*t = 0`. Thus `e` reduces to `t`.
6. Compose the étale maps and the quotient isomorphisms. The tensor quotient
   equivalence for the composite has the required values on representatives,
   and the preceding equality is exactly the asserted lifting condition.
-/
theorem exists_etale_lift_isIdempotentElem
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (I : Ideal A)
    [Algebra A B] [Algebra.IsIntegral A B]
    (ebar : B ⧸ I.map (algebraMap A B)) (hebar : IsIdempotentElem ebar) :
    ∃ (A' : CommRingCat.{u}) (g : CommRingCat.of A ⟶ A'),
      letI : Algebra A A' := g.hom.toAlgebra;
      Etale (Spec.map g) ∧
      ∃ α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A'),
        (∀ a : A, α (Ideal.Quotient.mk I a) =
          Ideal.Quotient.mk _ (algebraMap A A' a)) ∧
        ∃ (e' : TensorProduct A B (A' : Type u)), IsIdempotentElem e' ∧
          ∃ β : B ⧸ I.map (algebraMap A B) ≃+*
              (TensorProduct A B (A' : Type u)) ⧸
                I.map (algebraMap A (TensorProduct A B (A' : Type u))),
            (∀ b : B, β (Ideal.Quotient.mk _ b) =
              Ideal.Quotient.mk _
                (Algebra.TensorProduct.includeLeftRingHom (R := A) (B := A') b)) ∧
            β ebar = Ideal.Quotient.mk _ e' := by
  classical
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ebar
  obtain ⟨d, f, hd, hf, hfy, hfmod⟩ :=
    Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient I y
      (hy.symm ▸ hebar)
  have hbase : IsCoprime (Polynomial.X : Polynomial (A ⧸ I)) (Polynomial.X - 1) := by
    refine ⟨1, -1, ?_⟩
    ring
  have hcop := hbase.pow (m := d) (n := d)
  have hlead : IsUnit ((Polynomial.X : Polynomial (A ⧸ I)) ^ d).leadingCoeff := by
    rw [(Polynomial.monic_X.pow d).leadingCoeff]
    exact isUnit_one
  obtain ⟨C, instC, φ, hφ, hbij, g, h, hfactor, hg, hh⟩ :=
    Polynomial.exists_etale_lift_coprime_factorization I f hf
      (Polynomial.X ^ d) ((Polynomial.X - 1) ^ d) hfmod hlead hcop
  let : CommRing C := instC
  let : Algebra A C := φ.toAlgebra
  let J := I.map φ
  let α₁ := RingEquiv.ofBijective (Ideal.quotientMap J φ Ideal.le_comap_map) hbij
  have hα₁ : ∀ a : A, α₁ (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (algebraMap A C a) := fun _ => rfl
  obtain ⟨β₁, hβ₁⟩ := tensor_quotient_equiv (B := B) (C := C) I α₁ hα₁
  let T := TensorProduct A B C
  let ι : C →+* T := (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom
  let κ : B →+* T := Algebra.TensorProduct.includeLeftRingHom (R := A) (B := C)
  let K := J.map ι
  have hK : K = I.map (algebraMap A T) := by
    dsimp only [K, J]
    rw [Ideal.map_map]
    congr 1
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap).symm
  let q := Ideal.Quotient.mk K
  let δ := Ideal.quotientMap K ι Ideal.le_comap_map
  let y₁ := κ y
  let x := g.eval₂ ι y₁
  let z := h.eval₂ ι y₁
  have heval (p : Polynomial C) : q (p.eval₂ ι y₁) =
      (p.map (Ideal.Quotient.mk J)).eval₂ δ (q y₁) := by
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
    rfl
  have hg' : g.map (Ideal.Quotient.mk J) = Polynomial.X ^ d := by simpa using hg
  have hh' : h.map (Ideal.Quotient.mk J) = (Polynomial.X - 1) ^ d := by simpa using hh
  have hx : q x = q y₁ := by
    rw [heval, hg']
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    have hid : IsIdempotentElem (q y₁) := by
      change IsIdempotentElem (Ideal.Quotient.mk K
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (B := C) y))
      rw [hK, ← hβ₁ y, hy]
      exact hebar.map β₁.toRingHom
    exact hid.pow_eq (by omega)
  have hxz : x * z = 0 := by
    change (Polynomial.eval₂RingHom ι y₁) g * (Polynomial.eval₂RingHom ι y₁) h = 0
    rw [← map_mul, ← hfactor]
    change (f.map φ).eval₂ ι y₁ = 0
    rw [Polynomial.eval₂_map]
    have hcomp : ι.comp φ = κ.comp (algebraMap A B) :=
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
    rw [hcomp, ← Polynomial.hom_eval₂]
    simpa [Polynomial.aeval_def] using congrArg κ hfy
  have hcop₁ : IsCoprime (q x) (q z) := by
    rw [heval, heval, hg', hh']
    have hc : IsCoprime (Polynomial.X : Polynomial (C ⧸ J)) (Polynomial.X - 1) := by
      refine ⟨1, -1, ?_⟩
      ring
    exact (hc.pow (m := d) (n := d)).map (Polynomial.eval₂RingHom δ (q y₁))
  obtain ⟨D, instD, ψ, hψ, hbij₂, hcop₂⟩ :=
    exists_etale_isCoprime_tensor_of_isCoprime_quotient J x z hcop₁
  let : CommRing D := instD
  let : Algebra A D := (ψ.comp φ).toAlgebra
  let ψA : C →ₐ[A] D := { ψ with commutes' := fun _ => rfl }
  let m := Algebra.TensorProduct.map (AlgHom.id A B) ψA
  let T₂ := TensorProduct A B D
  let K₂ := I.map (algebraMap A T₂)
  let q₂ := Ideal.Quotient.mk K₂
  obtain ⟨u, v, huv⟩ := hcop₂
  let e := u * m x
  have hmzero : m x * m z = 0 := by rw [← map_mul, hxz, map_zero]
  have he : IsIdempotentElem e := by
    change (u * m x) * (u * m x) = u * m x
    have hz : (u * m x) * (v * m z) = 0 := by
      calc
        _ = (u * v) * (m x * m z) := by ring
        _ = 0 := by rw [hmzero, mul_zero]
    calc
      _ = (u * m x) * (u * m x + v * m z) := by rw [mul_add, hz, add_zero]
      _ = u * m x := by rw [huv, mul_one]
  let α₂ := RingEquiv.ofBijective (Ideal.quotientMap (J.map ψ) ψ
    Ideal.le_comap_map) hbij₂
  have hJ : J.map ψ = I.map (ψ.comp φ) := Ideal.map_map _ _
  let α := α₁.trans (α₂.trans (Ideal.quotEquivOfEq hJ))
  have hα : ∀ a : A, α (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk _ (algebraMap A D a) := by
    intro a
    rfl
  obtain ⟨β, hβ⟩ := tensor_quotient_equiv (B := B) (C := D) I α hα
  have hKm : K ≤ K₂.comap m.toRingHom := by
    rw [hK]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change m (algebraMap A T a) ∈ K₂
    rw [m.commutes]
    exact Ideal.mem_map_of_mem _ ha
  let δ₂ := Ideal.quotientMap K₂ m.toRingHom hKm
  have hx₂ : q₂ (m x) = β ebar := by
    have hmx := congrArg δ₂ hx
    change q₂ (m x) = q₂ (m y₁) at hmx
    rw [hmx, ← hy, hβ]
    change q₂ (m (y ⊗ₜ[A] (1 : C))) = _
    rw [Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.id_apply, map_one]
    rfl
  have hid₂ : IsIdempotentElem (β ebar) := hebar.map β.toRingHom
  have hemod : q₂ e = β ebar := by
    have hzero : (β ebar) * q₂ (m z) = 0 := by
      rw [← hx₂, ← map_mul, hmzero, map_zero]
    have hbez := congrArg q₂ huv
    simp only [map_add, map_mul, map_one] at hbez
    rw [hx₂] at hbez
    calc
      q₂ e = q₂ u * β ebar := by rw [map_mul, hx₂]
      _ = (q₂ u * β ebar + q₂ v * q₂ (m z)) * β ebar := by
        rw [add_mul, mul_assoc, hid₂.eq]
        simp [mul_assoc, mul_comm (q₂ (m z)) (β ebar), hzero]
      _ = β ebar := by rw [hbez, one_mul]
  have hfinal : Etale (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    have : Etale (Spec.map (CommRingCat.ofHom φ)) := hφ
    have : Etale (Spec.map (CommRingCat.ofHom ψ)) := hψ
    change Etale (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ))
    rw [Spec.map_comp]
    infer_instance
  refine ⟨CommRingCat.of D, CommRingCat.ofHom (ψ.comp φ), hfinal, α, hα,
    e, he, β, hβ, hemod.symm⟩

end AlgebraicGeometry
