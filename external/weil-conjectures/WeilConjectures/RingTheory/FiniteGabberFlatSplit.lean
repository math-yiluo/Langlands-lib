/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.RingTheory.LiftIdempotentUpstairs
import WeilConjectures.RingTheory.FiniteTensorFactorLocalization
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.RingHom.Etale

/-!
# The flat split neighbourhood in Gabber's finite-algebra argument

Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`,
from lifting the idempotent through choosing the coefficient in the first factor.
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- A flat neighbourhood preserving the quotient splits the finite algebra into two
factors. The first factor admits a scalar lift of `b - 1`, and `b` in the second factor
belongs to the extended ideal. The kernels of the two factor projections have zero
intersection. No polynomial relation or faithful flatness is asserted here.
Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`.
(blueprint: lem-weil-pbc-gabber-flat-split-neighbourhood)

Proof:
1. Finiteness makes B integral. Apply 07M4 to the idempotent represented by b
   modulo IB. This gives an etale A-algebra A' preserving A/I, and an idempotent
   in B tensor_A A' reducing to (1,0).
2. The idempotent decomposes the tensor algebra into its quotient by (1-e') and
   its quotient by e'. Both factors are finite over A'. Their reductions are B1
   and B2, and the image of b reduces respectively to 1 and 0.
3. The cokernel of A' -> the first factor is finite and equals IA' times itself,
   because A/I -> B1 is surjective. Nakayama 00DV gives g with g-1 in IA' which
   annihilates this cokernel. Localize A' and both factors at g to obtain C.
4. C is flat over A: etale algebras and localizations are flat, and flatness
   composes. Since g reduces to 1, A/I -> C/IC is still an isomorphism, agreeing
   with the structure map on representatives.
5. The first structure map is now surjective: y/g^n is the image of a/g^(n+1)
   whenever gy is the image of a. Its extended ideal is therefore the image of
   IC, so lift the first component of b-1 to a in IC. Let K and L be the kernels
   of the two factor projections from C tensor_A B. Their intersection is zero.
   The first equality says b-1-a belongs to K. The second component of b is in
   IC times that factor, equivalently b belongs to L plus the extended ideal.
   These conclusions also hold when either factor is the zero ring. -/
theorem exists_flat_split_gabber_neighbourhood
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (C : CommRingCat.{u}) (f : A →+* C),
      letI : Algebra A C := f.toAlgebra
      Module.Flat A C ∧
        ∃ α : A ⧸ I ≃+* C ⧸ I.map (algebraMap A C),
          (∀ a : A, α (Ideal.Quotient.mk I a) =
            Ideal.Quotient.mk _ (algebraMap A C a)) ∧
          ∃ K L : Ideal (TensorProduct A C B), K ⊓ L = ⊥ ∧
            ∃ a : C, a ∈ I.map (algebraMap A C) ∧
              ((1 : C) ⊗ₜ[A] b) - 1 - algebraMap C (TensorProduct A C B) a ∈ K ∧
              ((1 : C) ⊗ₜ[A] b) ∈ L ⊔
                (I.map (algebraMap A C)).map (algebraMap C (TensorProduct A C B)) := by
  classical
  let qB := Ideal.Quotient.mk (I.map (algebraMap A B))
  have heb : IsIdempotentElem (qB b) := by
    apply e.injective
    rw [map_mul]
    change e (qB b) * e (qB b) = e (qB b)
    rw [show e (qB b) = (1, 0) from hb]
    simp
  obtain ⟨D, g, hg, αD, hαD, ε, hε, β, hβ, hεmod⟩ :=
    AlgebraicGeometry.exists_etale_lift_isIdempotentElem I (qB b) heb
  let : Algebra A D := g.hom.toAlgebra
  let T := TensorProduct A D B
  let c := Algebra.TensorProduct.comm A B D
  let εD : T := c ε
  let H := I.map (algebraMap A T)
  let J := I.map (algebraMap A D)
  have hH : H = (I.map (algebraMap A (TensorProduct A B D))).map c.toRingEquiv := by
    change H = (I.map (algebraMap A (TensorProduct A B D))).map c.toRingHom
    dsimp only [H]
    rw [Ideal.map_map]
    congr 1
    ext a
    exact (c.commutes a).symm
  let δ := Ideal.quotientEquiv _ H c.toRingEquiv hH
  let βD := β.trans δ
  have hβD (y : B) : βD (qB y) =
      Ideal.Quotient.mk H ((1 : D) ⊗ₜ[A] y) := by
    change δ (β (qB y)) = _
    rw [hβ, Ideal.quotientEquiv_mk]
    change Ideal.Quotient.mk H (Algebra.TensorProduct.comm A B D (y ⊗ₜ[A] 1)) = _
    rw [Algebra.TensorProduct.comm_tmul]
  have hεD : IsIdempotentElem εD := hε.map c.toRingHom
  have hεDmod : Ideal.Quotient.mk H εD = βD (qB b) := by
    change Ideal.Quotient.mk H (c ε) = δ (β (qB b))
    rw [hεmod, Ideal.quotientEquiv_mk]
    rfl
  let ρ := βD.symm.trans e
  let q := Ideal.Quotient.mk H
  have hρε : ρ (q εD) = (1, 0) := by
    rw [hεDmod]
    simpa only [ρ, RingEquiv.trans_apply, RingEquiv.symm_apply_apply] using hb
  have hρa (a : A) : ρ (q (algebraMap A T a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)) := by
    have htm : ((1 : D) ⊗ₜ[A] algebraMap A B a) = algebraMap A T a := by
      exact (Algebra.TensorProduct.includeRight (R := A) (A := D) (B := B)).commutes a
    rw [← htm, ← hβD]
    simpa only [ρ, RingEquiv.trans_apply, RingEquiv.symm_apply_apply] using he a
  have hfactor : ∀ t : T, ∃ d : D,
      t - algebraMap D T d ∈ Ideal.span {1 - εD} ⊔ J.map (algebraMap D T) := by
    intro t
    obtain ⟨a₀, ha₀⟩ := h₁ (ρ (q t)).1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a₀
    let d := algebraMap A D a
    let r := t - algebraMap D T d
    have hr₁ : (ρ (q r)).1 = 0 := by
      dsimp only [r, d]
      rw [← IsScalarTower.algebraMap_apply A D T, map_sub, map_sub, hρa]
      exact sub_eq_zero.mpr ha₀.symm
    have hrq : q ((1 - εD) * r) = q r := by
      apply ρ.injective
      rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one, hρε]
      apply Prod.ext
      · simp [hr₁]
      · simp
    have hrH : r - (1 - εD) * r ∈ H := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hrq, sub_self]
    have hHJ : H = J.map (algebraMap D T) := by
      dsimp only [H, J]
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A D T]
    refine ⟨d, ?_⟩
    change r ∈ _
    rw [← hHJ]
    have hK : (1 - εD) * r ∈ Ideal.span {1 - εD} :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have := (Ideal.span {1 - εD} ⊔ H).add_mem
      (Ideal.mem_sup_left hK) (Ideal.mem_sup_right hrH)
    simpa only [add_sub_cancel] using this
  obtain ⟨C, ψ, hψ, hbij, hsurj⟩ :=
    exists_flat_tensor_factor_localization J εD hfactor
  let f := ψ.comp (algebraMap A D)
  let : Algebra A C := f.toAlgebra
  let ψA : D →ₐ[A] C := { ψ with commutes' := fun _ => rfl }
  let m := Algebra.TensorProduct.map ψA (AlgHom.id A B)
  let S := TensorProduct A C B
  let εC := m εD
  let JC := I.map (algebraMap A C)
  let HS := JC.map (algebraMap C S)
  have hJ : J.map ψ = JC := by
    dsimp only [J, JC]
    rw [Ideal.map_map]
    rfl
  let αC := RingEquiv.ofBijective (Ideal.quotientMap (J.map ψ) ψ
    Ideal.le_comap_map) hbij
  let α := αD.trans (αC.trans (Ideal.quotEquivOfEq hJ))
  have hα (a : A) : α (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk JC (algebraMap A C a) := by
    change Ideal.quotEquivOfEq hJ (αC (αD (Ideal.Quotient.mk I a))) = _
    rw [hαD]
    rfl
  have hflatD : (algebraMap A D).Flat := by
    have het : (algebraMap A D).Etale :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mp hg
    exact (RingHom.Etale.iff_flat_and_formallyUnramified.mp het).1
  have hflat : Module.Flat A C := RingHom.flat_algebraMap_iff.mp (hflatD.comp hψ)
  have hεC : IsIdempotentElem εC := hεD.map m.toRingHom
  let K : Ideal S := Ideal.span {1 - εC}
  let L : Ideal S := Ideal.span {εC}
  have hKL : K ⊓ L = ⊥ := by
    apply le_antisymm _ bot_le
    intro t ht
    have hinj := (RingHom.prod_bijective_of_isIdempotentElem hεC.one_sub hεC
      (by ring) (by simpa using hεC.one_sub_mul_self)).1
    have hzero : t = 0 := by
      apply hinj
      apply Prod.ext <;> simp only [RingHom.prod_apply, map_zero]
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr ht.1
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr ht.2
    exact hzero ▸ (Submodule.zero_mem _)
  let x : S := (1 : C) ⊗ₜ[A] b
  have hxε : x - εC ∈ HS := by
    have hD : (1 : D) ⊗ₜ[A] b - εD ∈ H := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hεDmod, hβD, sub_self]
    have hm : H.map m.toRingHom = HS := by
      dsimp only [H, HS, JC]
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
    have hmem := Ideal.mem_map_of_mem m.toRingHom hD
    rw [hm] at hmem
    rw [map_sub] at hmem
    change m ((1 : D) ⊗ₜ[A] b) - m εD ∈ HS at hmem
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hmem
    exact hmem
  have hxK : x - 1 ∈ HS ⊔ K := by
    have hK : εC - 1 ∈ K := by
      simpa only [neg_sub] using K.neg_mem (Ideal.mem_span_singleton_self (1 - εC))
    have := (HS ⊔ K).add_mem (Ideal.mem_sup_left hxε) (Ideal.mem_sup_right hK)
    simpa only [sub_add_sub_cancel] using this
  have hxL : x ∈ L ⊔ HS := by
    have := (L ⊔ HS).add_mem (Ideal.mem_sup_right hxε)
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self εC))
    simpa only [sub_add_cancel] using this
  let p := Ideal.Quotient.mk K
  have hp : p (x - 1) ∈ JC.map (algebraMap C (S ⧸ K)) := by
    have hh := Ideal.mem_quotient_iff_mem_sup.mpr hxK
    change p (x - 1) ∈ HS.map p at hh
    dsimp only [HS] at hh
    rw [Ideal.map_map] at hh
    exact hh
  obtain ⟨a, ha, hpa⟩ := Ideal.mem_map_iff_of_surjective _ hsurj |>.mp hp
  have hxKa : x - 1 - algebraMap C S a ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change p (x - 1) - algebraMap C (S ⧸ K) a = 0
    rw [← hpa, sub_self]
  exact ⟨C, f, hflat, α, hα, K, L, hKL, a, ha, hxKa, hxL⟩

end Algebra
