/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Ring maps which are isomorphisms modulo powers of an ideal

Let `f : A → B` be a ring map and `I ⊆ A` an ideal. If all maps `A / Iⁿ → B / IⁿB` are
bijective, then `f` induces a ring isomorphism of adic completions `Â_I ≃ B̂_{IB}` compatible
with the completion maps (Stacks, Lemma 0AGV). For flat `f` with `A / I → B / IB` bijective,
the bijectivity of all `A / Iⁿ → B / IⁿB` (Stacks, proof of Lemma 0AGU) is
`RingHom.bijective_quotientMap_pow_of_flat` in
`WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat`.

We also construct the ring map `AdicCompletion.mapRingHom f I : Â_I → B̂_{IB}` induced by `f`.

## Main results

- `RingHom.injective_of_flat_of_surjective_of_le_nilpotent`
- `AdicCompletion.mapRingHom`
- `AdicCompletion.exists_ringEquiv_of_bijective_quotientMap`

## References

- Stacks Project, Lemma 15.11.8, <https://stacks.math.columbia.edu/tag/0AGU>
- Stacks Project, Lemma 15.11.9, <https://stacks.math.columbia.edu/tag/0AGV>
-/

@[expose] public section

open Ideal

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A flat surjective ring map whose kernel is contained in a nilpotent ideal is injective. -/
theorem RingHom.injective_of_flat_of_surjective_of_le_nilpotent {R S : Type*} [CommRing R]
    [CommRing S] (g : R →+* S) (hg : g.Flat) (hs : Function.Surjective g) {K : Ideal R}
    (hK : RingHom.ker g ≤ K) {n : ℕ} (hn : K ^ (n + 1) = ⊥) : Function.Injective g := by
  let _ := g.toAlgebra
  have : Module.Flat R S := hg
  have : (RingHom.ker g).Pure := by
    let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hs
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have hid := Ideal.isIdempotentElem_of_pure (RingHom.ker g)
  rw [RingHom.injective_iff_ker_eq_bot, ← hid.pow_succ_eq n, ← le_bot_iff, ← hn]
  exact Ideal.pow_right_mono hK _

/-- If `B = A + IB` (as `A`-modules), then `B = A + IⁿB` for every `n`. -/
theorem Ideal.range_sup_pow_smul_top_eq_top [Algebra A B] (I : Ideal A)
    (h : LinearMap.range (Algebra.linearMap A B) ⊔ I • ⊤ = ⊤) (n : ℕ) :
    LinearMap.range (Algebra.linearMap A B) ⊔ I ^ n • ⊤ = ⊤ := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
  | succ n ih =>
    have key : I ^ n • (⊤ : Submodule A B) ≤
        LinearMap.range (Algebra.linearMap A B) ⊔ I ^ (n + 1) • ⊤ := calc
      I ^ n • (⊤ : Submodule A B)
        = I ^ n • (LinearMap.range (Algebra.linearMap A B) ⊔ I • ⊤) := by rw [h]
      _ = I ^ n • LinearMap.range (Algebra.linearMap A B) ⊔ I ^ (n + 1) • ⊤ := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
      _ ≤ _ := sup_le_sup_right Submodule.smul_le_right _
    refine top_le_iff.mp ?_
    calc ⊤ = LinearMap.range (Algebra.linearMap A B) ⊔ I ^ n • ⊤ := ih.symm
      _ ≤ _ := sup_le le_sup_left key

namespace AdicCompletion

/-- The transition maps `A / Iⁿ → A / Iᵐ` are compatible with evaluation of the completion. -/
theorem factorPow_evalₐ (I : Ideal A) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hle r

lemma le_comap_pow_map (f : A →+* B) (I : Ideal A) (n : ℕ) :
    I ^ n ≤ ((I.map f) ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]

/-- The ring map `Â_I → B̂_{IB}` between adic completions induced by a ring map `f : A → B`. -/
noncomputable def mapRingHom (f : A →+* B) (I : Ideal A) :
    AdicCompletion I A →+* AdicCompletion (I.map f) B :=
  liftRingHom (I.map f)
    (fun n ↦ (Ideal.quotientMap _ f (le_comap_pow_map f I n)).comp (evalₐ I n).toRingHom)
    (fun {m n} hmn ↦ by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← factorPow_evalₐ I hmn x]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      rw [← ha]
      simp)

@[simp]
theorem evalₐ_mapRingHom (f : A →+* B) (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) :
    evalₐ (I.map f) n (mapRingHom f I x) =
      Ideal.quotientMap _ f (le_comap_pow_map f I n) (evalₐ I n x) := by
  simp only [mapRingHom]; rw [evalₐ_liftRingHom]; rfl

theorem mapRingHom_algebraMap (f : A →+* B) (I : Ideal A) (a : A) :
    mapRingHom f I (algebraMap A _ a) = algebraMap B _ (f a) := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_mapRingHom, algebraMap_apply, algebraMap_apply, evalₐ_of, evalₐ_of,
    Ideal.quotientMap_mk]
  simp

/-- Let `f : A → B` be a ring map and `I ⊆ A` an ideal such that `A / Iⁿ → B / IⁿB` is bijective
for every `n ≥ 1`. Then there is a ring isomorphism `θ : Â_I ≃ B̂_{IB}` of adic completions with
`θ(x)ₙ = f(a) mod (IB)ⁿ` whenever `xₙ = a mod Iⁿ`, and `θ⁻¹ ∘ c_B ∘ f = c_A`.
(blueprint: `lem-weil-pbc-henselization-completion-data`) -/
theorem exists_ringEquiv_of_bijective_quotientMap (f : A →+* B) (I : Ideal A)
    (hq : ∀ n, 1 ≤ n → Function.Bijective (Ideal.quotientMap ((I ^ n).map f) f le_comap_map)) :
    ∃ θ : AdicCompletion I A ≃+* AdicCompletion (I.map f) B,
      (∀ (n : ℕ) (x : AdicCompletion I A) (a : A), evalₐ I n x = Ideal.Quotient.mk _ a →
        evalₐ (I.map f) n (θ x) = Ideal.Quotient.mk _ (f a)) ∧
      θ.symm.toRingHom.comp ((algebraMap B _).comp f) = algebraMap A _ := by
  set J := I.map f
  have hle (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  let q (n : ℕ) : A ⧸ I ^ n →+* B ⧸ J ^ n := Ideal.quotientMap (J ^ n) f (hle n)
  have hq_mk (n : ℕ) (a : A) : q n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) :=
    Ideal.quotientMap_mk
  have hbij (n : ℕ) : Function.Bijective (q n) := by
    obtain _ | n := n
    · have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      have : Subsingleton (B ⧸ J ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact ⟨Function.injective_of_subsingleton _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · have h : q (n + 1) = (Ideal.quotEquivOfEq (Ideal.map_pow f I (n + 1))).toRingHom.comp
          (Ideal.quotientMap ((I ^ (n + 1)).map f) f le_comap_map) := by
        ext a
        simp [q, J]
      rw [h, RingHom.coe_comp]
      exact (RingEquiv.bijective _).comp (hq (n + 1) (by omega))
  let e (n : ℕ) : A ⧸ I ^ n ≃+* B ⧸ J ^ n := RingEquiv.ofBijective (q n) (hbij n)
  have he (n : ℕ) (a : A) : e n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) :=
    hq_mk n a
  have hfac {m n : ℕ} (hmn : m ≤ n) (y : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow J hmn (e n y) = e m (Ideal.Quotient.factorPow I hmn y) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [he]
  have hfac' {m n : ℕ} (hmn : m ≤ n) (y : B ⧸ J ^ n) :
      Ideal.Quotient.factorPow I hmn ((e n).symm y) =
        (e m).symm (Ideal.Quotient.factorPow J hmn y) := by
    apply (e m).injective
    rw [← hfac, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let F : AdicCompletion I A →+* AdicCompletion J B :=
    liftRingHom J (fun n ↦ (e n).toRingHom.comp (evalₐ I n).toRingHom) (fun hmn ↦ by
      ext x
      simp [hfac, factorPow_evalₐ])
  let G : AdicCompletion J B →+* AdicCompletion I A :=
    liftRingHom I (fun n ↦ (e n).symm.toRingHom.comp (evalₐ J n).toRingHom) (fun hmn ↦ by
      ext x
      simp [hfac', factorPow_evalₐ])
  have hF (n : ℕ) (x) : evalₐ J n (F x) = e n (evalₐ I n x) := by
    simp only [F]; rw [evalₐ_liftRingHom]; rfl
  have hG (n : ℕ) (y) : evalₐ I n (G y) = (e n).symm (evalₐ J n y) := by
    simp only [G]; rw [evalₐ_liftRingHom]; rfl
  let θ : AdicCompletion I A ≃+* AdicCompletion J B :=
    { F with
      invFun := G
      left_inv := fun x ↦ ext_evalₐ fun n ↦ by simp [hF, hG]
      right_inv := fun y ↦ ext_evalₐ fun n ↦ by simp [hF, hG] }
  refine ⟨θ, fun n x a hx ↦ ?_, ?_⟩
  · change evalₐ J n (F x) = _
    rw [hF, hx, he]
  · refine RingHom.ext fun a ↦ ext_evalₐ fun n ↦ ?_
    change evalₐ I n (G _) = _
    rw [hG, RingHom.comp_apply, algebraMap_apply, algebraMap_apply, evalₐ_of, evalₐ_of]
    apply (e n).injective
    simp [he]

end AdicCompletion
