/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion of a quotient of a Noetherian local ring

Source: Stacks Project, Algebra, Tag 00MA, parts (2) and (3), and the proof of
Tag 00MB; the module/ring completion identification used in Tag 0325
(blueprint: lem-weil-pbc-local-completion-quotient).
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- For a surjection `φ : A →+* B`, completion at the image of the maximal ideal is
completion of `A` modulo the extended kernel. The maps `θk` are the induced surjections
on quotient rings. Their compatibility with evaluations specifies `θ` coordinatewise;
the last equation says that the quotient isomorphism is induced by this same `θ`.
Source: Stacks Project, Algebra, Tag 00MA (2), (3), Tag 00MB, and Tag 0325
(blueprint: lem-weil-pbc-local-completion-quotient).

Proof:
1. Regard `B` as an `A`-module via `φ`. Surjectivity gives `m^k B = n^k`, where
   `m` is the maximal ideal of `A` and `n = m.map φ`. Thus the module completion of `B`
   at `m` is its ring completion at `n` (def-weil-pbc-adic-completion). The quotient maps
   induced by `φ` are surjective and compatible. They define the coordinatewise ring map
   `θ`, which commutes with the canonical maps from `A` and `B`.
2. Noetherianity makes `J = ker φ` finite, and `A` and `B` are cyclic `A`-modules
   (def-weil-pbc-noetherian-ring, def-weil-finitely-generated-module).
   Apply lem-weil-pbc-completion-exact-finite-modules (00MA (2)) to `0 → J → A → B → 0`.
   This makes `θ` surjective and identifies its kernel with the image of the completion
   of `J` in the completion of `A`.
3. By lem-weil-pbc-completion-finite-module-tensor (00MA (3)), the completed `J` is
   the tensor product of the completed `A` with `J` (def-weil-module-base-change).
   Naturality identifies its image with the finite sums `Σ y_i * cA(j_i)`, exactly the
   ideal `J.map cA`. This is the image identification used in the proof of 00MB.
4. The ring homomorphism theorem gives the quotient isomorphism, sending the class of
   `x` to `θ x`. -/
theorem exists_local_completion_quotient
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A]
    (φ : A →+* B) (hφ : Function.Surjective φ) :
    let m := IsLocalRing.maximalIdeal A
    let n := m.map φ
    let Ahat := AdicCompletion m A
    let Bhat := AdicCompletion n B
    let cA := algebraMap A Ahat
    let cB := algebraMap B Bhat
    let Jhat := (RingHom.ker φ).map cA
    (∀ k : ℕ, (m ^ k).map φ = n ^ k) ∧
    ∃ θ : Ahat →+* Bhat,
      (∀ k : ℕ, ∃ θk : (A ⧸ m ^ k) →+* (B ⧸ n ^ k),
        Function.Surjective θk ∧
        θk.comp (Ideal.Quotient.mk (m ^ k)) = (Ideal.Quotient.mk (n ^ k)).comp φ ∧
        (evalₐ n k).toRingHom.comp θ = θk.comp (evalₐ m k).toRingHom) ∧
      θ.comp cA = cB.comp φ ∧
      Function.Surjective θ ∧
      RingHom.ker θ = Jhat ∧
      ∃ e : (Ahat ⧸ Jhat) ≃+* Bhat,
        ∀ x : Ahat, e (Ideal.Quotient.mk Jhat x) = θ x := by
  classical
  dsimp only
  let m := IsLocalRing.maximalIdeal A
  let n := m.map φ
  let q (k : ℕ) : (A ⧸ m ^ k) →+* (B ⧸ n ^ k) :=
    Ideal.quotientMap (n ^ k) φ (by
      dsimp [n]
      rw [← Ideal.map_pow]
      exact Ideal.le_comap_map)
  have hqmk (k : ℕ) (a : A) :
      q k (Ideal.Quotient.mk (m ^ k) a) = Ideal.Quotient.mk (n ^ k) (φ a) := rfl
  have htrans {i j : ℕ} (hij : i ≤ j) (x : A ⧸ m ^ j) :
      Ideal.Quotient.factorPow n hij (q j x) =
        q i (Ideal.Quotient.factorPow m hij x) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [hqmk, Ideal.Quotient.factor_mk]
  have heval {i j : ℕ} (hij : i ≤ j) (x : AdicCompletion m A) :
      Ideal.Quotient.factorPow m hij (evalₐ m j x) = evalₐ m i x := by
    obtain ⟨s, rfl⟩ := mk_surjective m A x
    simp only [evalₐ_mk, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk m hij s
  let g (k : ℕ) := (q k).comp (evalₐ m k).toRingHom
  have hg {i j : ℕ} (hij : i ≤ j) :
      (Ideal.Quotient.factorPow n hij).comp (g j) = g i := by
    ext x
    exact (htrans hij _).trans (congrArg (q i) (heval hij x))
  let θ := liftRingHom n g hg
  have hθ (k : ℕ) (x : AdicCompletion m A) :
      evalₐ n k (θ x) = q k (evalₐ m k x) :=
    evalₐ_liftRingHom n g hg k x
  have hc : θ.comp (algebraMap A _) = (algebraMap B _).comp φ := by
    apply RingHom.ext
    intro a
    apply ext_evalₐ
    intro k
    change evalₐ n k (θ (algebraMap A _ a)) = evalₐ n k (algebraMap B _ (φ a))
    rw [hθ]
    simp only [algebraMap_apply, evalₐ_of, hqmk, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hs : Function.Surjective θ := by
    let := φ.toAlgebra
    let f := (Algebra.ofId A B).toLinearMap
    have hp (k : ℕ) : (m ^ k • ⊤ : Submodule A B) = (n ^ k).restrictScalars A := by
      rw [Ideal.smul_top_eq_map]
      congr 1
      exact Ideal.map_pow φ m k
    intro y
    obtain ⟨b, rfl⟩ := mk_surjective n B y
    let bA : AdicCauchySequence m B := ⟨b.val, fun {i j} hij ↦ by
      rw [hp i, SModEq.restrictScalars]
      simpa using b.property hij⟩
    obtain ⟨x, hx⟩ := map_surjective m (f := f) hφ (mk m B bA)
    obtain ⟨s, rfl⟩ := mk_surjective m A x
    refine ⟨mk m A s, ?_⟩
    apply ext_evalₐ
    intro k
    rw [hθ, evalₐ_mk, hqmk, evalₐ_mk]
    have hk := congrArg (fun z : AdicCompletion m B ↦ z.val k) hx
    simp only [map_mk, mk_apply_coe, AdicCauchySequence.map_apply_coe] at hk
    have hd := (Submodule.Quotient.eq _).mp hk
    rw [hp k] at hd
    apply Ideal.Quotient.eq.mpr
    exact hd
  have hk : RingHom.ker θ = (RingHom.ker φ).map (algebraMap A _) := by
    let J := RingHom.ker φ
    let c := algebraMap A (AdicCompletion m A)
    let f : A →ₗ[A] A ⧸ J := (Ideal.Quotient.mkₐ A J).toLinearMap
    let i : J →ₗ[A] A := J.subtype
    have hfi : Function.Exact i f := by
      intro a
      change Ideal.Quotient.mk J a = 0 ↔ ∃ j : J, (j : A) = a
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact ⟨fun ha ↦ ⟨⟨a, ha⟩, rfl⟩, fun ⟨j, hj⟩ ↦ hj ▸ j.property⟩
    have he := map_exact (I := m) (f := i) (g := f)
      Subtype.val_injective hfi Ideal.Quotient.mk_surjective
    apply le_antisymm
    · intro x hx
      have hz : map m f x = 0 := by
        obtain ⟨s, rfl⟩ := mk_surjective m A x
        ext k
        simp only [map_mk, mk_apply_coe, AdicCauchySequence.map_apply_coe]
        have hz := congrArg (evalₐ n k) (RingHom.mem_ker.mp hx)
        rw [hθ, evalₐ_mk, hqmk, _root_.map_zero] at hz
        have hm : φ (s k) ∈ (m ^ k).map φ := by
          rw [Ideal.map_pow]
          exact Ideal.Quotient.eq_zero_iff_mem.mp hz
        obtain ⟨a, ha, heq⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hm
        have hj : s k - a ∈ J := by
          change φ (s k - a) = 0
          rw [map_sub, heq, sub_self]
        have hfa : f (s k) = f a := Ideal.Quotient.eq.mpr hj
        rw [hfa]
        change Submodule.Quotient.mk (f a) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        have hmem : f a ∈ Submodule.map f (m ^ k • ⊤ : Submodule A A) :=
          ⟨a, by simpa using ha, rfl⟩
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr (show Function.Surjective f from
            Ideal.Quotient.mk_surjective)] at hmem
        exact hmem
      obtain ⟨y, hy⟩ := (he x).mp hz
      obtain ⟨t, ht⟩ := ofTensorProduct_surjective_of_finite m J y
      rw [← hy, ← ht]
      clear ht hy hx he hfi
      induction t using TensorProduct.inductionOn with
      | tmul a j =>
        rw [ofTensorProduct_tmul, map_smul, map_of]
        change a * c j ∈ J.map c
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem c j.property)
      | add a b ha hb =>
        simpa only [map_add] using (J.map c).add_mem ha hb
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change θ (c a) = 0
      have h := RingHom.congr_fun hc a
      change θ (c a) = algebraMap B _ (φ a) at h
      rw [h, RingHom.mem_ker.mp ha, _root_.map_zero]
  refine ⟨fun k ↦ Ideal.map_pow φ m k, θ, ?_, hc, hs, hk, ?_⟩
  · intro k
    refine ⟨q k, Ideal.quotientMap_surjective hφ, ?_, ?_⟩
    · ext a
      exact hqmk k a
    · ext x
      exact hθ k x
  · refine ⟨(Ideal.quotientEquivAlgOfEq A hk.symm).toRingEquiv.trans
      (θ.quotientKerEquivOfSurjective hs), ?_⟩
    intro x
    exact (congrArg (θ.quotientKerEquivOfSurjective hs)
      (Ideal.quotientEquivAlgOfEq_mk A hk.symm x)).trans
      (RingHom.quotientKerEquivOfSurjective_apply_mk hs x)

end AdicCompletion
