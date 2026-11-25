/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Completion comparison from quotient isomorphisms

Source: Stacks Project, More on Algebra, Tag 0AGV, first paragraph of the proof.
(blueprint: lem-weil-pbc-henselization-completion-data).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- Compatible quotient isomorphisms induce the canonical completion isomorphism.
Source: Stacks Project, More on Algebra, Tag 0AGV, first paragraph of the proof.
(blueprint: lem-weil-pbc-henselization-completion-data).

Proof: For each positive n the hypothesis gives the ring isomorphism
A/I^n → B/(I^n B). Ideal.map_pow identifies I^n B with (IB)^n. For n = 0
both quotients are zero rings, so the same conclusion holds. The quotient maps
commute with the transition maps because they all send a representative a to f(a).
Their inverses therefore also commute with the transition maps. Apply the inverse
limit construction to the maps and their inverses, obtaining mutually inverse ring
maps θ and θ⁻¹. Evaluation on any coordinate is the corresponding quotient map;
this proves the displayed compatibility with representatives. Applying that identity
to the image of a in the completion shows that θ sends the completion image of a
to that of f(a). Applying θ⁻¹ gives the displayed equality of composite ring maps. -/
theorem pair_henselization_completion_data
    (A : Type u) [CommRing A] (B : Type v) [CommRing B]
    (I : Ideal A) (f : A →+* B)
    (hf : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map)) :
    ∃ θ : AdicCompletion I A ≃+* AdicCompletion (I.map f) B,
      (∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
        AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
        AdicCompletion.evalₐ (I.map f) n (θ x) =
          Ideal.Quotient.mk ((I.map f) ^ n) (f a)) ∧
      (θ.symm.toRingHom.comp (algebraMap B (AdicCompletion (I.map f) B))).comp f =
        algebraMap A (AdicCompletion I A) := by
  classical
  let J := I.map f
  let q (n : ℕ) : A ⧸ I ^ n →+* B ⧸ J ^ n :=
    Ideal.quotientMap (J ^ n) f (by
      dsimp [J]
      rw [← Ideal.map_pow]
      exact Ideal.le_comap_map)
  have hq (n : ℕ) : Function.Bijective (q n) := by
    cases n with
    | zero =>
      have hA : Subsingleton (A ⧸ I ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      have hB : Subsingleton (B ⧸ J ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    | succ n =>
      have htransfer (K : Ideal B) (hK : K = (I ^ (n + 1)).map f)
          (hle : I ^ (n + 1) ≤ K.comap f) :
          Function.Bijective (Ideal.quotientMap K f hle) := by
        subst K
        exact hf (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      exact htransfer (J ^ (n + 1)) (Ideal.map_pow f I (n + 1)).symm _
  let e (n : ℕ) := RingEquiv.ofBijective (q n) (hq n)
  have hqmk (n : ℕ) (a : A) : e n (Ideal.Quotient.mk (I ^ n) a) =
      Ideal.Quotient.mk (J ^ n) (f a) := rfl
  have htrans {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow J hmn (e n x) =
        e m (Ideal.Quotient.factorPow I hmn x) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [hqmk, Ideal.Quotient.factor_mk]
  have hevalA {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I A) :
      Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
        AdicCompletion.evalₐ I m x := by
    obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I hmn s
  have hevalB {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion J B) :
      Ideal.Quotient.factorPow J hmn (AdicCompletion.evalₐ J n x) =
        AdicCompletion.evalₐ J m x := by
    obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J B x
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk J hmn s
  let g (n : ℕ) := (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom
  have hg {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow J hmn).comp (g n) = g m := by
    ext x
    exact (htrans hmn _).trans (congrArg (e m) (hevalA hmn x))
  let gi (n : ℕ) := (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom
  have hgi {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow I hmn).comp (gi n) = gi m := by
    ext x
    change Ideal.Quotient.factorPow I hmn
      ((e n).symm (AdicCompletion.evalₐ J n x)) =
        (e m).symm (AdicCompletion.evalₐ J m x)
    apply (e m).injective
    rw [← htrans hmn, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hevalB hmn x
  let F := AdicCompletion.liftRingHom J g hg
  let G := AdicCompletion.liftRingHom I gi hgi
  have hF (n : ℕ) (x : AdicCompletion I A) :
      AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    AdicCompletion.evalₐ_liftRingHom J g hg n x
  have hG (n : ℕ) (x : AdicCompletion J B) :
      AdicCompletion.evalₐ I n (G x) = (e n).symm (AdicCompletion.evalₐ J n x) :=
    AdicCompletion.evalₐ_liftRingHom I gi hgi n x
  let θ : AdicCompletion I A ≃+* AdicCompletion J B :=
    { F with
      invFun := G
      left_inv := fun x ↦ AdicCompletion.ext_evalₐ (fun n ↦ by
        change AdicCompletion.evalₐ I n (G (F x)) = AdicCompletion.evalₐ I n x
        rw [hG, hF, RingEquiv.symm_apply_apply])
      right_inv := fun x ↦ AdicCompletion.ext_evalₐ (fun n ↦ by
        change AdicCompletion.evalₐ J n (F (G x)) = AdicCompletion.evalₐ J n x
        rw [hF, hG, RingEquiv.apply_symm_apply]) }
  refine ⟨θ, ?_, ?_⟩
  · intro n x a hx
    exact (hF n x).trans (hx ▸ hqmk n a)
  · apply RingHom.ext
    intro a
    apply θ.injective
    change θ (θ.symm (algebraMap B _ (f a))) = θ (algebraMap A _ a)
    rw [RingEquiv.apply_symm_apply]
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ J n (algebraMap B _ (f a)) =
      AdicCompletion.evalₐ J n (F (algebraMap A _ a))
    rw [hF]
    simp only [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, hqmk,
      Algebra.algebraMap_self, RingHom.id_apply]


end RingTheory
