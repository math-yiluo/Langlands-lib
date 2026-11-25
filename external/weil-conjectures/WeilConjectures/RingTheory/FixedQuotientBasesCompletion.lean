/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Completion comparison from fixed quotient bases

Source: Stacks Project, Tag 06LJ(c), using the fixed lifts of Tag 07QM(4).
(blueprint: lem-sc-fixed-quotient-bases-completion).
-/

@[expose] public section

universe u v w

namespace AdicCompletion

private theorem ker_coefficients
    {A : Type u} [CommRing A] (I : Ideal A) (X : Type v) :
    LinearMap.ker (Finsupp.mapRange.linearMap (α := X) I.mkQ) =
      I • (⊤ : Submodule A (X →₀ A)) := by
  rw [Finsupp.ker_mapRange, Submodule.ker_mkQ]
  ext f
  constructor
  · intro hf
    rw [← Finsupp.sum_single f]
    apply Submodule.sum_mem
    intro i _
    have hi : f i ∈ I := hf i
    have h := Submodule.smul_mem_smul hi
      (Submodule.mem_top (x := Finsupp.single i (1 : A)))
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using h
  · intro hf
    refine Submodule.smul_induction_on hf ?_ ?_
    · intro r hr g _ i
      exact I.mul_mem_right (g i) hr
    · intro g h hg hh i
      exact I.add_mem (hg i) (hh i)

private noncomputable def coefficientsEquiv
    {A : Type u} [CommRing A] (I : Ideal A) (X : Type v) :
    ((X →₀ A) ⧸ (I • (⊤ : Submodule A (X →₀ A)))) ≃ₗ[A] (X →₀ A ⧸ I) :=
  (Submodule.quotEquivOfEq _ _ (ker_coefficients I X).symm).trans
    ((Finsupp.mapRange.linearMap (α := X) I.mkQ).quotKerEquivOfSurjective
      (Finsupp.mapRange_surjective _ (map_zero I.mkQ) I.mkQ_surjective))

private theorem coefficientsEquiv_mk
    {A : Type u} [CommRing A] (I : Ideal A) (X : Type v) (f : X →₀ A) :
    coefficientsEquiv I X (Submodule.Quotient.mk f) =
      f.mapRange (Ideal.Quotient.mk I) (map_zero (Ideal.Quotient.mk I)) := by
  simp [coefficientsEquiv]
  rfl


private def ringCoordinates
    {A : Type u} {C : Type w} [CommRing A] [CommRing C] [Algebra A C]
    (J : Ideal C) (n : ℕ) :
    (C ⧸ (J ^ n • ⊤ : Ideal C)) ≃ₗ[A] C ⧸ J ^ n :=
  (Ideal.quotientEquivAlgOfEq C (by simp)).toLinearEquiv.restrictScalars A

private theorem ringCoordinates_mk
    {A : Type u} {C : Type w} [CommRing A] [CommRing C] [Algebra A C]
    (J : Ideal C) (n : ℕ) (c : C) :
    ringCoordinates (A := A) J n (Submodule.Quotient.mk c) =
      Ideal.Quotient.mk (J ^ n) c := rfl

/-- Fixed lifts giving quotient bases induce an equivalence of completions.
Source: Stacks Project, Tag 06LJ(c), completion identification from Tag 07QM(4).
(blueprint: lem-sc-fixed-quotient-bases-completion).

Proof: The quotient of the free module by I^n is the finitely supported module
of coefficients in A/I^n, by the kernel and surjectivity of coefficient reduction.
Compose this equivalence with the given bases. On representatives these maps all
send f to the class of the same sum of f i times x i; hence they commute with
transition maps. The zero-th quotients are zero modules. Apply the equivalences
coordinatewise to compatible families, and their inverses coordinatewise for the
inverse map. Compatibility for the inverses follows by injectivity of each forward
map. The inverse identities and linearity are coordinatewise identities. Evaluation
at n then gives the asserted formula for every representative f of that coordinate.
-/
theorem equiv_of_fixed_quotient_bases
    {A : Type u} {C : Type w} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) (X : Type v) (x : X → C)
    (e : ∀ (r : ℕ), 1 ≤ r → (X →₀ A ⧸ I ^ r) ≃ₗ[A]
      C ⧸ (I.map (algebraMap A C)) ^ r)
    (he : ∀ (r : ℕ) (hr : 1 ≤ r) (i : X),
      e r hr (Finsupp.single i 1) =
        Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ r) (x i)) :
    ∃ E : AdicCompletion I (X →₀ A) ≃ₗ[A]
        AdicCompletion (I.map (algebraMap A C)) C,
      ∀ (r : ℕ) (hr : 1 ≤ r) (z : AdicCompletion I (X →₀ A)) (f : X →₀ A),
        AdicCompletion.eval I (X →₀ A) r z =
          (I ^ r • (⊤ : Submodule A (X →₀ A))).mkQ f →
        AdicCompletion.evalₐ (I.map (algebraMap A C)) r (E z) =
          e r hr (f.mapRange (Ideal.Quotient.mk (I ^ r))
            (map_zero (Ideal.Quotient.mk (I ^ r)))) := by
  classical
  let J := I.map (algebraMap A C)
  let F := X →₀ A
  let phi : F →ₗ[A] C := Finsupp.linearCombination A x
  have hphi (n : ℕ) (hn : 1 ≤ n) (f : F) :
      e n hn ((coefficientsEquiv (I ^ n) X) (Submodule.Quotient.mk f)) =
        Ideal.Quotient.mk (J ^ n) (phi f) := by
    have hmaps : (e n hn).toLinearMap.comp
        (Finsupp.mapRange.linearMap (α := X) (I ^ n).mkQ) =
        ((Ideal.Quotient.mkₐ A (J ^ n)).toLinearMap).comp phi := by
      ext i
      simpa [phi, LinearMap.comp_apply, J] using he n hn i
    exact LinearMap.congr_fun hmaps f
  let q : ∀ n : ℕ, (F ⧸ (I ^ n • (⊤ : Submodule A F))) ≃ₗ[A]
      C ⧸ (J ^ n • ⊤ : Ideal C) := fun n => by
    cases n with
    | zero =>
      have hF : Subsingleton (F ⧸ (I ^ 0 • (⊤ : Submodule A F))) := by
        simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        infer_instance
      have hC : Subsingleton (C ⧸ (J ^ 0 • ⊤ : Ideal C)) := by
        simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        infer_instance
      exact LinearEquiv.ofSubsingleton _ _
    | succ n =>
      exact ((coefficientsEquiv (I ^ (n + 1)) X).trans
        (e (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))).trans
        (ringCoordinates (A := A) J (n + 1)).symm
  have hq (n : ℕ) (f : F) :
      q n (Submodule.Quotient.mk f) = Submodule.Quotient.mk (phi f) := by
    cases n with
    | zero =>
      have : Subsingleton (C ⧸ (J ^ 0 • ⊤ : Ideal C)) := by
        simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        infer_instance
      exact Subsingleton.elim _ _
    | succ n =>
      apply (ringCoordinates (A := A) J (n + 1)).injective
      change (ringCoordinates (A := A) J (n + 1))
        ((ringCoordinates (A := A) J (n + 1)).symm
          (e (n + 1) _ ((coefficientsEquiv (I ^ (n + 1)) X)
            (Submodule.Quotient.mk f)))) = _
      rw [LinearEquiv.apply_symm_apply, ringCoordinates_mk]
      exact hphi (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) f
  have hcompat {m n : ℕ} (hmn : m ≤ n)
      (f : F ⧸ (I ^ n • (⊤ : Submodule A F))) :
      transitionMap J C hmn (q n f) = q m (transitionMap I F hmn f) := by
    induction f using Submodule.Quotient.induction_on with
    | _ f =>
      change transitionMap J C hmn (q n (Submodule.Quotient.mk f)) =
        q m (Submodule.Quotient.mk f)
      rw [hq, hq]
      rfl
  let E : AdicCompletion I F ≃ₗ[A] AdicCompletion J C :=
    { toFun := fun z => ⟨fun n => q n (z.val n), by
        intro m n hmn
        rw [hcompat, z.property hmn]⟩
      invFun := fun z => ⟨fun n => (q n).symm (z.val n), by
        intro m n hmn
        apply (q m).injective
        rw [← hcompat]
        simp only [LinearEquiv.apply_symm_apply, z.property hmn]⟩
      left_inv := fun z => by ext n; exact LinearEquiv.symm_apply_apply _ _
      right_inv := fun z => by ext n; exact LinearEquiv.apply_symm_apply _ _
      map_add' := fun z t => by ext n; exact map_add _ _ _
      map_smul' := fun a z => by ext n; exact (q n).map_smul a (z.val n) }
  refine ⟨E, ?_⟩
  intro r hr z f hf
  change ringCoordinates (A := A) J r (q r (z.val r)) = _
  change z.val r = Submodule.Quotient.mk f at hf
  rw [hf, hq, ringCoordinates_mk]
  exact (hphi r hr f).symm

end AdicCompletion
