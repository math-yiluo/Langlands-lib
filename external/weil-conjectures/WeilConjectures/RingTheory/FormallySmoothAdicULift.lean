/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Universe transport for adic formal smoothness

Source: Stacks Project, More on Algebra, Definition 07EB and Definition 07NI;
universe bookkeeping in the proof of Lemma 07NR and Remark 07NS.
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Raising the universe of an algebra preserves its adic lifting property.
Source: Stacks Project, More on Algebra, Definitions 07EB and 07NI, applied to
Lemma 07NR and Remark 07NS.
(blueprint: lem-weil-pbc-formally-smooth-adic-ulift)

Proof (universe bookkeeping written by T2): Write e : ULift S ≃ₐ[R] S. Given
J squared equal to zero in a test algebra D and g : ULift S →ₐ[R] D/J, choose a
representative r(s) of g(e.symm s) for every s in S. Evaluate the polynomial
algebra R[X_s | s in S] in D at these representatives and quotient it by the
kernel of evaluation. This constructs an algebra T in universe max u v with an
injective algebra map i : T → D. Set K = i⁻¹(J). Since i is injective and J is
square-zero, K is square-zero. The induced map j : T/K → D/J is injective.
Send s to the class of X_s in T/K. Its image under j is g(e.symm s), so
injectivity of j proves that this is an R-algebra map g' : S → T/K. The ideal
map under e.symm commutes with powers; therefore g' kills the same positive
power of n that g kills after transport. Apply the original lifting property
to T, K, and g'. Compose the resulting lift with i and e. Applying j to its
quotient equality gives the required lift of g. The construction works also
for zero rings and the zero and unit ideals; no nontriviality is required. -/
theorem formallySmoothAdic_ulift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (n : Ideal S) (h : FormallySmoothAdic R S n) :
    FormallySmoothAdic R (ULift.{w} S)
      (n.map (ULift.ringEquiv : ULift.{w} S ≃+* S).symm.toRingHom) := by
  classical
  intro D _ _ J hJ g hg
  let e : ULift.{w} S ≃ₐ[R] S := ULift.algEquiv
  let g₀ : S →ₐ[R] D ⧸ J := g.comp e.symm.toAlgHom
  choose r hr using (fun s : S ↦ Ideal.Quotient.mk_surjective (g₀ s))
  let q : MvPolynomial S R →ₐ[R] D := MvPolynomial.aeval r
  let T := MvPolynomial S R ⧸ RingHom.ker q.toRingHom
  let i : T →ₐ[R] D := Ideal.kerLiftAlg q
  have hi : Function.Injective i := Ideal.kerLiftAlg_injective q
  let K : Ideal T := J.comap i.toRingHom
  have hK : K ^ 2 = ⊥ := by
    apply le_antisymm _ bot_le
    have hp := Ideal.le_comap_pow (f := i.toRingHom) (K := J) 2
    rw [hJ, Ideal.comap_bot_of_injective i.toRingHom hi] at hp
    exact hp
  let j : T ⧸ K →ₐ[R] D ⧸ J := Ideal.quotientMapₐ J i le_rfl
  have hj : Function.Injective j := Ideal.quotientMap_injective
  let t : S → T ⧸ K := fun s ↦ Ideal.Quotient.mk K
    (Ideal.Quotient.mk (RingHom.ker q.toRingHom) (MvPolynomial.X s))
  have ht (s : S) : j (t s) = g₀ s := by
    change Ideal.Quotient.mk J (q (MvPolynomial.X s)) = g₀ s
    simpa only [q, MvPolynomial.aeval_X] using hr s
  let g' : S →ₐ[R] T ⧸ K :=
    { toFun := t
      map_one' := hj (by rw [ht, map_one, map_one])
      map_mul' := fun x y ↦ hj (by simp only [map_mul, ht])
      map_zero' := hj (by rw [ht, map_zero, map_zero])
      map_add' := fun x y ↦ hj (by simp only [map_add, ht])
      commutes' := fun a ↦ hj (by rw [ht, g₀.commutes, j.commutes]) }
  have hg' : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g' x = 0 := by
    obtain ⟨k, hk, hkill⟩ := hg
    refine ⟨k, hk, fun x hx ↦ hj ?_⟩
    rw [map_zero]
    change j (t x) = 0
    rw [ht]
    apply hkill
    change e.symm x ∈ (n.map e.symm.toRingHom) ^ k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨f, hf⟩ := h K hK g' hg'
  refine ⟨(i.comp f).comp e.toAlgHom, ?_⟩
  ext x
  have hf' := DFunLike.congr_fun hf (e x)
  have heq := congrArg j hf'
  change Ideal.Quotient.mk J (i (f (e x))) = g x
  change Ideal.Quotient.mk J (i (f (e x))) = j (t (e x)) at heq
  rw [heq, ht]
  exact congrArg g (e.symm_apply_apply x)

end Algebra
