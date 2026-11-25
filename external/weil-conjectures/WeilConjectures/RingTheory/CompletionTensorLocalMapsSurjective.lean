/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.CompletionFiniteExtensionTensorBijective
import WeilConjectures.RingTheory.CompletionLocalizedAlgebraProductSurjective

/-!
# Surjectivity of the local completion comparison

Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension).
(blueprint: lem-weil-pbc-completion-tensor-local-maps-surjective)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- Functoriality of ring completions for a homomorphism preserving ideals. -/
private noncomputable def completionMap
    {T : Type*} {U : Type*} [CommRing T] [CommRing U]
    (I : Ideal T) (K : Ideal U) (φ : T →+* U) (hφ : I.map φ ≤ K) :
    AdicCompletion I T →+* AdicCompletion K U := by
  let hpow (n : ℕ) : I ^ n ≤ (K ^ n).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' hφ n
  let f (n : ℕ) : AdicCompletion I T →+* U ⧸ K ^ n :=
    (Ideal.quotientMap (K ^ n) φ (hpow n)).comp (evalₐ I n).toRingHom
  have hf {i j : ℕ} (hij : i ≤ j) :
      (Ideal.Quotient.factorPow K hij).comp (f j) = f i := by
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I j x)
    have hi : evalₐ I i x = Ideal.Quotient.mk (I ^ i) r := by
      have hv : x.val j = Submodule.Quotient.mk r := by
        have h := factor_evalₐ_eq_eval I (n := j) x (by simp)
        rw [← hr] at h
        exact h.symm
      have hvi := x.property hij
      rw [hv] at hvi
      have h := factor_eval_eq_evalₐ I (n := i) x (by simp)
      rw [show eval I T i x = Submodule.Quotient.mk r from hvi.symm] at h
      exact h.symm
    simp [f, ← hr, hi]
  exact liftRingHom K f (fun hij ↦ hf hij)

private theorem completionMap_eval
    {T : Type*} {U : Type*} [CommRing T] [CommRing U]
    (I : Ideal T) (K : Ideal U) (φ : T →+* U) (hφ : I.map φ ≤ K)
    (n : ℕ) (x : AdicCompletion I T) (r : T)
    (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r) :
    evalₐ K n (completionMap I K φ hφ x) = Ideal.Quotient.mk (K ^ n) (φ r) := by
  rw [completionMap, evalₐ_liftRingHom]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    hx, Ideal.quotientMap_mk]

/-- Local completion tuples can be interpolated by completed tensors.
Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension),
the inverse limit of the quotient product decompositions and Tag 00MA.
(blueprint: lem-weil-pbc-completion-tensor-local-maps-surjective)

Proof:
1. Put A = R_p and B = A tensor_R S. B is finite over the Noetherian local ring A.
   The finitely many primes over m correspond to Q and have local rings S_q.
   For n > 0 the Artinian ring B/m^n B is canonically the product of the
   S_q/m^n S_q by Tags 00JA and 00CT. The isomorphisms commute with reduction
   because their maps are induced by the same localization maps at every level.
2. In each S_q the m S_q-adic and maximal-ideal-adic filtrations are cofinal:
   m S_q is contained in q S_q, and finite generation plus radical equality
   gives (q S_q)^t contained in m S_q. Tag 0394 gives the canonical comparison
   of completions, induced by the identity on S_q.
3. Given a tuple in the maximal-ideal completions, use these comparisons to
   obtain m-adic sequences in all factors. At each positive n apply the inverse
   quotient product isomorphism to their coordinates. These preimages commute
   with reduction by uniqueness, hence define an element of the m-adic
   completion of B. The n = 0 coordinate belongs to the zero quotient.
4. Tag 00MA and tensor cancellation express that element as a tensor in
   C tensor_R S. The quotient equation in the hypothesis pins down the maps on
   a tensor 1 by extensionality of completion coordinates. The S-algebra property
   then pins down the whole map by tensor induction. Its value on the tensor
   just constructed is the prescribed tuple, proving surjectivity. For empty Q
   there is one tuple in the zero product ring, and zero is its preimage. -/
theorem completion_tensor_localMaps_surjective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    ∀ (f : (C ⊗[R] S) →ₐ[S] (∀ q : Q, D q)),
      (∀ (q : Q) (n : ℕ) (a : C) (r : A),
        evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
        evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
            (f (a ⊗ₜ[R] (1 : S)) q) =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
            (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p)) r)) →
      Function.Surjective f := by
  intro A m C Q D
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  intro f hf
  let B := A ⊗[R] S
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let J := p.map (algebraMap R B)
  let φ (q : Q) : A →+* Localization.AtPrime q.1 :=
    Localization.localRingHom p q.1 (algebraMap R S)
      (Ideal.LiesOver.over (P := q.1) (p := p))
  let φR (q : Q) : A →ₐ[R] Localization.AtPrime q.1 :=
    { toRingHom := φ q
      commutes' := fun r ↦ by
        change φ q (algebraMap R A r) = algebraMap R (Localization.AtPrime q.1) r
        simpa only [φ, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.1)]
          using Localization.localRingHom_to_map p q.1 (algebraMap R S)
            (Ideal.LiesOver.over (P := q.1) (p := p)) r }
  let ψ (q : Q) : B →ₐ[S] Localization.AtPrime q.1 :=
    ((AlgHom.liftEquiv R S A (Localization.AtPrime q.1)) (φR q)).comp
      (Algebra.TensorProduct.commRight R S A).symm.toAlgHom
  have hψ (q : Q) (r : A) : ψ q (r ⊗ₜ[R] (1 : S)) = φ q r := by
    change (1 : S) • φR q r = φ q r
    simp only [one_smul]
    rfl
  have hJ : m.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] B).toRingHom = J := by
    rw [show m = p.map (algebraMap R A) from
      (Localization.AtPrime.map_eq_maximalIdeal (I := p)).symm, Ideal.map_map]
    congr 1
  have hψJ (q : Q) : J.map (ψ q).toRingHom ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q.1) := by
    rw [← hJ, Ideal.map_map]
    have heq : (ψ q).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] B).toRingHom = φ q := by
      ext r
      exact hψ q r
    rw [heq]
    have : IsLocalHom (φ q) := Localization.isLocalHom_localRingHom _ _ _ _
    exact IsLocalRing.map_maximalIdeal_le (φ q)
  let g : AdicCompletion J B →+* (∀ q : Q, D q) :=
    RingHom.pi (fun q ↦ completionMap J
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) (ψ q).toRingHom (hψJ q))
  have hg (q : Q) (n : ℕ) (x : AdicCompletion J B) (b : B)
      (hx : evalₐ J n x = Ideal.Quotient.mk (J ^ n) b) :
      evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g x q) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
          (ψ q b) := completionMap_eval J
            (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
            (ψ q).toRingHom (hψJ q) n x b hx
  have hgsurj : Function.Surjective g :=
    completion_localizedAlgebra_product_surjective R S p ψ hψ g hg
  let t := completionFiniteExtensionTensorMap R S p
  have ht (n : ℕ) (a : C) (r : A)
      (ha : evalₐ m n a = Ideal.Quotient.mk (m ^ n) r) :
      evalₐ J n (t (a ⊗ₜ[R] (1 : S))) =
        Ideal.Quotient.mk (J ^ n) (r ⊗ₜ[R] (1 : S)) := by
    unfold t completionFiniteExtensionTensorMap
    dsimp only
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.commRight_symm_tmul, AlgHom.liftEquiv_tmul, one_smul]
    rw [evalₐ_liftAlgHom]
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, ha]
    rfl
  have hfg (x : C ⊗[R] S) : f x = g (t x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a s =>
      have hbase : f (a ⊗ₜ[R] (1 : S)) = g (t (a ⊗ₜ[R] (1 : S))) := by
        funext q
        apply ext_evalₐ
        intro n
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ m n a)
        rw [hf q n a r hr.symm, hg q n _ _ (ht n a r hr.symm), hψ]
      have hscalar : f (1 ⊗ₜ[R] s) = g (t (1 ⊗ₜ[R] s)) := by
        funext q
        apply ext_evalₐ
        intro n
        have hts : t (1 ⊗ₜ[R] s) = of J B (1 ⊗ₜ[R] s) := by
          exact t.commutes s
        rw [hts, hg q n _ _ (evalₐ_of J n _)]
        change evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
          (f (algebraMap S (C ⊗[R] S) s) q) = _
        rw [f.commutes]
        change evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
          (algebraMap S (D q) s) = _
        rw [algebraMap_apply, evalₐ_of]
        congr 1
        exact ((ψ q).commutes s).symm
      rw [show a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * (1 ⊗ₜ[R] s) by
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      simp only [map_mul, hbase, hscalar]
  intro y
  obtain ⟨z, hz⟩ := hgsurj y
  obtain ⟨x, hx⟩ := (completion_finite_extension_tensor_bijective R S p).2 z
  exact ⟨x, (hfg x).trans ((congrArg g hx).trans hz)⟩

end AdicCompletion
