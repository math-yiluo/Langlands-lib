/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EtalePolynomialCertificate
public import Mathlib.RingTheory.Ideal.Cotangent

/-! # Polynomial witnesses for an inverse conormal differential

Source: Stacks Project, Algebra, proof of Tag 07RI, inverse differential calculation.
(blueprint: lem-weil-pbc-conormal-polynomial-inverse).
-/

@[expose] public section

universe u

namespace Algebra

/-- A differential on a finitely generated relation ideal is bijective precisely when
its two inverse identities have finite polynomial witnesses.

Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47654-47662.
(blueprint: lem-weil-pbc-conormal-polynomial-inverse).

Proof: write J = ker α = (f_j). If d is bijective, lift each inverse image of the
coordinate vector e_k to an element g_k of J. Express g_k = sum_j c_jk f_j using
finite ideal generation. The equality d([g_k]) = e_k says exactly that the first
certificate expressions lie in J. Applying injectivity of d to the relation
classes gives [sum_k (∂_k f_j)g_k] = [f_j]. Equality in J/J² is precisely the
second certificate membership.
Conversely, given c, put g_k = sum_j c_jk f_j and define the S-linear map
h(v) = sum_k v_k [g_k]. The first certificate gives d(h(e_k)) = e_k, hence
d composed with h is the identity on the free module. The second gives
h(d([f_j])) = [f_j]. The classes [f_j] generate J/J² over S, since α is
surjective and f_j generate J. Thus h composed with d is also the identity.
The two identities imply bijectivity. No independence of the relations is
assumed. If n or m is zero the corresponding generator check is empty;
if S is the zero ring both modules vanish and the same argument applies. -/
theorem conormal_bijective_iff_polynomialCertificate
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n m : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α) (f : Fin m → MvPolynomial (Fin n) R)
    (hker : RingHom.ker α.toRingHom = Ideal.span (Set.range f)) :
    let J := RingHom.ker α.toRingHom
    let e := RingHom.quotientKerEquivOfSurjective hα
    letI : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom
    ∀ (d : J.Cotangent →ₗ[S] (Fin n → S)),
      (∀ (g : J) (i : Fin n),
        d (Ideal.toCotangent J g) i = α (MvPolynomial.pderiv i g.1)) →
      (Function.Bijective d ↔ EtalePolynomialCertificate f) := by
  classical
  dsimp only
  intro d hd
  let J := RingHom.ker α.toRingHom
  let e := RingHom.quotientKerEquivOfSurjective hα
  let : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom
  have hsmul (r : MvPolynomial (Fin n) R) (x : J.Cotangent) :
      α r • x = r • x := by
    change e.symm (α r) • x = r • x
    rw [show e.symm (α r) = Ideal.Quotient.mk J r from
      RingHom.quotientKerEquivOfSurjective_symm_apply hα r]
    exact IsScalarTower.algebraMap_smul (MvPolynomial (Fin n) R ⧸ J) r x
  have hf (j : Fin m) : f j ∈ J := by
    rw [show J = Ideal.span (Set.range f) from hker]
    exact Ideal.subset_span (Set.mem_range_self j)
  let F : Fin m → J := fun j ↦ ⟨f j, hf j⟩
  have hdF (j : Fin m) (l : Fin n) :
      d (J.toCotangent (F j)) l = α (MvPolynomial.pderiv l (f j)) := hd (F j) l
  have hsum (c : Fin m → MvPolynomial (Fin n) R) :
      J.toCotangent (∑ j, c j • F j) =
        ∑ j, α (c j) • J.toCotangent (F j) := by
    simp only [map_sum, map_smul, hsmul]
  have hgen (x : J.Cotangent) :
      ∃ c : Fin m → MvPolynomial (Fin n) R,
        x = ∑ j, α (c j) • J.toCotangent (F j) := by
    obtain ⟨g, rfl⟩ := J.toCotangent_surjective x
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
      (show g.val ∈ Ideal.span (Set.range f) by
        rw [← hker]; exact g.property)
    refine ⟨c, ?_⟩
    rw [← hsum]
    congr 1
    apply Subtype.ext
    simpa [F, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using hc.symm
  let G (c : Fin m → Fin n → MvPolynomial (Fin n) R) (k : Fin n) : J :=
    ∑ j, c j k • F j
  have hG (c : Fin m → Fin n → MvPolynomial (Fin n) R) (k : Fin n) :
      (G c k).val = ∑ j, c j k * f j := by
    simp [G, F, smul_eq_mul]
  have hGc (c : Fin m → Fin n → MvPolynomial (Fin n) R) (k : Fin n) :
      J.toCotangent (G c k) = ∑ j, α (c j k) • J.toCotangent (F j) :=
    hsum (fun j ↦ c j k)
  have hdG (c : Fin m → Fin n → MvPolynomial (Fin n) R) (k l : Fin n) :
      d (J.toCotangent (G c k)) l =
        α (∑ j, c j k * MvPolynomial.pderiv l (f j)) := by
    rw [hGc, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hdF, map_sum, map_mul]
  have hsecond (c : Fin m → Fin n → MvPolynomial (Fin n) R) (j : Fin m) :
      (∑ k, MvPolynomial.pderiv k (f j) * ∑ j', c j' k * f j') - f j ∈ J ^ 2 ↔
        (∑ k, α (MvPolynomial.pderiv k (f j)) • J.toCotangent (G c k)) =
          J.toCotangent (F j) := by
    let z : J := ∑ k, MvPolynomial.pderiv k (f j) • G c k
    have hz : z.val = ∑ k, MvPolynomial.pderiv k (f j) * ∑ j', c j' k * f j' := by
      simp [z, smul_eq_mul, hG]
    rw [← hz]
    change (z.val - (F j).val ∈ J ^ 2) ↔ _
    rw [← J.toCotangent_eq]
    simp only [z, map_sum, map_smul, hsmul]
  constructor
  · intro hb
    have hx (k : Fin n) : ∃ c : Fin m → MvPolynomial (Fin n) R,
        d (∑ j, α (c j) • J.toCotangent (F j)) = Pi.single k 1 := by
      obtain ⟨x, hx⟩ := hb.2 (Pi.single k 1)
      obtain ⟨c, hc⟩ := hgen x
      exact ⟨c, hc ▸ hx⟩
    choose c hc using hx
    refine ⟨fun j k ↦ c k j, ?_, ?_⟩
    · intro k l
      rw [← hker, RingHom.mem_ker, map_sub]
      have he := congrFun (hc k) l
      rw [← hGc (fun j k ↦ c k j) k] at he
      rw [hdG (fun j k ↦ c k j) k l] at he
      simpa [Pi.single_apply, eq_comm, apply_ite] using sub_eq_zero.mpr he
    · intro j
      rw [← hker, hsecond]
      apply hb.1
      rw [map_sum]
      simp only [map_smul, hGc, hc]
      ext l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      exact (hdF j l).symm
  · rintro ⟨c, hc₁, hc₂⟩
    have hright (v : Fin n → S) :
        d (∑ k, v k • J.toCotangent (G c k)) = v := by
      ext l
      rw [map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hdG]
      have hfirst (k : Fin n) :
          α (∑ j, c j k * MvPolynomial.pderiv l (f j)) =
            (if k = l then 1 else 0) := by
        have hz : α ((∑ j, c j k * MvPolynomial.pderiv l (f j)) -
            (if k = l then 1 else 0)) = 0 := by
          exact hc₁ k l |> (hker ▸ ·) |> RingHom.mem_ker.mp
        rw [map_sub] at hz
        exact (by simpa only [apply_ite, map_one, map_zero] using sub_eq_zero.mp hz)
      simp only [hfirst]
      simp
    have hleft (x : J.Cotangent) :
        (∑ k, d x k • J.toCotangent (G c k)) = x := by
      obtain ⟨a, rfl⟩ := hgen x
      have hj (j : Fin m) :
          (∑ k, d (J.toCotangent (F j)) k • J.toCotangent (G c k)) =
            J.toCotangent (F j) := by
        simpa only [hdF] using (hsecond c j).mp
          (show _ ∈ J ^ 2 by simpa only [J, hker] using hc₂ j)
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      simp_rw [smul_eq_mul, ← smul_smul, ← Finset.smul_sum, hj]
    constructor
    · intro x y hxy
      rw [← hleft x, ← hleft y, hxy]
    · intro v
      exact ⟨∑ k, v k • J.toCotangent (G c k), hright v⟩

end Algebra
