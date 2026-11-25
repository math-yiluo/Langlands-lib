/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
import all WeilConjectures.RingTheory.SyntomicPolynomialFibreComparison
import WeilConjectures.RingTheory.LciConormalFreeRankCodimension
import WeilConjectures.RingTheory.SyntomicLocalKernelIntersection
import WeilConjectures.RingTheory.LocalizedIdealConormalGeneratorBound
import all WeilConjectures.RingTheory.SyntomicFibreKernelGenerators
import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.RingTheory.FibreLocalRingNaturalIso

/-!
# Local kernel generators with the fibre codimension count

Source: Stacks Project, Algebra, Tags 00SY and 00SC.
(blueprint: lem-weil-pbc-syntomic-codimension-local-kernel-generators).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

/-- The local fibre equivalence commutes with the maps from the presenting ring. -/
private theorem exists_localized_fibre_comparison
    {R P T : Type*} [CommRing R] [CommRing P] [CommRing T] [Algebra R P]
    (p : Ideal R) [p.IsPrime] (E : p.Fiber P ≃+* T)
    (Qk : Ideal T) [Qk.IsPrime] (Q : Ideal P) [Q.IsPrime]
    (hQ : Q = (Qk.comap E.toRingHom).comap
      Algebra.TensorProduct.includeRight.toRingHom) :
    ∃ e : (Localization.AtPrime Q ⧸ p.map (algebraMap R (Localization.AtPrime Q))) ≃+*
        Localization.AtPrime Qk,
      ∀ a : P, e (Ideal.Quotient.mk _ (algebraMap P (Localization.AtPrime Q) a)) =
        algebraMap T (Localization.AtPrime Qk) (E (1 ⊗ₜ[R] a)) := by
  subst Q
  let U := Qk.comap E.toRingHom
  let j : P →+* p.Fiber P := Algebra.TensorProduct.includeRight.toRingHom
  let A := Localization.AtPrime (U.comap j)
  let m := p.map (algebraMap R A)
  obtain ⟨_, _, _, e₀, he₀⟩ := Ideal.Fiber.localRingHom_surjective_ker_quotientEquiv p U
  have hm : m = (p.map (algebraMap R P)).map (algebraMap P A) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e₁ := Localization.localRingEquiv U Qk E rfl
  let e₂ := Ideal.quotientEquivAlgOfEq A hm
  refine ⟨e₂.toRingEquiv.trans (e₀.trans e₁), fun a ↦ ?_⟩
  change e₁ (e₀ (e₂ (Ideal.Quotient.mk m (algebraMap P A a)))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, he₀]
  change e₁ (Localization.localRingHom (U.comap j) U j rfl (algebraMap P A a)) = _
  rw [Localization.localRingHom_to_map]
  exact Localization.localRingHom_to_map U Qk E.toRingHom rfl (j a)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_counted_polynomial_fibre_comparison
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    let p := q.asIdeal.comap (algebraMap R S)
    let k := p.ResidueField
    let P := MvPolynomial (Fin n) R
    let A := Localization.AtPrime (q.asIdeal.comap φ.toRingHom)
    let m := p.map (algebraMap R A)
    let Ibar := (RingHom.ker φ.toRingHom).map (MvPolynomial.map (algebraMap R k))
    ∃ t : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ Ibar),
      topologicalKrullDimAt t = topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩) ∧
      (∃ h : MvPolynomial (Fin n) k ⧸ Ibar,
        h ∉ t.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away h)) ∧
      ∃ e : (A ⧸ m) ≃+*
          Localization.AtPrime (t.asIdeal.comap (Ideal.Quotient.mk Ibar)),
        ((RingHom.ker φ.toRingHom).map (algebraMap P A)).map
            (e.toRingHom.comp (Ideal.Quotient.mk m)) =
          Ibar.map (algebraMap _
            (Localization.AtPrime (t.asIdeal.comap (Ideal.Quotient.mk Ibar)))) := by
  classical
  dsimp only
  let p := q.asIdeal.comap (algebraMap R S)
  let k := p.ResidueField
  let P := MvPolynomial (Fin n) R
  let Pk := MvPolynomial (Fin n) k
  let I := RingHom.ker φ.toRingHom
  let Q := q.asIdeal.comap φ.toRingHom
  let A := Localization.AtPrime Q
  let m := p.map (algebraMap R A)
  let ρ : P →+* Pk := MvPolynomial.map (algebraMap R k)
  let Ibar := I.map ρ
  let F := p.Fiber P
  let j : P →+* F := Algebra.TensorProduct.includeRight.toRingHom
  let E : F ≃ₐ[k] Pk := MvPolynomial.algebraTensorAlgEquiv R k
  let EF := PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
  let qb := EF ⟨q, rfl⟩
  let eF : p.Fiber S ≃ₐ[k] (Pk ⧸ Ibar) := polynomial_fiber_equiv_quotient n φ hφ p
  let t : PrimeSpectrum (Pk ⧸ Ibar) := qb.comap eF.symm.toRingHom
  let Qk := t.asIdeal.comap (Ideal.Quotient.mk Ibar)
  let U := Qk.comap E.toRingHom
  have hq : qb.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
    exact congrArg (fun z ↦ z.val.asIdeal) (EF.symm_apply_apply ⟨q, rfl⟩)
  have heF (a : P) : eF (1 ⊗ₜ[R] φ a) = Ideal.Quotient.mk Ibar (ρ a) := by
    simpa only [eF, Ibar, ρ, I, Pk, k, MvPolynomial.C_1, one_mul] using
      polynomial_fiber_equiv_quotient_tmul n φ hφ p 1 a
  have hgj (a : P) : E (j a) = ρ a := by
    change MvPolynomial.algebraTensorAlgEquiv R k (1 ⊗ₜ[R] a) = ρ a
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hcontract : U.comap j = Q := by
    ext a
    change E (j a) ∈ Qk ↔ φ a ∈ q.asIdeal
    rw [hgj]
    change eF.symm (Ideal.Quotient.mk Ibar (ρ a)) ∈ qb.asIdeal ↔ φ a ∈ q.asIdeal
    rw [← heF, eF.symm_apply_apply]
    exact (show (1 ⊗ₜ[R] φ a) ∈ qb.asIdeal ↔ φ a ∈ q.asIdeal by
      change φ a ∈ qb.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom ↔ _
      rw [hq])
  have hcit : ∃ h : Pk ⧸ Ibar,
      h ∉ t.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away h) := by
    obtain ⟨h, hh, hci⟩ := hci
    refine ⟨eF h, ?_, ?_⟩
    · change eF.symm (eF h) ∉ qb.asIdeal
      rwa [eF.symm_apply_apply]
    · let EL : Localization.Away (eF h) ≃ₐ[k] Localization.Away h :=
        IsLocalization.algEquivOfAlgEquiv
          (M := Submonoid.powers (eF h)) (T := Submonoid.powers h)
          (Localization.Away (eF h)) (Localization.Away h) eF.symm (by
          rw [Submonoid.map_powers]
          exact congrArg Submonoid.powers (eF.symm_apply_apply h))
      exact completeIntersection_of_algEquiv EL hci
  obtain ⟨e, he₀⟩ := exists_localized_fibre_comparison p E.toRingEquiv Qk Q hcontract.symm
  have he (a : P) : e (Ideal.Quotient.mk m (algebraMap P A a)) =
      algebraMap Pk (Localization.AtPrime Qk) (ρ a) := by
    exact (he₀ a).trans (congrArg (algebraMap Pk (Localization.AtPrime Qk)) (hgj a))
  have hdim : topologicalKrullDimAt t = topologicalKrullDimAt qb := by
    let H := PrimeSpectrum.homeomorphOfRingEquiv eF.toRingEquiv
    exact (dimAt_openEmbedding H.isOpenEmbedding qb).symm
  refine ⟨t, hdim, hcit, e, ?_⟩
  change (I.map (algebraMap P A)).map (e.toRingHom.comp (Ideal.Quotient.mk m)) =
    (I.map ρ).map (algebraMap Pk (Localization.AtPrime Qk))
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg (fun f ↦ I.map f) (RingHom.ext he)


/-- Choose local presentation-kernel generators whose number is the fibre codimension.
Source: Stacks Project, Algebra, Tag 00SY, proof of (3) implies (2), choice of the
conormal basis and Nakayama; Tag 00SC, (1) implies (4), and Tag 00P2.
(blueprint: lem-weil-pbc-syntomic-codimension-local-kernel-generators).

Proof: Set P = R[x_1,...,x_n], I = ker φ, p = q ∩ R, Q = φ⁻¹(q), k = κ(p).
Coefficient reduction and tensoring the surjection identify the fibre with
k[x_1,...,x_n]/Ibar and its canonical prime with a quotient prime t. The complete
intersection neighbourhood hypothesis transfers to this quotient. By 00SC its localized
conormal module is free of rank c = n-d, where d is the local topological dimension
at t; 00P2 gives d ≤ n. The same homeomorphism identifies d with the stated dimension
of the fibre of S. Write Qbar for the inverse-image prime in k[x_1,...,x_n]. The vector space
Ibar_Qbar / Qbar Ibar_Qbar has dimension c: it is the residue reduction of the
localized conormal module, since Ibar_Qbar is contained in Qbar. The images of I
span this vector space, so select c of those images as a basis and use their
original representatives f_i in I. Equivalently, clear denominators outside Qbar
in these selected representatives; multiplying individual basis vectors by units
preserves their linear independence and span.
Nakayama over the polynomial fibre local ring makes these c images generate Ibar
there. The polynomial local ring A = P_Q modulo pA is this polynomial fibre local
ring, so, with J = (f_i), IA ≤ JA + pA. More precisely IA ≤ JA + (IA ∩ pA).
Flatness of S_q over R_p gives IA ∩ pA = pIA by tensoring the kernel sequence;
thus IA ≤ JA + pIA. The ideal IA is finite by hfg, and pA lies in the maximal
ideal of A. Nakayama applied to IA/JA gives IA = JA. Since d ≤ n and c = n-d,
we have c ≤ n and n-c = d. For c = 0 the same argument makes IA zero; the
specified fibre prime excludes the empty fibre. No regularity of R is required. -/
theorem exists_codimension_local_kernel_generators
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ) (hfg : (RingHom.ker φ.toRingHom).FG)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      c ≤ n ∧ Ideal.span (Set.range f) ≤ RingHom.ker φ.toRingHom ∧
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (Ideal.span (Set.range f)) =
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) ∧
      topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩) =
          (n - c : ℕ) := by
  classical
  let P := MvPolynomial (Fin n) R
  let Q := q.asIdeal.comap φ.toRingHom
  let A := Localization.AtPrime Q
  let p := q.asIdeal.comap (algebraMap R S)
  let m := p.map (algebraMap R A)
  let I := RingHom.ker φ.toRingHom
  let k := p.ResidueField
  let Ibar := I.map (MvPolynomial.map (algebraMap R k))
  obtain ⟨t, hdim, hcit, e, he⟩ :=
    exists_counted_polynomial_fibre_comparison q n φ hφ hci
  obtain ⟨d, hd, hdn, ⟨b⟩⟩ :=
    Ideal.exists_basis_cotangent_localization_of_completeIntersection n Ibar t hcit
  let B := Localization.AtPrime (t.asIdeal.comap (Ideal.Quotient.mk Ibar))
  let L := Ibar.map (algebraMap _ B)
  have hLfg : L.FG := Ibar.fg_of_isNoetherianRing.map _
  have hLrank : L.spanFinrank ≤ n - d :=
    Ideal.spanFinrank_localized_ideal_le_of_conormal_generators Ibar
      Ibar.fg_of_isNoetherianRing t (n - d) b b.span_eq
  let K := (I.map (algebraMap P A)).map (Ideal.Quotient.mk m)
  have hKL : K.map e.toRingHom = L := by
    rw [Ideal.map_map]
    exact he
  have hKfg : K.FG := by
    have hh := hLfg.map e.symm.toRingHom
    rw [← hKL] at hh
    have hback : (K.map e.toRingHom).map e.symm.toRingHom = K :=
      Ideal.map_of_equiv e
    exact hback ▸ hh
  have hKrank : K.spanFinrank ≤ n - d := by
    have hr := Ideal.spanFinrank_map_eq_of_ringEquiv e K
    change (K.map e.toRingHom).spanFinrank = K.spanFinrank at hr
    rw [← hr, hKL]
    exact hLrank
  obtain ⟨c, f, hc, hfI, hgen⟩ :=
    lift_generators_from_localized_quotient Q.primeCompl I m hKfg
  have hcd : c ≤ n - d := hc.trans_le hKrank
  let g : Fin (n - d) → P := fun i ↦ if h : i.val < c then f ⟨i.val, h⟩ else 0
  have hgspan : Ideal.span (Set.range g) = Ideal.span (Set.range f) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      dsimp only [g]
      split
      · exact Ideal.subset_span ⟨_, rfl⟩
      · exact Ideal.zero_mem _
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : i.val < n - d := lt_of_lt_of_le i.isLt hcd
      have hgi : g ⟨i.val, hi⟩ = f i := by simp [g, i.isLt]
      exact Ideal.subset_span ⟨⟨i.val, hi⟩, hgi⟩
  refine ⟨n - d, g, Nat.sub_le _ _, hgspan ▸ hfI, ?_, ?_⟩
  · rw [hgspan]
    let IA : Ideal A := I.map (algebraMap P A)
    let J : Ideal A := (Ideal.span (Set.range f)).map (algebraMap P A)
    have hJI : J ≤ IA := Ideal.map_mono hfI
    have hinter : IA ⊓ m = m * IA := syntomic_local_kernel_intersection q n φ hφ hflat
    have hm : m ≤ IsLocalRing.maximalIdeal A := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      apply (IsLocalization.AtPrime.to_map_mem_maximal_iff A Q _).mpr
      change φ (algebraMap R (MvPolynomial (Fin n) R) r) ∈ q.asIdeal
      simpa only [φ.commutes] using (show (algebraMap R S) r ∈ q.asIdeal from hr)
    have hsmall : IA ≤ J ⊔ m * IA := by
      rw [← hinter]
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hgen hx)
      have hzI : z ∈ IA := by
        simpa only [add_sub_cancel_left] using IA.sub_mem hx (hJI hy)
      exact Submodule.mem_sup.mpr ⟨y, hy, z, ⟨hzI, hz⟩, rfl⟩
    apply le_antisymm hJI
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (hfg.map (algebraMap P A))
    · exact hm.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · exact hsmall
  · have harith : n - (n - d) = d := by omega
    rw [harith]
    exact hdim.symm.trans hd


end Algebra
