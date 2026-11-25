/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.PolynomialOriginRegularLocal
import WeilConjectures.RingTheory.PolynomialLocalClosedFiberEquiv
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Parameters of the closed fibre of a polynomial append

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, property (1),
and Algebra, Tags 00SV (first paragraph), 0H9M and 00OP.
-/

@[expose] public section

set_option autoImplicit false
universe u
namespace Algebra

/-- The appended variables are a regular system of parameters of the closed source fibre.

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, proof of lemma-solution-modulo,
property (1); Algebra, Tags 00SV (first paragraph), 0H9M and 00OP.
(blueprint: lem-weil-pbc-polynomial-append-closed-fibre-parameters).

Proof: Reindex the larger polynomial ring as P₀[Y₁,...,Yₑ] using renameEquiv
and sumAlgEquiv. Transport p₁ to its prime Q in this ring. Its contraction to
P₀ is p₀, and localization of the reindexing maps the extended maximal ideal
onto the extended maximal ideal for the coefficient inclusion. Quotienting gives
an isomorphism of the two closed fibres, with the natural formula on variables.
Apply exists_polynomial_local_closedFiber_equiv to Q. It gives a prime Qk over
Q in κ(p₀)[Yᵢ] and a natural isomorphism of the closed fibre with its localization.
Every Yᵢ belongs to Q, so its coefficientwise image belongs to Qk by contraction.
The origin ideal is maximal by polynomial_origin_regularLocal; thus Qk equals
that ideal. Compose the two fibre isomorphisms and check its formula on each
appended variable. Apply polynomial_origin_regularLocal over κ(p₀) and transport
regular locality and dimension e along this isomorphism. Map the ideal generated
by the displayed list; the variable formula identifies it with the origin's
maximal ideal. Injectivity of mapping ideals by a ring isomorphism gives the
claimed generation. For e=0 all variable arguments are empty, the origin is the
zero ideal, and the same proof gives dimension zero and the empty generator list. -/
theorem polynomial_append_closed_fibre_parameters
    (k : Type u) [Field k] (t e : ℕ)
    (p₀ : Ideal (MvPolynomial (Fin t) k)) [p₀.IsPrime]
    (p₁ : Ideal (MvPolynomial (Fin (t + e)) k)) [p₁.IsPrime]
    (hc : p₀ = p₁.comap (MvPolynomial.rename (Fin.castAdd e)).toRingHom)
    (hz : ∀ i : Fin e, MvPolynomial.X (Fin.natAdd t i) ∈ p₁) :
    let α := Localization.localRingHom p₀ p₁
      (MvPolynomial.rename (Fin.castAdd e)).toRingHom hc
    let J := (IsLocalRing.maximalIdeal (Localization.AtPrime p₀)).map α
    let C := Localization.AtPrime p₁ ⧸ J
    let xs := List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk J
      (algebraMap (MvPolynomial (Fin (t + e)) k) (Localization.AtPrime p₁)
        (MvPolynomial.X (Fin.natAdd t i))))
    ∃ h : IsRegularLocalRing C,
      letI := h
      ringKrullDim C = (e : WithBot ℕ∞) ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal C := by
  classical
  let R := MvPolynomial (Fin t) k
  let P := MvPolynomial (Fin e) R
  let E : MvPolynomial (Fin (t + e)) k ≃ₐ[k] P :=
    (MvPolynomial.renameEquiv k
      (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin t) (Fin e)))).trans
        (MvPolynomial.sumAlgEquiv k (Fin e) (Fin t))
  have hEX (i : Fin e) : E (MvPolynomial.X (Fin.natAdd t i)) = MvPolynomial.X i := by
    simp only [E, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumComm_apply]
    exact MvPolynomial.sumAlgEquiv_X_inl k (Fin e) (Fin t) i
  have hEC : E.toRingHom.comp (MvPolynomial.rename (Fin.castAdd e)).toRingHom =
      (MvPolynomial.C : R →+* P) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change E (MvPolynomial.rename (Fin.castAdd e) (MvPolynomial.C a)) =
        MvPolynomial.C (MvPolynomial.C a)
      simp only [MvPolynomial.rename_C, E, AlgEquiv.trans_apply,
        MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
      exact MvPolynomial.sumAlgEquiv_C_inl k (Fin e) (Fin t) a
    · intro i
      change E (MvPolynomial.rename (Fin.castAdd e) (MvPolynomial.X i)) =
        MvPolynomial.C (MvPolynomial.X i)
      simp only [MvPolynomial.rename_X, E, AlgEquiv.trans_apply,
        MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.trans_apply,
        finSumFinEquiv_symm_apply_castAdd, Equiv.sumComm_apply]
      exact MvPolynomial.sumAlgEquiv_X_inr k (Fin e) (Fin t) i
  let Q := p₁.comap E.symm.toRingHom
  have hQ : p₁ = Q.comap E.toRingHom := by
    ext a
    change a ∈ p₁ ↔ E.symm (E a) ∈ p₁
    rw [E.symm_apply_apply]
  have hcontract : Q.comap (algebraMap R P) = p₀ := by
    rw [hc]
    ext a
    change E.symm (MvPolynomial.C a) ∈ p₁ ↔
      MvPolynomial.rename (Fin.castAdd e) a ∈ p₁
    have hh := RingHom.congr_fun hEC a
    change E (MvPolynomial.rename (Fin.castAdd e) a) = MvPolynomial.C a at hh
    rw [← hh, E.symm_apply_apply]
  let α := Localization.localRingHom p₀ p₁
    (MvPolynomial.rename (Fin.castAdd e)).toRingHom hc
  let J := (IsLocalRing.maximalIdeal (Localization.AtPrime p₀)).map α
  let C := Localization.AtPrime p₁ ⧸ J
  let p := Q.comap (algebraMap R P)
  let γ := Localization.localRingHom p Q (algebraMap R P) rfl
  let I := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map γ
  let D := Localization.AtPrime Q ⧸ I
  let EL := Localization.localRingEquiv p₁ Q E.toRingEquiv hQ
  have hI : I = J.map EL.toRingHom := by
    dsimp only [I, J]
    rw [← Localization.AtPrime.map_eq_maximalIdeal,
      ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      Ideal.map_map, Ideal.map_map]
    have hγ : γ.comp (algebraMap R (Localization.AtPrime p)) =
        (algebraMap P (Localization.AtPrime Q)).comp (algebraMap R P) := by
      apply RingHom.ext
      intro a
      exact Localization.localRingHom_to_map p Q (algebraMap R P) rfl a
    have hα : (EL.toRingHom.comp α).comp
        (algebraMap R (Localization.AtPrime p₀)) =
        (algebraMap P (Localization.AtPrime Q)).comp (algebraMap R P) := by
      apply RingHom.ext
      intro a
      change EL (α (algebraMap R (Localization.AtPrime p₀) a)) =
        algebraMap P (Localization.AtPrime Q) (MvPolynomial.C a)
      dsimp only [α]
      rw [Localization.localRingHom_to_map]
      change Localization.localRingHom p₁ Q E.toRingHom hQ
        (algebraMap _ _ (MvPolynomial.rename (Fin.castAdd e) a)) = _
      rw [Localization.localRingHom_to_map]
      exact congrArg (algebraMap P (Localization.AtPrime Q))
        (RingHom.congr_fun hEC a)
    rw [hγ, hα, show p = p₀ from hcontract]
  let ED : C ≃+* D := Ideal.quotientEquiv J I EL hI
  obtain ⟨Qk, hQk, hback, Ek, hEk⟩ :=
    MvPolynomial.exists_polynomial_local_closedFiber_equiv e Q
  let := hQk
  let K := p.ResidueField
  let o := Ideal.span (Set.range (MvPolynomial.X : Fin e → MvPolynomial (Fin e) K))
  obtain ⟨ho, _, hregular, hdim, _, hgen⟩ :=
    MvPolynomial.polynomial_origin_regularLocal K e
  have hQo : Qk = o := by
    have hle : o ≤ Qk := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have h : MvPolynomial.X i ∈ Q := by
        change E.symm (MvPolynomial.X i) ∈ p₁
        rw [← hEX i, E.symm_apply_apply]
        exact hz i
      rw [← hback] at h
      simpa using h
    exact (ho.eq_of_le hQk.ne_top hle).symm
  subst Qk
  let F : C ≃+* Localization.AtPrime o := ED.trans Ek
  have hF (i : Fin e) : F (Ideal.Quotient.mk J
      (algebraMap (MvPolynomial (Fin (t + e)) k) (Localization.AtPrime p₁)
        (MvPolynomial.X (Fin.natAdd t i)))) =
      algebraMap (MvPolynomial (Fin e) K) (Localization.AtPrime o) (MvPolynomial.X i) := by
    change Ek (ED (Ideal.Quotient.mk J _)) = _
    rw [Ideal.quotientEquiv_mk]
    change Ek (Ideal.Quotient.mk I
      (Localization.localRingHom p₁ Q E.toRingHom hQ (algebraMap _ _ _))) = _
    rw [Localization.localRingHom_to_map]
    change Ek (Ideal.Quotient.mk I (algebraMap P (Localization.AtPrime Q)
      (E (MvPolynomial.X (Fin.natAdd t i))))) = _
    rw [hEX, hEk]
    rw [MvPolynomial.map_X]
  have hC : IsRegularLocalRing C := IsRegularLocalRing.of_ringEquiv F.symm
  let := hC
  refine ⟨hC, ?_, ?_⟩
  · exact (ringKrullDim_eq_of_ringEquiv F).trans hdim
  · have hmapped : (Ideal.ofList (List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk J
        (algebraMap (MvPolynomial (Fin (t + e)) k) (Localization.AtPrime p₁)
          (MvPolynomial.X (Fin.natAdd t i)))))).map F.toRingHom =
        (IsLocalRing.maximalIdeal C).map F.toRingHom := by
      change (Ideal.ofList _).map F = (IsLocalRing.maximalIdeal C).map F
      rw [IsLocalRing.map_ringEquiv_maximalIdeal]
      change (Ideal.ofList _).map F.toRingHom = _
      rw [Ideal.map_ofList]
      have hlist : (List.ofFn (fun i : Fin e ↦ Ideal.Quotient.mk J
          (algebraMap (MvPolynomial (Fin (t + e)) k) (Localization.AtPrime p₁)
            (MvPolynomial.X (Fin.natAdd t i))))).map F.toRingHom =
          List.ofFn (fun i : Fin e ↦ algebraMap (MvPolynomial (Fin e) K)
            (Localization.AtPrime o) (MvPolynomial.X i)) := by
        rw [List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        exact hF i
      rw [hlist]
      have hg : Ideal.span (Set.range (fun i : Fin e ↦
          algebraMap (MvPolynomial (Fin e) K) (Localization.AtPrime o)
            (MvPolynomial.X i))) = IsLocalRing.maximalIdeal (Localization.AtPrime o) :=
        hgen.symm
      rw [← hg]
      unfold Ideal.ofList
      congr 1
      ext a
      simp
    ext x
    change x ∈ Ideal.ofList _ ↔ x ∈ IsLocalRing.maximalIdeal C
    have hh := congrArg (fun I : Ideal (Localization.AtPrime o) ↦ F x ∈ I) hmapped
    change (F x ∈ (Ideal.ofList _).map F) =
      (F x ∈ (IsLocalRing.maximalIdeal C).map F) at hh
    simpa only [Ideal.apply_mem_of_equiv_iff, eq_iff_iff] using hh

end Algebra
