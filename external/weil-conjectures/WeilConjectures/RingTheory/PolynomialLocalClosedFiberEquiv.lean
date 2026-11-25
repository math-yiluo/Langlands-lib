/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.RingTheory.FibreLocalRingNaturalIso

/-! # The polynomial closed fibre as a polynomial local ring over a residue field

Source: Stacks Project, Algebra, Remark 0H9M and the first paragraph of Tag 00SV.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace MvPolynomial

/-- The closed fibre of a polynomial local map is a polynomial local ring over the
residue field, with the natural formula for every polynomial.
Source: Stacks Project, Algebra, Remark 0H9M and Tag 00SV, first proof paragraph.
(blueprint: lem-weil-pbc-polynomial-local-closed-fiber-equiv).

Proof: Set `P = R[x]` and `p = Q ∩ R`. By the fibre-prime correspondence there is a prime
`T` of `p.Fiber P` whose contraction along `j : P → p.Fiber P` is `Q`.
The polynomial scalar-extension equivalence identifies `p.Fiber P` with `κ(p)[x]`
and sends `j(a) = 1 ⊗ a` to `map (R → κ(p)) a`. Transport `T` through this equivalence
to the prime `Qk`. Its contraction to `P` is therefore `Q`.
The natural fibre-local-ring quotient equivalence (0H9M) identifies
`P_Q / p P_Q` with `(p.Fiber P)_T`, sending `[a/1]` to `j(a)/1`.
The maximal ideal of `R_p` is `p R_p`. Its image under the local map `φ` generates
exactly `p P_Q`: use the natural formula for `φ` on `r/1` and note that all denominators
outside `p` become units. Thus its image ideal `I` equals `p P_Q`.
Compose the quotient equivalence with the localization of the scalar-extension
ring equivalence to obtain `e : P_Q/I ≃ κ(p)[x]_{Qk}`. Both equivalences have their
specified natural fraction formula, so their composite sends `[a/1]` to the displayed
coefficientwise image of `a` divided by `1`. The argument includes no variables and
arbitrary coefficient rings; a prime `Q` already ensures that these local rings exist
and are nonzero. No complete-intersection or Noetherian hypothesis is used.
-/
theorem exists_polynomial_local_closedFiber_equiv
    {R : Type u} [CommRing R] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime] :
    let p := Q.comap (algebraMap R (MvPolynomial (Fin n) R))
    let φ := Localization.localRingHom p Q (algebraMap R (MvPolynomial (Fin n) R)) rfl
    let I := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map φ
    ∃ (Qk : Ideal (MvPolynomial (Fin n) p.ResidueField)) (hQk : Qk.IsPrime),
      letI := hQk
      Qk.comap (MvPolynomial.map (algebraMap R p.ResidueField)) = Q ∧
        ∃ e : (Localization.AtPrime Q ⧸ I) ≃+* Localization.AtPrime Qk,
          ∀ a : MvPolynomial (Fin n) R,
            e (Ideal.Quotient.mk I
              (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q) a)) =
              algebraMap (MvPolynomial (Fin n) p.ResidueField) (Localization.AtPrime Qk)
                (MvPolynomial.map (algebraMap R p.ResidueField) a)  := by
  classical
  let P := MvPolynomial (Fin n) R
  let p := Q.comap (algebraMap R P)
  let k := p.ResidueField
  let F := p.Fiber P
  let j : P →+* F := Algebra.TensorProduct.includeRight.toRingHom
  let EF := PrimeSpectrum.preimageEquivFiber R P ⟨p, inferInstance⟩
  let v : PrimeSpectrum.comap (algebraMap R P) ⁻¹' {⟨p, inferInstance⟩} :=
    ⟨⟨Q, inferInstance⟩, rfl⟩
  let T := (EF v).asIdeal
  have hcontract : T.comap j = Q := by
    have hh := congrArg (fun z ↦ z.val.asIdeal) (EF.symm_apply_apply v)
    exact hh
  let E : F ≃ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.algebraTensorAlgEquiv R k
  let Qk := T.comap E.symm.toRingHom
  have hback : T = Qk.comap E.toRingHom := by
    ext a
    change a ∈ T ↔ E.symm (E a) ∈ T
    rw [E.symm_apply_apply]
  let g : P →+* MvPolynomial (Fin n) k := MvPolynomial.map (algebraMap R k)
  have hgj (a : P) : E (j a) = g a := by
    change MvPolynomial.algebraTensorAlgEquiv R k (1 ⊗ₜ[R] a) = g a
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hcontractk : Qk.comap g = Q := by
    calc
      Qk.comap g = T.comap j := by
        ext a
        change g a ∈ Qk ↔ j a ∈ T
        rw [hback]
        change g a ∈ Qk ↔ E (j a) ∈ Qk
        rw [hgj]
      _ = Q := hcontract
  have model : ∀ (q : Ideal P) [q.IsPrime], q = T.comap j →
      ∃ e : (Localization.AtPrime q ⧸
          (p.map (algebraMap R P)).map (algebraMap P (Localization.AtPrime q))) ≃+*
            Localization.AtPrime T,
        ∀ a : P, e (Ideal.Quotient.mk _ (algebraMap P (Localization.AtPrime q) a)) =
          algebraMap F (Localization.AtPrime T) (j a) := by
    intro q hq heq
    subst q
    obtain ⟨_, _, _, e, he⟩ := Ideal.Fiber.localRingHom_surjective_ker_quotientEquiv p T
    refine ⟨e, fun a ↦ ?_⟩
    rw [he]
    exact Localization.localRingHom_to_map _ _ _ rfl a
  obtain ⟨e₀, he₀⟩ := model Q hcontract.symm
  let e₁ := Localization.localRingEquiv T Qk E.toRingEquiv hback
  let φ := Localization.localRingHom p Q (algebraMap R P) rfl
  let I := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map φ
  have hI : I = (p.map (algebraMap R P)).map (algebraMap P (Localization.AtPrime Q)) := by
    dsimp only [I]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    congr 1
    ext r
    exact Localization.localRingHom_to_map _ _ _ rfl r
  refine ⟨Qk, inferInstance, hcontractk, ?_⟩
  change ∃ e : (Localization.AtPrime Q ⧸ I) ≃+* Localization.AtPrime Qk, _
  let e₂ := Ideal.quotientEquivAlgOfEq (Localization.AtPrime Q) hI
  refine ⟨e₂.toRingEquiv.trans (e₀.trans e₁), fun a ↦ ?_⟩
  change e₁ (e₀ (e₂ (Ideal.Quotient.mk I
    (algebraMap P (Localization.AtPrime Q) a)))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, he₀]
  change Localization.localRingHom T Qk E.toRingHom hback
    (algebraMap F (Localization.AtPrime T) (j a)) = _
  rw [Localization.localRingHom_to_map]
  exact congrArg (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime Qk)) (hgj a)

end MvPolynomial
