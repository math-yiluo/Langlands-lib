/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
import WeilConjectures.RingTheory.MonicFactorizationOfIdempotent

/-!
# Idempotent lifting and simple-root lifting for local rings

Source: Stacks Project, Algebra, Tags 04GF and 04GG (1) iff (10), and More on Algebra,
Tags 09XE and 09XI (1) iff (3) (blueprint: lem-weil-pbc-henselian-local-root-lifting).
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem lift_idempotent_small
    (R : Type u) [CommRing R] [IsLocalRing R]
    (H : ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B],
      ∀ e₀ : B ⧸ (maximalIdeal R).map (algebraMap R B),
        IsIdempotentElem e₀ →
          ∃! e : B, IsIdempotentElem e ∧
            Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) e = e₀)
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (e₀ : B ⧸ (maximalIdeal R).map (algebraMap R B)) (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) e = e₀ := by
  let E : ULift.{v} B ≃ₐ[R] B := ULift.algEquiv
  have hI : (maximalIdeal R).map (algebraMap R B) =
      ((maximalIdeal R).map (algebraMap R (ULift.{v} B))).map E.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
  let Q := Ideal.quotientEquiv _ _ E.toRingEquiv hI
  obtain ⟨e, he, -⟩ := H (ULift.{v} B) (Q.symm e₀) (he₀.map Q.symm)
  refine ⟨E e, he.1.map E, ?_⟩
  have h := congrArg Q he.2
  rw [Q.apply_symm_apply] at h
  simpa only [Q, Ideal.quotientEquiv_mk, AlgEquiv.coe_toRingEquiv] using h

private theorem factorization_of_lifting
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Polynomial R) (hf : f.Monic)
    (H : ∀ e₀ : AdjoinRoot f ⧸ (maximalIdeal R).map (algebraMap R (AdjoinRoot f)),
      IsIdempotentElem e₀ → ∃ e : AdjoinRoot f, IsIdempotentElem e ∧
        Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (AdjoinRoot f))) e = e₀)
    (g₀ h₀ : Polynomial (ResidueField R)) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hc : IsCoprime g₀ h₀) (hfac : f.map (residue R) = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ := by
  open Polynomial in
  exact by
    obtain ⟨a, b, hab⟩ := hc
    let p₀ := b * h₀
    obtain ⟨p, hp⟩ := Polynomial.map_surjective (residue R) residue_surjective p₀
    let I := (maximalIdeal R).map (algebraMap R (AdjoinRoot f))
    let E := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) f
    let e₀ := Ideal.Quotient.mk I (AdjoinRoot.mk f p)
    have he₀ : IsIdempotentElem e₀ := by
      apply E.injective
      rw [map_mul]
      change (AdjoinRoot.mk (f.map (residue R)) (p.map (residue R))) *
        (AdjoinRoot.mk (f.map (residue R)) (p.map (residue R))) =
          AdjoinRoot.mk (f.map (residue R)) (p.map (residue R))
      rw [hp, ← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
      refine ⟨-(a * b), ?_⟩
      dsimp [p₀]
      rw [hfac]
      linear_combination (b * h₀) * hab
    obtain ⟨e, he, heq⟩ := H e₀ he₀
    have hmaps (q : (ResidueField R)[X]) (hq : q ∣ f.map (residue R)) :
        AdjoinRoot.map (residue R) f q hq e = AdjoinRoot.mk q p₀ := by
      let φ := AdjoinRoot.map (residue R) f q hq
      have hker : I ≤ RingHom.ker φ := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change φ (algebraMap R (AdjoinRoot f) r) = 0
        simp only [φ, AdjoinRoot.algebraMap_eq, AdjoinRoot.map_of]
        change AdjoinRoot.of q (Ideal.Quotient.mk (maximalIdeal R) r) = 0
        rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hr, map_zero]
      have h := congrArg (Ideal.Quotient.lift I φ hker) heq
      change φ e = φ (AdjoinRoot.mk f p) at h
      rw [h]
      change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk f p) = _
      rw [AdjoinRoot.lift_mk]
      rw [← Polynomial.eval₂_map]
      rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, hp]
    have he₁ : AdjoinRoot.map (residue R) f g₀
        (hfac.symm ▸ dvd_mul_right g₀ h₀) e = 1 := by
      rw [hmaps]
      have h := congrArg (AdjoinRoot.mk g₀) hab
      simpa [p₀, map_add, map_mul, AdjoinRoot.mk_self] using h
    have he₀' : AdjoinRoot.map (residue R) f h₀
        (hfac.symm ▸ dvd_mul_left h₀ g₀) e = 0 := by
      rw [hmaps]
      simp [p₀, map_mul, AdjoinRoot.mk_self]
    have hI : maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) := by
      rw [Ideal.jacobson, le_sInf_iff]
      rintro J ⟨-, hJ⟩
      exact (eq_maximalIdeal hJ).ge
    exact Polynomial.exists_monic_factorization_of_idempotent
      (maximalIdeal R) hI f hf g₀ h₀ hg₀ hh₀ ⟨a, b, hab⟩ hfac e he he₁ he₀'

/-- For a local ring, unique lifting of idempotents in every finite algebra modulo the
extended maximal ideal is equivalent to lifting simple residue-field roots of monic
polynomials. The left side spells out the idempotent formulation of
`def-weil-pbc-henselian-terminology`; the right side is the residue-field condition in
`HenselianLocalRing.TFAE`.
Source: Stacks Project, Algebra, Tags 04GF and 04GG, and More on Algebra, Tags 09XE and 09XI
(blueprint: lem-weil-pbc-henselian-local-root-lifting).

Proof:
1. Idempotent lifts are unique for every finite algebra B over a local ring R. For two
   lifts e and e', d = e - e' lies in mB and satisfies d^3 = d. The ideal mB lies in the
   Jacobson radical by lem-weil-pbc-finite-algebra-local-radical. Thus 1 - d^2 is a unit,
   and d(1 - d^2) = 0 forces d = 0.
2. Assume idempotents lift. For a monic f and a simple residue root a₀, write its reduction
   as (T - a₀)h₀, with h₀(a₀) nonzero. The Chinese remainder theorem splits the quotient
   by this reduction into the linear factor and its complement. The algebra S = R[T]/(f)
   is finite free and has this residue quotient by lem-weil-pbc-monic-quotient-free.
   Lift the idempotent selecting the linear factor. Its factor A = eS is a finite flat
   direct summand, hence free by lem-weil-pbc-finite-flat-local-free. Its residue algebra
   is κ, so its rank is one. Its unit e is a basis: its coefficient in any basis is a
   unit since e has nonzero residue. Hence the structure map R → A is an isomorphism.
   The image a of T under R[T] → S → A ≅ R satisfies f(a) = 0 and has residue a₀.
3. Assume simple roots lift. By lem-weil-pbc-root-lifting-etale-retraction, each étale
   algebra with a prime over m inducing an isomorphism of residue fields has a unique
   R-algebra retraction whose inverse image of m is that prime (Stacks 04GG (1) ⇒ (8)).
4. By lem-weil-pbc-etale-retraction-finite-product-local, these retractions imply that
   every finite algebra B is a finite product of local rings (Stacks 04GG (8) ⇒ (10)).
5. Each local factor Bᵢ is finite over R, so mBᵢ is contained in its maximal ideal by
   lem-weil-pbc-finite-algebra-local-radical. Thus Bᵢ/mBᵢ is nonzero and local. Reduction
   of the finite product is the product of these quotients. In a local ring an
   idempotent is zero or one, since one of e and 1 - e is a unit and e(1 - e) = 0.
   Every residue idempotent is therefore a zero/one vector and lifts by the same vector
   in the product B. Step 1 gives uniqueness. The empty product includes the zero algebra.
   This proves the converse and hence the equivalence. -/
theorem idempotent_lifting_iff_monic_simple_root_lifting
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B],
      ∀ e₀ : B ⧸ (maximalIdeal R).map (algebraMap R B),
        IsIdempotentElem e₀ →
          ∃! e : B, IsIdempotentElem e ∧
            Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) e = e₀) ↔
      (∀ f : Polynomial R, f.Monic → ∀ a₀ : ResidueField R,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ f.derivative ≠ 0 →
          ∃ a : R, f.IsRoot a ∧ residue R a = a₀) := by
  open Polynomial in
  exact by
    constructor
    · intro H f hf a₀ ha₀ ha₀'
      let f₀ := f.map (residue R)
      have hroot : f₀.IsRoot a₀ := by
        simpa [f₀, Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using ha₀
      have hder : f₀.derivative.eval a₀ ≠ 0 := by
        simpa [f₀, Polynomial.derivative_map, Polynomial.aeval_def, Polynomial.eval_map] using ha₀'
      have hfac : f₀ = (X - C a₀) * (f₀ /ₘ (X - C a₀)) :=
        (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
      have hmonic : (f₀ /ₘ (X - C a₀)).Monic :=
        (monic_X_sub_C a₀).of_mul_monic_left (hfac ▸ hf.map (residue R))
      have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
      obtain ⟨g, h, hg, -, hgh, hgm, -⟩ := factorization_of_lifting f hf
        (lift_idempotent_small R H (AdjoinRoot f)) (X - C a₀) (f₀ /ₘ (X - C a₀))
        (monic_X_sub_C a₀) hmonic
        (Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero f₀ a₀ hder) hfac
      have hdeg : g.natDegree = 1 := by
        rw [← hg.natDegree_map (residue R), hgm, natDegree_X_sub_C]
      refine ⟨-g.coeff 0, ?_, ?_⟩
      · rw [Polynomial.IsRoot, hgh, Polynomial.eval_mul, hg.eq_X_add_C hdeg]
        simp
      · have hc := congrArg (fun p : (ResidueField R)[X] ↦ p.coeff 0) hgm
        simpa using congrArg Neg.neg hc
    · intro H B _ _ _ e₀ he₀
      have : HenselianLocalRing R := ((HenselianLocalRing.TFAE R).out 2 1).mp H
      exact Algebra.existsUnique_isIdempotentElem_of_henselianRing
        R (maximalIdeal R) B e₀ he₀

end IsLocalRing
