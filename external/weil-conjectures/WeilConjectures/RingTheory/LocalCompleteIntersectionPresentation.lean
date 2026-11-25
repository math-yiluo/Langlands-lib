/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Logic.Equiv.Fin.Basic
import WeilConjectures.RingTheory.LocalGeneratorsClearing
import WeilConjectures.RingTheory.QuotientAwayClearing
import WeilConjectures.RingTheory.EquationCountLocalizePresentation

/-!
# Presentation of a principal localization from a local regular sequence

The construction is the presentation part of Stacks Project Lemma 00SC.
-/

@[expose] public section

universe u

namespace Algebra

/-- (blueprint: lem-weil-pbc-lci-regular-sequence-global-complete-intersection-presentation)
Local generators of an ideal in a polynomial ring give a presentation with one extra
variable on a principal neighborhood, and on every further principal localization.
Source: Stacks Project, Algebra, Lemma 00SC, (2) implies (1), clearing denominators
and the presentation by adjoining an inverse variable. Regularity and dimensions
are not used in this algebraic construction.

Proof: put P = k[x_1,...,x_n], S = P/I and p = the inverse image of q.
Since each h_i belongs to I P_p, write h_i = F_i/s_i with F_i in I and s_i
outside p. Multiplication by the units s_i shows that the F_i generate I P_p.
The ideal I is finitely generated because P is Noetherian. For each generator u_j
of I, clear denominators in an expression of u_j/1 in the localized ideal (F_i).
Equality in the localization supplies a further factor outside p, giving v_j u_j
in (F_i) for some v_j outside p. Set A = product v_j, with empty product one.
Then A is outside p, (F_i) is contained in I, and A I is contained in (F_i).
Let a be the image of A in S. For any b in S, lift b to B in P and put G = A B.
The evaluation P[x] → S_(a*b), with x mapping to the inverse of a*b, is surjective
and has kernel I P[x] + (Gx-1). This follows from the coefficient-map kernel and
the presentation S[x]/((a*b)x-1) of the localization. Its kernel equals
(F_1,...,F_e,Gx-1): for u in I, the identity
u = -u(Gx-1) + x B (A u) puts u in that ideal, and the reverse inclusion is immediate.
The first isomorphism theorem gives the required k-algebra equivalence. Rename the
n old variables and the inverse variable by Fin (n+1), and the e old relations and
the inverse relation by Fin (e+1). This argument also works for b = 0 and for e = 0. -/
theorem exists_principal_localization_presentation_of_local_generators
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) (hq : q.IsPrime)
    (e : ℕ) (h : Fin e → Localization.AtPrime (q.comap
      (Ideal.Quotient.mk I)))
    (hgen : Ideal.map
      (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))) I =
      Ideal.span (Set.range h)) :
    ∃ a : (MvPolynomial (Fin n) k ⧸ I), a ∉ q ∧
      ∀ b : (MvPolynomial (Fin n) k ⧸ I),
        ∃ f : Fin (e + 1) → MvPolynomial (Fin (n + 1)) k,
          Nonempty ((MvPolynomial (Fin (n + 1)) k ⧸
            Ideal.span (Set.range f)) ≃ₐ[k] Localization.Away (a * b)) := by
  classical
  let : q.IsPrime := hq
  let p := q.comap (Ideal.Quotient.mk I)
  obtain ⟨F, A, hA, hFI, hclear⟩ :=
    Ideal.exists_clearing_of_local_generators I p e h hgen
  let J := Ideal.span (Set.range F)
  have hJI : J ≤ I := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hFI i)
  refine ⟨Ideal.Quotient.mk I A, hA, ?_⟩
  intro b
  obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul]
  obtain ⟨comparison⟩ :=
    Ideal.nonempty_quotient_away_equiv_of_clearing (k := k) J I hJI A B hclear
  obtain ⟨pres, _, _⟩ := exists_localization_presentation k n e F (A * B)
  let rel : Option (Fin e) → MvPolynomial (Option (Fin n)) k :=
    Option.elim' (MvPolynomial.rename some (A * B) * MvPolynomial.X none - 1)
      (fun i ↦ MvPolynomial.rename some (F i))
  let ren := MvPolynomial.renameEquiv k (finSuccEquiv n).symm
  let f : Fin (e + 1) → MvPolynomial (Fin (n + 1)) k :=
    fun i ↦ ren (rel (finSuccEquiv e i))
  have hrange : Set.range f = ren '' Set.range rel := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rel (finSuccEquiv e i), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨(finSuccEquiv e).symm i, by simp [f]⟩
  have hmap : Ideal.span (Set.range f) =
      Ideal.map ren.toRingHom (Ideal.span (Set.range rel)) := by
    rw [Ideal.map_span]
    exact congrArg Ideal.span hrange
  let reindex := Ideal.quotientEquivAlg (Ideal.span (Set.range rel))
    (Ideal.span (Set.range f)) ren hmap
  refine ⟨f, ⟨?_⟩⟩
  exact reindex.symm.trans (pres.trans comparison)

end Algebra
