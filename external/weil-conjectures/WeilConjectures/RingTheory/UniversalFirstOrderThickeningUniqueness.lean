/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
/-!
# Uniqueness of universal first order thickenings

Source: Stacks Project, Algebra, Section 04EA, the remark following Lemma 04EB.
(blueprint: lem-weil-pbc-ring-universal-first-order-thickening-uniqueness).
-/
@[expose] public section
universe u
namespace Algebra
/-- Two square-zero thickenings with the universal lifting property are uniquely
isomorphic over the base. Source: Stacks Project, Algebra, Section 04EA, the remark
following Lemma 04EB.
(blueprint: lem-weil-pbc-ring-universal-first-order-thickening-uniqueness).

Proof: For any surjection `q : V → S` with square-zero kernel, the first isomorphism
theorem identifies `V/ker q` with `S`. Apply the lifting property of `U → S` to the
inverse identification. Composing with the identification converts the quotient
equation to `q.comp f = p`, so there is exactly one compatible map `U → V`.
Apply this with `U = S'`, `V = T` and then with `U = T`, `V = S'` to get maps `f`
and `g`. Their composites and the identity are compatible maps over `S`; apply
the same uniqueness with `U = V` to show both composites are identities.
`AlgEquiv.ofAlgHom` supplies the equivalence, and uniqueness of its forward
algebra homomorphism supplies uniqueness of the equivalence. No unramified
hypothesis is needed for this argument. -/
theorem universalFirstOrderThickening_unique
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra R S']
    (π : S' →ₐ[R] S) (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom ^ 2 = ⊥)
    (hprop : ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
      ∀ a : S →ₐ[R] A ⧸ I,
        ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π)
    (T : Type u) [CommRing T] [Algebra R T] (πT : T →ₐ[R] S)
    (hπT : Function.Surjective πT) (hkerT : RingHom.ker πT.toRingHom ^ 2 = ⊥)
    (hT : ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
      ∀ a : S →ₐ[R] A ⧸ I,
        ∃! a' : T →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp πT) :
    ∃! e : S' ≃ₐ[R] T, πT.comp e.toAlgHom = π := by
  classical
  have lift : ∀ (U V : Type u) [CommRing U] [CommRing V] [Algebra R U]
      [Algebra R V] (p : U →ₐ[R] S),
      (∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
        ∀ a : S →ₐ[R] A ⧸ I,
          ∃! a' : U →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp p) →
      ∀ (q : V →ₐ[R] S), Function.Surjective q → RingHom.ker q.toRingHom ^ 2 = ⊥ →
        ∃! f : U →ₐ[R] V, q.comp f = p := by
    intro U V _ _ _ _ p hp q hq hk
    let e := Ideal.quotientKerAlgEquivOfSurjective hq
    have cond (f : U →ₐ[R] V) :
        (Ideal.Quotient.mkₐ R (RingHom.ker q.toRingHom)).comp f =
          e.symm.toAlgHom.comp p ↔ q.comp f = p := by
      constructor
      · intro hf
        ext x
        have hx := congrArg e (AlgHom.congr_fun hf x)
        change e (Ideal.Quotient.mk _ (f x)) = e (e.symm (p x)) at hx
        rw [AlgEquiv.apply_symm_apply] at hx
        exact hx
      · intro hf
        ext x
        apply e.injective
        change e (Ideal.Quotient.mk _ (f x)) = e (e.symm (p x))
        rw [AlgEquiv.apply_symm_apply]
        exact AlgHom.congr_fun hf x
    obtain ⟨f, hf, hu⟩ := hp V (RingHom.ker q.toRingHom) hk e.symm.toAlgHom
    exact ⟨f, (cond f).mp hf, fun g hg ↦ hu g ((cond g).mpr hg)⟩
  obtain ⟨f, hf, hfu⟩ := lift S' T π hprop πT hπT hkerT
  obtain ⟨g, hg, hgu⟩ := lift T S' πT hT π hπ hker
  have hgf : g.comp f = AlgHom.id R S' := by
    obtain ⟨i, hi, hui⟩ := lift S' S' π hprop π hπ hker
    apply (hui _ _).trans (hui _ _).symm
    · rw [← AlgHom.comp_assoc, hg, hf]
    · simp
  have hfg : f.comp g = AlgHom.id R T := by
    obtain ⟨i, hi, hui⟩ := lift T T πT hT πT hπT hkerT
    apply (hui _ _).trans (hui _ _).symm
    · rw [← AlgHom.comp_assoc, hf, hg]
    · simp
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, hf, ?_⟩
  intro e he
  apply AlgEquiv.coe_toAlgHom_injective
  exact hfu e.toAlgHom he
end Algebra
