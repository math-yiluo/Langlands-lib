/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Unramified.Basic
import WeilConjectures.RingTheory.UniversalFirstOrderThickeningCore
import WeilConjectures.RingTheory.UniversalFirstOrderThickeningUniqueness

/-!
# Universal first order thickenings of formally unramified algebras

Source: Stacks Project, Algebra, Lemma 04EB and the uniqueness remark in Section 04EA
(blueprint: lem-weil-pbc-ring-universal-first-order-thickening).
-/

@[expose] public section

universe u

namespace Algebra

/-- A formally unramified algebra admits a universal square-zero thickening, unique up to
unique algebra isomorphism over the given algebra. Source: Stacks Project, Algebra, Lemma
04EB and the following uniqueness remark in Section 04EA
(blueprint: lem-weil-pbc-ring-universal-first-order-thickening).

Proof:
1. Present `S` as `P/J`, where `P` is the polynomial algebra on generators indexed by `S`
   (def-weil-pbc-mv-polynomial-ring). The presentation map is surjective. Modules killed
   by `J`, and maps between them, descend to `S`.
2. The conormal map `d : J/J² → S ⊗[P] Ω[P/R]` is surjective by the differential exact
   sequence (lem-weil-pbc-jacobi-zariski-differential-maps) and vanishing of `Ω[S/R]`
   (lem-weil-pbc-formally-unramified-ring-iff-kahler-zero).
3. The target is free on the differentials of the variables
   (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables). Choose preimages of this
   basis to split `d`. Let `J'` be the inverse image in `J` of the splitting's image.
   Then `J² ⊆ J' ⊆ J`, and `d` restricts to an isomorphism from `J'/J²` to its target.
4. Set `S' = P/J'`. The induced surjection to `S` has kernel `J/J'`, whose square is zero.
5. For a square-zero ideal `I` of `A` and `a : S → A/I`, lift the images of the variables
   to obtain `β : P → A`. Other lifts differ from `β` by an `R`-derivation into `I`:
   square-zero makes the difference satisfy Leibniz, and conversely adding a derivation
   preserves multiplication. By def-weil-pbc-kahler-differentials these are parametrized
   by `S`-linear maps `φ : S ⊗[P] Ω[P/R] → I`.
6. The obstruction to annihilating `J'` is the `S`-linear map `βbar : J'/J² → I`.
   The modified lift annihilates `J'` exactly when `βbar + φ ∘ d = 0` on `J'/J²`.
   Since the restriction of `d` is an isomorphism, exactly one `φ` satisfies this.
   Factoring this lift through `P/J'` gives the required unique lift.
7. For two such thickenings, apply each lifting property to the other thickening with
   its kernel ideal, using the inverse of the quotient-to-`S` isomorphism. This gives
   unique algebra maps in both directions over `S`. Their composites and the identity
   are lifts of the same maps, so uniqueness makes the maps inverse. This also proves
   uniqueness of the compatible algebra equivalence. -/
theorem exists_universalFirstOrderThickening
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [FormallyUnramified R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (π : S' →ₐ[R] S),
      Function.Surjective π ∧ RingHom.ker π.toRingHom ^ 2 = ⊥ ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
        ∀ a : S →ₐ[R] A ⧸ I,
          ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T] (πT : T →ₐ[R] S),
        Function.Surjective πT → RingHom.ker πT.toRingHom ^ 2 = ⊥ →
        (∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
          ∀ a : S →ₐ[R] A ⧸ I,
            ∃! a' : T →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp πT) →
        ∃! e : S' ≃ₐ[R] T, πT.comp e.toAlgHom = π) := by
  obtain ⟨S', instCR, instAlg, π, hsurj, hker, hprop⟩ :=
    exists_universalFirstOrderThickening_core R S
  let : CommRing S' := instCR
  let : Algebra R S' := instAlg
  refine ⟨S', inferInstance, inferInstance, π, hsurj, hker, hprop, ?_⟩
  intro T _ _ πT hπT hkerT hT
  exact universalFirstOrderThickening_unique R S S' π hsurj hker hprop T πT hπT hkerT hT

end Algebra
