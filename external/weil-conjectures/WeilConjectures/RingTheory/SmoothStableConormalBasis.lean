/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import WeilConjectures.RingTheory.SmoothStableConormalBasisAux
import WeilConjectures.RingTheory.PresentationLocalizedConormalSplit

/-!
# A polynomial presentation with a basis of its localized conormal module

Source: Stacks Project, Tag 07EZ, proof of part (e), preparation of the presentation
(blueprint: lem-weil-pbc-smooth-stable-conormal-basis).
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra

/-- Stabilize a polynomial presentation so that the first relations give a basis of its
localized conormal module.

Source: Stacks Project, Tag 07EZ, proof of part (e), first paragraph through the choice of
`f₁, ..., f_c` and their extension to generators
(blueprint: lem-weil-pbc-smooth-stable-conormal-basis).

Proof: the input equivalence makes the localized conormal module stably free.
Adjoin `r` polynomial variables mapping to zero. The new conormal module is the old one
plus `A^r`: constant terms in the new variables and their linear coefficients give this
isomorphism, with products of kernel elements mapping to zero. After localization this
module is finite free. Lift its basis to kernel elements and multiply each vector by a
power of the now invertible element to clear its denominator. Append a finite generating
family of the kernel. Reindex the variables and relations by finite ordinals with these
basis elements first. The number of basis elements is at most the number of variables:
the split conormal injection, reduced modulo a maximal ideal, is an injection of vector
spaces. If the localization is the zero ring, use the empty basis instead. The number of
relations is at least the number of initial basis elements by construction. -/
theorem exists_presentation_localized_conormal_basis
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A) [Smooth R (Localization.Away a)]
    {n₀ m₀ : ℕ} (P₀ : Presentation R A (Fin n₀) (Fin m₀)) (r q : ℕ)
    (hstable : Nonempty
      (((Localization.Away a ⊗[A] P₀.toExtension.Cotangent) ×
        (Fin r → Localization.Away a)) ≃ₗ[Localization.Away a]
        (Fin q → Localization.Away a))) :
    ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m)) (hc : c ≤ min n m)
      (b : Module.Basis (Fin c) (Localization.Away a)
        (Localization.Away a ⊗[A] P.toExtension.Cotangent)),
      ∀ j : Fin c, b j = 1 ⊗ₜ[A]
        (Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j),
            P.relation_mem_ker _⟩) := by
  classical
  cases subsingleton_or_nontrivial (Localization.Away a) with
  | inl hzero =>
    let b : Module.Basis (Fin 0) (Localization.Away a)
        (Localization.Away a ⊗[A] P₀.toExtension.Cotangent) := Module.Basis.empty _
    refine ⟨n₀, m₀, 0, P₀, Nat.zero_le _, b, ?_⟩
    intro j
    exact Fin.elim0 j
  | inr hnonzero =>
    obtain ⟨m, P, hqm, b, hb⟩ :=
      exists_stabilized_presentation_localized_conormal_basis R A a P₀ r q hstable
    obtain ⟨e⟩ := P.localized_conormal_equiv a
    let f := e.toLinearMap.comp
      (LinearMap.inl (Localization.Away a)
        (Localization.Away a ⊗[A] P.toExtension.Cotangent)
        (KaehlerDifferential R (Localization.Away a)))
    have hf : Function.Injective f := e.injective.comp LinearMap.inl_injective
    have hqn : q ≤ n₀ + r := by
      simpa using
        (Pi.basisFun (Localization.Away a) (Fin (n₀ + r))).card_le_card_of_linearIndependent
          (b.linearIndependent.map_injOn f hf.injOn)
    have hc : q ≤ min (n₀ + r) m := Nat.le_min.mpr ⟨hqn, hqm⟩
    refine ⟨n₀ + r, m, q, P, hc, b, ?_⟩
    intro j
    simpa using hb j

end Algebra
