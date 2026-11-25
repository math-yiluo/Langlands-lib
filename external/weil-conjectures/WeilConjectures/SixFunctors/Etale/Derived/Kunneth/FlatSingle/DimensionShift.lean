/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Dimension shifting for a morphism of functors into an abelian category

Let `S_q, T_q : C ⥤ D` (`q : ℤ`) be families of functors and `τ_q : S_q ⟶ T_q`. Assume that the
`S_q` are exact on a class of short exact sequences, that the `T_q` have connecting maps making
them half exact on these sequences, that `τ_q` is an isomorphism in negative degrees, and that
every object `X` of a class `P` embeds, by a sequence of the class, into a good object (at which
all `τ_q` are isomorphisms) with cokernel in `P`. Then all `τ_q` are isomorphisms at the objects of
`P` (`CategoryTheory.isIso_app_of_dimensionShift`). This is the dimension shifting argument of the
proof of blueprint `lemma-kunneth-field-coefficients--1`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {D : Type*} [Category D] [Abelian D]

/-- **The epimorphism step of dimension shifting.** Given a commutative diagram

```
S'P --a--> S'Q
 |τP'       |τQ'
T'P --b--> T'Q --δ--> T X --ti--> T P --tπ--> T Q
                       ^τX         ^τP          ^τQ
                      S X --si--> S P --sπ--> S Q
```

with `b ≫ δ = 0`, `(δ, ti)` exact, `ti ≫ tπ = 0`, `(si, sπ)` exact, `a`, `τQ'` and `τP` epi and
`τQ` mono, the map `τX` is an epimorphism. -/
lemma epi_of_dimensionShift {SX SP SQ TX TP TQ S'P S'Q T'P T'Q : D}
    (si : SX ⟶ SP) (sπ : SP ⟶ SQ) (ti : TX ⟶ TP) (tπ : TP ⟶ TQ) (a : S'P ⟶ S'Q)
    (b : T'P ⟶ T'Q) (δ : T'Q ⟶ TX) (τX : SX ⟶ TX) (τP : SP ⟶ TP) (τQ : SQ ⟶ TQ)
    (τP' : S'P ⟶ T'P) (τQ' : S'Q ⟶ T'Q) (hsw : si ≫ sπ = 0)
    (hS : (ShortComplex.mk si sπ hsw).Exact) (htw : ti ≫ tπ = 0) (hδw : δ ≫ ti = 0)
    (hδ : (ShortComplex.mk δ ti hδw).Exact) (hbδ : b ≫ δ = 0)
    (n₁ : si ≫ τP = τX ≫ ti) (n₂ : sπ ≫ τQ = τP ≫ tπ) (n₃ : a ≫ τQ' = τP' ≫ b)
    [Epi a] [Epi τQ'] [Epi τP] [Mono τQ] : Epi τX := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A y
  obtain ⟨A₁, π₁, _, s, h₁⟩ := surjective_up_to_refinements_of_epi τP (y ≫ ti)
  have h₂ : s ≫ sπ = 0 := by
    rw [← cancel_mono τQ, Category.assoc, n₂, ← reassoc_of% h₁, htw, comp_zero, comp_zero,
      zero_comp]
  obtain ⟨A₂, π₂, _, s', h₃⟩ := hS.exact_up_to_refinements s h₂
  dsimp at s' h₃
  have h₄ : (π₂ ≫ π₁ ≫ y - s' ≫ τX) ≫ ti = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, Category.assoc, ← n₁, h₁,
      ← reassoc_of% h₃, sub_self]
  obtain ⟨A₃, π₃, _, t, h₅⟩ := hδ.exact_up_to_refinements _ h₄
  dsimp at t h₅
  obtain ⟨A₄, π₄, _, u, h₆⟩ := surjective_up_to_refinements_of_epi τQ' t
  obtain ⟨A₅, π₅, _, v, h₇⟩ := surjective_up_to_refinements_of_epi a u
  have h₈ : π₅ ≫ π₄ ≫ π₃ ≫ (π₂ ≫ π₁ ≫ y - s' ≫ τX) = 0 := by
    rw [h₅, reassoc_of% h₆, reassoc_of% h₇, reassoc_of% n₃, hbδ, comp_zero, comp_zero]
  refine ⟨A₅, π₅ ≫ π₄ ≫ π₃ ≫ π₂ ≫ π₁, inferInstance, π₅ ≫ π₄ ≫ π₃ ≫ s', ?_⟩
  rw [Preadditive.comp_sub, Preadditive.comp_sub, Preadditive.comp_sub, sub_eq_zero] at h₈
  simpa only [Category.assoc] using h₈

/-- **Dimension shifting.** Let `τ_q : S_q ⟶ T_q` (`q : ℤ`) be morphisms of functors `C ⥤ D`, `D`
abelian. Assume that `τ_q` is an isomorphism at the objects of a class `P` for `q < 0` and at the
objects of a class `G` for all `q`, and that every `X` in `P` has a sequence `X ⟶ P₀ ⟶ Q` with
`P₀` in `G` and `Q` in `P` which `S_q` sends to short exact sequences and for which `T` has
connecting maps `δ : T_{q-1} Q ⟶ T_q X` with `T_{q-1}(π) ≫ δ = 0` and `(δ, T_q(i))` exact. Then
`τ_q` is an isomorphism at every object of `P`, for every `q`. -/
theorem isIso_app_of_dimensionShift {C : Type*} [Category C] [HasZeroMorphisms C]
    (P G : ObjectProperty C) (S T : ℤ → C ⥤ D) [∀ q, (S q).PreservesZeroMorphisms]
    [∀ q, (T q).PreservesZeroMorphisms] (τ : ∀ q, S q ⟶ T q)
    (hneg : ∀ q < 0, ∀ X, P X → IsIso ((τ q).app X))
    (hG : ∀ q X, G X → IsIso ((τ q).app X))
    (hemb : ∀ X, P X → ∃ (P₀ Q : C) (i : X ⟶ P₀) (π : P₀ ⟶ Q) (hw : i ≫ π = 0), G P₀ ∧ P Q ∧
      ∀ q : ℤ, Mono ((S q).map i) ∧ Epi ((S q).map π) ∧
        (ShortComplex.mk ((S q).map i) ((S q).map π)
          (by rw [← Functor.map_comp, hw, Functor.map_zero])).Exact ∧
        ∃ (δ : (T (q - 1)).obj Q ⟶ (T q).obj X) (hδ : δ ≫ (T q).map i = 0),
          (T (q - 1)).map π ≫ δ = 0 ∧ (ShortComplex.mk δ _ hδ).Exact) :
    ∀ q X, P X → IsIso ((τ q).app X) := by
  suffices H : ∀ n : ℕ, ∀ q : ℤ, q < n → ∀ X, P X → IsIso ((τ q).app X) from
    fun q X hX ↦ H (q.toNat + 1) q (by lia) X hX
  intro n
  induction n with
  | zero => exact fun q hq X hX ↦ hneg q (by simpa using hq) X hX
  | succ n ih =>
    intro q hq
    by_cases hqn : q < n
    · exact ih q hqn
    have hmono (Y : C) (hY : P Y) : Mono ((τ q).app Y) := by
      obtain ⟨P₀, Q, i, π, hw, hP₀, -, hq'⟩ := hemb Y hY
      have := hG q P₀ hP₀
      have := (hq' q).1
      have : Mono ((τ q).app Y ≫ (T q).map i) := by
        rw [← (τ q).naturality i]
        infer_instance
      exact mono_of_mono ((τ q).app Y) ((T q).map i)
    intro X hX
    have := hmono X hX
    obtain ⟨P₀, Q, i, π, hw, hP₀, hQ, hq'⟩ := hemb X hX
    obtain ⟨-, -, hS, -⟩ := hq' q
    obtain ⟨-, hπ', -, -⟩ := hq' (q - 1)
    obtain ⟨-, -, -, δ, hδw, hbδ, hδ⟩ := hq' q
    have := hG q P₀ hP₀
    have := hmono Q hQ
    have := ih (q - 1) (by lia) Q hQ
    have : Epi ((τ q).app X) := epi_of_dimensionShift ((S q).map i) ((S q).map π)
      ((T q).map i) ((T q).map π) ((S (q - 1)).map π) ((T (q - 1)).map π) δ ((τ q).app X)
      ((τ q).app P₀) ((τ q).app Q) ((τ (q - 1)).app P₀) ((τ (q - 1)).app Q) _ hS
      (by rw [← Functor.map_comp, hw, Functor.map_zero]) hδw hδ hbδ ((τ q).naturality i)
      ((τ q).naturality π) ((τ (q - 1)).naturality π)
    exact isIso_of_mono_of_epi _

/-- **Comparison of right exact functors.** Let `α : Φ₁ ⟶ Φ₂` be a morphism of functors
`C ⥤ D` between abelian categories which send short exact sequences `K ⟶ P ⟶ X` to right exact
sequences `Φ K ⟶ Φ P ⟶ Φ X ⟶ 0`. If `α` is an isomorphism at the objects of a class `G` and every
object is a quotient of an object of `G`, then `α` is an isomorphism. -/
theorem isIso_app_of_rightExact {C : Type*} [Category C] [Abelian C] (Φ₁ Φ₂ : C ⥤ D)
    [Φ₁.PreservesZeroMorphisms] [Φ₂.PreservesZeroMorphisms] (α : Φ₁ ⟶ Φ₂) (G : ObjectProperty C)
    (hG : ∀ X, G X → IsIso (α.app X)) (hepi : ∀ X, ∃ (P : C) (π : P ⟶ X), G P ∧ Epi π)
    (hR₁ : ∀ (S : ShortComplex C), S.ShortExact → Epi (Φ₁.map S.g) ∧ (S.map Φ₁).Exact)
    (hR₂ : ∀ (S : ShortComplex C), S.ShortExact → Epi (Φ₂.map S.g) ∧ (S.map Φ₂).Exact)
    (X : C) : IsIso (α.app X) := by
  have hep (Y : C) : Epi (α.app Y) := by
    obtain ⟨P, π, hP, _⟩ := hepi Y
    have := hG P hP
    have := (hR₂ (ShortComplex.mk (kernel.ι π) π (kernel.condition π))
      (ShortComplex.ShortExact.mk' (S := ShortComplex.mk (kernel.ι π) π _)
        (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)) inferInstance inferInstance)).1
    have : Epi (Φ₁.map π ≫ α.app Y) := by
      rw [α.naturality]
      infer_instance
    exact epi_of_epi (Φ₁.map π) _
  obtain ⟨P, π, hP, _⟩ := hepi X
  have := hG P hP
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
      inferInstance inferInstance
  obtain ⟨h₁e, h₁⟩ := hR₁ S hS
  obtain ⟨-, h₂⟩ := hR₂ S hS
  have := hep (kernel π)
  have : Mono (α.app X) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨A₁, π₁, _, p, e₁⟩ := surjective_up_to_refinements_of_epi (Φ₁.map π) x
    have e₂ : (p ≫ α.app P) ≫ Φ₂.map π = 0 := by
      rw [Category.assoc, ← α.naturality, ← reassoc_of% e₁, hx, comp_zero]
    obtain ⟨A₂, π₂, _, k₂, e₃⟩ := h₂.exact_up_to_refinements (p ≫ α.app P) e₂
    obtain ⟨A₃, π₃, _, k, e₄⟩ := surjective_up_to_refinements_of_epi (α.app (kernel π)) k₂
    have e₅ : π₃ ≫ π₂ ≫ p = k ≫ Φ₁.map (kernel.ι π) := by
      rw [← cancel_mono (α.app P)]
      simp only [Category.assoc]
      rw [e₃, reassoc_of% e₄]
      exact congrArg _ (α.naturality _).symm
    have e₆ : (π₃ ≫ π₂ ≫ π₁) ≫ x = 0 := by
      rw [Category.assoc, Category.assoc, e₁, ← Category.assoc π₂, ← Category.assoc π₃, e₅,
        Category.assoc, ← Φ₁.map_comp, kernel.condition, Φ₁.map_zero, comp_zero]
    rwa [← cancel_epi (π₃ ≫ π₂ ≫ π₁), comp_zero]
  exact isIso_of_mono_of_epi _

end CategoryTheory
