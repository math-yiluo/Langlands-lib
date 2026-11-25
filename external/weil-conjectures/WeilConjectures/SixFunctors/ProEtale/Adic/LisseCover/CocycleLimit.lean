/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Trivialising a cocycle as a limit of finite-level trivialisations

Let `X` be a topological space and `p₁ p₂ : Z → X` two maps, to be thought of as the two
projections `V ×_T V ⇉ V` of a cover `V → T` (on underlying points). A function `g : Z → H` to a
group `H` is a "cocycle", and for a subgroup `K` of `H` a *section of the twisted `H ⧸ K`-sheaf*
(`IsCocycleSection`) is a locally constant `σ : X → H ⧸ K` with `σ (p₁ z) = g z • σ (p₂ z)`.

Suppose `H` comes with a decreasing sequence of subgroups `K 0 ≥ K 1 ≥ ⋯` such that

* only finitely many cosets of `K k` meet `K 0` (for `H = GL_n(E)` and the congruence subgroups
  `K k = 1 + ℓᵏ M_n(𝒪_E)` this is the finiteness of `GL_n(𝒪_E / ℓᵏ)`);
* `H` is complete and separated for the `K k`: compatible sequences of cosets have a unique limit;

that two sections of the twisted `H ⧸ K k`-sheaf which agree at one point agree everywhere (a
connectedness hypothesis, `hconn`), and that at every level there is a section through the
trivial coset at a given point (`hsec`). Then König's lemma (for the finite, nonempty sets of
sections at the levels `k` through cosets meeting `K 0`) and the completeness of `H` give a
function `σ : X → H` with `σ (p₁ z) = g z * σ (p₂ z)`, whose reductions modulo every `K k` are
locally constant (`exists_cocycle_trivialization`).

This is the limit argument of Bhatt–Scholze (*The pro-étale topology for schemes*, proof of
Lemma 7.4.10) that turns the triviality of the finite-level reductions `L / ℓᵏ` of a lisse
`𝒪_E`-sheaf into the triviality of the `E`-sheaf itself, in cocycle form.
-/

@[expose] public section

open CategoryTheory

namespace CocycleTrivialization

variable {X Z H : Type*} [TopologicalSpace X] [Group H] (p₁ p₂ : Z → X) (g : Z → H)

/-- A *section of the twisted `H ⧸ K`-sheaf* defined by the cocycle `g`: a locally constant
function `σ : X → H ⧸ K` with `σ (p₁ z) = g z • σ (p₂ z)` for all `z`. -/
def IsCocycleSection (K : Subgroup H) (σ : X → H ⧸ K) : Prop :=
  IsLocallyConstant σ ∧ ∀ z, σ (p₁ z) = g z • σ (p₂ z)

variable {p₁ p₂ g}

/-- Reducing a section along an inclusion of subgroups `K ≤ K'` gives a section. -/
lemma IsCocycleSection.map {K K' : Subgroup H} (h : K ≤ K') {σ : X → H ⧸ K}
    (hσ : IsCocycleSection p₁ p₂ g K σ) :
    IsCocycleSection p₁ p₂ g K' (Subgroup.quotientMapOfLE h ∘ σ) := by
  refine ⟨hσ.1.comp _, fun z ↦ ?_⟩
  simp only [Function.comp_apply, hσ.2 z]
  induction σ (p₂ z) using QuotientGroup.induction_on with
  | H a => rfl

/-- **Uniqueness of sections.** If every locally constant `Bool`-valued function on `X` which is
invariant under `p₁ z ↦ p₂ z` is constant, then two sections which agree at one point agree. -/
lemma IsCocycleSection.eq_of_apply_eq
    (hconn : ∀ τ : X → Bool, IsLocallyConstant τ → (∀ z, τ (p₁ z) = τ (p₂ z)) →
      ∀ x x', τ x = τ x')
    {K : Subgroup H} {σ σ' : X → H ⧸ K} (hσ : IsCocycleSection p₁ p₂ g K σ)
    (hσ' : IsCocycleSection p₁ p₂ g K σ') {x : X} (h : σ x = σ' x) : σ = σ' := by
  classical
  have := hconn (fun x ↦ decide (σ x = σ' x)) (hσ.1.comp₂ hσ'.1 fun a b ↦ decide (a = b))
    (fun z ↦ by
    simp only [hσ.2 z, hσ'.2 z, smul_left_cancel_iff])
  funext x'
  simpa [h] using (this x x').symm

/-- **A cocycle with finite-level trivialisations is trivial.** Let `K 0 ≥ K 1 ≥ ⋯` be subgroups
of `H` such that only finitely many cosets of `K k` meet `K 0`, and such that `H` is complete and
separated for the `K k`. If sections of the twisted `H ⧸ K k`-sheaves are determined by their
value at one point (`hconn`) and exist through the trivial coset at every point (`hsec`), then
there is `σ : X → H` with `σ (p₁ z) = g z * σ (p₂ z)` whose reductions modulo every `K k` are
locally constant. -/
theorem exists_cocycle_trivialization (K : ℕ → Subgroup H) (hK : ∀ k, K (k + 1) ≤ K k)
    (hfin : ∀ k, (QuotientGroup.mk '' (K 0 : Set H) : Set (H ⧸ K k)).Finite)
    (hcompl : ∀ b : ℕ → H, (∀ k, (b k)⁻¹ * b (k + 1) ∈ K k) → ∃ c, ∀ k, (b k)⁻¹ * c ∈ K k)
    (hsep : ∀ a : H, (∀ k, a ∈ K k) → a = 1)
    (hconn : ∀ τ : X → Bool, IsLocallyConstant τ → (∀ z, τ (p₁ z) = τ (p₂ z)) →
      ∀ x x', τ x = τ x')
    (hsec : ∀ k x, ∃ σ, IsCocycleSection p₁ p₂ g (K k) σ ∧ σ x = ((1 : H) : H ⧸ K k)) :
    ∃ σ : X → H, (∀ k, IsLocallyConstant fun x ↦ ((σ x : H) : H ⧸ K k)) ∧
      ∀ z, σ (p₁ z) = g z * σ (p₂ z) := by
  classical
  by_cases hX : Nonempty X
  swap
  · have : IsEmpty X := not_nonempty_iff.1 hX
    exact ⟨isEmptyElim, fun _ _ ↦ by simp [Set.preimage, Set.eq_empty_of_isEmpty],
      fun z ↦ isEmptyElim (p₁ z)⟩
  obtain ⟨x₀⟩ := hX
  -- the finite nonempty sets of values at `x₀` of sections through cosets meeting `K 0`
  let T (k : ℕ) : Type _ := {q : H ⧸ K k // q ∈ QuotientGroup.mk '' (K 0 : Set H) ∧
    ∃ σ, IsCocycleSection p₁ p₂ g (K k) σ ∧ σ x₀ = q}
  have hTfin (k : ℕ) : Finite (T k) := by
    have := (hfin k).to_subtype
    exact Finite.of_injective (fun q : T k ↦
      (⟨q.1, q.2.1⟩ : (QuotientGroup.mk '' (K 0 : Set H) : Set (H ⧸ K k))))
      fun q q' h ↦ Subtype.ext (by simpa using h)
  have hTne (k : ℕ) : Nonempty (T k) := by
    obtain ⟨σ, hσ, h1⟩ := hsec k x₀
    exact ⟨⟨_, ⟨1, (K 0).one_mem, rfl⟩, σ, hσ, h1⟩⟩
  let r (k : ℕ) : T (k + 1) → T k := fun q ↦ ⟨Subgroup.quotientMapOfLE (hK k) q.1, by
    obtain ⟨⟨a, ha, hq⟩, σ, hσ, hσx⟩ := q.2
    refine ⟨⟨a, ha, by rw [← hq]; rfl⟩, _, hσ.map (hK k), ?_⟩
    simp [hσx]⟩
  let F : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (X := T) fun k ↦ TypeCat.ofHom (r k)
  have : ∀ j, Finite (F.obj j) := fun j ↦ hTfin j.unop
  have : ∀ j, Nonempty (F.obj j) := fun j ↦ hTne j.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let t (k : ℕ) : T k := s (Opposite.op k)
  have ht (k : ℕ) : r k (t (k + 1)) = t k := by
    have := hs (homOfLE (Nat.le_add_right k 1)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact this
  choose σ hσ hσx using fun k ↦ (t k).2.2
  -- the sections are compatible
  have hcomp (k : ℕ) : Subgroup.quotientMapOfLE (hK k) ∘ σ (k + 1) = σ k := by
    refine ((hσ (k + 1)).map (hK k)).eq_of_apply_eq hconn (hσ k) (x := x₀) ?_
    simp only [Function.comp_apply, hσx]
    exact congrArg Subtype.val (ht k)
  -- representatives and their limits
  let b (x : X) (k : ℕ) : H := (σ k x).out
  have hb (x : X) (k : ℕ) : ((b x k : H) : H ⧸ K k) = σ k x := QuotientGroup.out_eq' _
  have hbb (x : X) (k : ℕ) : (b x k)⁻¹ * b x (k + 1) ∈ K k := by
    rw [← QuotientGroup.eq, hb, ← Subgroup.quotientMapOfLE_apply_mk (hK k), hb]
    exact (congrFun (hcomp k) x).symm
  choose c hc using fun x ↦ hcompl (b x) (hbb x)
  have hck (x : X) (k : ℕ) : ((c x : H) : H ⧸ K k) = σ k x := by
    rw [← hb, QuotientGroup.eq]
    simpa using (K k).inv_mem (hc x k)
  refine ⟨c, fun k ↦ ?_, fun z ↦ ?_⟩
  · simp only [hck]
    exact (hσ k).1
  · refine inv_mul_eq_one.1 (hsep _ fun k ↦ ?_)
    have h₁ : ((g z * c (p₂ z) : H) : H ⧸ K k) = ((c (p₁ z) : H) : H ⧸ K k) := by
      rw [hck, (hσ k).2 z, ← hck]
      rfl
    have := QuotientGroup.eq.1 h₁
    simpa [mul_assoc] using (K k).inv_mem this

end CocycleTrivialization
