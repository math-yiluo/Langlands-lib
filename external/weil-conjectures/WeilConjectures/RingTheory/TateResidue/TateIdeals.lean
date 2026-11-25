/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TateResidue.FinitePotent

/-!
# Tate's ideals of endomorphisms attached to a subspace

Let `V` be a vector space over a field `k` and `A ⊆ V` a subspace. Following Tate (*Residues of
differentials on curves*, §1) we consider, for endomorphisms `φ` of `V`:

- `E A φ`: `φ(A) ⊆ A + W` for a finite-dimensional `W` (written `φ A ≺ A`);
- `E₁ A φ`: `φ(V) ⊆ A + W` for a finite-dimensional `W`;
- `E₂ A φ`: `φ(A)` is finite-dimensional.

`E` is a subalgebra of `End_k V`, `E₁` and `E₂` are ideals of `E` (with `E₁` a right ideal and
`E₂` a left ideal of `End_k V`), and every element of `E₀ = E₁ ∩ E₂` is finite-potent. Tate's
trace is additive on `E₀`, and `Tr [φ, ψ] = 0` if `φ ∈ E₀, ψ ∈ E` or `φ ∈ E₁, ψ ∈ E₂`.

## Main definitions

- `Submodule.AlmostLE X Y`: `X ⊆ Y + W` for some finite-dimensional `W`.
- `TateResidue.E`, `TateResidue.E₁`, `TateResidue.E₂`.

## Main results

- `TateResidue.tateTrace_add_of_mem`: additivity of the trace on `E₀`.
- `TateResidue.tateTrace_commutator_eq_zero`, `TateResidue.tateTrace_commutator_eq_zero'`.
-/

@[expose] public section

open LinearMap Module.End

namespace Submodule

variable {k V V₂ : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup V₂]
  [Module k V₂]

/-- `X` is *almost contained* in `Y`: `X ⊆ Y + W` for a finite-dimensional subspace `W`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
def AlmostLE (X Y : Submodule k V) : Prop :=
  ∃ W : Submodule k V, W.FG ∧ X ≤ Y ⊔ W

/-- If the image of `N` under `q` is finitely generated, then `N ⊆ ker q + W` for a finitely
generated `W`. -/
lemma exists_fg_le_ker_sup {M : Type*} [AddCommGroup M] [Module k M] (q : V →ₗ[k] M)
    {N : Submodule k V} (h : (N.map q).FG) : ∃ W : Submodule k V, W.FG ∧ N ≤ ker q ⊔ W := by
  obtain ⟨S, hS⟩ := h
  have hmem : ∀ s : S, ∃ n ∈ N, q n = s := fun s ↦ by
    have : (s : M) ∈ N.map q := hS ▸ subset_span s.2
    simpa using this
  choose g hgN hg using hmem
  refine ⟨span k (Set.range g), fg_span (Set.finite_range g), fun x hx ↦ ?_⟩
  have hmap : (span k (Set.range g)).map q = N.map q := by
    rw [map_span, ← hS, ← Set.range_comp]
    congr 1
    ext m
    simp [hg]
  obtain ⟨w, hw, hqw⟩ : q x ∈ (span k (Set.range g)).map q := hmap ▸ mem_map_of_mem hx
  have : x = (x - w) + w := by abel
  rw [this]
  exact add_mem_sup (by simp [hqw]) hw

namespace AlmostLE

variable {X X' Y Z W : Submodule k V}

lemma of_le (h : X ≤ Y) : X.AlmostLE Y := ⟨⊥, fg_bot, by simpa using h⟩

@[refl]
lemma refl (X : Submodule k V) : X.AlmostLE X := of_le le_rfl

lemma of_fg (hX : X.FG) : X.AlmostLE Y := ⟨X, hX, le_sup_right⟩

lemma trans (h₁ : X.AlmostLE Y) (h₂ : Y.AlmostLE Z) : X.AlmostLE Z := by
  obtain ⟨W₁, hW₁, h₁⟩ := h₁
  obtain ⟨W₂, hW₂, h₂⟩ := h₂
  exact ⟨W₂ ⊔ W₁, hW₂.sup hW₁, h₁.trans ((sup_le_sup_right h₂ W₁).trans (sup_assoc _ _ _).le)⟩

lemma mono_left (h : X' ≤ X) (hX : X.AlmostLE Y) : X'.AlmostLE Y := (of_le h).trans hX

lemma mono_right (hX : X.AlmostLE Y) (h : Y ≤ Z) : X.AlmostLE Z := hX.trans (of_le h)

lemma sup (h₁ : X.AlmostLE Z) (h₂ : Y.AlmostLE Z) : (X ⊔ Y).AlmostLE Z := by
  obtain ⟨W₁, hW₁, h₁⟩ := h₁
  obtain ⟨W₂, hW₂, h₂⟩ := h₂
  refine ⟨W₁ ⊔ W₂, hW₁.sup hW₂, sup_le (h₁.trans ?_) (h₂.trans ?_)⟩
  · exact sup_le_sup_left le_sup_left _
  · exact sup_le_sup_left le_sup_right _

lemma sup_fg (hX : X.AlmostLE Y) (hW : W.FG) : (X ⊔ W).AlmostLE Y := hX.sup (of_fg hW)

lemma map (f : V →ₗ[k] V₂) (h : X.AlmostLE Y) : (X.map f).AlmostLE (Y.map f) := by
  obtain ⟨W, hW, h⟩ := h
  exact ⟨W.map f, hW.map f, (map_mono h).trans (Submodule.map_sup _ _ _).le⟩

lemma comap (f : V₂ →ₗ[k] V) (h : X.AlmostLE Y) : (X.comap f).AlmostLE (Y.comap f) := by
  obtain ⟨W, hW, h⟩ := h
  have hfg : ((Y ⊔ W).comap f |>.map (Y.mkQ ∘ₗ f)).FG := by
    refine (hW.map Y.mkQ).of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, w, hw, hyw⟩ := mem_sup.1 (mem_comap.1 hx)
    refine ⟨w, hw, ?_⟩
    simp only [mkQ_apply, comp_apply, ← hyw, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero Y).2 hy, zero_add]
  obtain ⟨W', hW', hle⟩ := exists_fg_le_ker_sup _ hfg
  refine ⟨W', hW', (comap_mono h).trans (hle.trans ?_)⟩
  rw [ker_comp, ker_mkQ]

lemma prod {X₂ Y₂ : Submodule k V₂} (h₁ : X.AlmostLE Y) (h₂ : X₂.AlmostLE Y₂) :
    (X.prod X₂).AlmostLE (Y.prod Y₂) := by
  obtain ⟨W₁, hW₁, h₁⟩ := h₁
  obtain ⟨W₂, hW₂, h₂⟩ := h₂
  exact ⟨W₁.prod W₂, hW₁.prod hW₂, (prod_mono h₁ h₂).trans (prod_sup_prod _ _ _ _).ge⟩

end AlmostLE

end Submodule

namespace TateResidue

open Submodule

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (A : Submodule k V)

/-- Tate's algebra `E`: endomorphisms `φ` with `φ(A) ≺ A`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
def E (φ : Module.End k V) : Prop := (A.map φ).AlmostLE A

/-- Tate's ideal `E₁`: endomorphisms `φ` with `φ(V) ≺ A`. -/
def E₁ (φ : Module.End k V) : Prop := (range φ).AlmostLE A

/-- Tate's ideal `E₂`: endomorphisms `φ` with `φ(A)` finite-dimensional. -/
def E₂ (φ : Module.End k V) : Prop := (A.map φ).FG

variable {A} {φ ψ θ : Module.End k V}

lemma map_mul (φ ψ : Module.End k V) : A.map (φ * ψ) = (A.map ψ).map φ := by
  rw [mul_eq_comp, map_comp]

lemma range_mul (φ ψ : Module.End k V) : range (φ * ψ) = (range ψ).map φ := by
  rw [mul_eq_comp, range_comp]

lemma map_add_le' (φ ψ : Module.End k V) : A.map (φ + ψ) ≤ A.map φ ⊔ A.map ψ := by
  rintro _ ⟨x, hx, rfl⟩
  exact add_mem_sup (mem_map_of_mem hx) (mem_map_of_mem hx)

lemma map_smul_le' (c : k) (φ : Module.End k V) : A.map (c • φ) ≤ A.map φ := by
  rintro _ ⟨x, hx, rfl⟩
  exact smul_mem _ c (mem_map_of_mem hx)

lemma map_neg' (φ : Module.End k V) : A.map (-φ) = A.map φ := by
  ext y
  constructor <;>
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, A.neg_mem hx, by simp⟩

lemma range_add_le' (φ ψ : Module.End k V) : range (φ + ψ) ≤ range φ ⊔ range ψ := by
  simp only [range_eq_map]; exact map_add_le' φ ψ

lemma range_smul_le' (c : k) (φ : Module.End k V) : range (c • φ) ≤ range φ := by
  simp only [range_eq_map]; exact map_smul_le' c φ

lemma range_neg' (φ : Module.End k V) : range (-φ) = range φ := by
  simp only [range_eq_map]; exact map_neg' φ

namespace E

lemma one : E A 1 := by rw [E, Module.End.one_eq_id, map_id]

lemma zero : E A 0 := by simp [E, AlmostLE.of_fg fg_bot]

lemma add (hφ : E A φ) (hψ : E A ψ) : E A (φ + ψ) := (hφ.sup hψ).mono_left (map_add_le' φ ψ)

lemma smul (c : k) (hφ : E A φ) : E A (c • φ) := hφ.mono_left (map_smul_le' c φ)

lemma neg (hφ : E A φ) : E A (-φ) := by rw [E, map_neg']; exact hφ

lemma sub (hφ : E A φ) (hψ : E A ψ) : E A (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

lemma mul (hφ : E A φ) (hψ : E A ψ) : E A (φ * ψ) := by
  rw [E, map_mul]; exact (hψ.map φ).trans hφ

end E

namespace E₁

lemma toE (hφ : E₁ A φ) : E A φ := hφ.mono_left (map_le_range)

lemma zero : E₁ A 0 := by simp [E₁, AlmostLE.of_fg fg_bot]

lemma of_fg (hφ : (range φ).FG) : E₁ A φ := AlmostLE.of_fg hφ

lemma of_le (hφ : range φ ≤ A) : E₁ A φ := AlmostLE.of_le hφ

lemma add (hφ : E₁ A φ) (hψ : E₁ A ψ) : E₁ A (φ + ψ) :=
  (hφ.sup hψ).mono_left (range_add_le' φ ψ)

lemma smul (c : k) (hφ : E₁ A φ) : E₁ A (c • φ) := hφ.mono_left (range_smul_le' c φ)

lemma neg (hφ : E₁ A φ) : E₁ A (-φ) := by rw [E₁, range_neg']; exact hφ

lemma sub (hφ : E₁ A φ) (hψ : E₁ A ψ) : E₁ A (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

lemma mul_left (hθ : E A θ) (hφ : E₁ A φ) : E₁ A (θ * φ) := by
  rw [E₁, range_mul]; exact (hφ.map θ).trans hθ

lemma mul_right (hφ : E₁ A φ) (θ : Module.End k V) : E₁ A (φ * θ) := by
  rw [E₁, mul_eq_comp]; exact hφ.mono_left (range_comp_le_range _ _)

end E₁

namespace E₂

lemma toE (hφ : E₂ A φ) : E A φ := AlmostLE.of_fg hφ

lemma zero : E₂ A 0 := by simp [E₂, fg_bot]

lemma of_fg (hφ : (range φ).FG) : E₂ A φ := hφ.of_le map_le_range

lemma add (hφ : E₂ A φ) (hψ : E₂ A ψ) : E₂ A (φ + ψ) := (hφ.sup hψ).of_le (map_add_le' φ ψ)

lemma smul (c : k) (hφ : E₂ A φ) : E₂ A (c • φ) := hφ.of_le (map_smul_le' c φ)

lemma neg (hφ : E₂ A φ) : E₂ A (-φ) := by rw [E₂, map_neg']; exact hφ

lemma sub (hφ : E₂ A φ) (hψ : E₂ A ψ) : E₂ A (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

lemma mul_left (θ : Module.End k V) (hφ : E₂ A φ) : E₂ A (θ * φ) := by
  rw [E₂, map_mul]; exact hφ.map θ

lemma mul_right (hφ : E₂ A φ) (hθ : E A θ) : E₂ A (φ * θ) := by
  obtain ⟨W, hW, h⟩ := hθ
  rw [E₂, map_mul]
  exact (hφ.sup (hW.map φ)).of_le ((map_mono h).trans (Submodule.map_sup _ _ _).le)

end E₂

/-- The product of an element of `E₂` and an element of `E₁` has finite-dimensional range. -/
lemma fg_range_mul (hφ : E₂ A φ) (hψ : E₁ A ψ) : (range (φ * ψ)).FG := by
  obtain ⟨W, hW, h⟩ := hψ
  rw [range_mul]
  exact (hφ.sup (hW.map φ)).of_le ((map_mono h).trans (Submodule.map_sup _ _ _).le)

/-- Elements of `E₀ = E₁ ∩ E₂` are finite-potent. -/
lemma isFinitePotent_of_mem (hφ₁ : E₁ A φ) (hφ₂ : E₂ A φ) : φ.IsFinitePotent :=
  ⟨2, by rw [sq]; exact fg_range_mul hφ₂ hφ₁⟩

/-- Additivity of Tate's trace on `E₀`. -/
theorem tateTrace_add_of_mem (hφ₁ : E₁ A φ) (hφ₂ : E₂ A φ) (hψ₁ : E₁ A ψ) (hψ₂ : E₂ A ψ) :
    (φ + ψ).tateTrace = φ.tateTrace + ψ.tateTrace :=
  tateTrace_add (fg_range_mul hφ₂ hφ₁) (fg_range_mul hφ₂ hψ₁) (fg_range_mul hψ₂ hφ₁)
    (fg_range_mul hψ₂ hψ₁)

theorem tateTrace_sub_of_mem (hφ₁ : E₁ A φ) (hφ₂ : E₂ A φ) (hψ₁ : E₁ A ψ) (hψ₂ : E₂ A ψ) :
    (φ - ψ).tateTrace = φ.tateTrace - ψ.tateTrace := by
  rw [sub_eq_add_neg, tateTrace_add_of_mem hφ₁ hφ₂ hψ₁.neg hψ₂.neg, tateTrace_neg, sub_eq_add_neg]

/-- **Tate**: `Tr [φ, ψ] = 0` for `φ ∈ E₀` and `ψ ∈ E`. -/
theorem tateTrace_commutator_eq_zero (hφ₁ : E₁ A φ) (hφ₂ : E₂ A φ) (hψ : E A ψ) :
    (φ * ψ - ψ * φ).tateTrace = 0 := by
  have h₁ : E₁ A (φ * ψ) := hφ₁.mul_right ψ
  have h₂ : E₂ A (φ * ψ) := hφ₂.mul_right hψ
  have h₃ : E₁ A (ψ * φ) := hφ₁.mul_left hψ
  have h₄ : E₂ A (ψ * φ) := hφ₂.mul_left ψ
  rw [tateTrace_sub_of_mem h₁ h₂ h₃ h₄, sub_eq_zero, mul_eq_comp, mul_eq_comp,
    tateTrace_comp_comm ψ φ (by rw [← mul_eq_comp]; exact isFinitePotent_of_mem h₁ h₂)]

/-- **Tate**: `Tr [φ, ψ] = 0` for `φ ∈ E₁` and `ψ ∈ E₂`. -/
theorem tateTrace_commutator_eq_zero' (hφ : E₁ A φ) (hψ : E₂ A ψ) :
    (φ * ψ - ψ * φ).tateTrace = 0 := by
  have h₁ : E₁ A (φ * ψ) := hφ.mul_right ψ
  have h₂ : E₂ A (φ * ψ) := hψ.mul_left φ
  have h₃ : E₁ A (ψ * φ) := E₁.of_fg (fg_range_mul hψ hφ)
  have h₄ : E₂ A (ψ * φ) := hψ.mul_right hφ.toE
  rw [tateTrace_sub_of_mem h₁ h₂ h₃ h₄, sub_eq_zero, mul_eq_comp, mul_eq_comp,
    tateTrace_comp_comm ψ φ (by rw [← mul_eq_comp]; exact isFinitePotent_of_mem h₁ h₂)]

end TateResidue
