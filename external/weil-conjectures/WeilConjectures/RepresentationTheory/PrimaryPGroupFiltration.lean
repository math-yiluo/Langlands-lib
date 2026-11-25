/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.PGroup
import WeilConjectures.RepresentationTheory.PrimaryInvariantExtension
import Mathlib.Order.Preorder.Finite

/-!
# Filtrations of finite primary modules with a p-group action

Source: Stacks Project, Tags 0GIZ and 0GJ0
(blueprint: lem-sc-primary-pgroup-filtration).
-/

@[expose] public section

universe u v

namespace Representation

/-- A finite primary abelian group with a p-group action has a stable filtration
with trivial quotients killed by the prime.

Proof: Consider the subgroups attainable as endpoints of finite stable chains
starting at zero with trivial successive quotients killed by ℓ. Zero is
attainable by a chain of length zero. Since V is finite, its subgroup lattice is
finite, so an attainable subgroup W maximal for inclusion exists. If W is
proper, `exists_primary_invariant_extension` supplies a strictly larger stable
subgroup W' whose quotient by W is trivial and killed by ℓ. Append W' to the
chain for W, contradicting maximality. Hence the maximal endpoint is the whole
module. Restrict the resulting natural-number indexed chain to `Fin (n + 1)`.
The extension argument works also when V is zero, where no extension is needed.

Source: Stacks Project, Etale Cohomology, Lemma 0GIZ (lemma-action-l-group), and
Lemma 0GJ0 (lemma-pullback-filtered-modules), the finite-module filtration part of the
proof of theorem-cohomology-curves
(blueprint: lem-sc-primary-pgroup-filtration). -/
theorem exists_primary_filtration_of_isPGroup
    (Q : Type u) [Group Q] (ℓ : ℕ) (hℓ : ℓ.Prime) (hQ : IsPGroup ℓ Q)
    (V : Type v) [AddCommGroup V] [Module ℤ V] [Finite V]
    (ρ : Representation ℤ Q V) (hV : IsPGroup ℓ (Multiplicative V)) :
    ∃ (n : ℕ) (F : Fin (n + 1) → AddSubgroup V),
      Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
      (∀ (i : Fin (n + 1)) (g : Q) (x : V), x ∈ F i → ρ g x ∈ F i) ∧
      (∀ (i : Fin n) (x : V), x ∈ F i.succ →
        ℓ • x ∈ F i.castSucc ∧ ∀ g : Q, ρ g x - x ∈ F i.castSucc) := by
  classical
  let : Finite (AddSubgroup V) :=
    Finite.of_injective (fun W : AddSubgroup V ↦ (W : Set V)) SetLike.coe_injective
  let good : AddSubgroup V → Prop := fun W ↦
    ∃ (n : ℕ) (F : ℕ → AddSubgroup V),
      Monotone F ∧ F 0 = ⊥ ∧ F n = W ∧
      (∀ i g x, x ∈ F i → ρ g x ∈ F i) ∧
      (∀ i < n, ∀ x ∈ F (i + 1),
        ℓ • x ∈ F i ∧ ∀ g : Q, ρ g x - x ∈ F i)
  have hbot : good ⊥ := by
    refine ⟨0, fun _ ↦ ⊥, monotone_const, rfl, rfl, ?_, ?_⟩
    · intro i g x hx
      rw [AddSubgroup.mem_bot] at hx ⊢
      rw [hx, map_zero]
    · intro i hi
      omega
  obtain ⟨W, _, hmax⟩ := Finite.exists_le_maximal hbot
  obtain ⟨n, F, hmono, hzero, hend, hstable, hstep⟩ := hmax.1
  have htop : W = ⊤ := by
    by_contra hne
    have hW : ∀ g : Q, ∀ x : V, x ∈ W → ρ g x ∈ W := by
      intro g x hx
      rw [← hend] at hx ⊢
      exact hstable n g x hx
    obtain ⟨W', hlt, hW', hquot⟩ :=
      exists_primary_invariant_extension Q ℓ hℓ hQ V ρ hV W hW hne
    let F' : ℕ → AddSubgroup V := fun i ↦ if i ≤ n then F i else W'
    have hgood : good W' := by
      refine ⟨n + 1, F', ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        dsimp [F']
        split_ifs with hi hj hj
        · exact hmono hij
        · exact (hmono hi).trans (hend ▸ hlt.le)
        · omega
        · exact le_rfl
      · simp [F', hzero]
      · simp [F']
      · intro i g x hx
        dsimp [F'] at hx ⊢
        split_ifs at hx ⊢ with hi
        · exact hstable i g x hx
        · exact hW' g x hx
      · intro i hi x hx
        by_cases hin : i < n
        · have hi0 : i ≤ n := by omega
          have hi1 : i + 1 ≤ n := by omega
          simpa only [F', ite_eq_left hi0, ite_eq_left hi1] using
            hstep i hin x (by simpa only [F', ite_eq_left hi1] using hx)
        · have hieq : i = n := by omega
          subst i
          have hx' : x ∈ W' := by simpa [F'] using hx
          simpa [F', hend] using hquot x hx'
    exact (not_le_of_gt hlt) (hmax.2 hgood hlt.le)
  refine ⟨n, fun i ↦ F i.val, ?_, hzero, hend.trans htop, ?_, ?_⟩
  · intro i j hij
    exact hmono hij
  · intro i g x hx
    exact hstable i.val g x hx
  · intro i x hx
    exact hstep i.val i.isLt x hx

end Representation
