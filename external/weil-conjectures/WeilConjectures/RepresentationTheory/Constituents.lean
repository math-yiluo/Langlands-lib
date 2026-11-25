/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.RepresentationTheory.CompositionSeries

/-!
# Comparing the constituents of representations

A *constituent* of a representation `ρ` is an irreducible subquotient `S / U`. The relation
`Representation.ConstituentsLE ρ σ` says that every constituent of `ρ` is equivalent to a
constituent of `σ`. This file proves the standard closure properties of this relation: it passes
along injective and surjective intertwining maps, the constituents of the middle term of a short
exact sequence are constituents of its ends, those of a representation with a finite filtration
are constituents of its graded pieces, and it is compatible with tensor products.

## Main definitions

- `Subrepresentation.quotient`: the quotient representation `V ⧸ U`.
- `Representation.ConstituentsLE`: every constituent of `ρ` is a constituent of `σ`.

## Main results

- `Subrepresentation.exists_subquotient_equiv_of_chain`: an irreducible subquotient of a
  representation with a finite filtration is a subquotient of one of the graded pieces.
- `Representation.ConstituentsLE.of_exact`: constituents of the middle of a short exact sequence.
- `Representation.ConstituentsLE.of_chain`: constituents of a representation with a finite
  filtration are constituents of the graded pieces.
- `Representation.ConstituentsLE.tprod`: `ρ ≤ ρ'` implies `ρ ⊗ σ ≤ ρ' ⊗ σ`.

## Blueprint

- `lemma-tensor-exterior-powers-filtered-representations--3`,
`lemma-tensor-exterior-powers-filtered-representations--1`: the constituents of a filtered
  representation and of a tensor product.
-/

@[expose] public section

open TensorProduct

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The quotient map `V → V ⧸ U` as an intertwining map. -/
noncomputable def mkQ (U : Subrepresentation ρ) : ρ.IntertwiningMap U.quotient :=
  ⟨U.toSubmodule.mkQ, fun _ ↦ rfl⟩

theorem mkQ_surjective (U : Subrepresentation ρ) : Function.Surjective U.mkQ :=
  U.toSubmodule.mkQ_surjective

/-- The inclusion `U → V` as an intertwining map. -/
noncomputable def subtype (U : Subrepresentation ρ) : U.toRepresentation.IntertwiningMap ρ :=
  ⟨U.toSubmodule.subtype, fun _ ↦ rfl⟩

theorem subtype_injective (U : Subrepresentation ρ) : Function.Injective U.subtype :=
  U.toSubmodule.injective_subtype

theorem exact_subtype_mkQ (U : Subrepresentation ρ) : Function.Exact U.subtype U.mkQ := fun y ↦ by
  change U.toSubmodule.mkQ y = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

/-- Every irreducible subquotient `S / U` of `ρ` with `S ≤ F n`, for a chain of
subrepresentations `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n`, is equivalent to a subquotient of one of the steps
`F (i + 1) / F i`. -/
theorem exists_subquotient_equiv_of_chain {n : ℕ} {F : ℕ → Subrepresentation ρ}
    (h0 : F 0 = ⊥) (hF : ∀ i < n, F i ≤ F (i + 1)) {U S : Subrepresentation ρ} (hS : S ≤ F n)
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ i < n, ∃ U' S' : Subrepresentation ((F (i + 1)).subquotient (F i)),
      Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  induction n generalizing U S with
  | zero =>
    have := inf_lt_of_isIrreducible hirr
    rw [h0, le_bot_iff] at hS
    subst hS
    exact absurd this (by simp)
  | succ n ih =>
    by_cases h : F n ⊓ S ≤ U
    · -- the subquotient survives in `F (n + 1) / F n`
      let π : (F (n + 1)).toRepresentation.IntertwiningMap ((F (n + 1)).subquotient (F n)) :=
        ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
      let ι : (F (n + 1)).toRepresentation.IntertwiningMap ρ := ⟨Submodule.subtype _, fun _ ↦ rfl⟩
      let e₁ : ((comap ι S).subquotient (comap ι U)).Equiv (S.subquotient U) :=
        subquotientEquivOfIntertwiningMap ι (fun _ hx ↦ hx) (fun _ _ hx ↦ hx) (fun _ _ hx ↦ hx)
          fun y hy ↦ ⟨⟨y, hS hy⟩, hy, (congrArg (· ∈ U) (sub_self y)).mpr U.toSubmodule.zero_mem⟩
      have hinj (x) (hxS : x ∈ comap ι S) (hx : π x ∈ map π (comap ι U ⊓ comap ι S)) :
          x ∈ comap ι U := by
        obtain ⟨u, hu, hux⟩ := mem_map.1 hx
        have hxu : ((x - u : (F (n + 1)).toSubmodule) : V) ∈ F n := by
          have : π (x - u) = 0 := by rw [map_sub, hux, sub_self]
          exact (Submodule.Quotient.mk_eq_zero
            ((F n).toSubmodule.comap (F (n + 1)).toSubmodule.subtype)).1 this
        have hxuS : ((x - u : (F (n + 1)).toSubmodule) : V) ∈ S :=
          S.toSubmodule.sub_mem hxS (mem_inf.1 hu).2
        have hu' : (u : V) ∈ U := (mem_inf.1 hu).1
        have := U.toSubmodule.add_mem (h (mem_inf.2 ⟨hxu, hxuS⟩)) hu'
        rwa [Submodule.coe_sub, sub_add_cancel] at this
      let e₂ : ((comap ι S).subquotient (comap ι U)).Equiv
          ((map π (comap ι S)).subquotient (map π (comap ι U ⊓ comap ι S))) :=
        subquotientEquivOfIntertwiningMap π (fun x hx ↦ mem_map.2 ⟨x, hx, rfl⟩)
          (fun x hxS hxU ↦ mem_map.2 ⟨x, mem_inf.2 ⟨hxU, hxS⟩, rfl⟩) hinj fun y hy ↦ by
            obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
            exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩
      exact ⟨n, Nat.lt_succ_self n, _, _, ⟨e₂.symm.trans e₁⟩⟩
    · -- the subquotient comes from `F n`
      let e : ((F n ⊓ S).subquotient U).Equiv (S.subquotient U) :=
        subquotientEquivOfIntertwiningMap (.id ρ) (fun _ hx ↦ (mem_inf.1 hx).2) (fun _ _ hx ↦ hx)
          (fun _ _ hx ↦ hx) fun y hy ↦ exists_mem_inf_sub_mem_of_isIrreducible hirr h hy
      obtain ⟨i, hi, U', S', ⟨e'⟩⟩ := ih (fun i hi ↦ hF i (by omega)) inf_le_left
        (e.isIrreducible_iff.2 hirr)
      exact ⟨i, by omega, U', S', ⟨e'.trans e⟩⟩

/-- Every irreducible subquotient `S / U` of `ρ` with `S ≤ P 0`, for a decreasing chain of
subrepresentations `P 0 ≥ P 1 ≥ ⋯ ≥ P n = 0`, is equivalent to a subquotient of one of the steps
`P j / P (j + 1)`. -/
theorem exists_subquotient_equiv_of_antitone_chain {n : ℕ} {P : ℕ → Subrepresentation ρ}
    (hn : P n = ⊥) (hP : ∀ j < n, P (j + 1) ≤ P j) {U S : Subrepresentation ρ} (hS : S ≤ P 0)
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ j < n, ∃ U' S' : Subrepresentation ((P j).subquotient (P (j + 1))),
      Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  obtain ⟨i, hi, U', S', ⟨e⟩⟩ := exists_subquotient_equiv_of_chain (F := fun i ↦ P (n - i))
    (n := n) (by rw [Nat.sub_zero, hn]) (fun i hi ↦ by
      have h : n - i = n - (i + 1) + 1 := by omega
      rw [h]
      exact hP _ (by omega)) (by rwa [Nat.sub_self]) hirr
  have key (a b : ℕ) (ha : a = n - (i + 1)) (hb : b = n - i) :
      ∃ U' S' : Subrepresentation ((P a).subquotient (P b)),
        Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
    subst ha hb
    exact ⟨U', S', ⟨e⟩⟩
  exact ⟨n - (i + 1), by omega, key _ _ rfl (by omega)⟩

end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
  {V V' V'' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V''] [Module k V'']

/-- Every constituent (irreducible subquotient) of `ρ` is equivalent to a constituent of `σ`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--3`) -/
def ConstituentsLE (ρ : Representation k W V) (σ : Representation k W V') : Prop :=
  ∀ U S : Subrepresentation ρ, (S.subquotient U).IsIrreducible →
    ∃ U' S' : Subrepresentation σ, (S'.subquotient U').IsIrreducible ∧
      Nonempty ((S.subquotient U).Equiv (S'.subquotient U'))

namespace ConstituentsLE

variable {ρ : Representation k W V} {σ : Representation k W V'} {τ : Representation k W V''}

theorem refl (ρ : Representation k W V) : ConstituentsLE ρ ρ := fun U S h ↦
  ⟨U, S, h, ⟨Equiv.refl _⟩⟩

theorem trans (h₁ : ConstituentsLE ρ σ) (h₂ : ConstituentsLE σ τ) : ConstituentsLE ρ τ :=
  fun U S h ↦ by
    obtain ⟨U', S', h', ⟨e⟩⟩ := h₁ U S h
    obtain ⟨U'', S'', h'', ⟨e'⟩⟩ := h₂ U' S' h'
    exact ⟨U'', S'', h'', ⟨e.trans e'⟩⟩

/-- The constituents of `ρ` are constituents of `σ` if `ρ` embeds into `σ`. -/
theorem of_injective (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    ConstituentsLE ρ σ := fun U S h ↦
  let e := (Subrepresentation.subquotientMapEquiv f hf U S).symm
  ⟨_, _, e.isIrreducible_iff.1 h, ⟨e⟩⟩

/-- The constituents of `σ` are constituents of `ρ` if `σ` is a quotient of `ρ`. -/
theorem of_surjective (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    ConstituentsLE σ ρ := fun U S h ↦ by
  let e := Subrepresentation.subquotientComapEquiv f hf U S
  exact ⟨_, _, e.isIrreducible_iff.2 h, ⟨e.symm⟩⟩

theorem of_equiv (e : ρ.Equiv σ) : ConstituentsLE ρ σ :=
  of_injective e.toIntertwiningMap e.injective

/-- The constituents of a subquotient `S / U` are constituents of `ρ`. -/
theorem subquotient (U S : Subrepresentation ρ) : ConstituentsLE (S.subquotient U) ρ :=
  (of_surjective (σ := S.subquotient U) (ρ := S.toRepresentation) ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
    (Submodule.mkQ_surjective _)).trans (of_injective S.subtype S.subtype_injective)

/-- **Constituents of a short exact sequence.** If `σ₁ → ρ → σ₂` is exact, every constituent
of `ρ` is a constituent of `σ₁` or of `σ₂`. -/
theorem of_exact {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {σ₁ : Representation k W V₁} {σ₂ : Representation k W V₂} (f : σ₁.IntertwiningMap ρ)
    (g : ρ.IntertwiningMap σ₂) (hexact : Function.Exact f g)
    (h₁ : ConstituentsLE σ₁ τ) (h₂ : ConstituentsLE σ₂ τ) : ConstituentsLE ρ τ := by
  intro U S hirr
  by_cases h : f.range ⊓ S ≤ U
  · -- the constituent survives in `σ₂`
    have hinj (x) (hxS : x ∈ S) (hx : g x ∈ Subrepresentation.map g (U ⊓ S)) : x ∈ U := by
      obtain ⟨u, hu, hux⟩ := Subrepresentation.mem_map.1 hx
      have hxu : x - u ∈ f.range := (hexact (x - u)).1 (by rw [map_sub, hux, sub_self])
      have := h (Subrepresentation.mem_inf.2
        ⟨hxu, S.toSubmodule.sub_mem hxS (Subrepresentation.mem_inf.1 hu).2⟩)
      have hx := U.toSubmodule.add_mem this (Subrepresentation.mem_inf.1 hu).1
      rwa [sub_add_cancel] at hx
    let e := (Subrepresentation.subquotientEquivOfIntertwiningMap g
      (U' := Subrepresentation.map g (U ⊓ S)) (S' := Subrepresentation.map g S)
      (fun x hx ↦ Subrepresentation.mem_map.2 ⟨x, hx, rfl⟩)
      (fun x hxS hxU ↦ Subrepresentation.mem_map.2 ⟨x, Subrepresentation.mem_inf.2 ⟨hxU, hxS⟩,
        rfl⟩) hinj
      fun y hy ↦ by
        obtain ⟨x, hx, rfl⟩ := Subrepresentation.mem_map.1 hy
        exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩)
    obtain ⟨U', S', h', ⟨e'⟩⟩ := h₂ _ _ (e.isIrreducible_iff.1 hirr)
    exact ⟨U', S', h', ⟨e.trans e'⟩⟩
  · -- the constituent comes from `σ₁`
    let e := Subrepresentation.subquotientEquivOfIntertwiningMap f
      (U := Subrepresentation.comap f U) (S := Subrepresentation.comap f S)
      (U' := U) (S' := S) (fun _ hx ↦ hx) (fun _ _ hx ↦ hx) (fun _ _ hx ↦ hx) fun y hy ↦ by
        obtain ⟨x, hx, hxy⟩ := Subrepresentation.exists_mem_inf_sub_mem_of_isIrreducible hirr h hy
        obtain ⟨⟨x', rfl⟩, hxS⟩ := Subrepresentation.mem_inf.1 hx
        exact ⟨x', hxS, hxy⟩
    obtain ⟨U', S', h', ⟨e'⟩⟩ := h₁ _ _ (e.isIrreducible_iff.2 hirr)
    exact ⟨U', S', h', ⟨e.symm.trans e'⟩⟩

/-- The constituents of `ρ` are constituents of a subrepresentation `U` or of the quotient
`V ⧸ U`. -/
theorem of_subrepresentation (U : Subrepresentation ρ) (h₁ : ConstituentsLE U.toRepresentation τ)
    (h₂ : ConstituentsLE U.quotient τ) : ConstituentsLE ρ τ :=
  of_exact U.subtype U.mkQ U.exact_subtype_mkQ h₁ h₂

/-- The zero representation has no constituents. -/
theorem of_subsingleton [Subsingleton V] (ρ : Representation k W V) (σ : Representation k W V') :
    ConstituentsLE ρ σ := fun U S hirr ↦ by
  have := hirr.nontrivial
  obtain ⟨q₁, q₂, hq⟩ := exists_pair_ne (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype)
  induction q₁ using Submodule.Quotient.induction_on with | _ x
  induction q₂ using Submodule.Quotient.induction_on with | _ y
  exact (hq (congrArg _ (Subtype.ext (Subsingleton.elim (x : V) y)))).elim

/-- **Constituents of a filtered representation.** If `0 = F_m ≤ ⋯ ≤ F_1 ≤ F_0 = V` is a finite
decreasing filtration by subrepresentations, every constituent of `ρ` is a constituent of one of
the graded pieces `F_j ⧸ F_{j+1}`. (blueprint:
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem of_chain (F : ℕ → Subrepresentation ρ) (hF : ∀ j, F (j + 1) ≤ F j) (h0 : F 0 = ⊤)
    {m : ℕ} (hm : F m = ⊥) (h : ∀ j < m, ConstituentsLE ((F j).subquotient (F (j + 1))) τ) :
    ConstituentsLE ρ τ := fun U S hirr ↦ by
  obtain ⟨j, hj, U', S', ⟨e⟩⟩ := Subrepresentation.exists_subquotient_equiv_of_antitone_chain hm
    (fun j _ ↦ hF j) (h0 ▸ le_top) hirr
  obtain ⟨U'', S'', h'', ⟨e'⟩⟩ := h j hj U' S' (e.isIrreducible_iff.2 hirr)
  exact ⟨U'', S'', h'', ⟨e.symm.trans e'⟩⟩

/-- An equivalence `ρ ≅ ρ'` induces `ρ ⊗ σ ≅ ρ' ⊗ σ`. -/
noncomputable def _root_.Representation.Equiv.rTensor {V₁ : Type*} [AddCommGroup V₁] [Module k V₁]
    {ρ₁ : Representation k W V₁} (e : ρ.Equiv ρ₁) (σ : Representation k W V'') :
    (ρ.tprod σ).Equiv (ρ₁.tprod σ) :=
  Equiv.mk (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k V'')) fun w ↦ by
    refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, tprod_apply,
      TensorProduct.map_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    congr 1
    exact e.apply_apply w x

/-- **Constituents of a tensor product.** If every constituent of `ρ` is a constituent of `ρ'`,
then every constituent of `ρ ⊗ σ` is a constituent of `ρ' ⊗ σ`: a constituent of `ρ ⊗ σ` is a
subquotient of `A ⊗ σ` for a constituent `A` of `ρ`, and `A' ⊗ σ` is a subquotient of `ρ' ⊗ σ`
for a constituent `A'` of `ρ'`. (blueprint:
`lemma-tensor-exterior-powers-filtered-representations--1`) -/
theorem tprod_left [FiniteDimensional k V] (h : ConstituentsLE ρ σ) (τ : Representation k W V'') :
    ConstituentsLE (ρ.tprod τ) (σ.tprod τ) := by
  intro U S hirr
  obtain ⟨UV, SV, -, hV, U₁, S₁, ⟨e₁⟩⟩ := Subrepresentation.exists_subquotient_tprod_left_equiv hirr
  obtain ⟨U₂, S₂, -, ⟨e₂⟩⟩ := h UV SV hV
  -- `A' ⊗ τ` is a subquotient of `σ ⊗ τ`, for the constituent `A' = S₂ / U₂` of `σ`
  let q : S₂.toRepresentation.IntertwiningMap (S₂.subquotient U₂) := ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
  have hq : Function.Surjective (q.rTensor τ) :=
    LinearMap.rTensor_surjective V'' (Submodule.mkQ_surjective _)
  have hi : Function.Injective ((Subrepresentation.subtype S₂).rTensor τ) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Subrepresentation.subtype_injective S₂)
  have hA : ConstituentsLE ((S₂.subquotient U₂).tprod τ) (σ.tprod τ) :=
    (of_surjective _ hq).trans (of_injective _ hi)
  have hB : ConstituentsLE (((SV.subquotient UV)).tprod τ) (σ.tprod τ) :=
    (of_equiv (e₂.rTensor τ)).trans hA
  obtain ⟨U₃, S₃, h₃, ⟨e₃⟩⟩ := hB U₁ S₁ (e₁.isIrreducible_iff.2 hirr)
  exact ⟨U₃, S₃, h₃, ⟨e₁.symm.trans e₃⟩⟩

/-- The symmetric version of `tprod_left`. -/
theorem tprod_right [FiniteDimensional k V] (h : ConstituentsLE ρ σ) (τ : Representation k W V'') :
    ConstituentsLE (τ.tprod ρ) (τ.tprod σ) :=
  ((of_equiv (Representation.TensorProduct.comm τ ρ)).trans (h.tprod_left τ)).trans
    (of_equiv (Representation.TensorProduct.comm σ τ))

end ConstituentsLE

end Representation
