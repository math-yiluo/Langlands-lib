/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.RepresentationTheory.Filtration

/-!
# Filtrations of the contragredient representation

Let `ρ` be a representation of a group `W` on a `k`-vector space `V`, and `ρ^∨ = ρ.dual` its
contragredient on `V^∨ = Hom_k(V, k)`. A subrepresentation `U ≤ V` has an *annihilator*
`U^⊥ ≤ V^∨`, again a subrepresentation, and `U ↦ U^⊥` reverses inclusions. For `U ≤ S` the
subquotient `U^⊥ / S^⊥` of `ρ^∨` is the contragredient of the subquotient `S / U`: a linear form
on `S / U` is a linear form on `S` vanishing on `U`, and extends to `V` because `k` is a field.

Consequently a finite filtration `0 = F₀ ≤ ⋯ ≤ F_m = V` induces the filtration
`0 = F_m^⊥ ≤ ⋯ ≤ F₀^⊥ = V^∨` of `ρ^∨`, whose graded pieces are the contragredients of the graded
pieces of `F`, and the constituents of `ρ^∨` are the contragredients of those of `ρ`. This is the
case of the dual in part L3 (tensor filtration) of the linear-algebra library
`lemma-tensor-exterior-powers-filtered-representations--3`; the cases of tensor products and
exterior powers are `Representation.HasGradedPieces.tprod_left`,
`Representation.CompositionSeries.hasGradedPieces_tprod` and
`Representation.CompositionSeries.hasGradedPieces_exteriorPower`.

The annihilator `Subrepresentation.dualAnnihilator` and the equivalence
`Subrepresentation.subquotientDualEquiv : U^⊥ / S^⊥ ≅ (S / U)^∨` are in
`WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation`, and
`Representation.IsIrreducible.dual` is in
`WeilConjectures.Mathlib.RepresentationTheory.Irreducible`.

## Main results

- `Representation.HasGradedPieces.dual`: the dual filtration of the contragredient has as graded
  pieces the contragredients of the graded pieces.
- `Representation.CompositionSeries.exists_equiv_dual`: the composition factors of `ρ^∨` are the
  contragredients of the composition factors of `ρ`, with multiplicities.
- `Representation.ConstituentsLE.dual`: if every constituent of `ρ` is a constituent of `σ`, then
  every constituent of `ρ^∨` is a constituent of `σ^∨`.
-/

@[expose] public section

namespace Representation

namespace HasGradedPieces

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V} {ι : Type*} {X : ι → Type*} [∀ i, AddCommGroup (X i)]
  [∀ i, Module k (X i)] {τ : ∀ i, Representation k W (X i)}

/-- **The dual filtration.** If `ρ` has a finite filtration with graded pieces equivalent to the
`τ i`, then the annihilators of the filtration form a finite filtration of the contragredient
`ρ^∨` whose graded pieces are equivalent to the contragredients `τ i ^∨`.
(blueprint: part L3 of `lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem dual (h : HasGradedPieces ρ fun i ↦ EquivTo (τ i)) :
    HasGradedPieces ρ.dual fun i ↦ EquivTo (τ i).dual := by
  obtain ⟨m, F, e, hF, h0, hl, hP⟩ := h
  refine ⟨m, fun j ↦ (F j.rev).dualAnnihilator, Fin.revPerm.trans e,
    fun i j hij ↦ Subrepresentation.dualAnnihilator_antitone (hF (Fin.rev_le_rev.2 hij)),
    by simp [hl], by simp [h0], fun i ↦ ?_⟩
  exact ⟨(Subrepresentation.subquotientCongr (congrArg _ (congrArg F (Fin.rev_succ i)))
    (congrArg _ (congrArg F (Fin.rev_castSucc i)))).trans
    ((Subrepresentation.subquotientDualEquiv (hF i.rev.castSucc_le_succ)).trans
      (hP i.rev).equiv.dualCongr)⟩

end HasGradedPieces

namespace CompositionSeries

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The annihilators of a composition series of `ρ` form a filtration of the contragredient whose
graded pieces are the contragredients of the composition factors.
(blueprint: part L3 of `lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem hasGradedPieces_dual (s : ρ.CompositionSeries) :
    HasGradedPieces ρ.dual fun i : Fin s.length ↦ EquivTo (s.factor i).dual :=
  s.hasGradedPieces.dual

/-- **Composition factors of the contragredient.** For a finite-dimensional representation `ρ`,
the composition factors of any composition series `c` of the contragredient `ρ^∨` are, with
multiplicities, the contragredients of the composition factors of a composition series `s` of `ρ`.
(blueprint: part L3 of `lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem exists_equiv_dual [FiniteDimensional k V] (s : ρ.CompositionSeries)
    (c : ρ.dual.CompositionSeries) :
    ∃ e : Fin c.length ≃ Fin s.length, ∀ j, Nonempty ((c.factor j).Equiv (s.factor (e j)).dual) :=
  exists_equiv_of_hasGradedPieces s.hasGradedPieces_dual (fun _ ↦ isInvariant_equivTo _)
    (fun i {_} {_} {_} _ hτ ↦ hτ.some.isIrreducible_iff.2 (s.isIrreducible_factor i).dual) c

end CompositionSeries

namespace ConstituentsLE

variable {k : Type*} [Field k] {W : Type*} [Group W] {V V' : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k W V} {σ : Representation k W V'}

/-- **Constituents of contragredients.** If every constituent of the finite-dimensional
representation `ρ` is a constituent of `σ`, then every constituent of the contragredient `ρ^∨` is
a constituent of `σ^∨`. (blueprint: part L3 of
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem dual [FiniteDimensional k V] (h : ConstituentsLE ρ σ) : ConstituentsLE ρ.dual σ.dual := by
  obtain ⟨s⟩ := ρ.exists_compositionSeries
  -- the contragredient of a composition factor `S' / U'` of `σ` is the subquotient
  -- `(U' ⊓ S')^⊥ / S'^⊥` of `σ^∨`
  have hfac (i : Fin s.length) : ConstituentsLE (s.factor i).dual σ.dual := by
    obtain ⟨U', S', -, ⟨e⟩⟩ := h _ _ (s.isIrreducible_factor i)
    exact ((of_equiv (e.trans (Subrepresentation.subquotientInfEquiv U' S').symm).dualCongr).trans
      (of_equiv (Subrepresentation.subquotientDualEquiv inf_le_right).symm)).trans
      (subquotient _ _)
  -- the annihilators of the composition series form a decreasing filtration of `ρ^∨`
  have hmono : Monotone s.series := Fin.monotone_iff_le_succ.2 fun i ↦ (s.covBy i).le
  let F : ℕ → Subrepresentation ρ.dual := fun j ↦
    (s.series ⟨min j s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩).dualAnnihilator
  refine of_chain F (fun j ↦ Subrepresentation.dualAnnihilator_antitone
    (hmono (Fin.mk_le_mk.2 (by omega)))) ?_ (m := s.length) ?_ fun j hj ↦ ?_
  · change (s.series ⟨min 0 s.length, _⟩).dualAnnihilator = ⊤
    rw [show (⟨min 0 s.length, _⟩ : Fin (s.length + 1)) = 0 from Fin.ext (by simp),
      show s.series 0 = ⊥ from s.head_eq, Subrepresentation.dualAnnihilator_bot]
  · change (s.series ⟨min s.length s.length, _⟩).dualAnnihilator = ⊥
    rw [show (⟨min s.length s.length, _⟩ : Fin (s.length + 1)) = Fin.last _ from
      Fin.ext (by simp), show s.series (Fin.last _) = ⊤ from s.last_eq,
      Subrepresentation.dualAnnihilator_top]
  · let i : Fin s.length := ⟨j, hj⟩
    refine (of_equiv ((Subrepresentation.subquotientCongr
      (S' := (s.series i.castSucc).dualAnnihilator) (U' := (s.series i.succ).dualAnnihilator)
      (congrArg _ (congrArg s.series (Fin.ext (by simp [i]; omega))))
      (congrArg _ (congrArg s.series (Fin.ext (by simp [i]; omega))))).trans
      (Subrepresentation.subquotientDualEquiv (s.covBy i).le))).trans (hfac i)

end ConstituentsLE

end Representation
