/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.JordanHolder
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Composition series of representations

Let `ρ` be a representation of a group `W` on a vector space `V` over a field `k`. A *composition
series* of `ρ` is a finite chain `0 = V₀ ⋖ V₁ ⋖ ⋯ ⋖ V_t = V` of subrepresentations, each covering
the previous one; equivalently every quotient `V_i / V_{i-1}` is irreducible
(`Subrepresentation.isIrreducible_subquotient_iff`). These quotients are its *composition
factors*.

## Main definitions

- `Subrepresentation.subquotientOrderIso`: the subrepresentations of `S / U` are the
  subrepresentations between `U` and `S`.
- `Representation.CompositionSeries`: a composition series of `ρ`, with its composition factors
  `Representation.CompositionSeries.factor`.
- `Representation.CompositionSeries.semisimplification`: the direct sum of the composition factors.

## Main results

- `Representation.CompositionSeries.isIrreducible_factor`: the composition factors are irreducible.
- `Representation.exists_compositionSeries`: a finite-dimensional representation has a composition
  series.
- `Representation.CompositionSeries.jordanHolder`: two composition series have the same factors,
  up to permutation and isomorphism.
- `Representation.CompositionSeries.nonempty_semisimplification_equiv`: the semisimplification does
  not depend on the composition series.

## Blueprint

- `prose-14-13`: composition series and composition factors.
- `definition-determinant-weight--2`, `lemma-tensor-exterior-powers-filtered-representations--3`:
existence, and Jordan–Hölder.
- `prose-14-13`, `lemma-tensor-exterior-powers-filtered-representations--3`: the
  semisimplification.
-/

@[expose] public section

open Set

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The subrepresentation of `ρ` between `U` and `S` corresponding to a subrepresentation `T` of
the subquotient `S / U`: the preimage of `T` in `S`. -/
def ofSubquotient (S U : Subrepresentation ρ) (T : Subrepresentation (S.subquotient U)) :
    Subrepresentation ρ where
  toSubmodule := (T.toSubmodule.comap (Submodule.mkQ _)).map S.toSubmodule.subtype
  apply_mem_toSubmodule w := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨ρ w x, S.apply_mem_toSubmodule w x.2⟩, T.apply_mem_toSubmodule w hx, rfl⟩

theorem mem_ofSubquotient {S U : Subrepresentation ρ} {T : Subrepresentation (S.subquotient U)}
    (x : S.toSubmodule) : (x : V) ∈ ofSubquotient S U T ↔ Submodule.Quotient.mk x ∈ T :=
  ⟨fun ⟨_, hy, h⟩ ↦ Subtype.ext h ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩

theorem ofSubquotient_le (S U : Subrepresentation ρ) (T : Subrepresentation (S.subquotient U)) :
    ofSubquotient S U T ≤ S := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem inf_le_ofSubquotient (S U : Subrepresentation ρ)
    (T : Subrepresentation (S.subquotient U)) : U ⊓ S ≤ ofSubquotient S U T := fun x hx ↦ by
  obtain ⟨hxU, hxS⟩ := mem_inf.1 hx
  refine (mem_ofSubquotient ⟨x, hxS⟩).2 ?_
  have : (Submodule.Quotient.mk ⟨x, hxS⟩ : S.toSubmodule ⧸ U.toSubmodule.comap _) = 0 :=
    (Submodule.Quotient.mk_eq_zero (U.toSubmodule.comap S.toSubmodule.subtype)).2
      (Submodule.mem_comap.2 hxU)
  rw [this]
  exact T.toSubmodule.zero_mem

/-- The subrepresentation of `S / U` given by a subrepresentation `C` of `ρ`: the image of
`C ∩ S`. -/
def toSubquotient (S U C : Subrepresentation ρ) : Subrepresentation (S.subquotient U) where
  toSubmodule := (C.toSubmodule.comap S.toSubmodule.subtype).map (Submodule.mkQ _)
  apply_mem_toSubmodule w := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨ρ w x, S.apply_mem_toSubmodule w x.2⟩, C.apply_mem_toSubmodule w hx, rfl⟩

theorem toSubquotient_ofSubquotient (S U : Subrepresentation ρ)
    (T : Subrepresentation (S.subquotient U)) : toSubquotient S U (ofSubquotient S U T) = T := by
  refine toSubmodule_injective (Submodule.ext fun q ↦ ?_)
  induction q using Submodule.Quotient.induction_on with | _ x
  refine ⟨?_, fun h ↦ ⟨x, (mem_ofSubquotient x).2 h, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  rw [← hyx]
  exact (mem_ofSubquotient y).1 hy

theorem ofSubquotient_toSubquotient {S U C : Subrepresentation ρ} (hU : U ≤ C) (hS : C ≤ S) :
    ofSubquotient S U (toSubquotient S U C) = C := by
  ext x
  refine ⟨?_, fun hx ↦ (mem_ofSubquotient ⟨x, hS hx⟩).2 ⟨⟨x, hS hx⟩, hx, rfl⟩⟩
  rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
  have hd : (z : V) - y ∈ U := by
    have := (Submodule.Quotient.eq _).1 hzy
    exact this
  have : (y : V) = z - (z - y) := by abel
  rw [Submodule.subtype_apply, this]
  exact C.toSubmodule.sub_mem hz (hU hd)

/-- **The subrepresentations of a subquotient.** For `U ≤ S`, the subrepresentations of `S / U`
correspond to the subrepresentations of `ρ` between `U` and `S`. -/
def subquotientOrderIso {S U : Subrepresentation ρ} (h : U ≤ S) :
    Subrepresentation (S.subquotient U) ≃o Icc U S where
  toFun T := ⟨ofSubquotient S U T, (inf_eq_left.2 h).symm.le.trans (inf_le_ofSubquotient S U T),
    ofSubquotient_le S U T⟩
  invFun C := toSubquotient S U C
  left_inv T := toSubquotient_ofSubquotient S U T
  right_inv C := Subtype.ext (ofSubquotient_toSubquotient C.2.1 C.2.2)
  map_rel_iff' {T₁ T₂} := by
    refine ⟨fun h12 ↦ ?_, fun h12 x hx ↦ ?_⟩
    · intro q hq
      induction q using Submodule.Quotient.induction_on with | _ x
      exact (mem_ofSubquotient x).1 (h12 ((mem_ofSubquotient x).2 hq))
    · obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, h12 hy, rfl⟩

@[simp]
theorem coe_subquotientOrderIso_apply {S U : Subrepresentation ρ} (h : U ≤ S)
    (T : Subrepresentation (S.subquotient U)) :
    (subquotientOrderIso h T : Subrepresentation ρ) = ofSubquotient S U T :=
  rfl

theorem ofSubquotient_bot {S U : Subrepresentation ρ} (h : U ≤ S) :
    ofSubquotient S U ⊥ = U := by
  ext x
  refine ⟨?_, fun hx ↦ (mem_ofSubquotient ⟨x, h hx⟩).2 ?_⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' := Submodule.mem_comap.1 hy
    rw [toSubmodule_bot, Submodule.mem_bot] at hy'
    exact Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 hy')
  · have : (Submodule.Quotient.mk ⟨x, h hx⟩ : S.toSubmodule ⧸ U.toSubmodule.comap _) = 0 :=
      (Submodule.Quotient.mk_eq_zero (U.toSubmodule.comap S.toSubmodule.subtype)).2
        (Submodule.mem_comap.2 hx)
    rw [this]
    exact (⊥ : Subrepresentation (S.subquotient U)).toSubmodule.zero_mem

theorem ofSubquotient_top (S U : Subrepresentation ρ) : ofSubquotient S U ⊤ = S :=
  le_antisymm (ofSubquotient_le S U ⊤) fun x hx ↦
    (mem_ofSubquotient ⟨x, hx⟩).2 Submodule.mem_top

end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  (ρ : Representation k W V)

/-- A *composition series* of a representation `ρ`: a finite chain
`0 = V₀ ⋖ V₁ ⋖ ⋯ ⋖ V_t = V` of subrepresentations, each covering the previous one, that is with
irreducible successive quotients (`Representation.CompositionSeries.isIrreducible_factor`).
(blueprint: `prose-14-13`) -/
structure CompositionSeries where
  /-- The chain of subrepresentations `V₀ ⋖ V₁ ⋖ ⋯ ⋖ V_t`. -/
  series : _root_.CompositionSeries (Subrepresentation ρ)
  head_eq : series.head = ⊥
  last_eq : series.last = ⊤

namespace CompositionSeries

variable {ρ} (s : ρ.CompositionSeries)

/-- The length `t` of a composition series. -/
abbrev length : ℕ :=
  s.series.length

/-- The `i`-th composition factor `V_{i+1} / V_i` of a composition series.
(blueprint: `prose-14-13`) -/
noncomputable abbrev factor (i : Fin s.length) :=
  (s.series i.succ).subquotient (s.series i.castSucc)

theorem covBy (i : Fin s.length) : s.series i.castSucc ⋖ s.series i.succ :=
  s.series.step i

/-- The composition factors are irreducible. -/
theorem isIrreducible_factor (i : Fin s.length) : (s.factor i).IsIrreducible :=
  (Subrepresentation.isIrreducible_subquotient_iff (s.covBy i).le).2 (s.covBy i)

/-- **Jordan–Hölder.** Any two composition series of a representation have the same composition
factors, up to permutation and isomorphism, with the same multiplicities.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--3`, part L1 of
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem jordanHolder (s₁ s₂ : ρ.CompositionSeries) :
    ∃ e : Fin s₁.length ≃ Fin s₂.length, ∀ i, Nonempty ((s₁.factor i).Equiv (s₂.factor (e i))) := by
  obtain ⟨e, he⟩ := _root_.CompositionSeries.jordan_holder s₁.series s₂.series
    (s₁.head_eq.trans s₂.head_eq.symm) (s₁.last_eq.trans s₂.last_eq.symm)
  exact ⟨e, fun i ↦ JordanHolderLattice.Iso.rel
    (fun X Y ↦ Nonempty ((X.2.subquotient X.1).Equiv (Y.2.subquotient Y.1)))
    ⟨Representation.Equiv.refl _⟩ (fun ⟨f⟩ ↦ ⟨f.symm⟩) (fun ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩)
    (fun {x y} _ ↦ ⟨(Subrepresentation.subquotientSupEquiv x y).symm⟩) (he i)⟩

end CompositionSeries

/-- Every subrepresentation `A` of a finite-dimensional representation is the end of a chain of
subrepresentations starting at `0`, each covering the previous one. -/
theorem exists_compositionSeries_last_eq [FiniteDimensional k V] (A : Subrepresentation ρ) :
    ∃ s : _root_.CompositionSeries (Subrepresentation ρ), s.head = ⊥ ∧ s.last = A := by
  induction A using WellFoundedLT.induction with | _ A ih
  by_cases hA : A = ⊥
  · exact ⟨RelSeries.singleton _ ⊥, rfl, hA.symm⟩
  · obtain ⟨B, hBA, hB⟩ := Subrepresentation.exists_lt_isIrreducible_subquotient hA
    obtain ⟨s, hs, hl⟩ := ih B hBA
    have hcov : B ⋖ A := (Subrepresentation.isIrreducible_subquotient_iff hBA.le).1 hB
    exact ⟨s.snoc A (by rw [hl]; exact hcov), by rw [RelSeries.head_snoc, hs],
      RelSeries.last_snoc _ _ _⟩

/-- **Existence of a composition series.** Every finite-dimensional representation has a
composition series. (blueprint: `definition-determinant-weight--2`) -/
theorem exists_compositionSeries [FiniteDimensional k V] : Nonempty ρ.CompositionSeries := by
  obtain ⟨s, hs, hl⟩ := ρ.exists_compositionSeries_last_eq ⊤
  exact ⟨⟨s, hs, hl⟩⟩

section DirectSum

open DirectSum

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {V' : ι → Type*}
  [∀ i, AddCommGroup (V' i)] [∀ i, Module k (V' i)] {U' : κ → Type*} [∀ j, AddCommGroup (U' j)]
  [∀ j, Module k (U' j)] {ρs : ∀ i, Representation k W (V' i)}
  {σs : ∀ j, Representation k W (U' j)}

/-- Direct sums of two families of representations equivalent along a bijection `e` of the
indices are equivalent. -/
noncomputable def Equiv.directSumCongr (e : ι ≃ κ) (g : ∀ i, (ρs i).Equiv (σs (e i))) :
    (directSum σs).Equiv (directSum ρs) :=
  Equiv.mk ((lequivCongrLeft k e.symm).trans
    (DFinsupp.mapRange.linearEquiv fun i ↦ (g i).toLinearEquiv.symm)) fun w ↦ by
    refine LinearMap.ext fun y ↦ DFinsupp.ext fun i ↦ ?_
    change (g i).toLinearEquiv.symm ((σs (e i) w) (y (e i))) =
      ρs i w ((g i).toLinearEquiv.symm (y (e i)))
    exact (g i).symm.apply_apply w _

end DirectSum

open DirectSum

namespace CompositionSeries

variable {ρ} (s : ρ.CompositionSeries)

/-- The *semisimplification* `⨁ᵢ V_{i+1} / V_i` of a composition series: the direct sum of its
composition factors. Its isomorphism class does not depend on the series
(`nonempty_semisimplification_equiv`), and its simple summands are the composition factors
(`isIrreducible_directSumSummand`). (blueprint: `prose-14-13`) -/
noncomputable def semisimplification :
    Representation k W (⨁ (i : Fin s.length), ((s.series i.succ).toSubmodule ⧸
      (s.series i.castSucc).toSubmodule.comap (s.series i.succ).toSubmodule.subtype)) :=
  directSum fun i ↦ s.factor i

/-- The summands of the semisimplification are irreducible. -/
theorem isIrreducible_directSumSummand (i : Fin s.length) :
    (directSumSummand (fun i ↦ s.factor i) i).toRepresentation.IsIrreducible :=
  (directSumSummandEquiv (fun i ↦ s.factor i) i).isIrreducible_iff.1 (s.isIrreducible_factor i)

/-- The semisimplification is the internal direct sum of its summands. -/
theorem isInternal_semisimplification :
    DirectSum.IsInternal fun i ↦ (directSumSummand (fun i ↦ s.factor i) i).toSubmodule :=
  isInternal_directSumSummand _

/-- A composition series of a nonzero representation has positive length. -/
theorem length_pos [Nontrivial V] : 0 < s.length := by
  by_contra! h
  have h0 : s.series 0 = s.series (Fin.last s.length) :=
    congrArg s.series (Fin.ext (by simp; omega))
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hxtop : x ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
  rw [← s.last_eq, RelSeries.last, ← h0, ← RelSeries.head, s.head_eq] at hxtop
  exact hx ((Submodule.mem_bot k).1 hxtop)

/-- The semisimplification of a nonzero representation is nonzero. -/
theorem nontrivial_semisimplification [Nontrivial V] :
    Nontrivial (⨁ (i : Fin s.length), ((s.series i.succ).toSubmodule ⧸
      (s.series i.castSucc).toSubmodule.comap (s.series i.succ).toSubmodule.subtype)) :=
  have := (s.isIrreducible_factor ⟨0, s.length_pos⟩).nontrivial
  (DirectSum.of_injective (β := fun i : Fin s.length ↦ ((s.series i.succ).toSubmodule ⧸
    (s.series i.castSucc).toSubmodule.comap (s.series i.succ).toSubmodule.subtype))
    ⟨0, s.length_pos⟩).nontrivial

/-- **The semisimplification does not depend on the composition series**: the
semisimplifications of two composition series are equivalent (Jordan–Hölder).
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem nonempty_semisimplification_equiv (s₁ s₂ : ρ.CompositionSeries) :
    Nonempty (s₁.semisimplification.Equiv s₂.semisimplification) := by
  obtain ⟨e, he⟩ := jordanHolder s₂ s₁
  exact ⟨Equiv.directSumCongr e fun i ↦ (he i).some⟩

end CompositionSeries

end Representation
