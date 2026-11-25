/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.Filtration

/-!
# Invariants of the composition factors of a representation

A composition series `Representation.CompositionSeries` of a representation `ρ` can be given by a
chain of subrepresentations `0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ`
(`Representation.CompositionSeries.ofChain`, `Representation.CompositionSeries.exists_chain`).
This file records invariants of the composition factors `F (i + 1) / F i`, counted with
multiplicity: by Jordan–Hölder
(`Representation.CompositionSeries.jordanHolder`), the multiset of the values of an invariant on
the factors does not depend on the composition series. It also builds composition series from a
subrepresentation and its quotient, and from a decomposition into irreducible summands.

## Main statements

- `Subrepresentation.exists_equiv_of_isIrreducible_subquotient`: every irreducible subquotient
  is equivalent to a factor of any composition series.
- `Subrepresentation.factorMultiset_eq`: the multiset of an invariant of the composition factors
  does not depend on the composition series.
- `Subrepresentation.exists_compositionSeries_append`: composition series of a subrepresentation
  and of the quotient concatenate.
- `Subrepresentation.exists_compositionSeries_of_iSupIndep`: a decomposition into irreducible
  summands gives a composition series.
- `Subrepresentation.le_iSup_of_isInternal`: an irreducible subrepresentation of a direct sum of
  irreducibles lies in the sum of the summands equivalent to it (Schur).
-/

@[expose] public section

namespace Representation.CompositionSeries

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The composition series given by a chain of subrepresentations
`0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ`; its factors are the `F (i + 1) / F i`. -/
def ofChain {n : ℕ} {F : ℕ → Subrepresentation ρ} (h0 : F 0 = ⊥) (hn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) : ρ.CompositionSeries where
  series := { length := n, toFun := fun i ↦ F i, step := fun i ↦ hF i i.2 }
  head_eq := by simpa [RelSeries.head] using h0
  last_eq := by simpa [RelSeries.last] using hn

/-- A composition series is given by a chain of subrepresentations
`0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ`. -/
theorem exists_chain (s : ρ.CompositionSeries) :
    ∃ F : ℕ → Subrepresentation ρ, F 0 = ⊥ ∧ F s.length = ⊤ ∧
      ∀ i < s.length, F i ⋖ F (i + 1) := by
  refine ⟨fun i ↦ s.series ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩, ?_, ?_,
    fun i hi ↦ ?_⟩
  · rw [← s.head_eq, RelSeries.head]
    exact congrArg s.series (Fin.ext (by simp))
  · rw [← s.last_eq, RelSeries.last]
    exact congrArg s.series (Fin.ext (by simp))
  · convert s.covBy ⟨i, hi⟩ using 2 <;> refine Fin.ext ?_ <;> simp <;> omega

end Representation.CompositionSeries

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

open Representation

/-- Every irreducible subquotient `S / U` of a finite-dimensional representation is equivalent
to a composition factor `F (i + 1) / F i` of any composition series `F` (Jordan–Hölder). -/
theorem exists_equiv_of_isIrreducible_subquotient [FiniteDimensional k V] {n : ℕ}
    {F : ℕ → Subrepresentation ρ} (hF0 : F 0 = ⊥) (hFn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) {U S : Subrepresentation ρ}
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ i : Fin n, Nonempty ((S.subquotient U).Equiv ((F (i + 1)).subquotient (F i))) := by
  have e₀ := subquotientInfEquiv U S
  have hcov : U ⊓ S ⋖ S := (isIrreducible_subquotient_iff inf_le_right).1
    (e₀.isIrreducible_iff.2 hirr)
  obtain ⟨m, G, i₀, hG0, hGm, hG, hi₀, hGi₀, hGi₀'⟩ := exists_covBy_chain hcov
  obtain ⟨e, he⟩ := CompositionSeries.jordanHolder (CompositionSeries.ofChain hG0 hGm hG)
    (CompositionSeries.ofChain hF0 hFn hF)
  obtain ⟨e₁⟩ := he ⟨i₀, hi₀⟩
  change ((G (i₀ + 1)).subquotient (G i₀)).Equiv _ at e₁
  rw [hGi₀, hGi₀'] at e₁
  exact ⟨e ⟨i₀, hi₀⟩, ⟨e₀.symm.trans e₁⟩⟩

/-- The multiset of values of `f` on the composition factors `F (i + 1) / F i` of a chosen
composition series of a finite-dimensional representation. When `f N M` only depends on the
factor `M / N` up to equivalence, it can be computed from any composition series
(`Subrepresentation.factorMultiset_eq`). -/
noncomputable def factorMultiset (ρ : Representation k W V) [FiniteDimensional k V] {α : Type*}
    (f : Subrepresentation ρ → Subrepresentation ρ → α) : Multiset α :=
  (Finset.univ : Finset (Fin ρ.exists_compositionSeries.some.length)).val.map fun i ↦
    f (ρ.exists_compositionSeries.some.series i.castSucc)
      (ρ.exists_compositionSeries.some.series i.succ)

/-- **Jordan–Hölder for invariants of composition factors**: if `f N M` only depends on the
composition factor `M / N` up to equivalence, then `Subrepresentation.factorMultiset` can be
computed from any composition series. -/
theorem factorMultiset_eq [FiniteDimensional k V] {α : Type*}
    (f : Subrepresentation ρ → Subrepresentation ρ → α)
    (hf : ∀ N M N' M' : Subrepresentation ρ,
      Nonempty ((M.subquotient N).Equiv (M'.subquotient N')) → f N M = f N' M')
    {n : ℕ} {F : ℕ → Subrepresentation ρ} (hF0 : F 0 = ⊥) (hFn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) :
    factorMultiset ρ f =
      (Finset.univ : Finset (Fin n)).val.map fun i : Fin n ↦ f (F i) (F ((i : ℕ) + 1)) := by
  obtain ⟨e, he⟩ := CompositionSeries.jordanHolder ρ.exists_compositionSeries.some
    (CompositionSeries.ofChain hF0 hFn hF)
  rw [factorMultiset, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ ↦ hf _ _ _ _ (he i)

/-- The dimensions of the factors `F (i + 1) / F i` of a chain `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n` of
subrepresentations add up to the dimension of `F n`. -/
theorem sum_finrank_subquotient [FiniteDimensional k V] {n : ℕ} {F : ℕ → Subrepresentation ρ}
    (h0 : F 0 = ⊥) (hF : ∀ i < n, F i ≤ F (i + 1)) :
    ∑ i ∈ Finset.range n, Module.finrank k ((F (i + 1)).toSubmodule ⧸
      (F i).toSubmodule.comap (F (i + 1)).toSubmodule.subtype) =
      Module.finrank k (F n).toSubmodule := by
  induction n with
  | zero => rw [h0, toSubmodule_bot, finrank_bot, Finset.sum_range_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih fun i hi ↦ hF i (by omega)]
    have h := Submodule.finrank_quotient_add_finrank
      ((F n).toSubmodule.comap (F (n + 1)).toSubmodule.subtype)
    rw [(Submodule.comapSubtypeEquivOfLe (hF n (by omega))).finrank_eq] at h
    omega

/-- Composition series of a subrepresentation `A` and of the quotient `ρ / A`, of lengths `m`
and `n`, can be concatenated to a composition series of `ρ` of length `m + n` whose first `m`
factors are those of `A` and whose last `n` factors are those of `ρ / A`. -/
theorem exists_compositionSeries_append (A : Subrepresentation ρ) {m n : ℕ}
    {F₁ : ℕ → Subrepresentation A.toRepresentation} (h₁0 : F₁ 0 = ⊥) (h₁m : F₁ m = ⊤)
    (h₁ : ∀ i < m, F₁ i ⋖ F₁ (i + 1))
    {F₂ : ℕ → Subrepresentation A.quotient} (h₂0 : F₂ 0 = ⊥) (h₂n : F₂ n = ⊤)
    (h₂ : ∀ i < n, F₂ i ⋖ F₂ (i + 1)) :
    ∃ F : ℕ → Subrepresentation ρ, F 0 = ⊥ ∧ F (m + n) = ⊤ ∧ (∀ i < m + n, F i ⋖ F (i + 1)) ∧
      (∀ i < m,
        Nonempty (((F (i + 1)).subquotient (F i)).Equiv ((F₁ (i + 1)).subquotient (F₁ i)))) ∧
      ∀ i < n, Nonempty (((F (m + i + 1)).subquotient (F (m + i))).Equiv
        ((F₂ (i + 1)).subquotient (F₂ i))) := by
  let F : ℕ → Subrepresentation ρ := fun i ↦
    if i ≤ m then map A.subtype (F₁ i) else comap A.mkQ (F₂ (i - m))
  have hF₁ {i : ℕ} (hi : i ≤ m) : F i = map A.subtype (F₁ i) := ite_eq_left hi
  have hF₂ (i : ℕ) : F (m + i) = comap A.mkQ (F₂ i) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [add_zero, hF₁ le_rfl, h₁m, h₂0, map_subtype_top, comap_mkQ_bot]
    · exact (ite_eq_right (by omega)).trans (by rw [Nat.add_sub_cancel_left])
  have he₁ (i : ℕ) (hi : i < m) :
      Nonempty (((F (i + 1)).subquotient (F i)).Equiv ((F₁ (i + 1)).subquotient (F₁ i))) := by
    rw [hF₁ hi.le, hF₁ hi]
    exact ⟨subquotientMapEquiv _ A.subtype_injective _ _⟩
  have he₂ (i : ℕ) (_ : i < n) : Nonempty (((F (m + i + 1)).subquotient (F (m + i))).Equiv
      ((F₂ (i + 1)).subquotient (F₂ i))) := by
    rw [add_assoc, hF₂, hF₂]
    exact ⟨subquotientComapEquiv _ A.mkQ_surjective _ _⟩
  refine ⟨F, by rw [hF₁ (Nat.zero_le m), h₁0, map_bot], by rw [hF₂, h₂n, comap_top],
    fun i hi ↦ ?_, he₁, he₂⟩
  rcases lt_or_ge i m with him | him
  · have hle : F i ≤ F (i + 1) := by
      rw [hF₁ him.le, hF₁ him]
      exact map_mono _ (h₁ i him).le
    obtain ⟨e⟩ := he₁ i him
    exact (isIrreducible_subquotient_iff hle).1 (e.isIrreducible_iff.2
      ((isIrreducible_subquotient_iff (h₁ i him).le).2 (h₁ i him)))
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le him
    have hi' : i < n := by omega
    have hle : F (m + i) ≤ F (m + i + 1) := by
      rw [add_assoc, hF₂, hF₂]
      exact comap_mono _ (h₂ i hi').le
    obtain ⟨e⟩ := he₂ i hi'
    exact (isIrreducible_subquotient_iff hle).1 (e.isIrreducible_iff.2
      ((isIrreducible_subquotient_iff (h₂ i hi').le).2 (h₂ i hi')))

/-- `ρ` is the internal direct sum of the one-member family `⊤`. -/
theorem isInternal_const_top {ι : Type*} [Unique ι] :
    DirectSum.IsInternal fun _ : ι ↦ (⊤ : Subrepresentation ρ).toSubmodule :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_subsingleton _)
    (by simp)

/-- Let `ρ` be the internal direct sum of a finite family of irreducible subrepresentations `Vs`.
Then an irreducible subrepresentation `S` lies in the sum of those `Vs a` which are equivalent to
`S`: by Schur's lemma, the projection `S → Vs a` vanishes unless `S ≅ Vs a`. -/
theorem le_iSup_of_isInternal {ι : Type*} [Finite ι] [DecidableEq ι]
    {Vs : ι → Subrepresentation ρ} (hint : DirectSum.IsInternal fun a ↦ (Vs a).toSubmodule)
    (hVs : ∀ a, (Vs a).toRepresentation.IsIrreducible) {S : Subrepresentation ρ}
    (hS : S.toRepresentation.IsIrreducible) :
    S ≤ ⨆ (a) (_ : Nonempty (S.toRepresentation.Equiv (Vs a).toRepresentation)), Vs a := by
  have := Fintype.ofFinite ι
  let M : ι → Submodule k V := fun a ↦ (Vs a).toSubmodule
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap M) hint
  have hsum (x : DirectSum ι fun a ↦ M a) : e x = ∑ b, (x b : V) := by
    change DirectSum.coeLinearMap M x = _
    conv_lhs => rw [← DirectSum.sum_univ_of x]
    simp only [map_sum, DirectSum.coeLinearMap_of]
  -- the projection onto `Vs a` is intertwining
  have hproj (g : W) (v : V) (a : ι) : ((e.symm (ρ g v)) a : V) = ρ g (e.symm v a) := by
    set x := e.symm v
    let y : DirectSum ι fun a ↦ M a := DFinsupp.equivFunOnFintype.symm fun b ↦
      ⟨ρ g (x b), (Vs b).apply_mem_toSubmodule g (x b).2⟩
    have hy : e y = ρ g v := by
      rw [hsum, ← e.apply_symm_apply v, hsum, map_sum]
      rfl
    rw [← hy, e.symm_apply_apply]
    rfl
  intro v hv
  rw [← e.apply_symm_apply v, hsum]
  refine Submodule.sum_mem _ fun a _ ↦ ?_
  by_cases ha : Nonempty (S.toRepresentation.Equiv (Vs a).toRepresentation)
  · exact (le_iSup₂ (f := fun a (_ : Nonempty (S.toRepresentation.Equiv
      (Vs a).toRepresentation)) ↦ Vs a) a ha : _) (e.symm v a).2
  · let f : S.toRepresentation.IntertwiningMap (Vs a).toRepresentation :=
      ⟨DirectSum.component k ι (fun a ↦ M a) a ∘ₗ e.symm.toLinearMap ∘ₗ S.toSubmodule.subtype,
        fun g ↦ by
          ext w
          exact hproj g w a⟩
    have := hS
    have := hVs a
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
    · exact absurd ⟨Representation.IntertwiningMap.ofBijective f hf⟩ ha
    · have : (e.symm v a : V) = 0 := congrArg Subtype.val (congrArg (· ⟨v, hv⟩) hf :)
      rw [this]
      exact zero_mem _

/-- A finite family `Vs` of irreducible subrepresentations which is independent and spans `ρ`
gives a composition series `F i = ⨆_{j < i} Vs j` whose factors are the `Vs j`. -/
theorem exists_compositionSeries_of_iSupIndep {t : ℕ} {Vs : Fin t → Subrepresentation ρ}
    (hind : iSupIndep Vs) (htop : ⨆ i, Vs i = ⊤)
    (hirr : ∀ i, (Vs i).toRepresentation.IsIrreducible) :
    ∃ F : ℕ → Subrepresentation ρ, F 0 = ⊥ ∧ F t = ⊤ ∧ (∀ i < t, F i ⋖ F (i + 1)) ∧
      ∀ i : Fin t, Nonempty (((F (i + 1)).subquotient (F i)).Equiv (Vs i).toRepresentation) := by
  let F : ℕ → Subrepresentation ρ := fun i ↦ ⨆ (j : Fin t) (_ : (j : ℕ) < i), Vs j
  have hsucc (i : Fin t) : F (i + 1) = F i ⊔ Vs i := by
    refine le_antisymm (iSup₂_le fun j hj ↦ ?_) (sup_le (iSup₂_le fun j hj ↦ ?_) ?_)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact le_sup_of_le_left (le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < i) ↦ Vs j) j hj)
      · exact le_sup_of_le_right (le_of_eq (congrArg Vs (Fin.ext hj)))
    · exact le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < i + 1) ↦ Vs j) j (by omega)
    · exact le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < i + 1) ↦ Vs j) i (by omega)
  have hdisj (i : Fin t) : F i ⊓ Vs i = ⊥ :=
    (hind.disjoint_biSup (y := {j | (j : ℕ) < i}) (by simp)).symm.eq_bot
  have hequiv (i : Fin t) :
      Nonempty (((F (i + 1)).subquotient (F i)).Equiv (Vs i).toRepresentation) := by
    have h₁ : Nonempty (((Vs i).subquotient (F i ⊓ Vs i)).Equiv (Vs i).toRepresentation) := by
      rw [hdisj i]
      exact ⟨subquotientBotEquiv _⟩
    rw [hsucc i]
    exact ⟨(subquotientSupEquiv (F i) (Vs i)).symm.trans h₁.some⟩
  refine ⟨F, by simp [F], ?_, fun i hi ↦ ?_, hequiv⟩
  · simp only [F]
    rw [← htop]
    exact le_antisymm (iSup₂_le fun j _ ↦ le_iSup Vs j)
      (iSup_le fun j ↦ le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < t) ↦ Vs j) j j.2)
  · have hle : F i ≤ F (i + 1) := by
      rw [show i + 1 = ((⟨i, hi⟩ : Fin t) : ℕ) + 1 from rfl, hsucc ⟨i, hi⟩]
      exact le_sup_left
    exact (isIrreducible_subquotient_iff hle).1
      ((hequiv ⟨i, hi⟩).some.isIrreducible_iff.2 (hirr _))

end Subrepresentation
