/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import WeilConjectures.RepresentationTheory.ExteriorPower
public import WeilConjectures.RepresentationTheory.PiTensorProduct

/-!
# The exterior powers of a filtered representation

Let `0 = V₀ ≤ V₁ ≤ ⋯ ≤ V_t = V` be a finite filtration of a finite-dimensional representation, with
graded pieces `A_i = V_i / V_{i-1}`. Then `⋀^r V` has a finite filtration whose graded pieces are
the tensor products `⨂ᵢ ⋀^{nᵢ} A_i` over the tuples `(n₁, …, n_t)` with `∑ nᵢ = r`, each tuple
occurring once. The piece of a tuple is nonzero exactly when `nᵢ ≤ dim A_i` for all `i`.

The proof is by induction on `t`, from the two-step filtration of `⋀^r V` by a subrepresentation
`P` (`Subrepresentation.exteriorPowerGradedEquiv`), with graded pieces `⋀^{r-j} P ⊗ ⋀^j (V ⧸ P)`.

## Main results

- `Subrepresentation.hasGradedPieces_exteriorPower`: the two-step filtration.
- `Representation.hasGradedPieces_exteriorPower_of_monotone`: the filtration of `⋀^r V` induced
  by a finite filtration of `V`.
- `Representation.CompositionSeries.hasGradedPieces_exteriorPower`: the same for a composition
  series.
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Representation

variable {k : Type u} [Field k] {W : Type w} [Group W] {V : Type v} [AddCommGroup V]
  [Module k V]

/-- Equal exterior powers are equivalent. -/
noncomputable def exteriorPowerCongr (ρ : Representation k W V) {a b : ℕ} (h : a = b) :
    (ρ.exteriorPower a).Equiv (ρ.exteriorPower b) := by
  subst h
  exact .refl _

end Representation

namespace Subrepresentation

variable {k : Type u} [Field k] {W : Type w} [Group W] {V : Type v} [AddCommGroup V]
  [Module k V] {ρ : Representation k W V}

theorem exteriorPowerFiltration_anti (P : Subrepresentation ρ) (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    P.exteriorPowerFiltration n j ≤ P.exteriorPowerFiltration n i :=
  exteriorPower.countSpan_anti _ n h

/-- **The exterior powers of an extension.** For a subrepresentation `P` of a finite-dimensional
representation `ρ`, the exterior power `⋀^r V` has a finite filtration with graded pieces
`⋀^{r-j} P ⊗ ⋀^j (V ⧸ P)`, `0 ≤ j ≤ r`. -/
theorem hasGradedPieces_exteriorPower [FiniteDimensional k V] (P : Subrepresentation ρ)
    (r : ℕ) : Representation.HasGradedPieces (ρ.exteriorPower r) fun j : Fin (r + 1) ↦
      Representation.EquivTo ((P.toRepresentation.exteriorPower (r - j)).tprod
        (P.quotient.exteriorPower j)) := by
  refine ⟨r + 1, fun i ↦ P.exteriorPowerFiltration r (r + 1 - i), .refl _,
    fun a b hab ↦ P.exteriorPowerFiltration_anti r (by have : (a : ℕ) ≤ b := hab; omega),
    by simp [P.exteriorPowerFiltration_eq_bot r (Nat.lt_succ_self r)],
    by simp [exteriorPowerFiltration_zero], fun i ↦ ⟨?_⟩⟩
  have hi := i.2
  have h1 : P.exteriorPowerFiltration r (r + 1 - (i.succ : ℕ)) =
      P.exteriorPowerFiltration r (r - i) := by
    congr 1
    rw [Fin.val_succ]
    omega
  have h2 : P.exteriorPowerFiltration r (r + 1 - (i.castSucc : ℕ)) =
      P.exteriorPowerFiltration r (r - i + 1) := by
    congr 1
    rw [Fin.val_castSucc]
    omega
  exact (subquotientCongr h1 h2).trans
    (P.exteriorPowerGradedEquiv r (j := r - i) (l := i) (by omega)).symm

end Subrepresentation

namespace Representation

variable {k : Type u} [Field k] {W : Type w} [Group W]

/-- The tensor product `⨂ᵢ ⋀^{nᵢ} Xᵢ` of exterior powers of a family of representations. -/
noncomputable def piTprodExteriorPower {ι : Type*} {X : ι → Type*} [∀ i, AddCommGroup (X i)]
    [∀ i, Module k (X i)] (ρs : ∀ i, Representation k W (X i)) (n : ι → ℕ) :
    Representation k W (⨂[k] i, ⋀[k]^(n i) (X i)) :=
  piTprod fun i ↦ (ρs i).exteriorPower (n i)

section PiTprodExteriorPower

variable {ι : Type*} {X Y : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module k (Y i)]

/-- Tensor products of exterior powers of equivalent families, with equal exponents, are
equivalent. -/
noncomputable def Equiv.piTprodExteriorPowerCongr {ρs : ∀ i, Representation k W (X i)}
    {σs : ∀ i, Representation k W (Y i)} (e : ∀ i, (ρs i).Equiv (σs i)) {n m : ι → ℕ}
    (h : ∀ i, n i = m i) : (piTprodExteriorPower ρs n).Equiv (piTprodExteriorPower σs m) :=
  Equiv.piTprodCongr fun i ↦ ((e i).exteriorPower (n i)).trans (exteriorPowerCongr _ (h i))

/-- The tensor product of exterior powers over `Fin (t + 1)` splits off the last factor. -/
noncomputable def piTprodExteriorPowerSuccEquiv {t : ℕ} {X : Fin (t + 1) → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] (ρs : ∀ i, Representation k W (X i))
    (n : Fin (t + 1) → ℕ) :
    (piTprodExteriorPower ρs n).Equiv ((piTprodExteriorPower (fun i : Fin t ↦ ρs i.castSucc)
      (fun i ↦ n i.castSucc)).tprod ((ρs (Fin.last t)).exteriorPower (n (Fin.last t)))) :=
  piTprodSuccEquiv _

end PiTprodExteriorPower

/-- A tuple `(n₁, …, n_{t+1})` with sum `r` is a last entry `j ≤ r` and a tuple `(n₁, …, n_t)` with
sum `r - j`. -/
def sigmaSnocEquiv (t r : ℕ) :
    (Σ j : Fin (r + 1), {n : Fin t → ℕ // ∑ i, n i = r - j}) ≃
      {n : Fin (t + 1) → ℕ // ∑ i, n i = r} where
  toFun x := ⟨Fin.snoc (α := fun _ ↦ ℕ) x.2.1 (x.1 : ℕ), by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, x.2.2]
    have := x.1.2
    omega⟩
  invFun n := ⟨⟨n.1 (Fin.last t), by
      have := n.2
      rw [Fin.sum_univ_castSucc] at this
      omega⟩, ⟨Fin.init n.1, by
      have := n.2
      rw [Fin.sum_univ_castSucc] at this
      simp only [Fin.init]
      omega⟩⟩
  left_inv x := by
    refine Sigma.subtype_ext (Fin.ext ?_) ?_
    · simp
    · simp [Fin.init_snoc]
  right_inv n := Subtype.ext (by simp [Fin.snoc_init_self])

/-- **The exterior powers of a filtered representation.** Let `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_t = V` be a
finite filtration of a finite-dimensional representation, with graded pieces
`A_i = F_{i+1} / F_i`. Then `⋀^r V` has a finite filtration whose graded pieces are the tensor
products `⨂ᵢ ⋀^{nᵢ} A_i`, one for each tuple `(n₁, …, n_t)` with `∑ nᵢ = r`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`) -/
theorem hasGradedPieces_exteriorPower_of_monotone (t : ℕ) : ∀ {V : Type v} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k W V)
    (F : Fin (t + 1) → Subrepresentation ρ) (_ : Monotone F) (_ : F 0 = ⊥)
    (_ : F (Fin.last t) = ⊤) (r : ℕ),
    HasGradedPieces (ρ.exteriorPower r) fun n : {n : Fin t → ℕ // ∑ i, n i = r} ↦
      EquivTo (piTprodExteriorPower (fun i ↦ (F i.succ).subquotient (F i.castSucc)) n.1)
:= by
  induction t with
  | zero =>
    intro V _ _ _ ρ F _ h0 hl r
    have hV : Subsingleton V := by
      have htop : (⊤ : Subrepresentation ρ) = ⊥ := hl.symm.trans h0
      refine ⟨fun x y ↦ ?_⟩
      have hx : x ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
      have hy : y ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
      rw [htop] at hx hy
      rw [(Submodule.mem_bot k).1 hx, (Submodule.mem_bot k).1 hy]
    rcases r with _ | r
    · let : Unique {n : Fin 0 → ℕ // ∑ i, n i = 0} :=
        { default := ⟨Fin.elim0, rfl⟩, uniq := fun a ↦ Subtype.ext (funext fun i ↦ i.elim0) }
      exact ((HasGradedPieces.single (isInvariant_equivTo _) ⟨exteriorPowerZeroEquiv ρ⟩).reindex
        (Equiv.ofUnique Unit {n : Fin 0 → ℕ // ∑ i, n i = 0})).mono
          fun n {_} {_} {_} τ ⟨f⟩ ↦ ⟨f.trans (piTprodIsEmptyEquiv
            (fun i : Fin 0 ↦ ((F i.succ).subquotient (F i.castSucc)).exteriorPower (n.1 i))).symm⟩
    · have : Subsingleton (⋀[k]^(r + 1) V) := by
        rw [← Module.finrank_zero_iff (R := k), exteriorPower.finrank_eq,
          Module.finrank_zero_of_subsingleton, Nat.choose_zero_succ]
      have : IsEmpty {n : Fin 0 → ℕ // ∑ i, n i = r + 1} :=
        ⟨fun n ↦ by simpa using n.2⟩
      exact (HasGradedPieces.of_subsingleton (ρ := ρ.exteriorPower (r + 1))
        (P := fun _ : PEmpty.{1} ↦ EquivTo (trivial k W k))).reindex
          (Equiv.equivOfIsEmpty _ _) |>.mono
          fun n ↦ isEmptyElim n
  | succ t ih =>
    intro V _ _ _ ρ F hF h0 hl r
    -- the subrepresentation `A = F t` and the restriction of the filtration to it
    let A := F (Fin.last t).castSucc
    let F' : Fin (t + 1) → Subrepresentation A.toRepresentation :=
      fun j ↦ Subrepresentation.comap A.subtype (F j.castSucc)
    have hFA (j : Fin (t + 1)) : F j.castSucc ≤ A := hF (Fin.castSucc_le_castSucc_iff.2 j.le_last)
    have hF' : Monotone F' := fun a b hab x hx ↦ hF (Fin.castSucc_le_castSucc_iff.2 hab) hx
    have h0' : F' 0 = ⊥ := by
      simp only [F', Fin.castSucc_zero, h0, Subrepresentation.comap_subtype_bot]
    have hl' : F' (Fin.last t) = ⊤ := Subrepresentation.comap_subtype_self A
    -- the graded pieces of `F'` and the last graded piece of `F`
    let e' (i : Fin t) : ((F' i.succ).subquotient (F' i.castSucc)).Equiv
        ((F i.castSucc.succ).subquotient (F i.castSucc.castSucc)) :=
      Subrepresentation.subquotientComapSubtypeEquiv (hFA i.succ)
    let eA : A.quotient.Equiv ((F (Fin.last (t + 1))).subquotient (F (Fin.last t).castSucc)) :=
      (Subrepresentation.quotientEquivTopSubquotient A).trans
        (Subrepresentation.subquotientCongr hl.symm rfl)
    -- the piece of a tuple `snoc n' j`
    let eP (j : ℕ) (n' : Fin t → ℕ) :
        (piTprodExteriorPower (fun i ↦ (F i.succ).subquotient (F i.castSucc))
          (Fin.snoc (α := fun _ ↦ ℕ) n' j)).Equiv
        ((piTprodExteriorPower (fun i : Fin t ↦ (F' i.succ).subquotient (F' i.castSucc)) n').tprod
          (A.quotient.exteriorPower j)) :=
      (piTprodExteriorPowerSuccEquiv _ _).trans (Equiv.tprodCongr
        (Equiv.piTprodExteriorPowerCongr (fun i ↦ (e' i).symm)
          (fun i ↦ Fin.snoc_castSucc (α := fun _ ↦ ℕ) _ _ _))
        ((eA.symm.exteriorPower _).trans
          (exteriorPowerCongr _ (Fin.snoc_last (α := fun _ ↦ ℕ) _ _))))
    have h1 := A.hasGradedPieces_exteriorPower r
    have h2 := h1.trans
      (R := fun (j : Fin (r + 1)) (n' : {n' : Fin t → ℕ // ∑ i, n' i = r - j}) ↦
        EquivTo (piTprodExteriorPower
          (fun i : Fin (t + 1) ↦ (F i.succ).subquotient (F i.castSucc))
          (Fin.snoc (α := fun _ ↦ ℕ) n'.1 (j : ℕ))))
      (fun _ _ ↦ isInvariant_equivTo _) fun j {_} {_} {_} τ hτ ↦
        (((ih A.toRepresentation F' hF' h0' hl' (r - j)).tprod_right
          (A.quotient.exteriorPower j)).of_equiv (fun _ ↦ isInvariant_equivTo _) hτ.equiv.symm).mono
          fun n' {_} {_} {_} τ' hg ↦ hg.trans (eP j n'.1).symm
    exact (h2.reindex (sigmaSnocEquiv t r)).mono fun n {_} {_} {_} τ hτ ↦ hτ.trans
      (Equiv.piTprodExteriorPowerCongr (fun _ ↦ .refl _)
        (congrFun (Fin.snoc_init_self (α := fun _ ↦ ℕ) n.1)))

/-- The piece `⨂ᵢ ⋀^{nᵢ} Xᵢ` is nonzero exactly when `nᵢ ≤ dim Xᵢ` for every `i`. -/
theorem nontrivial_piTensorProduct_exteriorPower_iff {ι : Type*} [Finite ι] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, FiniteDimensional k (X i)]
    (n : ι → ℕ) :
    Nontrivial (⨂[k] i, ⋀[k]^(n i) (X i)) ↔ ∀ i, n i ≤ Module.finrank k (X i) := by
  classical
  have := Fintype.ofFinite ι
  let B := Basis.piTensorProduct fun i ↦ Module.finBasis k (⋀[k]^(n i) (X i))
  have : Module.Finite k (⨂[k] i, ⋀[k]^(n i) (X i)) := Module.Finite.of_basis B
  rw [← Module.finrank_pos_iff (R := k), Module.finrank_eq_card_basis B, Fintype.card_pi]
  simp only [Fintype.card_fin, exteriorPower.finrank_eq, Nat.pos_iff_ne_zero,
    Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies, ne_eq, Nat.choose_eq_zero_iff, not_lt]

namespace CompositionSeries

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {ρ : Representation k W V}

/-- **The exterior power of a filtered representation.** Let `0 = V₀ ⋖ ⋯ ⋖ V_t = V` be a
composition series, with factors `A_i`, and `r ≥ 0`. Then `⋀^r V` has a finite filtration whose
graded pieces, in a suitable order, are the representations `⨂ᵢ ⋀^{nᵢ} A_i`, each tuple
`(n₁, …, n_t)` with `∑ nᵢ = r` occurring exactly once; by
`nontrivial_piTensorProduct_exteriorPower_iff` the nonzero ones are those with `nᵢ ≤ dim A_i`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`) -/
theorem hasGradedPieces_exteriorPower (s : ρ.CompositionSeries) (r : ℕ) :
    HasGradedPieces (ρ.exteriorPower r) fun n : {n : Fin s.length → ℕ // ∑ i, n i = r} ↦
      EquivTo (piTprodExteriorPower (fun i ↦ s.factor i) n.1) :=
  hasGradedPieces_exteriorPower_of_monotone s.length ρ s.series
    (Fin.monotone_iff_le_succ.2 fun i ↦ (s.covBy i).le) s.head_eq s.last_eq r

end CompositionSeries

end Representation
