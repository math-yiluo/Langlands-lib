/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Absolute irreducibility has a finite matrix witness

Let `O` be a Noetherian local domain with fraction field `E` (in the application, the ring of
integers `𝒪_E` of a finite extension `E/ℚ_ℓ`), and let `ρ` be a representation of a group `G` on
a finite-dimensional `E`-vector space `V` which is absolutely irreducible: irreducible after
extension of scalars to an algebraically closed field. If `ρ` preserves an `O`-lattice `L`, then
there is `N ≥ 1` such that every subgroup `H ≤ G` with the same image as `G` on `L / 𝔪ᴺ L` still
acts absolutely irreducibly on `V`.

The proof is Burnside's theorem: by Schur's lemma and the Jacobson density theorem, the
`E`-span of `ρ(G)` is all of `End_E(V)`. Choosing `g₁, …, g_{n²}` whose matrices form a basis,
the determinant `Δ ∈ O` of their vectorised matrices is nonzero, and for `N` with `Δ ∉ 𝔪ᴺ`
(Krull's intersection theorem) congruent matrices modulo `𝔪ᴺ` still form a basis.

## Main statements

- `Representation.exists_forall_isIrreducible_baseChange_of_congr`: blueprint
  `lemma-detecting-irreducibility-finite-quotient--1`.

## Implementation notes

The stable lattice `L` is recorded as a basis `b` of `V` in which all the matrices of `ρ` have
entries in `O`; its existence for a continuous representation of a profinite group is
`proposition-lattices-representations-normal-scheme`
(`AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`). Extension of scalars of `ρ` to a field `K`
is `(Module.End.baseChangeHom E K V).toMonoidHom.comp ρ`.
-/

@[expose] public section

universe w

/-- `Module.End.baseChangeHom` sends an endomorphism `f` to `f.baseChange A`. -/
@[simp]
theorem Module.End.baseChangeHom_apply {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] (f : Module.End R M) :
    Module.End.baseChangeHom R A M f = f.baseChange A :=
  rfl

namespace Module.Basis

variable {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M] [Fintype ι] [DecidableEq ι]

/-- The entries of the matrix of an endomorphism in a basis, as a linear equivalence
`Module.End F M ≃ₗ[F] (ι × ι → F)`. -/
noncomputable def endEquivPiProd (c : Basis ι F M) : Module.End F M ≃ₗ[F] (ι × ι → F) :=
  (LinearMap.toMatrix c c).trans
    ((Matrix.ofLinearEquiv F).symm.trans (LinearEquiv.curry F F ι ι).symm)

@[simp]
theorem endEquivPiProd_apply (c : Basis ι F M) (f : Module.End F M) (p : ι × ι) :
    c.endEquivPiProd f p = LinearMap.toMatrix c c f p.1 p.2 :=
  rfl

/-- If the matrices of `n²` endomorphisms of an `n`-dimensional space are linearly
independent, as witnessed by a nonzero determinant, then they span all endomorphisms. -/
theorem span_range_eq_top_of_det_ne_zero (c : Basis ι F M) (f : ι × ι → Module.End F M)
    (h : (Matrix.of fun k p ↦ LinearMap.toMatrix c c (f k) p.1 p.2).det ≠ 0) :
    Submodule.span F (Set.range f) = ⊤ := by
  have : FiniteDimensional F M := .of_basis c
  have hli : LinearIndependent F (c.endEquivPiProd ∘ f) :=
    Matrix.linearIndependent_row_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr h.isUnit)
  refine (LinearIndependent.of_comp c.endEquivPiProd.toLinearMap hli)
    |>.span_eq_top_of_card_eq_finrank' ?_
  rw [c.endEquivPiProd.finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- If endomorphisms `f a` span all endomorphisms of an `n`-dimensional space, then `n²` of them
have linearly independent matrices, as witnessed by a nonzero determinant. -/
theorem exists_det_ne_zero_of_span_range_eq_top {α : Type*} (c : Basis ι F M)
    (f : α → Module.End F M) (h : Submodule.span F (Set.range f) = ⊤) :
    ∃ s : ι × ι → α, (Matrix.of fun k p ↦ LinearMap.toMatrix c c (f (s k)) p.1 p.2).det ≠ 0 := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' F (c.endEquivPiProd ∘ f)
  have htop : Submodule.span F (Set.range (c.endEquivPiProd ∘ f ∘ a)) = ⊤ := by
    rw [← Function.comp_assoc, hspan, Set.range_comp, Submodule.span_image_linearEquiv, h,
      Submodule.map_top, LinearEquiv.range]
  let e := (Basis.mk hli htop.ge).indexEquiv (Pi.basisFun F (ι × ι))
  refine ⟨a ∘ e.symm, ?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp (hli.comp e.symm e.symm.injective))).ne_zero

end Module.Basis

namespace Representation

open scoped MonoidAlgebra

section Burnside

variable {F G M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- A representation whose operators span all endomorphisms of a nonzero space is
irreducible. -/
theorem isIrreducible_of_span_range_eq_top [Monoid G] [Nontrivial M]
    (σ : Representation F G M) (h : Submodule.span F (Set.range σ) = ⊤) : IsIrreducible σ where
  exists_pair_ne := ⟨⊥, ⊤, fun h' ↦ bot_ne_top congr(($h').toSubmodule)⟩
  eq_bot_or_eq_top W := by
    let W' : Submodule (Module.End F M) M :=
      { carrier := W
        add_mem' := W.toSubmodule.add_mem
        zero_mem' := W.toSubmodule.zero_mem
        smul_mem' f v hv := by
          have hf : f ∈ Submodule.span F (Set.range σ) := h ▸ Submodule.mem_top
          induction hf using Submodule.span_induction with
          | mem f hf =>
            obtain ⟨g, rfl⟩ := hf
            exact W.apply_mem_toSubmodule g hv
          | zero => exact W.toSubmodule.zero_mem
          | add f₁ f₂ _ _ h₁ h₂ => exact W.toSubmodule.add_mem h₁ h₂
          | smul a f _ hf => exact W.toSubmodule.smul_mem a hf }
    rcases eq_bot_or_eq_top W' with hW | hW
    · left
      ext v
      exact congr(v ∈ $hW)
    · right
      ext v
      exact congr(v ∈ $hW)

/-- **Burnside's theorem**: the operators of an irreducible finite-dimensional representation
over an algebraically closed field span all endomorphisms. -/
theorem span_range_eq_top_of_isIrreducible [Monoid G] [IsAlgClosed F] [FiniteDimensional F M]
    (σ : Representation F G M) [IsIrreducible σ] : Submodule.span F (Set.range σ) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  have hS := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := F[G]) (V := σ.asModule) F
  have : Module.Finite (Module.End F[G] σ.asModule) σ.asModule :=
    Module.Finite.of_restrictScalars_finite F _ _
  let f' : Module.End (Module.End F[G] σ.asModule) σ.asModule :=
    { toFun := f
      map_add' := f.map_add
      map_smul' φ m := by
        obtain ⟨c, rfl⟩ := hS.2 φ
        exact f.map_smul c m }
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective f'
  have hf : f = σ.asAlgebraHom r := LinearMap.ext fun m ↦ (congr($hr m)).symm
  rw [hf]
  clear hf hr
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | single g a =>
    rw [asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end Burnside

open IsLocalRing

variable {O E K G V ι : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
  [Field E] [Algebra O E] [IsFractionRing O E] [Field K] [IsAlgClosed K] [Algebra E K]
  [Group G] [AddCommGroup V] [Module E V] [Fintype ι] [DecidableEq ι]

/-- **Absolute irreducibility has a finite matrix witness**
(blueprint: `lemma-detecting-irreducibility-finite-quotient--1`). Let `ρ` be a representation of `G`
on an `E`-vector space `V` with basis `b`, in which the matrices of `ρ` have entries in `O`, and
assume that `ρ` is irreducible over an algebraically closed field `K ⊇ E`. Then there is
`N ≥ 1` such that every subgroup `H ≤ G` whose matrices are congruent modulo `𝔪ᴺ` to all the
matrices of `ρ(G)` acts absolutely irreducibly on `V`: irreducibly after extension of scalars
to any field `K' ⊇ E`. -/
theorem exists_forall_isIrreducible_baseChange_of_congr (ρ : Representation E G V)
    (b : Module.Basis ι E V)
    (hb : ∀ g i j, LinearMap.toMatrix b b (ρ g) i j ∈ (algebraMap O E).range)
    (hρ : IsIrreducible ((Module.End.baseChangeHom E K V).toMonoidHom.comp ρ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ H : Subgroup G,
      (∀ g, ∃ h ∈ H, ∀ i j, ∃ x ∈ maximalIdeal O ^ N,
        LinearMap.toMatrix b b (ρ h) i j - LinearMap.toMatrix b b (ρ g) i j = algebraMap O E x) →
      ∀ (K' : Type w) [Field K'] [Algebra E K'],
        IsIrreducible ((Module.End.baseChangeHom E K' V).toMonoidHom.comp (ρ.comp H.subtype)) := by
  classical
  let bK := Algebra.TensorProduct.basis K b
  have : FiniteDimensional K (TensorProduct E K V) := Module.Finite.of_basis bK
  obtain ⟨s, hs⟩ := bK.exists_det_ne_zero_of_span_range_eq_top _
    (span_range_eq_top_of_isIrreducible ((Module.End.baseChangeHom E K V).toMonoidHom.comp ρ))
  choose c hc using hb
  set D : Matrix (ι × ι) (ι × ι) O := Matrix.of fun k p ↦ c (s k) p.1 p.2
  have hD0 : D.det ≠ 0 := by
    intro h0
    apply hs
    have hmap : (Matrix.of fun k p ↦ LinearMap.toMatrix bK bK
        ((Module.End.baseChangeHom E K V).toMonoidHom.comp ρ (s k)) p.1 p.2) =
        D.map ((algebraMap E K).comp (algebraMap O E)) := by
      ext k p
      simp [bK, D, hc]
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨N, hN⟩ : ∃ N, D.det ∉ maximalIdeal O ^ N := by
    by_contra! h
    have h' := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal O) Ideal.IsPrime.ne_top'
    exact hD0 (by simpa [h'] using Ideal.mem_iInf.mpr h)
  refine ⟨N + 1, N.succ_pos, fun H hH K' _ _ ↦ ?_⟩
  choose h hhH x hx hxeq using fun k ↦ hH (s k)
  set D' : Matrix (ι × ι) (ι × ι) O := Matrix.of fun k p ↦ c (s k) p.1 p.2 + x k p.1 p.2
  have hD'0 : D'.det ≠ 0 := by
    intro h0
    apply hN
    apply Ideal.pow_le_pow_right (Nat.le_add_right N 1)
    have hmap : D.map (Ideal.Quotient.mk (maximalIdeal O ^ (N + 1))) =
        D'.map (Ideal.Quotient.mk _) := by
      ext k p
      simp [D, D', Ideal.Quotient.eq_zero_iff_mem.mpr (hx k p.1 p.2)]
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let bK' := Algebra.TensorProduct.basis K' b
  have : Nonempty ι := by
    have : Nontrivial (TensorProduct E K V) := by
      by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      exact bot_ne_top (α := Subrepresentation
        ((Module.End.baseChangeHom E K V).toMonoidHom.comp ρ))
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    exact bK.index_nonempty
  have : Nontrivial (TensorProduct E K' V) := Module.nontrivial_of_finrank_pos
    (by rw [Module.finrank_eq_card_basis bK']; exact Fintype.card_pos)
  apply isIrreducible_of_span_range_eq_top
  rw [eq_top_iff, ← bK'.span_range_eq_top_of_det_ne_zero (fun k ↦
    (Module.End.baseChangeHom E K' V).toMonoidHom.comp (ρ.comp H.subtype) ⟨h k, hhH k⟩)]
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩
  · have hmap : (Matrix.of fun k p ↦ LinearMap.toMatrix bK' bK'
        ((Module.End.baseChangeHom E K' V).toMonoidHom.comp (ρ.comp H.subtype) ⟨h k, hhH k⟩)
          p.1 p.2) = D'.map ((algebraMap E K').comp (algebraMap O E)) := by
      ext k p
      simp [bK', D', hc, sub_eq_iff_eq_add'.mp (hxeq k p.1 p.2)]
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine (map_ne_zero_iff _ ?_).mpr hD'0
    exact ((algebraMap E K').injective.comp (IsFractionRing.injective O E) :
      Function.Injective (algebraMap E K' ∘ algebraMap O E))



end Representation
