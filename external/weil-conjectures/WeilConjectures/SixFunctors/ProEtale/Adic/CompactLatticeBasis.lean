/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension

/-!
# Compact lattices of `ℚ̄_ℓ` are free `ℤ_ℓ`-modules

A compact subgroup `Λ` of `ℚ̄_ℓ` spanning a finite-dimensional `ℚ_ℓ`-subspace
(`PadicAlgCl.CompactLattice`) is a `ℤ_ℓ`-submodule (`PadicAlgCl.CompactLattice.toSubmodule`):
it is closed and the integers are dense in `ℤ_ℓ`. It is finitely generated, being contained in
the `ℤ_ℓ`-span of a scaled `ℚ_ℓ`-basis of its span, hence free. A basis `e : ι → Λ` identifies
`Λ` with `ℤ_ℓ^ι` as topological groups, the identification being a continuous bijection from a
compact space; so the coordinates `Λ ⟶ ℤ_ℓ` are continuous
(`PadicAlgCl.CompactLattice.continuous_coord`).

Consequently the pro-étale sheaf `C(-, Λ)` is a finite direct sum of copies of `C(-, ℤ_ℓ)`, which
identifies the cohomology of the constant sheaf `ℚ̄_ℓ = colim_Λ C(-, Λ)` with the extension of
scalars of the integral cohomology `Hⁿ(-, ℤ_ℓ)`.
-/

@[expose] public section

open Topology

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime]

/-- The structure map `ℤ_ℓ ⟶ ℚ̄_ℓ` is continuous. -/
lemma continuous_algebraMap_padicInt : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) := by
  have : (algebraMap ℤ_[l] (PadicAlgCl l)) =
      (algebraMap ℚ_[l] (PadicAlgCl l)) ∘ fun c : ℤ_[l] ↦ (c : ℚ_[l]) := by
    funext c
    exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) c
  rw [this]
  exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val

namespace CompactLattice

/-- A compact lattice is stable under `ℤ_ℓ`: it is closed and contains the integer multiples of
its elements, which are dense. -/
lemma smul_mem (Λ : CompactLattice l) (c : ℤ_[l]) {x : PadicAlgCl l} (hx : x ∈ Λ.1) :
    c • x ∈ Λ.1 := by
  have hcl : IsClosed {c : ℤ_[l] | c • x ∈ Λ.1} := by
    have : {c : ℤ_[l] | c • x ∈ Λ.1} =
        (fun c : ℤ_[l] ↦ algebraMap ℤ_[l] (PadicAlgCl l) c * x) ⁻¹' (Λ.1 : Set (PadicAlgCl l)) := by
      ext c
      simp [Algebra.smul_def]
    rw [this]
    exact Λ.2.1.isClosed.preimage (continuous_algebraMap_padicInt.mul continuous_const)
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[l]) ⊆ {c : ℤ_[l] | c • x ∈ Λ.1} := by
    rintro _ ⟨n, rfl⟩
    simpa [Nat.cast_smul_eq_nsmul] using Λ.1.nsmul_mem hx n
  have := hcl.closure_subset_iff.2 hsub
  rw [PadicInt.denseRange_natCast.closure_range] at this
  exact this (Set.mem_univ c)

/-- A compact lattice as a `ℤ_ℓ`-submodule of `ℚ̄_ℓ`. -/
def toSubmodule (Λ : CompactLattice l) : Submodule ℤ_[l] (PadicAlgCl l) where
  __ := Λ.1
  smul_mem' c _ hx := Λ.smul_mem c hx

lemma mem_toSubmodule {Λ : CompactLattice l} {x : PadicAlgCl l} :
    x ∈ Λ.toSubmodule ↔ x ∈ Λ.1 :=
  Iff.rfl

/-- A compact lattice is a finitely generated `ℤ_ℓ`-module: it lies in the `ℤ_ℓ`-span of a
scaled `ℚ_ℓ`-basis of its `ℚ_ℓ`-span, its coordinates being bounded by compactness. -/
instance (Λ : CompactLattice l) : Module.Finite ℤ_[l] Λ.toSubmodule := by
  classical
  have := Λ.2.2
  set E := Submodule.span ℚ_[l] (Λ.1 : Set (PadicAlgCl l))
  let b := Module.finBasis ℚ_[l] E
  let ι : Λ.1 → E := fun x ↦ ⟨x, Submodule.subset_span x.2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hcont (i : Fin (Module.finrank ℚ_[l] E)) : Continuous fun x ↦ b.coord i (ι x) :=
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hι
  choose C hC using fun i ↦ isCompact_univ.exists_bound_of_continuousOn (hcont i).continuousOn
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ i, |C i|)
    (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  have hCN (i : Fin (Module.finrank ℚ_[l] E)) : C i ≤ (l : ℝ) ^ N :=
    ((le_abs_self _).trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j))
      (Finset.mem_univ i))).trans hN.le
  let v (i : Fin (Module.finrank ℚ_[l] E)) : PadicAlgCl l := ((l : ℚ_[l]) ^ N)⁻¹ • (b i : _)
  have hle : Λ.toSubmodule ≤ Submodule.span ℤ_[l] (Set.range v) := by
    intro x hx
    have hx' : x = ∑ i, b.coord i (ι ⟨x, hx⟩) • (b i : PadicAlgCl l) := by
      have h := congrArg Subtype.val (b.sum_repr (ι ⟨x, hx⟩))
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul, Module.Basis.coord_apply] at h ⊢
      exact h.symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hnorm : ‖(l : ℚ_[l]) ^ N * b.coord i (ι ⟨x, hx⟩)‖ ≤ 1 := by
      rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
      have := (hC i ⟨x, hx⟩ (Set.mem_univ _)).trans (hCN i)
      rw [inv_mul_le_one₀ (pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _)]
      exact this
    let c : ℤ_[l] := ⟨_, hnorm⟩
    have : b.coord i (ι ⟨x, hx⟩) • (b i : PadicAlgCl l) = c • v i := by
      rw [← IsScalarTower.algebraMap_smul ℚ_[l] c (v i)]
      simp only [v, smul_smul]
      congr 1
      change _ = ((l : ℚ_[l]) ^ N * b.coord i (ι ⟨x, hx⟩)) * ((l : ℚ_[l]) ^ N)⁻¹
      rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast
        (Fact.out : l.Prime).ne_zero)), one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Module.Finite.iff_fg]
  exact (Submodule.fg_span (Set.finite_range v)).of_le hle

instance : FaithfulSMul ℤ_[l] (PadicAlgCl l) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l]]
  exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp
    (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])

instance (Λ : CompactLattice l) : Module.Free ℤ_[l] Λ.toSubmodule :=
  Module.free_of_finite_type_torsion_free'

/-- The index type of the chosen `ℤ_ℓ`-basis of a compact lattice. -/
abbrev BasisIndex (Λ : CompactLattice l) : Type :=
  Module.Free.ChooseBasisIndex ℤ_[l] Λ.toSubmodule

/-- The chosen `ℤ_ℓ`-basis of a compact lattice. -/
noncomputable abbrev basis (Λ : CompactLattice l) : Module.Basis Λ.BasisIndex ℤ_[l] Λ.toSubmodule :=
  Module.Free.chooseBasis ℤ_[l] Λ.toSubmodule

/-- The `i`-th coordinate of an element of a compact lattice in the chosen basis. -/
noncomputable def coord (Λ : CompactLattice l) (i : Λ.BasisIndex) (x : Λ.1) : ℤ_[l] :=
  Λ.basis.equivFun ⟨x, x.2⟩ i

/-- Every element of a compact lattice is the combination of the basis with its coordinates. -/
lemma sum_coord_smul (Λ : CompactLattice l) (x : Λ.1) :
    ∑ i, Λ.coord i x • (Λ.basis i : PadicAlgCl l) = x := by
  have h := congrArg Subtype.val (Λ.basis.sum_equivFun ⟨x, x.2⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul] at h
  exact h

lemma coord_basis (Λ : CompactLattice l) (i j : Λ.BasisIndex) :
    Λ.coord i ⟨Λ.basis j, (Λ.basis j).2⟩ = if j = i then 1 else 0 := by
  classical
  simp [coord, Module.Basis.equivFun_self]

/-- The coordinates of a compact lattice are continuous: the map `ℤ_ℓ^ι ⟶ Λ` defined by the
basis is a continuous bijection from a compact space to a Hausdorff space. -/
lemma continuous_coord (Λ : CompactLattice l) (i : Λ.BasisIndex) : Continuous (Λ.coord i) := by
  let e : (Λ.BasisIndex → ℤ_[l]) ≃ Λ.1 :=
    Λ.basis.equivFun.symm.toEquiv.trans
      { toFun x := ⟨x, x.2⟩, invFun x := ⟨x, x.2⟩, left_inv _ := rfl, right_inv _ := rfl }
  have hcont : Continuous fun c : Λ.BasisIndex → ℤ_[l] ↦
      ((Λ.basis.equivFun.symm c : Λ.toSubmodule) : PadicAlgCl l) := by
    have : (fun c : Λ.BasisIndex → ℤ_[l] ↦
        ((Λ.basis.equivFun.symm c : Λ.toSubmodule) : PadicAlgCl l)) =
        fun c ↦ ∑ i, algebraMap ℤ_[l] (PadicAlgCl l) (c i) * (Λ.basis i : PadicAlgCl l) := by
      funext c
      simp [Module.Basis.equivFun_symm_apply, Algebra.smul_def]
    rw [this]
    exact continuous_finsetSum _ fun i _ ↦
      (continuous_algebraMap_padicInt.comp (continuous_apply i)).mul continuous_const
  have he : Continuous e := hcont.subtype_mk _
  let h := he.homeoOfEquivCompactToT2
  have : Λ.coord i = (fun c ↦ c i) ∘ h.symm := by
    funext x
    rfl
  rw [this]
  exact (continuous_apply i).comp h.symm.continuous

/-- Multiplication `c ↦ c • e` by an element `e` of a compact lattice, as a continuous
homomorphism `ℤ_ℓ ⟶ Λ`. -/
noncomputable def mulHom (Λ : CompactLattice l) (e : PadicAlgCl l)
    (he : e ∈ Λ.1) : ContinuousAddMonoidHom ℤ_[l] Λ.1 :=
  ⟨{ toFun c := ⟨c • e, Λ.smul_mem c he⟩
     map_zero' := Subtype.ext (zero_smul _ e)
     map_add' c d := Subtype.ext (add_smul c d e) },
    Continuous.subtype_mk (by
      simp only [Algebra.smul_def]
      exact continuous_algebraMap_padicInt.mul continuous_const) _⟩

/-- The `i`-th coordinate of a compact lattice, as a continuous homomorphism `Λ ⟶ ℤ_ℓ`. -/
noncomputable def coordHom (Λ : CompactLattice l) (i : Λ.BasisIndex) :
    ContinuousAddMonoidHom Λ.1 ℤ_[l] :=
  ⟨{ toFun := Λ.coord i
     map_zero' := congrFun (map_zero Λ.basis.equivFun) i
     map_add' x y := congrFun (map_add Λ.basis.equivFun ⟨x, x.2⟩ ⟨y, y.2⟩) i },
    Λ.continuous_coord i⟩

lemma coord_smul (Λ : CompactLattice l) (i : Λ.BasisIndex) (c : ℤ_[l])
    (x : Λ.1) : Λ.coord i ⟨c • (x : PadicAlgCl l), Λ.smul_mem c x.2⟩ = c * Λ.coord i x :=
  congrFun (map_smul Λ.basis.equivFun c ⟨x, x.2⟩) i

lemma _root_.ContinuousAddMonoidHom.sum_apply {A B : Type} [TopologicalSpace A]
    [AddCommGroup A] [IsTopologicalAddGroup A] [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] {ι : Type*} (s : Finset ι) (φ : ι → ContinuousAddMonoidHom A B)
    (x : A) : (∑ i ∈ s, φ i) x = ∑ i ∈ s, φ i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

lemma sum_mulHom_comp_coordHom (Λ : CompactLattice l) :
    ∑ i, (Λ.mulHom (Λ.basis i) (Λ.basis i).2).comp (Λ.coordHom i) =
      ContinuousAddMonoidHom.id Λ.1 := by
  refine ContinuousAddMonoidHom.ext fun x ↦ ?_
  rw [ContinuousAddMonoidHom.sum_apply]
  refine Subtype.ext (Eq.trans ?_ (Λ.sum_coord_smul x))
  rw [AddSubgroup.val_finsetSum]
  rfl

end CompactLattice

end PadicAlgCl
