/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# Integral models of continuous `ℓ`-adic representations of compact groups

Let `G` be a compact topological group acting continuously on a finite-dimensional
`ℚ̄_ℓ`-vector space `V`. This file shows that the action is defined over a finite extension
`E/ℚ_ℓ` and preserves an `𝒪_E`-lattice in `V`. These are the two steps of the proof of
`proposition-lattices-representations-normal-scheme`
(`AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`).

## Main statements

- `PadicAlgCl.exists_finiteDimensional_forall_mem`: the matrix coefficients of a continuous
  matrix representation of a compact group over `ℚ̄_ℓ` all lie in one finite extension `E`
  of `ℚ_ℓ`.
- `PadicAlgCl.exists_lattice_of_forall_mem`: a representation whose matrix coefficients lie in
  `E` and are bounded preserves an `𝒪_E`-lattice `L`, and has finite image on every
  `L / 𝔪_Eⁿ L`.

## Implementation notes

The first statement is a Baire category argument. By
`PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple` the countably many fields `ℚ_ℓ(T)`, for `T` a
finite set of elements of `ℚ̄_ℓ` algebraic over `ℚ`, cover `ℚ̄_ℓ`. The elements of `G` whose
matrix (and inverse matrix) has coefficients in `ℚ_ℓ(T)` form a closed subgroup, since
`ℚ_ℓ(T)` is closed in `ℚ̄_ℓ`. By the Baire category theorem one of these subgroups is open,
and by compactness a single one of them is all of `G`.

The `𝒪_E`-module structure on `V` is the restriction of scalars along `𝒪_E → E → ℚ̄_ℓ`. The
lattice is the `𝒪_E`-span of the orbit of a basis: it contains the basis, and it is contained
in `ℓ⁻ᵏ` times the span of the basis when the coefficients are bounded by `ℓᵏ`. So it is a
finitely generated torsion-free module over the principal ideal ring `𝒪_E`, hence free, and of
full rank.
-/

@[expose] public section

open Module Polynomial IntermediateField

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `proposition-lattices-representations-normal-scheme`: the first step of the proof.

The matrix coefficients of a continuous matrix representation `φ` of a compact group over
`ℚ̄_ℓ` all lie in a single finite extension `E` of `ℚ_ℓ`. -/
theorem exists_finiteDimensional_forall_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : G →* Matrix ι ι (PadicAlgCl l)) (hφ : ∀ i j, Continuous fun g ↦ φ g i j) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g i j, φ g i j ∈ E := by
  classical
  -- the countably many fields `F t = ℚ_ℓ(t)`, for `t` a finite set of algebraic numbers
  let T := {x : PadicAlgCl l // IsAlgebraic ℚ x}
  have : Countable T := (Algebraic.countable ℚ (PadicAlgCl l)).to_subtype
  choose β hβ using exists_isAlgebraic_mem_adjoin_simple l
  let F : Finset T → IntermediateField ℚ_[l] (PadicAlgCl l) := fun t ↦
    adjoin ℚ_[l] ((↑) '' (t : Set T))
  have hF (t : Finset T) : FiniteDimensional ℚ_[l] (F t) :=
    finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have hFmono : Monotone F := fun s t hst ↦ adjoin.mono _ _ _ (Set.image_mono hst)
  -- the closed subgroups `X t` of elements whose coefficients lie in `F t`; they cover `G`
  let X : Finset T → Subgroup G := fun t ↦
    { carrier := {g | ∀ i j, φ g i j ∈ F t ∧ φ g⁻¹ i j ∈ F t}
      mul_mem' := by
        intro a b ha hb i j
        simp only [Set.mem_ofPred_eq, map_mul, mul_inv_rev, Matrix.mul_apply] at ha hb ⊢
        exact ⟨sum_mem fun k _ ↦ mul_mem (ha i k).1 (hb k j).1,
          sum_mem fun k _ ↦ mul_mem (hb i k).2 (ha k j).2⟩
      one_mem' := by
        intro i j
        simp only [map_one, inv_one, and_self, Matrix.one_apply]
        split_ifs <;> simp [one_mem, zero_mem]
      inv_mem' := by
        intro a ha i j
        simpa [and_comm] using ha i j }
  have hXmono : Monotone X := fun s t hst g hg i j ↦
    ⟨hFmono hst (hg i j).1, hFmono hst (hg i j).2⟩
  have hXclosed (t : Finset T) : IsClosed (X t : Set G) := by
    have := hF t
    have hc := isClosed_intermediateField l (F t)
    simp only [X, Subgroup.coe_set_mk, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ (hc.preimage (hφ i j)).inter
      (hc.preimage ((hφ i j).comp continuous_inv))
  have hmem (g : G) : ∃ t, g ∈ X t := by
    let t : Finset T := Finset.univ.image fun p : ι × ι × Bool ↦
      ⟨β (φ (if p.2.2 then g else g⁻¹) p.1 p.2.1),
        (hβ (φ (if p.2.2 then g else g⁻¹) p.1 p.2.1)).1⟩
    have key (h : G) (hh : h = g ∨ h = g⁻¹) (i j : ι) : φ h i j ∈ F t := by
      have hle : ℚ_[l]⟮β (φ h i j)⟯ ≤ F t := by
        rw [adjoin_simple_le_iff]
        refine subset_adjoin _ _ ⟨⟨β (φ h i j), (hβ _).1⟩, ?_, rfl⟩
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, t]
        rcases hh with rfl | rfl
        · exact ⟨(i, j, true), rfl⟩
        · exact ⟨(i, j, false), rfl⟩
      exact hle (hβ _).2
    exact ⟨t, fun i j ↦ ⟨key g (.inl rfl) i j, key g⁻¹ (.inr rfl) i j⟩⟩
  -- by Baire one `X s` is open, and by compactness a single `X (s ∪ t)` is all of `G`
  obtain ⟨s, hs⟩ := nonempty_interior_of_iUnion_of_closed hXclosed
    (Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.mpr (hmem g))
  obtain ⟨g₀, hg₀⟩ := hs
  have hopen (t : Finset T) : IsOpen (X (s ∪ t) : Set G) :=
    Subgroup.isOpen_mono (hXmono Finset.subset_union_left)
      (Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.mp hg₀))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_directed_cover (fun t ↦ (X (s ∪ t) : Set G)) hopen
    (fun g _ ↦ by
      obtain ⟨t, ht⟩ := hmem g
      exact Set.mem_iUnion.mpr ⟨t, hXmono Finset.subset_union_right ht⟩)
    (fun a b ↦ ⟨a ∪ b, hXmono (Finset.union_subset_union_right Finset.subset_union_left),
      hXmono (Finset.union_subset_union_right Finset.subset_union_right)⟩)
  exact ⟨F (s ∪ t), hF _, fun g i j ↦ (ht (Set.mem_univ g) i j).1⟩

/-- Blueprint `proposition-lattices-representations-normal-scheme`: the second step of the proof.

Let `σ` be a representation of a group `G` on a `ℚ̄_ℓ`-vector space `V` with basis `b`, whose
matrix coefficients lie in a finite extension `E` of `ℚ_ℓ` and are bounded. Then the
`𝒪_E`-span `L` of the orbit of `b` is an `𝒪_E`-lattice in `V`: it is free of rank `dim V` and
spans `V`. It is stable under `σ`, and `G` has finite image on every `L / 𝔪_Eⁿ L`. This finite
image is expressed as in `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`, as the
finiteness of the set of induced maps `L → V / 𝔪_Eⁿ L`. -/
theorem exists_lattice_of_forall_mem {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl l) V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι (PadicAlgCl l) V) (σ : Representation (PadicAlgCl l) G V)
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E]
    (hE : ∀ g i j, LinearMap.toMatrix b b (σ g) i j ∈ E) (C : ℝ)
    (hC : ∀ g i j, ‖LinearMap.toMatrix b b (σ g) i j‖ ≤ C) :
    letI : Module (integers l (E : Type)) V :=
      Module.compHom V ((algebraMap (E : Type) (PadicAlgCl l)).comp
        (integers l (E : Type)).subtype)
    ∃ L : Submodule (integers l (E : Type)) V,
      Module.Free (integers l (E : Type)) L ∧
      Module.finrank (integers l (E : Type)) L = Module.finrank (PadicAlgCl l) V ∧
      Submodule.span (PadicAlgCl l) (L : Set V) = ⊤ ∧
      (∀ g, ∀ x ∈ L, σ g x ∈ L) ∧
      ∀ n : ℕ, (Set.range fun g : G ↦ fun x : L ↦
        Submodule.Quotient.mk (p := (IsLocalRing.maximalIdeal
          (integers l (E : Type)) ^ n) • L) (σ g x)).Finite := by
  classical
  set O := integers l (E : Type)
  let f : O →+* PadicAlgCl l := (algebraMap (E : Type) (PadicAlgCl l)).comp O.subtype
  let : Module O V := Module.compHom V f
  have : IsScalarTower O (PadicAlgCl l) V := ⟨fun a x v ↦ mul_smul (f a) x v⟩
  have hf : Function.Injective fun a : O ↦ a • (1 : PadicAlgCl l) := by
    intro a a' h
    exact Subtype.ext (Subtype.ext (by simpa using h))
  have : FaithfulSMul O (PadicAlgCl l) := (faithfulSMul_iff_injective_smul_one O _).mpr hf
  have : Module.IsTorsionFree O V := .trans_faithfulSMul O (PadicAlgCl l) V
  -- the scaling constant `c = ℓ ^ k`, with `‖c‖ * C ≤ 1`
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hl
  let c : PadicAlgCl l := algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ k)
  have hcnorm : ‖c‖ = ((l : ℝ) ^ k)⁻¹ := by
    rw [norm_extends, norm_pow, Padic.norm_p, inv_pow]
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hcnorm]
    positivity
  have hcE : c ∈ E := E.algebraMap_mem _
  -- the lattice `L`, spanned by the orbit of `b`, and the ambient lattice `N = c⁻¹ ⟨b⟩`
  let L : Submodule O V := Submodule.span O (Set.range fun p : G × ι ↦ σ p.1 (b p.2))
  let N : Submodule O V := Submodule.span O (Set.range fun j ↦ c⁻¹ • b j)
  have hbL (i : ι) : b i ∈ L := Submodule.subset_span ⟨(1, i), by simp⟩
  have hLN : L ≤ N := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨g, i⟩, rfl⟩
    have hsum : σ g (b i) = ∑ j, LinearMap.toMatrix b b (σ g) j i • b j := by
      simp [LinearMap.toMatrix_apply, b.sum_repr]
    change σ g (b i) ∈ N
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    let a : O := ⟨⟨c * LinearMap.toMatrix b b (σ g) j i, mul_mem hcE (hE g j i)⟩, by
      rw [mem_integers_iff, ← NNReal.coe_le_coe]
      change ‖c * LinearMap.toMatrix b b (σ g) j i‖ ≤ 1
      rw [norm_mul, hcnorm]
      calc ((l : ℝ) ^ k)⁻¹ * ‖LinearMap.toMatrix b b (σ g) j i‖
          ≤ ((l : ℝ) ^ k)⁻¹ * (l : ℝ) ^ k := by gcongr; exact (hC g j i).trans hk.le
        _ = 1 := inv_mul_cancel₀ (by positivity)⟩
    have : LinearMap.toMatrix b b (σ g) j i • b j = a • (c⁻¹ • b j) := by
      change _ = f a • (c⁻¹ • b j)
      rw [smul_smul]
      congr 1
      change _ = c * _ * c⁻¹
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hstab (g : G) : ∀ x ∈ L, σ g x ∈ L := by
    have : L ≤ L.comap ((σ g).restrictScalars O) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨h, i⟩, rfl⟩
      change σ g (σ h (b i)) ∈ L
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨(g * h, i), rfl⟩
    exact fun x hx ↦ this hx
  -- finiteness and freeness of `L`
  have hNli : LinearIndependent O fun j ↦ c⁻¹ • b j :=
    (b.linearIndependent.units_smul fun _ ↦
      (Units.mk0 c⁻¹ (inv_ne_zero hc0) : (PadicAlgCl l)ˣ)).restrict_scalars hf
  have hbli : LinearIndependent O b := b.linearIndependent.restrict_scalars hf
  let bN : Basis ι O N := Basis.span hNli
  have : Module.Finite O N := Module.Finite.of_basis bN
  have : IsNoetherian O L := isNoetherian_of_le hLN
  have hfree : Module.Free O L := inferInstance
  have hrank : Module.finrank O L = Fintype.card ι := by
    refine le_antisymm ?_ ?_
    · rw [← (Submodule.comapSubtypeEquivOfLe hLN).finrank_eq, ← Module.finrank_eq_card_basis bN]
      exact Submodule.finrank_le _
    · exact LinearIndependent.fintype_card_le_finrank (b := fun i ↦ (⟨b i, hbL i⟩ : L))
        (LinearIndependent.of_comp L.subtype hbli)
  refine ⟨L, hfree, by rw [hrank, Module.finrank_eq_card_basis b], ?_, hstab, fun n ↦ ?_⟩
  · rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono (Set.range_subset_iff.mpr hbL)
  -- the reductions modulo `𝔪 ^ n`
  set I := IsLocalRing.maximalIdeal O ^ n
  let P : Submodule O V := I • L
  let π' : (L ⧸ I • (⊤ : Submodule O L)) →ₗ[O] V ⧸ P :=
    (I • (⊤ : Submodule O L)).liftQ (P.mkQ ∘ₗ L.subtype) <| by
      rw [Submodule.smul_le]
      intro r hr m _
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr m.2)
  have : Finite (L ⧸ I • (⊤ : Submodule O L)) := Module.finite_of_finite (O ⧸ I)
  let cb := Module.Free.chooseBasis O L
  refine (Set.finite_range fun q : Module.Free.ChooseBasisIndex O L → L ⧸ I • (⊤ : Submodule O L) ↦
    fun x : L ↦ ∑ k, cb.repr x k • π' (q k)).subset ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨fun k ↦ Submodule.Quotient.mk ⟨σ g (cb k), hstab g _ (cb k).2⟩, funext fun x ↦ ?_⟩
  have hx : (x : V) = ∑ k, cb.repr x k • (cb k : V) := by
    nth_rw 1 [← cb.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  let T : V →ₗ[O] V ⧸ P := P.mkQ ∘ₗ (σ g).restrictScalars O
  change ∑ k, cb.repr x k • T (cb k) = T x
  rw [hx, map_sum]
  simp_rw [map_smul]

end PadicAlgCl
