/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.Mathlib.Topology.Algebra.Group.DenseExtension
public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization
public import WeilConjectures.RepresentationTheory.WeilGroupLattice

/-!
# Bounded representations of Weil groups extend to the profinite completion

Let `W` be a Weil-type group: a degree `deg : W → ℤ` with an element `γ` of degree one and a
compact group `G₀ → W` onto `ker deg`, and let `α : W →* Π` be a homomorphism with dense range in a
profinite group (e.g. the Weil group `W(X₀) ⊆ π₁(X₀)`), a closed embedding on `G₀` and detecting
the degree modulo every `m`. A finite-dimensional `ℚ̄_ℓ`-representation `ρ` of `W` which is
continuous on `G₀` and bounded extends to a continuous representation of `Π`
(`Representation.exists_continuous_extension_of_isBoundedOn`, Deligne, Weil II, 1.1.7 and the end
of the proof of 1.3.14).

The matrices of `ρ(W)` in a basis have entries in a finite extension `E` of `ℚ_ℓ` (Baire category,
`LinearEquiv.exists_isDefinedOver_of_compactSpace`) and are bounded, so their closure in
`GL_n(ℚ̄_ℓ)` is a profinite group (bounded closed subsets of `E` are compact); the extension is
then `MonoidHom.exists_continuous_comp_eq_of_deg`.

## Main statements

- `Representation.matrixUnits`: the matrices of a representation in a basis, as units.
- `Representation.exists_continuous_extension_of_isBoundedOn`.
-/

@[expose] public section

open Module Topology

namespace Representation

section Matrix

variable {k W V ι : Type*} [Field k] [Group W] [AddCommGroup V] [Module k V] [Fintype ι]
  [DecidableEq ι]

/-- The matrices of a representation in a basis `b`, as a homomorphism to `GL_ι(k)`. -/
noncomputable def matrixUnits (ρ : Representation k W V) (b : Basis ι k V) :
    W →* (Matrix ι ι k)ˣ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.asGroupHom

theorem coe_matrixUnits (ρ : Representation k W V) (b : Basis ι k V) (w : W) :
    (ρ.matrixUnits b w : Matrix ι ι k) = LinearMap.toMatrix b b (ρ w) :=
  rfl

theorem matrixUnits_apply (ρ : Representation k W V) (b : Basis ι k V) (w : W) (i j : ι) :
    (ρ.matrixUnits b w : Matrix ι ι k) i j = b.coord i (ρ w (b j)) := by
  rw [coe_matrixUnits, LinearMap.toMatrix_apply, Basis.coord_apply]

theorem coe_matrixUnits_inv (ρ : Representation k W V) (b : Basis ι k V) (w : W) :
    (((ρ.matrixUnits b w)⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) =
      (ρ.matrixUnits b w⁻¹ : Matrix ι ι k) := by
  rw [map_inv]


end Matrix

variable {ℓ : ℕ} [Fact ℓ.Prime] {W V : Type*} [Group W] [AddCommGroup V]
  [Module (PadicAlgCl ℓ) V]

/-- Bounded subsets of a finite-dimensional `ℚ_ℓ`-subalgebra of `ℚ̄_ℓ` are relatively compact:
`{x ∈ A | ‖x‖ ≤ C}` is compact. -/
theorem _root_.Subalgebra.isCompact_setOf_mem_norm_le (A : Subalgebra ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] A] (C : ℝ) :
    IsCompact {x : PadicAlgCl ℓ | x ∈ A ∧ ‖x‖ ≤ C} := by
  set S := Subalgebra.toSubmodule A
  have : FiniteDimensional ℚ_[ℓ] S := ‹FiniteDimensional ℚ_[ℓ] A›
  have : ProperSpace S := FiniteDimensional.proper ℚ_[ℓ] S
  have h := (isCompact_closedBall (0 : S) C).image continuous_subtype_val
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hC⟩
    exact ⟨⟨x, hx⟩, by simpa using hC, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩

/-- **Bounded representations of Weil groups extend continuously** (Deligne, Weil II, 1.1.7 and
the end of the proof of 1.3.14). Let `deg : W →* ℤ`, `γ` of degree one and `θ : G₀ →* W` from a
compact group onto `ker deg`; let `α : W →* Π` have dense range in a profinite group, be a
continuous injection on `G₀`, and detect the degree modulo every `m > 0`. Then every
finite-dimensional `ℚ̄_ℓ`-representation `ρ` of `W`, continuous on `G₀` and bounded on `W`, is the
restriction along `α` of a representation `σ` of `Π` with continuous matrix coefficients. -/
theorem exists_continuous_extension_of_isBoundedOn {P G₀ : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] [Group G₀]
    [TopologicalSpace G₀] [IsTopologicalGroup G₀] [CompactSpace G₀] [T2Space G₀]
    [FiniteDimensional (PadicAlgCl ℓ) V] (deg : W →* Multiplicative ℤ) {γ : W}
    (hγ : deg γ = Multiplicative.ofAdd 1) (θ : G₀ →* W) (hθ : ∀ w, deg w = 1 → ∃ g, θ g = w)
    (α : W →* P) (hα : DenseRange α) (hαθ : Continuous (α.comp θ))
    (hαθinj : Function.Injective (α.comp θ))
    (hdeg : ∀ m : ℕ, 0 < m → ∃ O : Set P, IsOpen O ∧ (1 : P) ∈ O ∧
      ∀ w, α w ∈ O → (m : ℤ) ∣ Multiplicative.toAdd (deg w))
    (ρ : Representation (PadicAlgCl ℓ) W V) (hρθ : ρ.IsContinuousOn θ)
    (hρ : ρ.IsBoundedOn Set.univ) :
    ∃ σ : Representation (PadicAlgCl ℓ) P V,
      (∀ (φ : Module.Dual (PadicAlgCl ℓ) V) (v : V), Continuous fun g ↦ φ (σ g v)) ∧
        ∀ w, σ (α w) = ρ w := by
  classical
  set b := Module.finBasis (PadicAlgCl ℓ) V
  set ι := Fin (Module.finrank (PadicAlgCl ℓ) V)
  set R := ρ.matrixUnits b
  -- the matrix coefficients are continuous on `G₀`
  have hcont (i j : ι) : Continuous fun g ↦ (R (θ g) : Matrix ι ι (PadicAlgCl ℓ)) i j := by
    simp_rw [R, matrixUnits_apply]
    exact hρθ (b.coord i) (b j)
  -- all matrices have entries in a finite extension `E` of `ℚ_ℓ`
  obtain ⟨E, hE, hEfd, hEcover⟩ := PadicAlgCl.exists_monotone_finiteDimensional_cover (ℓ := ℓ)
  set A : ℕ → Subalgebra ℚ_[ℓ] (PadicAlgCl ℓ) := fun m ↦ (E m).toSubalgebra
  have hA : Monotone A := fun m n h ↦ hE h
  set ρ' : W →* (V ≃ₗ[PadicAlgCl ℓ] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ V).toMonoidHom.comp ρ.asGroupHom
  have hρ' (w : W) : (ρ' w).toLinearMap = ρ w := rfl
  have hσ (i j : ι) :
      Continuous fun g ↦ LinearMap.toMatrix b b ((ρ'.comp θ) g).toLinearMap i j := hcont i j
  have hclosed (m : ℕ) : IsClosed (A m : Set (PadicAlgCl ℓ)) := by
    have := hEfd m
    exact Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (E m).toSubalgebra)
  obtain ⟨m₀, hm₀⟩ := LinearEquiv.exists_isDefinedOver_of_compactSpace (ρ'.comp θ) b hσ hA
    hclosed hEcover
  obtain ⟨m₁, hm₁⟩ := LinearEquiv.exists_isDefinedOver_of_monotone hA hEcover (ρ' γ) b
  set M := max m₀ m₁
  have hFD : FiniteDimensional ℚ_[ℓ] (A M) := hEfd M
  have hdef (w : W) : (ρ' w).IsDefinedOver b (A M) := by
    have hw : w ∈ (LinearEquiv.definedOverSubgroup b (A M)).comap ρ' := by
      have htop : Subgroup.closure (Set.range θ ∪ {γ}) = ⊤ := by
        refine (Subgroup.eq_top_iff' _).2 fun w ↦ ?_
        obtain ⟨g, hg⟩ := hθ (w * γ ^ (-Multiplicative.toAdd (deg w))) (by
          rw [map_mul, map_zpow, hγ, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_neg, ofAdd_toAdd,
            mul_inv_cancel])
        have h₁ : w * γ ^ (-Multiplicative.toAdd (deg w)) ∈
            Subgroup.closure (Set.range θ ∪ {γ}) :=
          Subgroup.subset_closure (Or.inl ⟨g, hg⟩)
        have h₂ : γ ∈ Subgroup.closure (Set.range θ ∪ {γ}) := Subgroup.subset_closure (Or.inr rfl)
        simpa using mul_mem h₁ (Subgroup.zpow_mem _ h₂ (Multiplicative.toAdd (deg w)))
      refine (Subgroup.closure_le _).2 ?_ (htop ▸ Subgroup.mem_top w)
      rintro _ (⟨g, rfl⟩ | rfl)
      · exact (hm₀ g).mono (hA (le_max_left _ _))
      · exact hm₁.mono (hA (le_max_right _ _))
    exact hw
  have hmemA (w : W) (i j : ι) : (R w : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ A M :=
    (hdef w i j).1
  -- the matrix coefficients are bounded
  choose C hC using fun p : ι × ι ↦ hρ (b p.2) (b.coord p.1)
  obtain ⟨C₀, hC₀⟩ := Finite.exists_le C
  have hbound (w : W) (i j : ι) : ‖(R w : Matrix ι ι (PadicAlgCl ℓ)) i j‖ ≤ C₀ := by
    rw [matrixUnits_apply]
    exact (hC (i, j) _ ⟨w, Set.mem_univ _, rfl⟩).trans (hC₀ (i, j))
  -- the closure of the image is a profinite group
  set T : Set (PadicAlgCl ℓ) := {x | x ∈ A M ∧ ‖x‖ ≤ C₀}
  have hT : IsCompact T := (A M).isCompact_setOf_mem_norm_le C₀
  set T' : Set (Matrix ι ι (PadicAlgCl ℓ)) := Set.univ.pi fun i ↦ Set.univ.pi fun j ↦ T
  have hT' : IsCompact T' := isCompact_univ_pi fun i ↦ isCompact_univ_pi fun j ↦ hT
  set K : Set (Matrix ι ι (PadicAlgCl ℓ))ˣ :=
    Units.embedProduct _ ⁻¹' (T' ×ˢ (MulOpposite.unop ⁻¹' T'))
  have hK : IsCompact K := by
    refine Units.isClosedEmbedding_embedProduct.isCompact_preimage (hT'.prod ?_)
    exact (MulOpposite.opHomeomorph.symm.isCompact_preimage (s := T')).2 hT'
  have hRK (w : W) : R w ∈ K := by
    refine ⟨fun i _ j _ ↦ ⟨hmemA w i j, hbound w i j⟩, fun i _ j _ ↦ ?_⟩
    change ((R w)⁻¹ : (Matrix ι ι (PadicAlgCl ℓ))ˣ) i j ∈ T
    rw [← map_inv]
    exact ⟨hmemA _ i j, hbound _ i j⟩
  set Γ := R.range.topologicalClosure
  have hΓK : (Γ : Set (Matrix ι ι (PadicAlgCl ℓ))ˣ) ⊆ K :=
    closure_minimal (by rintro _ ⟨w, rfl⟩; exact hRK w) hK.isClosed
  have : CompactSpace Γ := isCompact_iff_compactSpace.1
    (hK.of_isClosed_subset R.range.isClosed_topologicalClosure hΓK)
  have : TotallyDisconnectedSpace (Matrix ι ι (PadicAlgCl ℓ)) :=
    inferInstanceAs (TotallyDisconnectedSpace (ι → ι → PadicAlgCl ℓ))
  have : TotallyDisconnectedSpace (Matrix ι ι (PadicAlgCl ℓ))ˣ := by
    rw [totallyDisconnectedSpace_iff]
    exact isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  set R' : W →* Γ := R.codRestrict Γ fun w ↦ R.range.le_topologicalClosure ⟨w, rfl⟩
  have hR'θ : Continuous (R'.comp θ) := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact continuous_pi fun i ↦ continuous_pi fun j ↦ hcont i j
    · have h : (fun g ↦ (((R (θ g))⁻¹ : (Matrix ι ι (PadicAlgCl ℓ))ˣ) :
          Matrix ι ι (PadicAlgCl ℓ))) = fun g ↦ (R (θ g⁻¹) : Matrix ι ι (PadicAlgCl ℓ)) := by
        funext g
        rw [map_inv, map_inv]
      change Continuous fun g ↦ (((R (θ g))⁻¹ : (Matrix ι ι (PadicAlgCl ℓ))ˣ) :
        Matrix ι ι (PadicAlgCl ℓ))
      rw [h]
      exact continuous_pi fun i ↦ continuous_pi fun j ↦ (hcont i j).comp continuous_inv
  obtain ⟨σΓ, hσΓ, hσα⟩ := MonoidHom.exists_continuous_comp_eq_of_deg deg hγ θ hθ α R' hα hαθ
    hαθinj hR'θ hdeg
  let mat : P → Matrix ι ι (PadicAlgCl ℓ) := fun g ↦ ((σΓ g).1 : Matrix ι ι (PadicAlgCl ℓ))
  have hmat : Continuous mat := Units.continuous_val.comp (continuous_subtype_val.comp hσΓ)
  let σ : Representation (PadicAlgCl ℓ) P V :=
    (LinearMap.toMatrixAlgEquiv b).symm.toMonoidHom.comp
      ((Units.coeHom _).comp (Γ.subtype.comp σΓ))
  have hσval (g : P) : LinearMap.toMatrix b b (σ g) = mat g :=
    (LinearMap.toMatrixAlgEquiv b).apply_symm_apply _
  refine ⟨σ, fun φ v ↦ ?_, fun w ↦ ?_⟩
  · have h (g : P) : φ (σ g v) = ∑ j, Matrix.mulVec (mat g) (b.repr v) j * φ (b j) := by
      conv_lhs => rw [← Matrix.toLin_toMatrix b b (σ g), hσval, Matrix.toLin_apply]
      simp [map_sum, map_smul, smul_eq_mul]
    simp_rw [h]
    exact continuous_finsetSum _ fun j _ ↦
      ((continuous_apply j).comp (hmat.matrix_mulVec continuous_const)).mul continuous_const
  · have h1 : σΓ (α w) = R' w := DFunLike.congr_fun hσα w
    change (LinearMap.toMatrixAlgEquiv b).symm (mat (α w)) = ρ w
    simp only [mat, h1]
    exact (LinearMap.toMatrixAlgEquiv b).symm_apply_apply (ρ w)

end Representation
