/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.RepresentationTheory.IntegralModel
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Isometry

/-! # Continuous algebraic-closure representations have finite coefficient models

The private coordinate-model constructions are adapted from
`Sheaf.RepresentationTheory.LAdicSubrepresentation` (group N2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
namespace Representation
open scoped TensorProduct Matrix

private theorem isLAdic_of_basis_model
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (τ : G →* (V ≃ₗ[K] V)) (E : IntermediateField ℚ_[l] K)
    [FiniteDimensional ℚ_[l] E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V)
    (σ : G →* ((ι → E) ≃ₗ[E] (ι → E)))
    (hc : IsContinuousCoefficient l E G (ι → E) σ)
    (ha : letI := Module.compHom V (algebraMap E K)
      ∀ g v, Fintype.linearCombination E b (σ g v) =
        τ g (Fintype.linearCombination E b v)) :
    IsLAdic l K G V τ := by
  classical
  let := Module.compHom V (algebraMap E K)
  let f : (ι → E) →ₗ[E] V := Fintype.linearCombination E b
  have hf : Function.Injective f :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp
      (b.linearIndependent.restrict_scalars' E)
  let W : Submodule E V := f.range
  let c : (ι → E) ≃ₗ[E] W := LinearEquiv.ofInjective f hf
  let τW : G →* (W ≃ₗ[E] W) :=
    { toFun g := (c.symm.trans (σ g)).trans c
      map_one' := by ext v; simp
      map_mul' g h := by ext v; simp }
  have hW : FiniteDimensional E W := Module.Finite.equiv c
  refine ⟨Module.Finite.of_basis b, E, inferInstance, W, τW, ⟨hW, ?_⟩, ?_, ?_⟩
  · let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace (ι → E) := moduleTopology E (ι → E)
    let : TopologicalSpace W := moduleTopology E W
    have : IsTopologicalAddGroup (ι → E) := IsModuleTopology.isTopologicalAddGroup E _
    have : IsTopologicalAddGroup W := IsModuleTopology.isTopologicalAddGroup E _
    have : ContinuousSMul E (ι → E) := IsModuleTopology.toContinuousSMul E _
    have : ContinuousSMul E W := IsModuleTopology.toContinuousSMul E _
    have : ContinuousAdd (ι → E) :=
      (IsModuleTopology.isTopologicalAddGroup E (ι → E)).toContinuousAdd
    have : ContinuousAdd W := (IsModuleTopology.isTopologicalAddGroup E W).toContinuousAdd
    have hc' := IsModuleTopology.continuous_of_linearMap c.toLinearMap
    have hci := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
    exact hc'.comp (hc.2.comp (continuous_fst.prodMk (hci.comp continuous_snd)))
  · intro g x
    change f (σ g (c.symm x)) = τ g (x : V)
    rw [ha]
    congr 1
    exact congrArg Subtype.val (c.apply_symm_apply x)
  · let e := (c.symm.baseChange E K _ _).trans (IsBaseChange.of_fintype_basis E b).equiv
    refine ⟨e, ?_⟩
    intro a x
    change (IsBaseChange.of_fintype_basis E b).equiv
      (c.symm.baseChange E K _ _ (a ⊗ₜ[E] x)) = _
    rw [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul]
    congr 1
    exact congrArg Subtype.val (c.apply_symm_apply x)

private theorem isLAdic_of_matrix_model
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (τ : G →* (V ≃ₗ[K] V)) (E : IntermediateField ℚ_[l] K)
    [FiniteDimensional ℚ_[l] E] {ι : Type*} [Finite ι]
    (b : Module.Basis ι K V) (M : G → Matrix ι ι E)
    (he : ∀ g i j, algebraMap E K (M g i j) = b.repr (τ g (b j)) i)
    (hc : letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
      ∀ i j, Continuous (fun g ↦ M g i j)) :
    IsLAdic l K G V τ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let r : Representation K G V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ
  have he' (g : G) : (M g).map (algebraMap E K) = LinearMap.toMatrix b b (r g) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply]
    exact he g i j
  let m : G →* Matrix ι ι E :=
    { toFun := M
      map_one' := by
        apply Matrix.map_injective (algebraMap E K).injective
        change (M 1).map (algebraMap E K) = (1 : Matrix ι ι E).map (algebraMap E K)
        rw [he', Matrix.map_one _ (map_zero _) (map_one _), map_one,
          LinearMap.toMatrix_one]
      map_mul' g h := by
        apply Matrix.map_injective (algebraMap E K).injective
        change (M (g * h)).map (algebraMap E K) =
          (M g * M h).map (algebraMap E K)
        rw [Matrix.map_mul, he', he', he', map_mul, LinearMap.toMatrix_mul] }
  let σ : G →* ((ι → E) ≃ₗ[E] (ι → E)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E (ι → E)).toMonoidHom.comp
      ((Units.map (Matrix.toLinAlgEquiv' : Matrix ι ι E ≃ₐ[E] _).toMonoidHom).comp
        m.toHomUnits)
  have hσ (g : G) (v : ι → E) : σ g v = M g *ᵥ v := by
    change Matrix.toLinAlgEquiv' (M g) v = _
    exact Matrix.toLinAlgEquiv'_apply _ _
  have hcont : IsContinuousCoefficient l E G (ι → E) σ := by
    refine ⟨inferInstance, ?_⟩
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace (ι → E) := moduleTopology E (ι → E)
    have : IsTopologicalAddGroup (ι → E) := IsModuleTopology.isTopologicalAddGroup E _
    have : ContinuousSMul E (ι → E) := IsModuleTopology.toContinuousSMul E _
    have hcoord (j : ι) : Continuous (fun v : (ι → E) ↦ v j) :=
      IsModuleTopology.continuous_of_linearMap (LinearMap.proj j : (ι → E) →ₗ[E] E)
    have : ContinuousAdd (ι → E) :=
      (IsModuleTopology.isTopologicalAddGroup E (ι → E)).toContinuousAdd
    have hsum : Continuous (fun p : G × (ι → E) ↦ M p.1 *ᵥ p.2) := by
      have hvec : Continuous (fun p : G × (ι → E) ↦
          ∑ i, (∑ j, M p.1 i j * p.2 j) • Pi.single i (1 : E)) :=
        continuous_finsetSum _ (fun i _ ↦
          (continuous_finsetSum _ (fun j _ ↦
            ((hc i j).comp continuous_fst).mul ((hcoord j).comp continuous_snd))).smul
              continuous_const)
      exact hvec.congr (fun p ↦ by
        funext i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply])
    exact hsum.congr (fun p ↦ (hσ p.1 p.2).symm)
  let := Module.compHom V (algebraMap E K)
  let f := Fintype.linearCombination E b
  have hcoord (v : ι → E) :
      (fun i ↦ algebraMap E K (v i)) = b.equivFun (f v) :=
    (IsBaseChange.of_fintype_basis_eq (A := E) (b := b)).mp rfl
  apply isLAdic_of_basis_model l K G V τ E b σ hcont
  intro g v
  apply (IsBaseChange.of_fintype_basis_eq (A := E) (b := b)).mpr
  funext i
  change algebraMap E K ((σ g v) i) = b.repr (τ g (f v)) i
  rw [hσ, RingHom.map_mulVec]
  change ((M g).map (algebraMap E K) *ᵥ (fun j ↦ algebraMap E K (v j))) i = _
  rw [he', hcoord]
  exact congrFun (LinearMap.toMatrix_mulVec_repr b b (r g) (f v)) i


private theorem continuous_action_of_matrix
    {K : Type u} [NontriviallyNormedField K]
    {G : Type v} [TopologicalSpace G]
    {V : Type w} [AddCommGroup V] [Module K V]
    {ι : Type*} [Finite ι] (b : Module.Basis ι K V)
    (τ : G → (V ≃ₗ[K] V))
    (hc : ∀ i j, Continuous (fun g ↦ b.repr (τ g (b j)) i)) :
    let : TopologicalSpace V := moduleTopology K V
    Continuous (fun p : G × V ↦ τ p.1 p.2) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : TopologicalSpace V := moduleTopology K V
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  have : ContinuousSMul K V := IsModuleTopology.toContinuousSMul K V
  have hcoord (j : ι) : Continuous (fun v : V ↦ b.repr v j) :=
    IsModuleTopology.continuous_of_linearMap (b.coord j)
  have hsum : Continuous (fun p : G × V ↦
      ∑ i, (∑ j, b.repr (τ p.1 (b j)) i * b.repr p.2 j) • b i) :=
    continuous_finsetSum _ (fun i _ ↦
      (continuous_finsetSum _ (fun j _ ↦
        ((hc i j).comp continuous_fst).mul ((hcoord j).comp continuous_snd))).smul
          continuous_const)
  apply hsum.congr
  intro p
  have h := congrArg (fun z ↦ ∑ i, z i • b i)
    (LinearMap.toMatrix_mulVec_repr b b (τ p.1).toLinearMap p.2)
  simpa only [LinearMap.toMatrix_apply, Matrix.mulVec, dotProduct,
    Module.Basis.sum_repr, LinearEquiv.coe_coe] using h

private theorem coefficient_inclusion_isometry
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] :
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    Isometry (algebraMap E (PadicAlgCl l)) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  apply (AddMonoidHomClass.isometry_iff_norm (algebraMap E (PadicAlgCl l))).2
  intro z
  exact (spectralNorm.eq_of_tower (K := ℚ_[l]) (L := PadicAlgCl l) z).symm

private theorem continuous_model_entries
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] (G : ProfiniteGrp.{v})
    (W : Type w) [AddCommGroup W] [Module E W]
    (τE : G →* (W ≃ₗ[E] W)) (hcE : IsContinuousCoefficient l E G W τE)
    {ι : Type*} (c : Module.Basis ι E W) (i j : ι) :
    Continuous (fun g : G ↦ algebraMap E (PadicAlgCl l) (c.repr (τE g (c j)) i)) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace W := moduleTopology E W
  have : IsTopologicalAddGroup W := IsModuleTopology.isTopologicalAddGroup E W
  have : ContinuousSMul E W := IsModuleTopology.toContinuousSMul E W
  have hc : Continuous (fun g : G ↦ c.repr (τE g (c j)) i) :=
    (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp
      (hcE.2.comp (continuous_id.prodMk continuous_const))
  exact (coefficient_inclusion_isometry l E).continuous.comp hc

private theorem continuous_coefficient_function
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] {G : Type v} [TopologicalSpace G]
    (f : G → E) (hc : Continuous (fun g ↦ algebraMap E (PadicAlgCl l) (f g))) :
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    Continuous f := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  exact (coefficient_inclusion_isometry l E).isEmbedding.isInducing.continuous_iff.mpr hc

-- Finite-field model transport compares the full scalar-restriction and tensor structures.
/-- Continuous finite-dimensional representations over the p-adic algebraic closure
are exactly the representations with a continuous finite coefficient model.

Source: blueprint `proposition-lattices-representations-normal-scheme`, clause (5).
(blueprint: lisse-qlbar-continuous-finite-model)

Proof: choose a finite basis and apply compact-matrix coefficient descent to the
matrix monoid homomorphism. Its entries lie in one finite intermediate field E.
The inclusion E into the algebraic closure is isometric for the spectral norms,
so the entry functions remain continuous in E. The coordinate representation on
E^n has continuous action by its finite-sum formula. Its image under the basis map
is an actual invariant E-subspace, and the basis base-change equivalence gives
exactly the required tensor map. Conversely a finite model has continuous matrix
entries in an extended basis; compose these entries with the isometric field
inclusion and use the finite-sum action formula. The argument includes dimension zero. -/
theorem isLAdic_iff_continuous
    (l : ℕ) [Fact l.Prime] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module (PadicAlgCl l) V]
    (τ : G →* (V ≃ₗ[PadicAlgCl l] V)) :
    IsLAdic l (PadicAlgCl l) G V τ ↔
      FiniteDimensional (PadicAlgCl l) V ∧
      let : TopologicalSpace V := moduleTopology (PadicAlgCl l) V
      Continuous (fun p : G × V ↦ τ p.1 p.2) := by
  classical
  constructor
  · rintro ⟨hfin, E, hE, W, τE, hcE, hτE, e, he⟩
    have := hfin
    have := hE
    have : FiniteDimensional E W := hcE.1
    let c := Module.finBasis E W
    let b := (c.baseChange (PadicAlgCl l)).map e
    refine ⟨hfin, continuous_action_of_matrix b τ ?_⟩
    intro i j
    apply (continuous_model_entries l E G W τE hcE c i j).congr
    intro g
    have hb (j) : b j = (c j : V) := by
      change e (c.baseChange (PadicAlgCl l) j) = _
      rw [Module.Basis.baseChange_apply, he, one_smul]
    have hv : e (1 ⊗ₜ[E] τE g (c j)) = (τE g (c j) : V) := by
      rw [he, one_smul]
    rw [hb, ← hτE, ← hv]
    change algebraMap E (PadicAlgCl l) (c.repr (τE g (c j)) i) =
      (c.baseChange (PadicAlgCl l)).repr
        (e.symm (e (1 ⊗ₜ[E] τE g (c j)))) i
    rw [e.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
    simp [Algebra.smul_def]
  · rintro ⟨hfin, hcont⟩
    have := hfin
    let b := Module.finBasis (PadicAlgCl l) V
    let r : Representation (PadicAlgCl l) G V :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ
    let φ : G →* Matrix _ _ (PadicAlgCl l) :=
      (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp r
    have hc (i j) : Continuous (fun g ↦ φ g i j) := by
      let : TopologicalSpace V := moduleTopology (PadicAlgCl l) V
      have : IsTopologicalAddGroup V :=
        IsModuleTopology.isTopologicalAddGroup (PadicAlgCl l) V
      have : ContinuousSMul (PadicAlgCl l) V :=
        IsModuleTopology.toContinuousSMul (PadicAlgCl l) V
      exact (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp
        (hcont.comp (continuous_id.prodMk continuous_const))
    obtain ⟨E, hE, hcoeff⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem l φ hc
    have := hE
    let M (g : G) := fun i j ↦ (⟨φ g i j, hcoeff g i j⟩ : E)
    apply isLAdic_of_matrix_model l (PadicAlgCl l) G V τ E b M
      (fun g i j ↦ by
        change φ g i j = b.repr (τ g (b j)) i
        simp [φ, r, LinearMap.toMatrixAlgEquiv_apply])
    intro i j
    exact continuous_coefficient_function l E (fun g ↦ M g i j) (hc i j)

end Representation
