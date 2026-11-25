/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import WeilConjectures.RingTheory.PoincareDuality.AdicTowerReconstruction
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import WeilConjectures.RingTheory.FiniteModuleComplete

/-!
# Adic systems of finite modules over p-adic coefficient rings

Source: Stacks Project, Tags 09B8, 031D, 031B and 00MA;
blueprint `proposition-lattices-representations-normal-scheme`, steps 6, 7, 9 and 10
(blueprint: lem-pod-adic-limit-finite-modules).

Indices `n : ℕ` denote the positive exponent `n + 1`. A module over the coefficient
quotient is represented by its underlying module over the valuation ring, annihilated
by the corresponding ideal. Surjectivity and the specified kernel say that the
transition induces the required quotient isomorphism.
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped Pointwise
open Topology

namespace Padic

private theorem coefficientIntegers_complete (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsAdicComplete (coefficientExtensionMaximalIdeal l E)
      (coefficientExtensionIntegers l E) := by
  let R := coefficientExtensionIntegers l E
  let J := coefficientExtensionMaximalIdeal l E
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hR : ∀ x : E, x ∈ R ↔ coefficientExtensionAbsoluteValue l E x ≤ 1 := h.1
  let : IsLocalRing R := h.2.2.2.1
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hJ : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  let : NormedField E := spectralNorm.normedField ℚ_[l] E
  let : NormedSpace ℚ_[l] E := spectralNorm.normedSpace ℚ_[l] E
  let : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  have hball : (R : Set E) = Metric.closedBall 0 1 := by
    ext x
    change x ∈ R ↔ _
    rw [hR]
    simp only [Metric.mem_closedBall, dist_zero_right]
    rfl
  have : CompactSpace R := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    change IsCompact (R : Set E)
    rw [hball]
    exact isCompact_closedBall (0 : E) 1
  change IsAdicComplete J R
  rw [hJ]
  refine { prec' := ?_ }
  intro f hf
  let S n : Set R := f n +ᵥ (((IsLocalRing.maximalIdeal R) ^ n : Ideal R) : Set R)
  have hS n : S (n + 1) ⊆ S n := by
    apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
    simpa [S] using (hf n.le_succ).symm
  have hc n : IsClosed (S n) :=
    (IsNoetherianRing.isClosed_ideal ((IsLocalRing.maximalIdeal R) ^ n)).vadd (f n)
  obtain ⟨L, hL⟩ := (hc 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hS (by simp [S]) hc
  refine ⟨L, fun n ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
  simpa [SModEq.sub_mem] using hy

private theorem adicHomLift {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) (N : Type w) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsAdicComplete I N]
    (g : ∀ n : ℕ,
      (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) →ₗ[R ⧸ I ^ (n + 1)]
        (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)))
    (hg : ∀ n : ℕ,
      (Submodule.factorPow I N (Nat.le_succ (n + 1))).comp
        ((g (n + 1)).restrictScalars R) =
      ((g n).restrictScalars R).comp
        (Submodule.factorPow I M (Nat.le_succ (n + 1)))) :
    ∃! f : M →ₗ[R] N, ∀ n : ℕ, f.reduceModIdeal (I ^ (n + 1)) = g n := by
  let q : ∀ n : ℕ, M →ₗ[R] (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)) :=
    fun n ↦ ((g n).restrictScalars R).comp (I ^ (n + 1) • ⊤ : Submodule R M).mkQ
  have hq (n : ℕ) :
      (Submodule.factorPow I N (Nat.le_succ (n + 1))).comp (q (n + 1)) = q n := by
    change _ ∘ₗ (((g (n + 1)).restrictScalars R) ∘ₗ _) = _
    rw [← LinearMap.comp_assoc, hg n, LinearMap.comp_assoc]
    rfl
  let ha : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1
  let f : M →ₗ[R] N := IsAdicComplete.StrictMono.lift I ha q (fun {n} ↦ hq n)
  have hf (n : ℕ) : f.reduceModIdeal (I ^ (n + 1)) = g n := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    change Submodule.Quotient.mk (IsAdicComplete.StrictMono.lift I ha q
      (fun {n} ↦ hq n) x) = q n x
    exact IsAdicComplete.StrictMono.mk_lift I ha q (fun {n} ↦ hq n) (n := n) x
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n x
  have he := congrArg (fun g ↦ g (Submodule.Quotient.mk x)) ((hf' n).trans (hf n).symm)
  exact SModEq.mono (Submodule.pow_smul_top_le I N (Nat.le_succ n))
    (SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp he))

private theorem adicLinearMap_continuous {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  apply continuous_of_tendsto_nhds_zero f
  let : TopologicalSpace R := I.adicTopology
  let BM := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
  let BN := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis N)).toAddGroupFilterBasis
  rw [BM.nhds_zero_hasBasis.tendsto_iff BN.nhds_zero_hasBasis]
  rintro U ⟨n, rfl⟩
  refine ⟨(I ^ n • ⊤ : Submodule R M), ⟨n, rfl⟩, ?_⟩
  intro x hx
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) f hx

private theorem compatible_sections {R : Type u} [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) :
    (fun j : ℕᵒᵖ ↦ x j.unop) ∈ ModuleCat.sectionsSubmodule F := by
  have hall (m n : ℕ) (h : m ≤ n) : F.map (homOfLE h).op (x n) = x m := by
    induction n, h using Nat.le_induction with
    | base =>
      have he : (homOfLE (le_refl m)).op = 𝟙 (op m) := Subsingleton.elim _ _
      rw [he, F.map_id]
      rfl
    | succ n h ih =>
      have he : (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op =
          (homOfLE (Nat.le_trans h (Nat.le_succ n))).op := Subsingleton.elim _ _
      rw [← he, F.map_comp]
      change F.map (homOfLE h).op (F.map (homOfLE (Nat.le_succ n)).op (x (n + 1))) = _
      rw [hx n]
      exact ih
  intro i j f
  have he : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  change F.map f (x i.unop) = x j.unop
  rw [he]
  exact hall _ _ _

/-- Reconstruction of an adic system of finite coefficient modules.

Source: Stacks Tags 09B8 and 031D (blueprint: lem-pod-adic-limit-finite-modules), part 1.
Proof: apply lem-pod-adic-tower-reconstruction to the principal uniformizer ideal.
The sections submodule is the inverse limit. Its projections are surjective with
kernel the indicated ideal power, and identify its product-subspace topology with
its maximal-ideal-adic topology. By lem-weil-l-adic-extension-complete the coefficient
field is complete; its closed unit ball is complete too. The limit is separated and
its first reduction is finite, so lem-weil-pbc-finite-over-complete-ring (031D) makes
it finitely generated. Surjectivity and the kernel equality give the canonical
quotient isomorphisms by the first isomorphism theorem. -/
theorem adicLimit_finite_modules (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    let R := coefficientExtensionIntegers l E
    let I := Ideal.span ({coefficientExtensionUniformizer l E} : Set R)
    ∀ (F : ℕᵒᵖ ⥤ ModuleCat.{v} R),
      (∀ n : ℕ, Module.Finite R (F.obj (op n))) →
      (∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (F.obj (op n))) = ⊥) →
      (∀ n : ℕ,
        Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
        LinearMap.ker (F.map (homOfLE (Nat.le_succ n)).op).hom =
          I ^ (n + 1) • (⊤ : Submodule R (F.obj (op (n + 1))))) →
      let S := ModuleCat.sectionsSubmodule F
      Module.Finite R S ∧
        (∀ n : ℕ,
          let p := (LinearMap.proj (op n)).comp S.subtype
          Function.Surjective p ∧ LinearMap.ker p = I ^ (n + 1) • (⊤ : Submodule R S)) ∧
        (letI : ∀ j : ℕᵒᵖ, TopologicalSpace (F.obj j) := fun _ ↦ ⊥
         TopologicalSpace.induced (fun x : S ↦ x.val) inferInstance =
           (coefficientExtensionMaximalIdeal l E).adicModuleTopology S) := by
  classical
  intro R I F hfin hkill ht S
  let p (n : ℕ) : S →ₗ[R] F.obj (op n) := (LinearMap.proj (op n)).comp S.subtype
  have hp (n : ℕ) :
      (F.map (homOfLE (Nat.le_succ n)).op).hom.comp (p (n + 1)) = p n := by
    ext x
    exact x.property (homOfLE (Nat.le_succ n)).op
  have hlim (x : ∀ n : ℕ, F.obj (op n))
      (hx : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).hom (x (n + 1)) = x n) :
      ∃! y : S, ∀ n, p n y = x n := by
    refine ⟨⟨fun j ↦ x j.unop, compatible_sections F x hx⟩, fun _ ↦ rfl, ?_⟩
    intro y hy
    apply Subtype.ext
    funext j
    exact hy j.unop
  obtain ⟨he, _, hh, htop⟩ := Ideal.adic_tower_reconstruction I
    (Submodule.fg_span_singleton _) (fun n ↦ F.obj (op n))
    (fun n ↦ (F.map (homOfLE (Nat.le_succ n)).op).hom) hkill ht S p hp hlim
  have hproj (n : ℕ) : Function.Surjective (p n) ∧
      LinearMap.ker (p n) = I ^ (n + 1) • (⊤ : Submodule R S) := by
    obtain ⟨e, he⟩ := he n
    constructor
    · intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨y, (he y).symm⟩
    · ext x
      rw [LinearMap.mem_ker, ← he x, ← e.map_zero, e.injective.eq_iff]
      exact Submodule.Quotient.mk_eq_zero _
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hIJ : I = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let : IsAdicComplete I R := hIJ.symm ▸ coefficientIntegers_complete l E
  let : IsHausdorff I S := hh
  let : Module.Finite R (F.obj (op 0)) := hfin 0
  obtain ⟨e, _⟩ := he 0
  change (S ⧸ (I ^ 1 • ⊤ : Submodule R S)) ≃ₗ[R] F.obj (op 0) at e
  rw [pow_one] at e
  have hfinite : Module.Finite R (S ⧸ (I • ⊤ : Submodule R S)) :=
    Module.Finite.equiv e.symm
  let : Module.Finite R (S ⧸ (I • ⊤ : Submodule R S)) := hfinite
  let : Module.Finite (R ⧸ I) (S ⧸ (I • ⊤ : Submodule R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  refine ⟨(Module.finite_and_span_eq_top_of_adicComplete I S).1, hproj, ?_⟩
  let : ∀ j : ℕᵒᵖ, TopologicalSpace (F.obj j) := fun _ ↦ ⊥
  rw [induced_to_pi, ← hIJ, ← htop]
  apply le_antisymm
  · apply le_iInf
    intro n
    exact iInf_le_of_le (op n) le_rfl
  · apply le_iInf
    intro j
    exact iInf_le_of_le j.unop le_rfl

/-- Completeness, quotient towers, and Hom comparison for finite integral modules.

Source: Stacks Tags 031B, 09B8 and 00MA
(blueprint: lem-pod-adic-limit-finite-modules), part 2.
Proof: the valuation ring is Noetherian since it is a DVR and complete by
lem-weil-l-adic-extension-complete and the closed-unit-ball argument above.
Apply lem-weil-pbc-finite-module-complete-over-complete-noetherian to any finite
module. The canonical quotient transitions are surjective, with the stated kernels,
and the quotients are finite coefficient modules. A linear map preserves every ideal
power times the module and hence is continuous. Its reductions are compatible.
For a compatible family of reductions, send an element to the family of its images
in the target quotients, then use completeness of the target to reconstruct the
unique linear map. Separatedness gives uniqueness. The final unique-existence
clause is precisely bijectivity of the reduction map to the inverse limit of Hom. -/
theorem finite_module_adic_complete_and_hom (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    let R := coefficientExtensionIntegers l E
    let I := Ideal.span ({coefficientExtensionUniformizer l E} : Set R)
    let J := coefficientExtensionMaximalIdeal l E
    (∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      IsAdicComplete J M ∧ Function.Bijective (AdicCompletion.of I M) ∧
        (∀ n : ℕ,
          Module.Finite (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ∧
          let t := Submodule.factorPow I M (Nat.le_succ (n + 1))
          Function.Surjective t ∧ LinearMap.ker t =
            I ^ (n + 1) • (⊤ : Submodule R (M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M))))) ∧
    (∀ (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [AddCommGroup N] [Module R N] [Module.Finite R N],
      (∀ f : M →ₗ[R] N, @Continuous M N (J.adicModuleTopology M)
        (J.adicModuleTopology N) f) ∧
      (∀ g : ∀ n : ℕ,
        (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) →ₗ[R ⧸ I ^ (n + 1)]
          (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)),
        (∀ n : ℕ,
          (Submodule.factorPow I N (Nat.le_succ (n + 1))).comp
            ((g (n + 1)).restrictScalars R) =
          ((g n).restrictScalars R).comp
            (Submodule.factorPow I M (Nat.le_succ (n + 1)))) →
        ∃! f : M →ₗ[R] N, ∀ n : ℕ, f.reduceModIdeal (I ^ (n + 1)) = g n)) := by
  intro R I J
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hIJ : I = J := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let : IsAdicComplete J R := coefficientIntegers_complete l E
  let : IsAdicComplete I R := hIJ.symm ▸ (inferInstance : IsAdicComplete J R)
  constructor
  · intro M _ _ _
    let : IsAdicComplete I M :=
      finite_module_complete_over_complete_noetherian R I M
    refine ⟨hIJ ▸ (inferInstance : IsAdicComplete I M),
      AdicCompletion.of_bijective_iff.mpr inferInstance, ?_⟩
    intro n
    refine ⟨Module.Finite.of_restrictScalars_finite R _ _, ?_, ?_⟩
    · exact Submodule.factor_surjective _
    · change LinearMap.ker (Submodule.mapQ _ _ LinearMap.id _) = _
      rw [Submodule.ker_mapQ, Submodule.comap_id, Submodule.map_smul'',
        Submodule.map_top, Submodule.range_mkQ]
  · intro M N _ _ _ _ _ _
    let : IsAdicComplete I N :=
      finite_module_complete_over_complete_noetherian R I N
    constructor
    · intro f
      exact adicLinearMap_continuous J f
    · intro g hg
      exact adicHomLift I M N g hg

end Padic
