/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Invariants of discrete representations of pro-`p` groups

Let `G` be a compact topological group and `A` a commutative ring in which the index of every
open normal subgroup of `G` is invertible (e.g. `G` pro-`p` and `p` invertible in `A`). For a
*discrete* representation `ρ` of `G` on an `A`-module `E` (every vector has an open stabilizer,
`Representation.IsDiscrete`), we construct an `A`-linear retraction
`Representation.discreteAverage : E →ₗ[A] ρ.invariants` of the inclusion of the invariants; on
vectors fixed by an open normal subgroup `U` it is the average over the finite quotient `G ⧸ U`.
From this we deduce:

* `Representation.IsDiscrete.map_invariants_eq`: taking invariants is exact on discrete
  representations, i.e. an equivariant surjection is surjective on invariants;
* `Representation.invariantsTensorEquiv`: for an `A`-module `B` with trivial action, the natural
  map `ρ.invariants ⊗[A] B → (ρ ⊗ trivial)^G` is an isomorphism.

This is the blueprint lemma `prose-E-10`, used in Gabber's Künneth formula for
nearby cycles (Illusie, *Autour du théorème de monodromie locale*, 4.7).

The finite-level input is `Representation.cosetSum`, the sum of the `ρ g` over representatives
of the left cosets of a finite-index subgroup `N`; on vectors fixed by `N` (with `N` normal) it
takes values in the invariants and is both left and right `G`-invariant, and on invariant vectors
it is multiplication by the index of `N`.
-/

@[expose] public section

open TensorProduct

namespace Representation

variable {G A E : Type*} [Group G] [CommRing A] [AddCommGroup E] [Module A E]

section CosetSum

variable (ρ : Representation A G E) (N : Subgroup G)

/-- The sum of the operators `ρ g` over a set of representatives `g` of the left cosets of a
finite-index subgroup `N`. On vectors fixed by `N` this does not depend on the representatives. -/
noncomputable def cosetSum [Finite (G ⧸ N)] : E →ₗ[A] E :=
  haveI := Fintype.ofFinite (G ⧸ N)
  ∑ q : G ⧸ N, ρ q.out

lemma cosetSum_apply [Fintype (G ⧸ N)] [Finite (G ⧸ N)] (v : E) :
    ρ.cosetSum N v = ∑ q : G ⧸ N, ρ q.out v := by
  rw [cosetSum, LinearMap.sum_apply]
  convert rfl

variable {ρ N}

/-- For a vector fixed by `N`, `ρ g v` only depends on the coset `g N`. -/
lemma apply_out_mk_of_forall_mem {v : E} (hv : ∀ h ∈ N, ρ h v = v) (g : G) :
    ρ (QuotientGroup.mk g : G ⧸ N).out v = ρ g v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
  rw [hh, map_mul, Module.End.mul_apply, hv h h.2]

/-- The coset sum of a vector fixed by a normal subgroup is invariant. -/
lemma cosetSum_mem_invariants [N.Normal] [Finite (G ⧸ N)] {v : E} (hv : ∀ h ∈ N, ρ h v = v) :
    ρ.cosetSum N v ∈ ρ.invariants := by
  have := Fintype.ofFinite (G ⧸ N)
  intro g
  rw [cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (g : G ⧸ N)) _ _ fun q ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [Equiv.coe_mulLeft, ← QuotientGroup.mk_mul, apply_out_mk_of_forall_mem hv, map_mul,
    Module.End.mul_apply]

/-- The coset sum is right invariant on vectors fixed by a normal subgroup. -/
lemma cosetSum_apply_apply [N.Normal] [Finite (G ⧸ N)] {v : E} (hv : ∀ h ∈ N, ρ h v = v)
    (g : G) : ρ.cosetSum N (ρ g v) = ρ.cosetSum N v := by
  have := Fintype.ofFinite (G ⧸ N)
  have hgv (h : G) (hh : h ∈ N) : ρ h (ρ g v) = ρ g v := by
    have hconj : h * g = g * (g⁻¹ * h * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply,
      hv _ (‹N.Normal›.conj_mem' h hh g)]
  rw [cosetSum_apply, cosetSum_apply]
  refine Fintype.sum_equiv (Equiv.mulRight (g : G ⧸ N)) _ _ fun q ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [Equiv.coe_mulRight, ← QuotientGroup.mk_mul, apply_out_mk_of_forall_mem hv,
    apply_out_mk_of_forall_mem hgv, map_mul, Module.End.mul_apply]

/-- On invariant vectors the coset sum is multiplication by the index. -/
lemma cosetSum_of_mem_invariants [Finite (G ⧸ N)] {v : E} (hv : v ∈ ρ.invariants) :
    ρ.cosetSum N v = N.index • v := by
  have := Fintype.ofFinite (G ⧸ N)
  rw [cosetSum_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.sum_const]
  exact Finset.sum_congr rfl fun q _ ↦ hv q.out

/-- Coset sums commute with equivariant linear maps. -/
lemma map_cosetSum {E' : Type*} [AddCommGroup E'] [Module A E'] {ρ' : Representation A G E'}
    [Finite (G ⧸ N)] (π : E →ₗ[A] E') (hπ : ∀ g, π ∘ₗ ρ g = ρ' g ∘ₗ π)
    (v : E) : π (ρ.cosetSum N v) = ρ'.cosetSum N (π v) := by
  have := Fintype.ofFinite (G ⧸ N)
  rw [cosetSum_apply, cosetSum_apply, map_sum]
  exact Finset.sum_congr rfl fun q _ ↦ LinearMap.congr_fun (hπ q.out) v

/-- Comparison of the coset sums for two nested normal subgroups `N ≤ M` on a vector fixed
by `M`. -/
lemma index_smul_cosetSum_of_le {M : Subgroup G} [N.Normal] [M.Normal] [Finite (G ⧸ N)]
    [Finite (G ⧸ M)] (hle : N ≤ M) {v : E} (hv : ∀ h ∈ M, ρ h v = v) :
    M.index • ρ.cosetSum N v = N.index • ρ.cosetSum M v := by
  have := Fintype.ofFinite (G ⧸ M)
  have hvN : ∀ h ∈ N, ρ h v = v := fun h hh ↦ hv h (hle hh)
  rw [← cosetSum_of_mem_invariants (cosetSum_mem_invariants hv), cosetSum_apply ρ M, map_sum,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun q _ ↦ (cosetSum_apply_apply hvN q.out).symm

/-- The coset sum on a tensor product with a trivial representation. -/
lemma cosetSum_tprod_trivial_tmul {B : Type*} [AddCommGroup B] [Module A B] [Finite (G ⧸ N)]
    (v : E) (b : B) :
    (ρ.tprod (trivial A G B)).cosetSum N (v ⊗ₜ b) = ρ.cosetSum N v ⊗ₜ b := by
  have := Fintype.ofFinite (G ⧸ N)
  simp [cosetSum_apply, TensorProduct.sum_tmul]

end CosetSum

section TensorInvariants

variable {B : Type*} [AddCommGroup B] [Module A B]

/-- The image of `ρ.invariants ⊗ B` in `E ⊗ B` consists of invariants of `ρ ⊗ trivial`. -/
lemma rTensor_invariants_subtype_mem (ρ : Representation A G E) (x : ρ.invariants ⊗[A] B) :
    ρ.invariants.subtype.rTensor B x ∈ (ρ.tprod (trivial A G B)).invariants := by
  intro g
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [v.2 g]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The natural map `ρ.invariants ⊗[A] B → (ρ ⊗ trivial)^G`. -/
noncomputable def invariantsTensorToInvariants (ρ : Representation A G E) :
    ρ.invariants ⊗[A] B →ₗ[A] (ρ.tprod (trivial A G B)).invariants :=
  (ρ.invariants.subtype.rTensor B).codRestrict _ (rTensor_invariants_subtype_mem ρ)

@[simp]
lemma invariantsTensorToInvariants_tmul (ρ : Representation A G E) (v : ρ.invariants) (b : B) :
    (invariantsTensorToInvariants ρ (v ⊗ₜ b) : E ⊗[A] B) = (v : E) ⊗ₜ b :=
  rfl

end TensorInvariants

section Discrete

variable [TopologicalSpace G]

/-- A representation of a topological group is *discrete* (or *smooth*) if every vector has an
open stabilizer, i.e. the action map `G × E → E` is continuous for the discrete topology
on `E`. -/
def IsDiscrete (ρ : Representation A G E) : Prop :=
  ∀ v : E, IsOpen {g : G | ρ g v = v}

variable [IsTopologicalGroup G] [CompactSpace G] {ρ : Representation A G E}

/-- The stabilizer of a vector, as a subgroup. -/
private def stabilizerSubgroup (ρ : Representation A G E) (v : E) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- For a compact group, a representation is discrete iff every vector is fixed by an open normal
subgroup. -/
lemma isDiscrete_iff_exists_openNormalSubgroup :
    ρ.IsDiscrete ↔ ∀ v : E, ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ρ g v = v := by
  refine ⟨fun hρ v ↦ ?_, fun h v ↦ ?_⟩
  · have hopen : IsOpen (stabilizerSubgroup ρ v : Set G) := hρ v
    exact IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩ (stabilizerSubgroup ρ v).one_mem
  · obtain ⟨U, hU⟩ := h v
    exact Subgroup.isOpen_mono (H₂ := stabilizerSubgroup ρ v) hU U.isOpen'

lemma IsDiscrete.exists_openNormalSubgroup (hρ : ρ.IsDiscrete) (v : E) :
    ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ρ g v = v :=
  isDiscrete_iff_exists_openNormalSubgroup.1 hρ v

variable (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))

/-- The normalized coset sums for two open normal subgroups fixing `v` agree. -/
lemma unit_inv_smul_cosetSum_eq {U W : OpenNormalSubgroup G} {v : E}
    (hU : ∀ g ∈ U, ρ g v = v) (hW : ∀ g ∈ W, ρ g v = v) :
    (↑(hA U).unit⁻¹ : A) • ρ.cosetSum U.toSubgroup v =
      (↑(hA W).unit⁻¹ : A) • ρ.cosetSum W.toSubgroup v := by
  suffices key : ∀ {U W : OpenNormalSubgroup G}, U ≤ W → (∀ g ∈ W, ρ g v = v) →
      (↑(hA U).unit⁻¹ : A) • ρ.cosetSum U.toSubgroup v =
        (↑(hA W).unit⁻¹ : A) • ρ.cosetSum W.toSubgroup v by
    rw [← key inf_le_left hU, key inf_le_right hW]
  intro U W hle hW
  have h := index_smul_cosetSum_of_le (ρ := ρ) (N := U.toSubgroup) (M := W.toSubgroup) hle hW
  rw [← Nat.cast_smul_eq_nsmul A, ← Nat.cast_smul_eq_nsmul A] at h
  calc (↑(hA U).unit⁻¹ : A) • ρ.cosetSum U.toSubgroup v
      = (↑(hA U).unit⁻¹ : A) • (↑(hA W).unit⁻¹ : A) •
          ((W.toSubgroup.index : ℕ) : A) • ρ.cosetSum U.toSubgroup v := by
        rw [smul_smul (↑(hA W).unit⁻¹ : A), IsUnit.val_inv_mul, one_smul]
    _ = (↑(hA W).unit⁻¹ : A) • ρ.cosetSum W.toSubgroup v := by
        rw [h, smul_comm (↑(hA U).unit⁻¹ : A), smul_smul (↑(hA U).unit⁻¹ : A),
          IsUnit.val_inv_mul, one_smul]

/-- The averaging retraction onto the invariants, as a function. -/
noncomputable def discreteAverageFun (hρ : ρ.IsDiscrete) (v : E) : E :=
  (↑(hA (hρ.exists_openNormalSubgroup v).choose).unit⁻¹ : A) •
    ρ.cosetSum (hρ.exists_openNormalSubgroup v).choose.toSubgroup v

lemma discreteAverageFun_eq (hρ : ρ.IsDiscrete) {v : E} {U : OpenNormalSubgroup G}
    (hU : ∀ g ∈ U, ρ g v = v) :
    discreteAverageFun hA hρ v = (↑(hA U).unit⁻¹ : A) • ρ.cosetSum U.toSubgroup v :=
  unit_inv_smul_cosetSum_eq hA (hρ.exists_openNormalSubgroup v).choose_spec hU

/-- The averaging retraction `E → ρ.invariants` of a discrete representation of a compact group
in which the index of every open normal subgroup is invertible in `A`. On a vector fixed by an
open normal subgroup `U` it is `[G : U]⁻¹ • ∑_{g ∈ G/U} ρ g v`
(`Representation.discreteAverage_eq`). -/
noncomputable def discreteAverage (hρ : ρ.IsDiscrete) : E →ₗ[A] ρ.invariants where
  toFun v := ⟨discreteAverageFun hA hρ v, by
    obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
    rw [discreteAverageFun_eq hA hρ hU]
    exact Submodule.smul_mem _ _ (cosetSum_mem_invariants hU)⟩
  map_add' v w := by
    obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
    obtain ⟨W, hW⟩ := hρ.exists_openNormalSubgroup w
    have hUv : ∀ g ∈ U ⊓ W, ρ g v = v := fun g hg ↦ hU g hg.1
    have hWw : ∀ g ∈ U ⊓ W, ρ g w = w := fun g hg ↦ hW g hg.2
    have hvw : ∀ g ∈ U ⊓ W, ρ g (v + w) = v + w := fun g hg ↦ by
      rw [map_add, hUv g hg, hWw g hg]
    ext
    simp only [Submodule.coe_add]
    rw [discreteAverageFun_eq hA hρ hvw, discreteAverageFun_eq hA hρ hUv,
      discreteAverageFun_eq hA hρ hWw, map_add, smul_add]
  map_smul' c v := by
    obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
    have hcv : ∀ g ∈ U, ρ g (c • v) = c • v := fun g hg ↦ by rw [map_smul, hU g hg]
    ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [discreteAverageFun_eq hA hρ hcv, discreteAverageFun_eq hA hρ hU, map_smul,
      smul_comm]

/-- On a vector fixed by an open normal subgroup `U`, the averaging retraction is the normalized
sum over `G ⧸ U`. -/
lemma discreteAverage_eq (hρ : ρ.IsDiscrete) {v : E} {U : OpenNormalSubgroup G}
    (hU : ∀ g ∈ U, ρ g v = v) :
    (discreteAverage hA hρ v : E) = (↑(hA U).unit⁻¹ : A) • ρ.cosetSum U.toSubgroup v :=
  discreteAverageFun_eq hA hρ hU

/-- The averaging map is a retraction of the inclusion of the invariants. -/
@[simp]
lemma discreteAverage_apply_of_mem_invariants (hρ : ρ.IsDiscrete) {v : E}
    (hv : v ∈ ρ.invariants) : (discreteAverage hA hρ v : E) = v := by
  obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
  rw [discreteAverage_eq hA hρ hU, cosetSum_of_mem_invariants hv, ← Nat.cast_smul_eq_nsmul A,
    smul_smul, IsUnit.val_inv_mul, one_smul]

lemma discreteAverage_comp_subtype (hρ : ρ.IsDiscrete) :
    discreteAverage hA hρ ∘ₗ ρ.invariants.subtype = LinearMap.id := by
  ext v
  exact discreteAverage_apply_of_mem_invariants hA hρ v.2

/-- **Invariants are exact on discrete representations** (blueprint
`prose-E-10`, used in Gabber's Künneth formula for nearby cycles, Illusie,
*Autour du théorème de monodromie locale*, 4.7). Let `G` be a compact group such that the index of
every open normal subgroup is invertible in `A` (e.g. a pro-`p` group with `p` invertible in `A`).
If `π : E → E'` is a surjective equivariant map and `ρ` is discrete, then `π` maps the
invariants of `ρ` onto the invariants of `ρ'`. -/
theorem IsDiscrete.map_invariants_eq
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    {E' : Type*} [AddCommGroup E'] [Module A E']
    {ρ' : Representation A G E'} (hρ : ρ.IsDiscrete) (π : E →ₗ[A] E')
    (hπ : ∀ g, π ∘ₗ ρ g = ρ' g ∘ₗ π) (hsurj : Function.Surjective π) :
    ρ.invariants.map π = ρ'.invariants := by
  refine le_antisymm ?_ fun w hw ↦ ?_
  · rintro _ ⟨v, hv, rfl⟩ g
    rw [← LinearMap.comp_apply, ← hπ, LinearMap.comp_apply, hv g]
  · obtain ⟨v, rfl⟩ := hsurj w
    obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
    refine ⟨discreteAverage hA hρ v, (discreteAverage hA hρ v).2, ?_⟩
    rw [discreteAverage_eq hA hρ hU, map_smul, map_cosetSum π hπ, cosetSum_of_mem_invariants hw,
      ← Nat.cast_smul_eq_nsmul A, smul_smul, IsUnit.val_inv_mul, one_smul]

variable {B : Type*} [AddCommGroup B] [Module A B]

/-- Every tensor in `E ⊗ B` is, for all small enough open normal subgroups `W`, sent by the
averaging retraction to its normalized coset sum over `G ⧸ W`. -/
lemma exists_rTensor_discreteAverage_eq (hρ : ρ.IsDiscrete) (y : E ⊗[A] B) :
    ∃ U : OpenNormalSubgroup G, ∀ W ≤ U,
      (ρ.invariants.subtype ∘ₗ discreteAverage hA hρ).rTensor B y =
        (↑(hA W).unit⁻¹ : A) • (ρ.tprod (trivial A G B)).cosetSum W.toSubgroup y := by
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
    refine ⟨U, fun W hW ↦ ?_⟩
    rw [LinearMap.rTensor_tmul, cosetSum_tprod_trivial_tmul, LinearMap.comp_apply,
      Submodule.subtype_apply, discreteAverage_eq hA hρ fun g hg ↦ hU g (hW hg),
      TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨U, hU⟩ := hx
    obtain ⟨U', hU'⟩ := hy
    refine ⟨U ⊓ U', fun W hW ↦ ?_⟩
    rw [map_add, map_add, smul_add, hU W (hW.trans inf_le_left), hU' W (hW.trans inf_le_right)]

lemma invariantsTensorToInvariants_bijective
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) : Function.Bijective (invariantsTensorToInvariants (B := B) ρ) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have h := congrArg ((discreteAverage hA hρ).rTensor B) (congrArg Subtype.val hxy)
    simp only [invariantsTensorToInvariants, LinearMap.codRestrict_apply] at h
    rwa [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply,
      discreteAverage_comp_subtype, LinearMap.rTensor_id, LinearMap.id_apply,
      LinearMap.id_apply] at h
  · refine ⟨(discreteAverage hA hρ).rTensor B y, Subtype.ext ?_⟩
    obtain ⟨U, hU⟩ := exists_rTensor_discreteAverage_eq hA hρ (y : E ⊗[A] B)
    rw [invariantsTensorToInvariants, LinearMap.codRestrict_apply, ← LinearMap.rTensor_comp_apply,
      hU U le_rfl, cosetSum_of_mem_invariants y.2, ← Nat.cast_smul_eq_nsmul A, smul_smul,
      IsUnit.val_inv_mul, one_smul]

/-- **Invariants commute with tensor products** (blueprint `prose-E-10`,
used in Gabber's Künneth formula for nearby cycles, Illusie, *Autour du théorème de monodromie
locale*, 4.7). Let `G` be a compact group such that the index of every open normal subgroup is
invertible in `A` (e.g. a pro-`p` group with `p` invertible in `A`), `ρ` a discrete
representation of `G` on `E` and `B` an `A`-module with trivial action. Then the natural map
`ρ.invariants ⊗[A] B → (E ⊗[A] B)^G` is an isomorphism. -/
noncomputable def invariantsTensorEquiv (hρ : ρ.IsDiscrete) :
    ρ.invariants ⊗[A] B ≃ₗ[A] (ρ.tprod (trivial A G B)).invariants :=
  LinearEquiv.ofBijective (invariantsTensorToInvariants ρ)
    (invariantsTensorToInvariants_bijective hA hρ)

@[simp]
lemma invariantsTensorEquiv_tmul (hρ : ρ.IsDiscrete) (v : ρ.invariants) (b : B) :
    (invariantsTensorEquiv hA hρ (v ⊗ₜ b) : E ⊗[A] B) = (v : E) ⊗ₜ b :=
  rfl

end Discrete

end Representation
