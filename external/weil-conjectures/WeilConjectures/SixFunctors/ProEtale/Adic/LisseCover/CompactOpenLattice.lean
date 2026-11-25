/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Congruence
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Instances.Matrix

/-!
# Lattices in `Eⁿ` as compact open subgroups

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`. A *lattice* in `Eⁿ` is a compact open additive
subgroup `L ⊆ Eⁿ` (`PadicAlgCl.CompactOpenLattice E n`); these are the `ℤ_ℓ`-lattices of the
`ℚ_ℓ`-vector space `Eⁿ`. The group `GL_n(E)` acts on them by `g • L = g L`
(`PadicAlgCl.CompactOpenLattice.instMulAction`), and

* the stabilizer of a lattice contains a congruence subgroup
  (`PadicAlgCl.CompactOpenLattice.exists_smul_eq_of_mem_congruenceSubgroup`), so that for
  `γ : Z → GL_n(E)` with continuous entries `z ↦ γ z • L` is locally constant
  (`PadicAlgCl.CompactOpenLattice.isLocallyConstant_smul`);
* the sum of a nonempty finite set of lattices is a lattice
  (`PadicAlgCl.CompactOpenLattice.sum`), compatibly with the action
  (`PadicAlgCl.CompactOpenLattice.smul_sum`).

The sum is what makes a finite orbit of lattices produce a fixed lattice.
-/

@[expose] public section

open Filter Topology Matrix

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (n : ℕ)

/-- The *lattices* in `Eⁿ`: the compact open additive subgroups. -/
def CompactOpenLattice : Type :=
  {L : AddSubgroup (Fin n → E) // IsCompact (L : Set (Fin n → E)) ∧ IsOpen (L : Set (Fin n → E))}

namespace CompactOpenLattice

variable {E n}

/-- The continuous additive map `v ↦ A v` of a matrix. -/
noncomputable def mulVecHom (A : Matrix (Fin n) (Fin n) E) : (Fin n → E) →+ (Fin n → E) :=
  (Matrix.mulVecLin A).toAddMonoidHom

lemma continuous_mulVecHom (A : Matrix (Fin n) (Fin n) E) : Continuous (mulVecHom A) :=
  continuous_const.matrix_mulVec continuous_id

lemma mulVecHom_mul (A B : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    mulVecHom (A * B) v = mulVecHom A (mulVecHom B v) :=
  (Matrix.mulVec_mulVec v A B).symm

lemma mulVecHom_one (v : Fin n → E) : mulVecHom (1 : Matrix (Fin n) (Fin n) E) v = v :=
  Matrix.one_mulVec v

/-- The image of a lattice under an invertible matrix. -/
noncomputable def map (g : GL (Fin n) E) (L : CompactOpenLattice E n) : CompactOpenLattice E n :=
  ⟨L.1.map (mulVecHom (g : Matrix (Fin n) (Fin n) E)),
    L.2.1.image (continuous_mulVecHom _), by
      have : ((L.1.map (mulVecHom (g : Matrix (Fin n) (Fin n) E))) : Set (Fin n → E)) =
          mulVecHom ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ⁻¹' L.1 := by
        ext v
        simp only [AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rwa [← mulVecHom_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulVecHom_one]
        · intro hv
          refine ⟨_, hv, ?_⟩
          rw [← mulVecHom_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mulVecHom_one]
      rw [this]
      exact L.2.2.preimage (continuous_mulVecHom _)⟩

lemma coe_map (g : GL (Fin n) E) (L : CompactOpenLattice E n) :
    (map g L).1 = L.1.map (mulVecHom (g : Matrix (Fin n) (Fin n) E)) :=
  rfl

@[ext]
lemma ext {L L' : CompactOpenLattice E n} (h : L.1 = L'.1) : L = L' :=
  Subtype.ext h

noncomputable instance instMulAction : MulAction (GL (Fin n) E) (CompactOpenLattice E n) where
  smul := map
  one_smul L := by
    ext v
    change v ∈ L.1.map _ ↔ v ∈ L.1
    simp only [AddSubgroup.mem_map, Units.val_one]
    exact ⟨fun ⟨w, hw, h⟩ ↦ by rwa [← h, mulVecHom_one], fun h ↦ ⟨v, h, mulVecHom_one v⟩⟩
  mul_smul g h L := by
    ext v
    change v ∈ L.1.map _ ↔ v ∈ (L.1.map _).map _
    rw [AddSubgroup.map_map]
    have : mulVecHom ((g * h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (mulVecHom (g : Matrix (Fin n) (Fin n) E)).comp
          (mulVecHom (h : Matrix (Fin n) (Fin n) E)) := by
      refine AddMonoidHom.ext fun w ↦ ?_
      rw [Units.val_mul, AddMonoidHom.comp_apply, mulVecHom_mul]
    rw [this]

lemma smul_def (g : GL (Fin n) E) (L : CompactOpenLattice E n) : g • L = map g L :=
  rfl

/-- Every lattice contains a box `{v | ∀ i, ‖v i‖ ≤ r}` and is contained in a box. -/
lemma exists_box (L : CompactOpenLattice E n) :
    ∃ r > 0, ∃ R ≥ 0, (∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ r) → v ∈ L.1) ∧
      ∀ v ∈ L.1, ∀ i, ‖v i‖ ≤ R := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.2.2 0 L.1.zero_mem
  obtain ⟨R, hR⟩ := L.2.1.isBounded.exists_norm_le
  refine ⟨r / 2, half_pos hr, max R 0, le_max_right _ _, fun v hv ↦ hball ?_, fun v hv i ↦ ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (half_pos hr).le).2 hv) (half_lt_self hr)
  · exact ((norm_le_pi_norm v i).trans (hR v hv)).trans (le_max_left _ _)

/-- A matrix whose entries are bounded by `ε` shrinks the box norms by `ε`. -/
lemma norm_mulVecHom_apply_le {A : Matrix (Fin n) (Fin n) E} {ε R : ℝ} (hε : 0 ≤ ε)
    (hA : EntryBound A ε) {v : Fin n → E} (hv : ∀ i, ‖v i‖ ≤ R) (hR : 0 ≤ R) (i : Fin n) :
    ‖mulVecHom A v i‖ ≤ ε * R := by
  change ‖(A *ᵥ v) i‖ ≤ ε * R
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hε hR) fun j _ ↦ ?_
  rw [norm_mul]
  exact mul_le_mul (hA i j) (hv j) (norm_nonneg _) hε

/-- **The stabilizer of a lattice contains a congruence subgroup.** -/
lemma exists_smul_eq_of_mem_congruenceSubgroup (L : CompactOpenLattice E n) :
    ∃ k, ∀ A ∈ congruenceSubgroup E n k, A • L = L := by
  obtain ⟨r, hr, R, hR, hbox, hbound⟩ := exists_box L
  obtain ⟨k, hk⟩ := exists_congruenceRadius_lt (l := l) (div_pos hr (lt_of_lt_of_le
    zero_lt_one (le_max_right R 1)))
  have hk' : congruenceRadius l k * R ≤ r := by
    have h1 : congruenceRadius l k * max R 1 ≤ r := by
      rw [lt_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_right R 1))] at hk
      exact hk.le
    exact (mul_le_mul_of_nonneg_left (le_max_left R 1) (congruenceRadius_nonneg k)).trans h1
  -- an element of the congruence subgroup maps `L` into `L`
  have hle (B : GL (Fin n) E) (hB : EntryBound ((B : Matrix (Fin n) (Fin n) E) - 1)
      (congruenceRadius l k)) : ∀ v ∈ L.1, mulVecHom (B : Matrix (Fin n) (Fin n) E) v ∈ L.1 := by
    intro v hv
    have e : mulVecHom (B : Matrix (Fin n) (Fin n) E) v =
        v + mulVecHom ((B : Matrix (Fin n) (Fin n) E) - 1) v := by
      change B.1 *ᵥ v = v + (B.1 - 1) *ᵥ v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
    rw [e]
    refine L.1.add_mem hv (hbox _ fun i ↦ ?_)
    exact (norm_mulVecHom_apply_le (congruenceRadius_nonneg k) hB (hbound v hv) hR i).trans hk'
  refine ⟨k, fun A hA ↦ ?_⟩
  have h₁ : (A • L).1 ≤ L.1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hle A hA.1 v hv
  have h₂ : (A⁻¹ • L).1 ≤ L.1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hle A⁻¹ hA.2 v hv
  have h₃ : L.1 ≤ (A • L).1 := by
    intro v hv
    have : v ∈ (A • (A⁻¹ • L)).1 := by rw [smul_inv_smul]; exact hv
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨w, h₂ hw, rfl⟩
  exact ext (le_antisymm h₁ h₃)

/-- **Local constancy of the action.** For `γ : Z → GL_n(E)` with continuous entries (and
continuous entries of the inverse), `z ↦ γ z • L` is locally constant. -/
lemma isLocallyConstant_smul {Z : Type*} [TopologicalSpace Z] (γ : Z → GL (Fin n) E)
    (hγ : ∀ i j, Continuous fun z ↦ (γ z : Matrix (Fin n) (Fin n) E) i j)
    (hγ' : ∀ i j, Continuous fun z ↦ ((γ z)⁻¹ : GL (Fin n) E) i j) (L : CompactOpenLattice E n) :
    IsLocallyConstant fun z ↦ γ z • L := by
  obtain ⟨k, hk⟩ := exists_smul_eq_of_mem_congruenceSubgroup L
  let φ : GL (Fin n) E ⧸ congruenceSubgroup E n k → CompactOpenLattice E n :=
    Quotient.lift (fun g ↦ g • L) fun a b hab ↦ by
      have hab' : a⁻¹ * b ∈ congruenceSubgroup E n k := QuotientGroup.leftRel_apply.1 hab
      change a • L = b • L
      rw [← mul_inv_cancel_left a b, mul_smul, hk _ hab']
  have := (isLocallyConstant_smul_mk γ hγ hγ' k (QuotientGroup.mk 1)).comp φ
  convert this using 1
  funext z
  simp only [Function.comp_apply, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, φ]
  rfl

lemma isCompact_finsetSup (T : Finset (CompactOpenLattice E n)) :
    IsCompact ((T.sup (·.1) : AddSubgroup (Fin n → E)) : Set (Fin n → E)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert L T _ ih =>
    rw [Finset.sup_insert, AddSubgroup.normal_add]
    exact L.2.1.add ih

/-- The sum of a nonempty finite set of lattices. -/
noncomputable def sum (T : Finset (CompactOpenLattice E n)) (hT : T.Nonempty) :
    CompactOpenLattice E n :=
  ⟨T.sup (·.1), isCompact_finsetSup T, by
      obtain ⟨L, hL⟩ := hT
      exact AddSubgroup.isOpen_mono (Finset.le_sup (f := (·.1)) hL) L.2.2⟩

lemma le_sum {T : Finset (CompactOpenLattice E n)} (hT : T.Nonempty) {L : CompactOpenLattice E n}
    (hL : L ∈ T) : L.1 ≤ (sum T hT).1 :=
  Finset.le_sup (f := (·.1)) hL

open scoped Classical in
/-- The sum of lattices is compatible with the action. -/
lemma smul_sum (g : GL (Fin n) E) (T : Finset (CompactOpenLattice E n)) (hT : T.Nonempty) :
    g • sum T hT = sum (T.image (g • ·)) (hT.image _) := by
  ext v
  change v ∈ (T.sup (·.1)).map _ ↔ v ∈ (T.image (g • ·)).sup (·.1)
  rw [Finset.sup_image]
  have := Finset.apply_sup_eq_sup_comp (s := T) (f := (·.1))
    (AddSubgroup.map (mulVecHom (g : Matrix (Fin n) (Fin n) E)))
    (fun _ _ ↦ AddSubgroup.map_sup _ _ _) (AddSubgroup.map_bot _)
  rw [show (T.sup (·.1)).map _ = _ from this]
  rfl

section Standard

variable [FiniteDimensional ℚ_[l] E]

variable (E n) in
/-- The standard lattice `𝒪_Eⁿ = {v | ∀ i, ‖v i‖ ≤ 1}`. -/
noncomputable def standard : CompactOpenLattice E n :=
  ⟨{ carrier := {v | ∀ i, ‖v i‖ ≤ 1}
     add_mem' := fun ha hb i ↦
       (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
     zero_mem' := fun i ↦ by simp
     neg_mem' := fun ha i ↦ by simpa using ha i }, by
    have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
    have : ({v | ∀ i, ‖v i‖ ≤ 1} : Set (Fin n → E)) =
        Set.univ.pi fun _ ↦ Metric.closedBall 0 1 := by
      ext v
      simp
    refine ⟨?_, ?_⟩
    · change IsCompact ({v | ∀ i, ‖v i‖ ≤ 1} : Set (Fin n → E))
      rw [this]
      exact isCompact_univ_pi fun _ ↦ isCompact_closedBall 0 1
    · change IsOpen ({v | ∀ i, ‖v i‖ ≤ 1} : Set (Fin n → E))
      rw [this]
      exact isOpen_set_pi Set.finite_univ fun _ _ ↦
        IsUltrametricDist.isOpen_closedBall 0 one_ne_zero⟩

instance : Nonempty (CompactOpenLattice E n) :=
  ⟨standard E n⟩

end Standard

end CompactOpenLattice

end PadicAlgCl
