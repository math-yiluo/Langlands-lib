/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lattices in `Eⁿ` and restriction of scalars to `ℚ_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` of degree `d`. A choice of a `ℚ_ℓ`-basis of `E`
identifies `Eⁿ` with `ℚ_ℓᴺ`, `N = nd` (`PadicAlgCl.latticeCoords`), and a matrix `A` over `E`
with a matrix `R(A)` over `ℚ_ℓ` (`PadicAlgCl.restrictScalarsMatrix`), multiplicatively.

* Every lattice `L ⊆ Eⁿ` (compact open subgroup) is, in these coordinates, `g ℤ_ℓᴺ` for some
  `g ∈ GL_N(ℚ_ℓ)` (`PadicAlgCl.CompactOpenLattice.exists_glBasis`): it is a `ℤ_ℓ`-submodule
  squeezed between two scalings of `ℤ_ℓᴺ`, hence free of rank `N`, `ℤ_ℓ` being a PID.
* Over `ℚ̄_ℓ`, the multiplication map `ℚ̄_ℓ ⊗_{ℚ_ℓ} Eⁿ → ℚ̄_ℓⁿ` is a matrix `Q`
  (`PadicAlgCl.latticeQ`) with `Q R(A) = A Q`, and it has the section `P`
  (`PadicAlgCl.latticeP`), built from the trace dual basis, with `R(A) P = P A` and `Q P = 1`.
  This exhibits `ℚ̄_ℓⁿ` with the action of `A` as a direct summand of `ℚ̄_ℓᴺ` with the action of
  `R(A)`.
-/

@[expose] public section

open Matrix

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- The rank `N = n [E : ℚ_ℓ]` of `Eⁿ` over `ℚ_ℓ`. -/
noncomputable abbrev latticeRank : ℕ := n * Module.finrank ℚ_[l] E

/-- The chosen `ℚ_ℓ`-basis of `E`. -/
noncomputable abbrev fieldBasis : Module.Basis (Fin (Module.finrank ℚ_[l] E)) ℚ_[l] E :=
  Module.finBasis ℚ_[l] E

/-- The `ℚ_ℓ`-basis of `Eⁿ` given by the chosen basis of `E` in each coordinate. -/
noncomputable def coordBasis : Module.Basis (Fin (latticeRank E n)) ℚ_[l] (Fin n → E) :=
  (Pi.basis fun _ : Fin n ↦ fieldBasis E).reindex
    ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)

/-- The coordinates `Eⁿ ≃ ℚ_ℓᴺ`. -/
noncomputable def latticeCoords : (Fin n → E) ≃ₗ[ℚ_[l]] (Fin (latticeRank E n) → ℚ_[l]) :=
  (coordBasis E n).equivFun

variable {E n}

/-- The matrix over `ℚ_ℓ` of the `ℚ_ℓ`-linear map `v ↦ A v` of `Eⁿ`. -/
noncomputable def restrictScalarsMatrix (A : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) ℚ_[l] :=
  LinearMap.toMatrix (coordBasis E n) (coordBasis E n)
    ((Matrix.mulVecLin A).restrictScalars ℚ_[l])

lemma restrictScalarsMatrix_mulVec (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    restrictScalarsMatrix A *ᵥ latticeCoords E n x = latticeCoords E n (A *ᵥ x) := by
  have := LinearMap.toMatrix_mulVec_repr (coordBasis E n) (coordBasis E n)
    ((Matrix.mulVecLin A).restrictScalars ℚ_[l]) x
  exact this

lemma restrictScalarsMatrix_mul (A B : Matrix (Fin n) (Fin n) E) :
    restrictScalarsMatrix (A * B) = restrictScalarsMatrix A * restrictScalarsMatrix B := by
  rw [restrictScalarsMatrix, restrictScalarsMatrix, restrictScalarsMatrix,
    ← LinearMap.toMatrix_mul]
  congr 1
  refine LinearMap.ext fun x ↦ ?_
  simp [Matrix.mulVec_mulVec]

lemma restrictScalarsMatrix_one :
    restrictScalarsMatrix (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  rw [restrictScalarsMatrix, ← LinearMap.toMatrix_id (coordBasis E n)]
  congr 1
  refine LinearMap.ext fun x ↦ ?_
  simp

variable (E n) in
/-- Restriction of scalars of matrices, as a monoid homomorphism. -/
noncomputable def restrictScalarsMatrixHom :
    Matrix (Fin n) (Fin n) E →* Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) ℚ_[l] where
  toFun := restrictScalarsMatrix
  map_one' := restrictScalarsMatrix_one
  map_mul' := restrictScalarsMatrix_mul

variable (E n) in
/-- Restriction of scalars `GL_n(E) → GL_N(ℚ_ℓ)`. -/
noncomputable def restrictScalarsGL : GL (Fin n) E →* GL (Fin (latticeRank E n)) ℚ_[l] :=
  Units.map (restrictScalarsMatrixHom E n)

lemma coe_restrictScalarsGL (A : GL (Fin n) E) :
    ((restrictScalarsGL E n A : GL _ ℚ_[l]) : Matrix _ _ ℚ_[l]) =
      restrictScalarsMatrix (A : Matrix (Fin n) (Fin n) E) :=
  rfl

end PadicAlgCl

namespace PadicAlgCl.CompactOpenLattice

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E] {n : ℕ}

omit [FiniteDimensional ℚ_[l] E] in
/-- **Lattices are `ℤ_ℓ`-modules**: a compact open subgroup of `Eⁿ` is stable under
multiplication by `ℤ_ℓ`, being closed and stable under multiplication by the dense `ℕ`. -/
lemma padicInt_smul_mem (L : CompactOpenLattice E n) (c : ℤ_[l]) {x : Fin n → E}
    (hx : x ∈ L.1) : (c : ℚ_[l]) • x ∈ L.1 := by
  refine PadicInt.denseRange_natCast.induction_on (p := fun c : ℤ_[l] ↦ (c : ℚ_[l]) • x ∈ L.1)
    c ?_ fun m ↦ ?_
  · exact L.2.1.isClosed.preimage ((continuous_subtype_val.smul continuous_const))
  · simp only [PadicInt.coe_natCast, Nat.cast_smul_eq_nsmul]
    exact L.1.nsmul_mem hx m

/-- A lattice is squeezed between two scalings of `ℤ_ℓᴺ`, in coordinates: for some `A`,
`ℓᴬ` times the coordinates of a vector of `L` are integral, and every vector whose coordinates
are `ℓᴬ` times integers lies in `L`. -/
lemma exists_pow_bounds (L : CompactOpenLattice E n) :
    ∃ A : ℕ, (∀ x ∈ L.1, ∀ k, ‖(l : ℚ_[l]) ^ A * latticeCoords E n x k‖ ≤ 1) ∧
      ∀ y : Fin (latticeRank E n) → ℤ_[l],
        (latticeCoords E n).symm (fun k ↦ (l : ℚ_[l]) ^ A * y k) ∈ L.1 := by
  obtain ⟨r, hr, R, hR, hbox, hbound⟩ := exists_box L
  let C := (latticeCoords E n).toContinuousLinearEquiv
  have hC (x : Fin n → E) : C x = latticeCoords E n x := rfl
  have hC' (y : Fin (latticeRank E n) → ℚ_[l]) : C.symm y = (latticeCoords E n).symm y := rfl
  obtain ⟨A₁, hA₁⟩ := exists_congruenceRadius_lt (l := l)
    (ε := 1 / (‖C.toContinuousLinearMap‖ * R + 1)) (by positivity)
  obtain ⟨A₂, hA₂⟩ := exists_congruenceRadius_lt (l := l)
    (ε := r / (‖C.symm.toContinuousLinearMap‖ + 1)) (by positivity)
  have hpow (A : ℕ) : ‖(l : ℚ_[l]) ^ A‖ = congruenceRadius l A := by
    rw [Padic.norm_p_pow, congruenceRadius, zpow_neg, zpow_natCast, inv_pow]
  refine ⟨max A₁ A₂, fun x hx k ↦ ?_, fun y ↦ hbox _ fun i ↦ ?_⟩
  · have h₁ : ‖x‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).2 (hbound x hx)
    have h₂ : ‖latticeCoords E n x k‖ ≤ ‖C.toContinuousLinearMap‖ * R := by
      rw [← hC]
      exact (norm_le_pi_norm _ k).trans (C.toContinuousLinearMap.le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)))
    rw [norm_mul, hpow]
    have h₃ := congruenceRadius_antitone (l := l) (le_max_left A₁ A₂)
    have h₄ : congruenceRadius l (max A₁ A₂) * (‖C.toContinuousLinearMap‖ * R + 1) ≤ 1 := by
      rw [lt_div_iff₀ (by positivity)] at hA₁
      exact (mul_le_mul_of_nonneg_right h₃ (by positivity)).trans hA₁.le
    nlinarith [congruenceRadius_nonneg (l := l) (max A₁ A₂), norm_nonneg (latticeCoords E n x k)]
  · set v : Fin (latticeRank E n) → ℚ_[l] := fun k ↦ (l : ℚ_[l]) ^ max A₁ A₂ * y k
    have hv : ‖v‖ ≤ congruenceRadius l (max A₁ A₂) :=
      (pi_norm_le_iff_of_nonneg (congruenceRadius_nonneg (l := l) _)).2 fun k ↦ by
        rw [norm_mul, hpow]
        exact mul_le_of_le_one_right (congruenceRadius_nonneg (l := l) _) (PadicInt.norm_le_one _)
    have h₁ : ‖(latticeCoords E n).symm v‖ ≤
        ‖C.symm.toContinuousLinearMap‖ * congruenceRadius l (max A₁ A₂) := by
      rw [← hC']
      exact (C.symm.toContinuousLinearMap.le_opNorm v).trans
        (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    have h₃ := congruenceRadius_antitone (l := l) (le_max_right A₁ A₂)
    have h₄ : congruenceRadius l (max A₁ A₂) * (‖C.symm.toContinuousLinearMap‖ + 1) ≤ r := by
      rw [lt_div_iff₀ (by positivity)] at hA₂
      exact (mul_le_mul_of_nonneg_right h₃ (by positivity)).trans hA₂.le
    refine (norm_le_pi_norm _ i).trans (h₁.trans ?_)
    nlinarith [congruenceRadius_nonneg (l := l) (max A₁ A₂),
      norm_nonneg C.symm.toContinuousLinearMap]


/-- The inclusion `ℤ_ℓᴺ ⟶ ℚ_ℓᴺ`, as a `ℤ_ℓ`-linear map. -/
noncomputable def intCoe (N : ℕ) : (Fin N → ℤ_[l]) →ₗ[ℤ_[l]] (Fin N → ℚ_[l]) where
  toFun y k := (y k : ℚ_[l])
  map_add' _ _ := funext fun _ ↦ PadicInt.coe_add _ _
  map_smul' _ _ := funext fun _ ↦ PadicInt.coe_mul _ _

lemma intCoe_apply {N : ℕ} (y : Fin N → ℤ_[l]) (k : Fin N) : intCoe N y k = (y k : ℚ_[l]) :=
  rfl

lemma intCoe_injective (N : ℕ) : Function.Injective (intCoe (l := l) N) :=
  fun _ _ h ↦ funext fun k ↦ PadicInt.ext (congrFun h k)

/-- **Lattices are free**: in coordinates, a lattice of `Eⁿ` is `g ℤ_ℓᴺ` for some
`g ∈ GL_N(ℚ_ℓ)`. The lattice, scaled into `ℤ_ℓᴺ`, is a submodule of the free module `ℤ_ℓᴺ` over
the PID `ℤ_ℓ`, hence free; its basis is a `ℚ_ℓ`-basis of `ℚ_ℓᴺ`, the lattice containing a scaling
of `ℤ_ℓᴺ`. -/
theorem exists_glBasis (L : CompactOpenLattice E n) :
    ∃ g : GL (Fin (latticeRank E n)) ℚ_[l], ∀ x : Fin n → E, x ∈ L.1 ↔
      ∃ y : Fin (latticeRank E n) → ℤ_[l],
        latticeCoords E n x = (g : Matrix _ _ ℚ_[l]) *ᵥ intCoe _ y := by
  classical
  obtain ⟨A, hA₁, hA₂⟩ := exists_pow_bounds L
  set N := latticeRank E n
  set co := latticeCoords E n
  suffices H : ∃ g : GL (Fin N) ℚ_[l], ∀ x : Fin n → E, x ∈ L.1 ↔
      ∃ y : Fin N → ℤ_[l], co x = (g : Matrix _ _ ℚ_[l]) *ᵥ intCoe N y from H
  set lam : ℚ_[l] := (l : ℚ_[l]) ^ A
  have hlam : lam ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let S : Submodule ℤ_[l] (Fin N → ℤ_[l]) :=
    { carrier := {y | co.symm (lam⁻¹ • intCoe N y) ∈ L.1}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add, smul_add] at ha hb ⊢
        exact L.1.add_mem ha hb
      zero_mem' := by simp [L.1.zero_mem]
      smul_mem' := fun c y hy ↦ by
        simp only [Set.mem_ofPred_eq] at hy ⊢
        have : lam⁻¹ • intCoe N (c • y) = (c : ℚ_[l]) • (lam⁻¹ • intCoe N y) := by
          rw [map_smul, smul_comm]
          rfl
        rw [this, map_smul]
        exact padicInt_smul_mem L c hy }
  have hS (y : Fin N → ℤ_[l]) : y ∈ S ↔ co.symm (lam⁻¹ • intCoe N y) ∈ L.1 := Iff.rfl
  -- membership in `L` through `S`
  have hk₁ (x : Fin n → E) : x ∈ L.1 ↔ ∃ y ∈ S, co x = lam⁻¹ • intCoe N y := by
    refine ⟨fun hx ↦ ⟨fun k ↦ ⟨lam * co x k, hA₁ x hx k⟩, ?_, ?_⟩, ?_⟩
    · have : lam⁻¹ • intCoe N (fun k ↦ ⟨lam * co x k, hA₁ x hx k⟩) = co x := by
        funext k
        simp [intCoe_apply, hlam]
      rw [hS, this, LinearEquiv.symm_apply_apply]
      exact hx
    · funext k
      simp [intCoe_apply, hlam]
    · rintro ⟨y, hy, hxy⟩
      rw [hS, ← hxy, LinearEquiv.symm_apply_apply] at hy
      exact hy
  have hk₂ (z : Fin N → ℤ_[l]) : ((l : ℤ_[l]) ^ (2 * A)) • z ∈ S := by
    rw [hS]
    convert hA₂ z using 2
    funext k
    have key : (l : ℚ_[l]) ^ (2 * A) = lam * lam := by rw [two_mul, pow_add]
    simp only [intCoe_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, key]
    field_simp
  obtain ⟨m, bS⟩ := Submodule.basisOfPid (Pi.basisFun ℤ_[l] (Fin N)) S
  let w : Fin m → (Fin N → ℚ_[l]) := fun j ↦ intCoe N (bS j)
  have hw_sum (c : Fin m → ℤ_[l]) :
      intCoe N (∑ j, c j • (bS j : Fin N → ℤ_[l])) = ∑ j, (c j : ℚ_[l]) • w j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul]
    exact algebra_compatible_smul ℚ_[l] (c j) (w j)
  have hy_sum (y : S) : (y : Fin N → ℤ_[l]) = ∑ j, bS.repr y j • (bS j : Fin N → ℤ_[l]) := by
    have := congrArg Subtype.val (bS.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hli : LinearIndependent ℚ_[l] w := by
    refine (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 ?_
    exact bS.linearIndependent.map' ((intCoe N).comp S.subtype)
      (LinearMap.ker_eq_bot.2 ((intCoe_injective N).comp Subtype.val_injective))
  have hsp : ⊤ ≤ Submodule.span ℚ_[l] (Set.range w) := by
    intro v _
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ ?_
    let y : S := ⟨((l : ℤ_[l]) ^ (2 * A)) • fun k' ↦ if k = k' then 1 else 0, hk₂ _⟩
    have hy : (fun k' ↦ if k = k' then (1 : ℚ_[l]) else 0) =
        ((l : ℚ_[l]) ^ (2 * A))⁻¹ • ∑ j, (bS.repr y j : ℚ_[l]) • w j := by
      rw [← hw_sum, ← hy_sum]
      funext k'
      simp only [y, Pi.smul_apply, intCoe_apply, smul_eq_mul, PadicInt.coe_mul,
        PadicInt.coe_pow, PadicInt.coe_natCast]
      split_ifs <;> simp
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW := Module.Basis.mk hli hsp
  have hmN : m = N := by
    have := Module.finrank_eq_card_basis bW
    rw [Module.finrank_fin_fun, Fintype.card_fin] at this
    exact this.symm
  subst hmN
  let M := (Pi.basisFun ℚ_[l] (Fin N)).toMatrix bW
  have hM (c : Fin N → ℤ_[l]) : M *ᵥ intCoe N c = ∑ j, (c j : ℚ_[l]) • w j := by
    funext i
    simp only [M, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, intCoe_apply, bW, Module.Basis.mk_apply]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hdet : (lam⁻¹ • M).det ≠ 0 := by
    have : Invertible M := (Pi.basisFun ℚ_[l] (Fin N)).invertibleToMatrix bW
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam)) (Matrix.isUnit_det_of_invertible M).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun x ↦ ?_⟩
  have hg (v : Fin N → ℚ_[l]) : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet :
      GL (Fin N) ℚ_[l]) : Matrix _ _ ℚ_[l]) *ᵥ v = lam⁻¹ • (M *ᵥ v) := by
    funext i
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc]
  rw [hk₁]
  simp only [hg]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨bS.repr ⟨y, hy⟩, ?_⟩
    rw [hxy, hM, ← hw_sum, ← hy_sum]
  · rintro ⟨c, hc⟩
    refine ⟨∑ j, c j • (bS j : Fin N → ℤ_[l]), Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (bS j).2, ?_⟩
    rw [hc, hM, hw_sum]

end PadicAlgCl.CompactOpenLattice

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E] {n : ℕ}

section DualBasis

instance : Algebra.IsSeparable ℚ_[l] E :=
  have : Algebra.IsIntegral ℚ_[l] E := Algebra.IsIntegral.of_finite ℚ_[l] E
  Algebra.IsSeparable.of_integral ℚ_[l] E

variable (E) in
/-- The trace dual basis `b^∨` of the chosen basis `b` of `E` over `ℚ_ℓ`:
`Tr(b^∨_s b_t) = δ_{st}`. -/
noncomputable def fieldDualBasis : Module.Basis (Fin (Module.finrank ℚ_[l] E)) ℚ_[l] E :=
  (Algebra.traceForm ℚ_[l] E).dualBasis (traceForm_nondegenerate ℚ_[l] E) (fieldBasis E)

/-- The coordinates in the chosen basis are traces against the dual basis. -/
lemma fieldBasis_repr_eq_trace (y : E) (t : Fin (Module.finrank ℚ_[l] E)) :
    (fieldBasis E).repr y t = Algebra.trace ℚ_[l] E (fieldDualBasis E t * y) := by
  conv_rhs => rw [← (fieldBasis E).sum_repr y]
  rw [Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, map_smul]
  have h (s : Fin (Module.finrank ℚ_[l] E)) : Algebra.trace ℚ_[l] E
      (fieldDualBasis E t * fieldBasis E s) = if s = t then 1 else 0 := by
    have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ_[l] E)
      (fieldBasis E) t s
    rw [Algebra.traceForm_apply] at this
    exact this
  simp [h]

/-- The coordinates in the dual basis are traces against the basis. -/
lemma fieldDualBasis_repr_eq_trace (y : E) (t : Fin (Module.finrank ℚ_[l] E)) :
    (fieldDualBasis E).repr y t = Algebra.trace ℚ_[l] E (y * fieldBasis E t) := by
  rw [fieldDualBasis, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

/-- `∑ₛ b^∨_s b_s = 1`: both sides have the same trace pairing with every `y`, the trace of the
multiplication by `y` being `∑ₛ` of the `s`-th coordinate of `y bₛ`. -/
lemma sum_fieldDualBasis_mul_fieldBasis :
    ∑ s, fieldDualBasis E s * fieldBasis E s = 1 := by
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ_[l] E).1 _ fun y ↦ ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (fieldBasis E) y, Matrix.trace, sub_eq_zero]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, fieldBasis_repr_eq_trace, mul_assoc,
    mul_comm (fieldBasis E s) y]

/-- The key identity behind the section `P`: for a `ℚ_ℓ`-linear form `φ` on `E` and `a ∈ E`,
`∑ₛ b^∨_s φ(a bₛ) = ∑ₛ (a b^∨_s) φ(bₛ)` in `ℚ̄_ℓ`; both sides are
`∑_{s,t} Tr(a b^∨_t bₛ) b^∨_s φ(b_t)`. -/
lemma sum_fieldDualBasis_mul_apply (φ : E →ₗ[ℚ_[l]] ℚ_[l]) (a : E) :
    ∑ s, (fieldDualBasis E s : PadicAlgCl l) * algebraMap ℚ_[l] (PadicAlgCl l)
        (φ (a * fieldBasis E s)) =
      ∑ s, ((a * fieldDualBasis E s : E) : PadicAlgCl l) *
        algebraMap ℚ_[l] (PadicAlgCl l) (φ (fieldBasis E s)) := by
  have h₁ (s : Fin (Module.finrank ℚ_[l] E)) : φ (a * fieldBasis E s) =
      ∑ t, Algebra.trace ℚ_[l] E (fieldDualBasis E t * (a * fieldBasis E s)) *
        φ (fieldBasis E t) := by
    conv_lhs => rw [← (fieldBasis E).sum_repr (a * fieldBasis E s)]
    simp [fieldBasis_repr_eq_trace]
  have h₂ (s : Fin (Module.finrank ℚ_[l] E)) : ((a * fieldDualBasis E s : E) : PadicAlgCl l) =
      ∑ t, algebraMap ℚ_[l] (PadicAlgCl l)
        (Algebra.trace ℚ_[l] E (a * fieldDualBasis E s * fieldBasis E t)) *
          (fieldDualBasis E t : PadicAlgCl l) := by
    conv_lhs => rw [← (fieldDualBasis E).sum_repr (a * fieldDualBasis E s)]
    simp only [fieldDualBasis_repr_eq_trace, IntermediateField.coe_sum,
      Algebra.smul_def]
    rfl
  simp_rw [h₁, h₂, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
  rw [show fieldDualBasis E s * (a * fieldBasis E t) = a * fieldDualBasis E s * fieldBasis E t by
    ring]
  ring

end DualBasis

variable (E n) in
/-- The matrix `Q` of the multiplication map `ℚ̄_ℓ ⊗_{ℚ_ℓ} Eⁿ → ℚ̄_ℓⁿ` in the coordinates of
`PadicAlgCl.coordBasis`. -/
noncomputable def latticeQ : Matrix (Fin n) (Fin (latticeRank E n)) (PadicAlgCl l) :=
  Matrix.of fun i k ↦ (coordBasis E n k i : PadicAlgCl l)

variable (E n) in
/-- The section `P` of `PadicAlgCl.latticeQ`, built from the trace dual basis: the column `j`
is `∑ₛ b^∨_s ⊗ bₛ eⱼ`. -/
noncomputable def latticeP : Matrix (Fin (latticeRank E n)) (Fin n) (PadicAlgCl l) :=
  Matrix.of fun k j ↦ ∑ s, (fieldDualBasis E s : PadicAlgCl l) *
    algebraMap ℚ_[l] (PadicAlgCl l) ((coordBasis E n).repr (Pi.single j (fieldBasis E s)) k)

omit [FiniteDimensional ℚ_[l] E] in
/-- `ι(q • e) = q ι(e)` for the embedding `E ⊆ ℚ̄_ℓ`. -/
lemma coe_smul_eq (q : ℚ_[l]) (e : E) :
    ((q • e : E) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) q * (e : PadicAlgCl l) := by
  rw [Algebra.smul_def, IntermediateField.coe_mul]
  rfl

/-- `Q R(A) = A Q`. -/
lemma latticeQ_mul_restrictScalarsMatrix (A : Matrix (Fin n) (Fin n) E) :
    latticeQ E n * (restrictScalarsMatrix A).map (algebraMap ℚ_[l] (PadicAlgCl l)) =
      A.map (algebraMap E (PadicAlgCl l)) * latticeQ E n := by
  ext i k
  simp only [Matrix.mul_apply, latticeQ, Matrix.of_apply, Matrix.map_apply]
  have hcol : ∑ m, restrictScalarsMatrix A m k • coordBasis E n m =
      A *ᵥ coordBasis E n k := by
    simp only [restrictScalarsMatrix, LinearMap.toMatrix_apply]
    exact (coordBasis E n).sum_repr _
  have := congrArg (fun v : Fin n → E ↦ (v i : PadicAlgCl l)) hcol
  simp only [Finset.sum_apply, Pi.smul_apply, IntermediateField.coe_sum, coe_smul_eq,
    Matrix.mulVec, dotProduct, IntermediateField.coe_mul] at this
  exact (Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _).trans this

/-- `R(A) P = P A`. -/
lemma restrictScalarsMatrix_mul_latticeP (A : Matrix (Fin n) (Fin n) E) :
    (restrictScalarsMatrix A).map (algebraMap ℚ_[l] (PadicAlgCl l)) * latticeP E n =
      latticeP E n * A.map (algebraMap E (PadicAlgCl l)) := by
  classical
  ext k j
  simp only [Matrix.mul_apply, latticeP, Matrix.of_apply, Matrix.map_apply]
  set ι₀ := algebraMap ℚ_[l] (PadicAlgCl l)
  set r : Fin (Module.finrank ℚ_[l] E) → Fin n → Fin (latticeRank E n) → ℚ_[l] :=
    fun s i m ↦ (coordBasis E n).repr (Pi.single i (fieldBasis E s)) m
  -- the left side, through `R(A) (coords x) = coords (A x)`
  have hL (s : Fin (Module.finrank ℚ_[l] E)) :
      ∑ m, restrictScalarsMatrix A k m * r s j m =
        (coordBasis E n).repr (A *ᵥ Pi.single j (fieldBasis E s)) k := by
    have := congrFun (restrictScalarsMatrix_mulVec A (Pi.single j (fieldBasis E s))) k
    simpa [Matrix.mulVec, dotProduct, latticeCoords, r] using this
  have hA (s : Fin (Module.finrank ℚ_[l] E)) : A *ᵥ Pi.single j (fieldBasis E s) =
      ∑ i, Pi.single i (A i j * fieldBasis E s) := by
    funext i'
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
  have hLHS : ∑ m, ι₀ (restrictScalarsMatrix A k m) *
      ∑ s, (fieldDualBasis E s : PadicAlgCl l) * ι₀ (r s j m) =
      ∑ i, ∑ s, (fieldDualBasis E s : PadicAlgCl l) * ι₀
        ((coordBasis E n).repr (Pi.single i (A i j * fieldBasis E s)) k) := by
    calc _ = ∑ s, ∑ m, (fieldDualBasis E s : PadicAlgCl l) *
            (ι₀ (restrictScalarsMatrix A k m) * ι₀ (r s j m)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ ↦ by ring
      _ = ∑ s, (fieldDualBasis E s : PadicAlgCl l) *
            ι₀ ((coordBasis E n).repr (A *ᵥ Pi.single j (fieldBasis E s)) k) := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [← Finset.mul_sum, ← hL, map_sum]
          simp_rw [map_mul]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [hA, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum, Finset.mul_sum]
  rw [hLHS]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := sum_fieldDualBasis_mul_apply
    (((LinearMap.proj k).comp (coordBasis E n).equivFun.toLinearMap).comp
      (LinearMap.single ℚ_[l] (fun _ : Fin n ↦ E) i)) (A i j)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_single,
    LinearMap.coe_proj, Function.eval, Module.Basis.equivFun_apply] at this
  rw [this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hc : algebraMap E (PadicAlgCl l) (A i j) = (A i j : PadicAlgCl l) := rfl
  rw [IntermediateField.coe_mul, hc]
  ring

/-- `Q P = 1`. -/
lemma latticeQ_mul_latticeP : latticeQ E n * latticeP E n = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, latticeQ, latticeP, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (s : Fin (Module.finrank ℚ_[l] E)) : ∑ k, (coordBasis E n k i : PadicAlgCl l) *
      ((fieldDualBasis E s : PadicAlgCl l) * algebraMap ℚ_[l] (PadicAlgCl l)
        ((coordBasis E n).repr (Pi.single j (fieldBasis E s)) k)) =
      (fieldDualBasis E s : PadicAlgCl l) * ((Pi.single j (fieldBasis E s) : Fin n → E) i) := by
    have := congrArg (fun v : Fin n → E ↦ (v i : PadicAlgCl l))
      ((coordBasis E n).sum_repr (Pi.single j (fieldBasis E s)))
    simp only [Finset.sum_apply, Pi.smul_apply, IntermediateField.coe_sum, coe_smul_eq] at this
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp_rw [h]
  by_cases hij : i = j
  · subst hij
    have := congrArg (fun e : E ↦ (e : PadicAlgCl l)) (sum_fieldDualBasis_mul_fieldBasis (E := E))
    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul,
      IntermediateField.coe_one] at this
    simpa using this
  · simp [hij, Matrix.one_apply_ne hij]

end PadicAlgCl
