/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice

/-!
# `𝒪_E`-lattices spanned by lattices of `Eⁿ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`
(`PadicAlgCl.integers`). The `𝒪_E`-span of a lattice `L ⊆ Eⁿ` (a compact open subgroup,
`PadicAlgCl.CompactOpenLattice`) is `g 𝒪_Eⁿ` for some `g ∈ GL_n(E)`
(`PadicAlgCl.CompactOpenLattice.exists_glBasis_integers`): it is squeezed between two scalings
of `𝒪_Eⁿ`, hence a free `𝒪_E`-module of rank `n`, `𝒪_E` being a principal ideal domain.

The span is compatible with the action of `GL_n(E)`, so that if `A L = L'` and the spans of `L`,
`L'` are `g 𝒪_Eⁿ`, `g' 𝒪_Eⁿ`, then `g'⁻¹ A g` has integral entries
(`PadicAlgCl.CompactOpenLattice.norm_integersBasisGL_inv_mul_mul_le_one`). This turns a
lattice-valued twisted section of a `GL_n(E)`-valued cocycle into a change of trivialisation
making the cocycle integral.
-/

@[expose] public section

open Matrix

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}

/-- The norm of `E` is the norm of `ℚ̄_ℓ`. -/
lemma mem_integers_iff_norm_le_one_intermediateField (x : E) : x ∈ integers l E ↔ ‖x‖ ≤ 1 := by
  rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  rfl

/-- The norm of `ℓ` in `E` is `ℓ⁻¹`. -/
lemma norm_natCast_self_intermediateField : ‖(l : E)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : E) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by simp
  change ‖((l : E) : PadicAlgCl l)‖ = _
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

end PadicAlgCl

namespace PadicAlgCl.CompactOpenLattice

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)} {n : ℕ}

variable (l E n) in
/-- The inclusion `𝒪_Eⁿ ⟶ Eⁿ`, as an `𝒪_E`-linear map. -/
noncomputable def integersCoe : (Fin n → integers l E) →ₗ[integers l E] (Fin n → E) where
  toFun y k := (y k : E)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma integersCoe_apply (y : Fin n → integers l E) (k : Fin n) :
    integersCoe l E n y k = (y k : E) :=
  rfl

lemma integersCoe_injective : Function.Injective (integersCoe l E n) :=
  fun _ _ h ↦ funext fun k ↦ Subtype.ext (congrFun h k)

/-- The `𝒪_E`-span of a lattice. -/
noncomputable def integersSpan (L : CompactOpenLattice E n) :
    Submodule (integers l E) (Fin n → E) :=
  Submodule.span (integers l E) (L.1 : Set (Fin n → E))

/-- The box `{v | ∀ k, ‖v k‖ ≤ R}`, an `𝒪_E`-submodule of `Eⁿ`. -/
noncomputable def integersBox (R : ℝ) (hR : 0 ≤ R) : Submodule (integers l E) (Fin n → E) where
  carrier := {v | ∀ k, ‖v k‖ ≤ R}
  add_mem' ha hb k := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha k) (hb k))
  zero_mem' k := by simpa using hR
  smul_mem' c v hv k := by
    have hc : ‖(c : E)‖ ≤ 1 := (mem_integers_iff_norm_le_one_intermediateField _).1 c.2
    change ‖(c : E) * v k‖ ≤ R
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hv k)

variable [FiniteDimensional ℚ_[l] E]

omit [FiniteDimensional ℚ_[l] E] in
/-- The span of a lattice is squeezed between two scalings of `𝒪_Eⁿ`. -/
lemma exists_pow_bounds_integersSpan (L : CompactOpenLattice E n) :
    ∃ A : ℕ, (∀ x ∈ integersSpan L, ∀ k, ‖(l : E) ^ A * x k‖ ≤ 1) ∧
      ∀ y : Fin n → integers l E, (fun k ↦ (l : E) ^ A * (y k : E)) ∈ L.1 := by
  obtain ⟨r, hr, R, hR, hbox, hbound⟩ := exists_box L
  obtain ⟨A, hA⟩ := exists_congruenceRadius_lt (l := l) (ε := min r (1 / (R + 1)))
    (lt_min hr (by positivity))
  have hpow : ‖(l : E) ^ A‖ = congruenceRadius l A := by
    rw [norm_pow, norm_natCast_self_intermediateField, congruenceRadius]
  have hr' : ‖(l : E) ^ A‖ ≤ r := by
    rw [hpow]
    exact (hA.trans_le (min_le_left _ _)).le
  have hR' : ‖(l : E) ^ A‖ * R ≤ 1 := by
    have h₁ : ‖(l : E) ^ A‖ < 1 / (R + 1) := by
      rw [hpow]
      exact hA.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h₁
    nlinarith [norm_nonneg ((l : E) ^ A)]
  have hspan : integersSpan L ≤ integersBox R hR :=
    Submodule.span_le.2 fun v hv k ↦ hbound v hv k
  refine ⟨A, fun x hx k ↦ ?_, fun y ↦ hbox _ fun k ↦ ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hspan hx k) (norm_nonneg _)).trans hR'
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      ((mem_integers_iff_norm_le_one_intermediateField _).1 (y k).2)).trans hr'

/-- **The `𝒪_E`-span of a lattice is free**: it is `g 𝒪_Eⁿ` for some `g ∈ GL_n(E)`. The span,
scaled into `𝒪_Eⁿ`, is a submodule of the free module `𝒪_Eⁿ` over the principal ideal domain
`𝒪_E`, hence free; its basis is an `E`-basis of `Eⁿ`, the span containing a scaling of
`𝒪_Eⁿ`. -/
theorem exists_glBasis_integers (L : CompactOpenLattice E n) :
    ∃ g : GL (Fin n) E, ∀ x : Fin n → E, x ∈ integersSpan L ↔
      ∃ y : Fin n → integers l E, x = (g : Matrix (Fin n) (Fin n) E) *ᵥ integersCoe l E n y := by
  classical
  obtain ⟨A, hA₁, hA₂⟩ := exists_pow_bounds_integersSpan L
  set O := integers l E
  set lam : E := (l : E) ^ A
  have hlam : lam ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hlamO : lam ∈ O := by
    rw [mem_integers_iff_norm_le_one_intermediateField, norm_pow,
      norm_natCast_self_intermediateField]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by
      exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  let S : Submodule O (Fin n → O) :=
    { carrier := {y | lam⁻¹ • integersCoe l E n y ∈ integersSpan L}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add, smul_add] at ha hb ⊢
        exact (integersSpan L).add_mem ha hb
      zero_mem' := by simp [(integersSpan L).zero_mem]
      smul_mem' := fun c y hy ↦ by
        simp only [Set.mem_ofPred_eq] at hy ⊢
        have : lam⁻¹ • integersCoe l E n (c • y) = c • (lam⁻¹ • integersCoe l E n y) := by
          funext k
          change lam⁻¹ * ((c : E) * (y k : E)) = (c : E) * (lam⁻¹ * (y k : E))
          ring
        rw [this]
        exact (integersSpan L).smul_mem c hy }
  have hS (y : Fin n → O) : y ∈ S ↔ lam⁻¹ • integersCoe l E n y ∈ integersSpan L := Iff.rfl
  -- membership in the span through `S`
  have hk₁ (x : Fin n → E) : x ∈ integersSpan L ↔ ∃ y ∈ S, x = lam⁻¹ • integersCoe l E n y := by
    refine ⟨fun hx ↦ ⟨fun k ↦ ⟨lam * x k,
      (mem_integers_iff_norm_le_one_intermediateField _).2 (hA₁ x hx k)⟩, ?_, ?_⟩, ?_⟩
    · have : lam⁻¹ • integersCoe l E n (fun k ↦ ⟨lam * x k,
          (mem_integers_iff_norm_le_one_intermediateField _).2 (hA₁ x hx k)⟩) = x := by
        funext k
        simp [integersCoe_apply, hlam]
      rw [hS, this]
      exact hx
    · funext k
      simp [integersCoe_apply, hlam]
    · rintro ⟨y, hy, rfl⟩
      exact hy
  have hk₂ (z : Fin n → O) : ((⟨lam, hlamO⟩ : O) ^ 2) • z ∈ S := by
    rw [hS]
    refine Submodule.subset_span ?_
    have : lam⁻¹ • integersCoe l E n (((⟨lam, hlamO⟩ : O) ^ 2) • z) =
        fun k ↦ lam * (z k : E) := by
      funext k
      change lam⁻¹ * ((lam ^ 2) * (z k : E)) = _
      field_simp
    rw [this]
    exact hA₂ z
  obtain ⟨m, bS⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) S
  let w : Fin m → (Fin n → E) := fun j ↦ integersCoe l E n (bS j)
  have hw_sum (c : Fin m → O) :
      integersCoe l E n (∑ j, c j • (bS j : Fin n → O)) = ∑ j, (c j : E) • w j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul]
    exact algebra_compatible_smul E (c j) (w j)
  have hy_sum (y : S) : (y : Fin n → O) = ∑ j, bS.repr y j • (bS j : Fin n → O) := by
    have := congrArg Subtype.val (bS.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hli : LinearIndependent E w := by
    refine (LinearIndependent.iff_fractionRing O E).1 ?_
    exact bS.linearIndependent.map' ((integersCoe l E n).comp S.subtype)
      (LinearMap.ker_eq_bot.2 (integersCoe_injective.comp Subtype.val_injective))
  have hsp : ⊤ ≤ Submodule.span E (Set.range w) := by
    intro v _
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ ?_
    let y : S := ⟨((⟨lam, hlamO⟩ : O) ^ 2) • fun k' ↦ if k = k' then 1 else 0, hk₂ _⟩
    have hy : (fun k' ↦ if k = k' then (1 : E) else 0) =
        (lam ^ 2)⁻¹ • ∑ j, (bS.repr y j : E) • w j := by
      rw [← hw_sum, ← hy_sum]
      funext k'
      simp only [y, Pi.smul_apply, integersCoe_apply, smul_eq_mul]
      split_ifs <;> simp [hlam]
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW := Module.Basis.mk hli hsp
  have hmn : m = n := by
    have := Module.finrank_eq_card_basis bW
    rw [Module.finrank_fin_fun, Fintype.card_fin] at this
    exact this.symm
  subst hmn
  let M := (Pi.basisFun E (Fin m)).toMatrix bW
  have hM (c : Fin m → O) : M *ᵥ integersCoe l E m c = ∑ j, (c j : E) • w j := by
    funext i
    simp only [M, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integersCoe_apply, bW, Module.Basis.mk_apply]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hdet : (lam⁻¹ • M).det ≠ 0 := by
    have : Invertible M := (Pi.basisFun E (Fin m)).invertibleToMatrix bW
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam)) (Matrix.isUnit_det_of_invertible M).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun x ↦ ?_⟩
  have hg (v : Fin m → E) : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet :
      GL (Fin m) E) : Matrix _ _ E) *ᵥ v = lam⁻¹ • (M *ᵥ v) := by
    funext i
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc]
  rw [hk₁]
  simp only [hg]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨bS.repr ⟨y, hy⟩, ?_⟩
    rw [hM, ← hw_sum, ← hy_sum]
  · rintro ⟨c, rfl⟩
    refine ⟨∑ j, c j • (bS j : Fin m → O), Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (bS j).2, ?_⟩
    rw [hM, hw_sum]

/-- A choice of `g ∈ GL_n(E)` with `𝒪_E L = g 𝒪_Eⁿ`. -/
noncomputable def integersBasisGL (L : CompactOpenLattice E n) : GL (Fin n) E :=
  (exists_glBasis_integers L).choose

lemma mem_integersSpan_iff (L : CompactOpenLattice E n) (x : Fin n → E) :
    x ∈ integersSpan L ↔ ∃ y : Fin n → integers l E,
      x = ((integersBasisGL L : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ
        integersCoe l E n y :=
  (exists_glBasis_integers L).choose_spec x

omit [FiniteDimensional ℚ_[l] E] in
/-- The span is compatible with the action of `GL_n(E)`. -/
lemma mulVec_mem_integersSpan_smul (A : GL (Fin n) E) {L : CompactOpenLattice E n}
    {x : Fin n → E} (hx : x ∈ integersSpan L) :
    (A : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ integersSpan (A • L) := by
  let φ : (Fin n → E) →ₗ[integers l E] (Fin n → E) :=
    (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) E)).restrictScalars (integers l E)
  have himage : φ '' (L.1 : Set (Fin n → E)) = ((A • L).1 : Set (Fin n → E)) := by
    ext v
    simp only [Set.mem_image, SetLike.mem_coe, smul_def, coe_map, AddSubgroup.coe_map,
      Set.mem_image]
    rfl
  have h := Submodule.mem_map_of_mem (f := φ) hx
  rw [integersSpan, Submodule.map_span, himage] at h
  exact h

/-- **Integrality of the conjugated action**: if `A L = L'`, then `g'⁻¹ A g` has integral
entries, for the bases `g`, `g'` of the spans of `L`, `L'`. -/
lemma norm_integersBasisGL_inv_mul_mul_le_one (A : GL (Fin n) E) {L L' : CompactOpenLattice E n}
    (h : A • L = L') (i j : Fin n) :
    ‖((((integersBasisGL L')⁻¹ * A * integersBasisGL L : GL (Fin n) E)) :
      Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  classical
  set g := integersBasisGL L
  set g' := integersBasisGL L'
  let e : Fin n → integers l E := Pi.single j 1
  have he : integersCoe l E n e = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [e, integersCoe_apply]
    · simp [e, integersCoe_apply, hk]
  have hx : (g : Matrix (Fin n) (Fin n) E) *ᵥ integersCoe l E n e ∈ integersSpan L :=
    (mem_integersSpan_iff L _).2 ⟨e, rfl⟩
  have hAx := mulVec_mem_integersSpan_smul A hx
  rw [h, mem_integersSpan_iff] at hAx
  obtain ⟨y, hy⟩ := hAx
  have key : (((g'⁻¹ * A * g : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single j 1 =
      integersCoe l E n y := by
    rw [← he, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy,
      Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have := congrFun key i
  rw [Matrix.mulVec_single_one] at this
  rw [show ((((g'⁻¹ * A * g : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) i j) =
    integersCoe l E n y i from this, integersCoe_apply]
  exact (mem_integers_iff_norm_le_one_intermediateField _).1 (y i).2

end PadicAlgCl.CompactOpenLattice
