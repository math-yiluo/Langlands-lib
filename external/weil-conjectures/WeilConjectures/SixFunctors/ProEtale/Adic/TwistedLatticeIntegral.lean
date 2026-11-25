/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeBasis
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTower
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition

/-!
# The integral cocycle of a lattice

Let `f : V ⟶ Y` be a morphism and `γ : V ×_Y V → GL_n(E)` a continuous cocycle for a finite
extension `E` of `ℚ_ℓ`, with a lattice: a twisted section `σ` of `γ` acting on the lattices of
`Eⁿ` (`PadicAlgCl.CompactOpenLattice`). In the coordinates `Eⁿ = ℚ_ℓᴺ` of a basis of `E`, the
lattice at `v ∈ V` is `h(v) ℤ_ℓᴺ` for a locally constant `h : V → GL_N(ℚ_ℓ)`
(`PadicAlgCl.CompactOpenLattice.exists_glBasis`), and the conjugate
`γ'(v₁, v₂) = h(v₁)⁻¹ R(γ(v₁, v₂)) h(v₂)` of the restriction of scalars `R(γ)` of `γ` preserves
`ℤ_ℓᴺ`: it is a continuous integral cocycle (`AlgebraicGeometry.IsIntegralCocycle`,
`AlgebraicGeometry.exists_isIntegralCocycle_of_isTwistedSection`).

We also record that the transition matrices of a trivialisation of an `ℓ`-adic sheaf, with values
in `GL_n(E)`, form a continuous cocycle
(`AlgebraicGeometry.ProEtale.AdicSheaf.isTransitionCocycle_of_map_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Matrix

namespace AlgebraicGeometry

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} {f : V ⟶ Y}

section Points

variable (f)

/-- The first and second projections of the points of `V ×_Y V ×_Y V`, compared. -/
lemma tripleProduct_points (w : ↥(tripleProduct f)) :
    (pullback.fst f f).base ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) =
        (pullback.fst f f).base ((tripleProj₁₃ f).base w) ∧
      (pullback.snd f f).base ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) =
        (pullback.fst f f).base ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w) ∧
      (pullback.snd f f).base ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w) =
        (pullback.snd f f).base ((tripleProj₁₃ f).base w) := by
  have h₁ : tripleProj₁₃ f ≫ pullback.fst f f =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
    pullback.lift_fst _ _ _
  have h₂ : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
    pullback.condition
  have h₃ : tripleProj₁₃ f ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f :=
    pullback.lift_snd _ _ _
  have e₁ := congrArg (fun φ ↦ φ.base w) h₁
  have e₂ := congrArg (fun φ ↦ φ.base w) h₂
  have e₃ := congrArg (fun φ ↦ φ.base w) h₃
  simp only [Scheme.Hom.comp_apply] at e₁ e₂ e₃
  exact ⟨e₁.symm, e₂, e₃.symm⟩

/-- The projections of the diagonal points of `V ×_Y V`. -/
lemma diagonal_points (v : V) :
    (pullback.fst f f).base ((pullback.diagonal f).base v) = v ∧
      (pullback.snd f f).base ((pullback.diagonal f).base v) = v := by
  have e₁ := congrArg (fun φ ↦ φ.base v) (pullback.diagonal_fst f)
  have e₂ := congrArg (fun φ ↦ φ.base v) (pullback.diagonal_snd f)
  simp only [Scheme.Hom.comp_apply] at e₁ e₂
  exact ⟨e₁, e₂⟩

end Points

section Lattice

variable {E : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] E] {n : ℕ}

/-- Square matrices of the size `N = n [E : ℚ_ℓ]` of the restriction of scalars. -/
local notation "𝕄" => Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n))

/-- The restriction of scalars of matrices is continuous, being `ℚ_ℓ`-linear between
finite-dimensional spaces. -/
lemma continuous_restrictScalarsMatrix :
    Continuous (restrictScalarsMatrix : Matrix (Fin n) (Fin n) E → _) := by
  let φ : Matrix (Fin n) (Fin n) E →ₗ[ℚ_[l]]
      Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) ℚ_[l] :=
    { toFun := restrictScalarsMatrix
      map_add' A B := by
        rw [restrictScalarsMatrix, restrictScalarsMatrix, restrictScalarsMatrix, ← map_add]
        congr 1
        refine LinearMap.ext fun x ↦ ?_
        simp
      map_smul' r A := by
        rw [restrictScalarsMatrix, restrictScalarsMatrix, RingHom.id_apply, ← map_smul]
        congr 1
        refine LinearMap.ext fun x ↦ ?_
        simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearMap.smul_apply]
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum] }
  exact φ.continuous_of_finiteDimensional

/-- An invertible matrix over `ℚ_ℓ` which is integral together with its inverse comes from
`GL_N(ℤ_ℓ)`. -/
lemma exists_gl_padicInt_map_eq {N : ℕ} (B : GL (Fin N) ℚ_[l])
    (hB : ∀ i j, ∃ b : ℤ_[l], (b : ℚ_[l]) = (B : Matrix (Fin N) (Fin N) ℚ_[l]) i j)
    (hB' : ∀ i j, ∃ b : ℤ_[l],
      (b : ℚ_[l]) = ((B⁻¹ : GL (Fin N) ℚ_[l]) : Matrix (Fin N) (Fin N) ℚ_[l]) i j) :
    ∃ B₀ : GL (Fin N) ℤ_[l],
      (B₀ : Matrix (Fin N) (Fin N) ℤ_[l]).map (algebraMap ℤ_[l] ℚ_[l]) = B := by
  choose b hb using hB
  choose b' hb' using hB'
  have hinj : Function.Injective fun A : Matrix (Fin N) (Fin N) ℤ_[l] ↦
      A.map (algebraMap ℤ_[l] ℚ_[l]) :=
    fun A B hAB ↦ Matrix.ext fun i j ↦ PadicInt.ext (congrFun (congrFun hAB i) j)
  have hM : (Matrix.of b).map (algebraMap ℤ_[l] ℚ_[l]) = B := Matrix.ext fun i j ↦ hb i j
  have hM' : (Matrix.of b').map (algebraMap ℤ_[l] ℚ_[l]) = ((B⁻¹ : GL (Fin N) ℚ_[l]) :
      Matrix (Fin N) (Fin N) ℚ_[l]) := Matrix.ext fun i j ↦ hb' i j
  refine ⟨⟨Matrix.of b, Matrix.of b', hinj ?_, hinj ?_⟩, hM⟩
  · simp only [Matrix.map_mul, hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · simp only [Matrix.map_mul, hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

omit [FiniteDimensional ℚ_[l] E] in
/-- The coordinate columns of a matrix. -/
lemma mulVec_intCoe_single {N : ℕ} (B : Matrix (Fin N) (Fin N) ℚ_[l]) (i j : Fin N) :
    (B *ᵥ CompactOpenLattice.intCoe N (Pi.single j 1)) i = B i j := by
  have : CompactOpenLattice.intCoe (l := l) N (Pi.single j 1) = Pi.single j 1 := by
    funext k
    simp only [CompactOpenLattice.intCoe_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [this, Matrix.mulVec_single_one]
  rfl

/-- **Conjugating into the integral group.** If `A ∈ GL_n(E)` maps the lattice `L'` to `L`, and
`L = g ℤ_ℓᴺ`, `L' = g' ℤ_ℓᴺ` in coordinates, then `g⁻¹ R(A) g'` maps `ℤ_ℓᴺ` into itself. -/
lemma exists_mulVec_intCoe_eq (A : GL (Fin n) E) {L L' : CompactOpenLattice E n}
    (hA : L = A • L') {g g' : GL (Fin (latticeRank E n)) ℚ_[l]}
    (hg : ∀ x, x ∈ L.1 ↔ ∃ y : Fin (latticeRank E n) → ℤ_[l], latticeCoords E n x =
      (g : 𝕄 ℚ_[l]) *ᵥ CompactOpenLattice.intCoe _ y)
    (hg' : ∀ x, x ∈ L'.1 ↔ ∃ y : Fin (latticeRank E n) → ℤ_[l], latticeCoords E n x =
      (g' : 𝕄 ℚ_[l]) *ᵥ CompactOpenLattice.intCoe _ y)
    (y : Fin (latticeRank E n) → ℤ_[l]) :
    ∃ y' : Fin (latticeRank E n) → ℤ_[l], (((g⁻¹ : GL _ ℚ_[l]) : 𝕄 ℚ_[l]) *
      restrictScalarsMatrix (A : Matrix (Fin n) (Fin n) E) * (g' : 𝕄 ℚ_[l])) *ᵥ
        CompactOpenLattice.intCoe _ y = CompactOpenLattice.intCoe _ y' := by
  set x' := (latticeCoords E n).symm ((g' : 𝕄 ℚ_[l]) *ᵥ CompactOpenLattice.intCoe _ y)
  have hx' : x' ∈ L'.1 := (hg' x').2 ⟨y, LinearEquiv.apply_symm_apply _ _⟩
  have hAx : (A : Matrix (Fin n) (Fin n) E) *ᵥ x' ∈ L.1 := by
    rw [hA, CompactOpenLattice.smul_def, CompactOpenLattice.coe_map]
    exact ⟨x', hx', rfl⟩
  obtain ⟨y', hy'⟩ := (hg _).1 hAx
  refine ⟨y', ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← LinearEquiv.apply_symm_apply
    (latticeCoords E n) ((g' : 𝕄 ℚ_[l]) *ᵥ CompactOpenLattice.intCoe _ y),
    restrictScalarsMatrix_mulVec, hy', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mulVec]

variable (γ : ↥(pullback f f) → GL (Fin n) E)

/-- **The integral cocycle of a lattice.** For a continuous cocycle `γ : V ×_Y V → GL_n(E)`
with a lattice `σ`, there are a locally constant `h : V → GL_N(ℚ_ℓ)` (in coordinates, the lattice
at `v` is `h(v) ℤ_ℓᴺ`) and a continuous integral cocycle `γ'` with
`γ'(v₁, v₂) = h(v₁)⁻¹ R(γ(v₁, v₂)) h(v₂)`. -/
theorem exists_isIntegralCocycle_of_isTwistedSection
    (hγc : ∀ i j, Continuous fun z ↦ ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
    (hγc' : ∀ i j, Continuous fun z ↦ (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
    (hγd : ∀ v, γ ((pullback.diagonal f).base v) = 1)
    (hγco : ∀ w : ↥(tripleProduct f), γ ((tripleProj₁₃ f).base w) =
      γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
        γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w))
    (σ : ↥(pullback f (𝟙 Y)) → CompactOpenLattice E n)
    (hσ : IsTwistedSection f (fun z L ↦ γ z • L) (𝟙 Y) σ) :
    ∃ (h : V → GL (Fin (latticeRank E n)) ℚ_[l])
      (γ' : ↥(pullback f f) → GL (Fin (latticeRank E n)) ℤ_[l]),
      IsLocallyConstant h ∧ IsIntegralCocycle f γ' ∧
      ∀ z, (γ' z : 𝕄 ℤ_[l]).map (algebraMap ℤ_[l] ℚ_[l]) =
        (((h ((pullback.fst f f).base z))⁻¹ : GL _ ℚ_[l]) : 𝕄 ℚ_[l]) *
          restrictScalarsMatrix (γ z : Matrix (Fin n) (Fin n) E) *
            (h ((pullback.snd f f).base z) : 𝕄 ℚ_[l]) := by
  classical
  -- the lattices at the points of `V`
  let s : V ⟶ pullback f (𝟙 Y) := pullback.lift (𝟙 V) f (by rw [Category.id_comp,
    Category.comp_id])
  let Λ : V → CompactOpenLattice E n := σ ∘ s.base
  have hΛ : IsLocallyConstant Λ := hσ.1.comp_continuous s.base.hom.continuous
  have hΛγ (z : ↥(pullback f f)) :
      Λ ((pullback.fst f f).base z) = γ z • Λ ((pullback.snd f f).base z) := by
    let L : pullback f f ⟶ pullback (pullback.snd f (𝟙 Y)) (pullback.snd f (𝟙 Y)) :=
      pullback.lift (pullback.fst f f ≫ s) (pullback.snd f f ≫ s) (by
        simp only [Category.assoc, s, pullback.lift_snd, pullback.condition])
    have hL₁ : L ≫ pullback.fst _ _ = pullback.fst f f ≫ s := pullback.lift_fst _ _ _
    have hL₂ : L ≫ pullback.snd _ _ = pullback.snd f f ≫ s := pullback.lift_snd _ _ _
    have hL₃ : L ≫ twistedPairMap f (𝟙 Y) = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hL₁, Category.assoc,
          pullback.lift_fst, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hL₂, Category.assoc,
          pullback.lift_fst, Category.comp_id, Category.id_comp]
    have e₁ := congrArg (fun φ ↦ φ.base z) hL₁
    have e₂ := congrArg (fun φ ↦ φ.base z) hL₂
    have e₃ := congrArg (fun φ ↦ φ.base z) hL₃
    simp only [Scheme.Hom.comp_apply] at e₁ e₂ e₃
    have := hσ.2 (L.base z)
    rw [e₁, e₂, e₃] at this
    exact this
  -- bases of the lattices
  have hH (L : CompactOpenLattice E n) := (CompactOpenLattice.exists_glBasis L).choose_spec
  let H : CompactOpenLattice E n → GL (Fin (latticeRank E n)) ℚ_[l] :=
    fun L ↦ (CompactOpenLattice.exists_glBasis L).choose
  let h : V → GL (Fin (latticeRank E n)) ℚ_[l] := H ∘ Λ
  have hh : IsLocallyConstant h := hΛ.comp H
  -- the conjugated cocycle over `ℚ_ℓ`
  let R := restrictScalarsGL E n
  let γQ (z : ↥(pullback f f)) : GL (Fin (latticeRank E n)) ℚ_[l] :=
    (h ((pullback.fst f f).base z))⁻¹ * R (γ z) * h ((pullback.snd f f).base z)
  have hint (z : ↥(pullback f f)) : ∃ B₀ : GL (Fin (latticeRank E n)) ℤ_[l],
      (B₀ : 𝕄 ℤ_[l]).map (algebraMap ℤ_[l] ℚ_[l]) =
        ((γQ z : GL (Fin (latticeRank E n)) ℚ_[l]) :
          Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) ℚ_[l]) := by
    refine exists_gl_padicInt_map_eq _ (fun i j ↦ ?_) (fun i j ↦ ?_)
    · obtain ⟨y', hy'⟩ := exists_mulVec_intCoe_eq (γ z) (hΛγ z) (hH _) (hH _) (Pi.single j 1)
      refine ⟨y' i, ?_⟩
      have := congrFun hy' i
      rw [mulVec_intCoe_single] at this
      rw [← CompactOpenLattice.intCoe_apply, ← this]
      rfl
    · have hinv : Λ ((pullback.snd f f).base z) = (γ z)⁻¹ • Λ ((pullback.fst f f).base z) := by
        rw [hΛγ z, inv_smul_smul]
      obtain ⟨y', hy'⟩ := exists_mulVec_intCoe_eq (γ z)⁻¹ hinv (hH _) (hH _) (Pi.single j 1)
      refine ⟨y' i, ?_⟩
      have := congrFun hy' i
      rw [mulVec_intCoe_single] at this
      rw [← CompactOpenLattice.intCoe_apply, ← this]
      have hm : (((γQ z)⁻¹ : GL (Fin (latticeRank E n)) ℚ_[l]) :
          Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) ℚ_[l]) =
          ((H (Λ ((pullback.snd f f).base z)))⁻¹ : GL (Fin (latticeRank E n)) ℚ_[l]).val *
            restrictScalarsMatrix (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
              (H (Λ ((pullback.fst f f).base z))).val := by
        simp only [γQ, _root_.mul_inv_rev, inv_inv]
        rw [← mul_assoc, ← map_inv]
        rfl
      rw [hm]
  choose γ' hγ' using hint
  -- transferring identities along `GL_N(ℤ_ℓ) → GL_N(ℚ_ℓ)`
  have hmap (z : ↥(pullback f f)) :
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[l] ℚ_[l]) (γ' z) = γQ z :=
    Units.ext (hγ' z)
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin (latticeRank E n))
      (algebraMap ℤ_[l] ℚ_[l])) := fun A B hAB ↦ Units.ext (Matrix.map_injective
        (fun a b h ↦ PadicInt.ext h) (congrArg Units.val hAB))
  -- continuity of the entries
  have hcont (A : ↥(pullback f f) → GL (Fin (latticeRank E n)) ℤ_[l])
      (hA : Continuous fun z ↦ ((A z : GL (Fin (latticeRank E n)) ℤ_[l]) :
        Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) ℤ_[l]).map
          (algebraMap ℤ_[l] ℚ_[l])) (i j : Fin (latticeRank E n)) :
      Continuous fun z ↦ (A z : 𝕄 ℤ_[l]) i j := by
    rw [PadicInt.isOpenEmbedding_coe.isInducing.continuous_iff]
    exact (continuous_apply j).comp ((continuous_apply i).comp hA)
  have hloc (g : GL (Fin (latticeRank E n)) ℚ_[l] → 𝕄 ℚ_[l])
      (p : pullback f f ⟶ V) :
      Continuous fun z ↦ g (h (p.base z)) :=
    ((hh.comp g).comp_continuous p.base.hom.continuous).continuous
  have hR (g : GL (Fin n) E → GL (Fin n) E)
      (hg : ∀ i j, Continuous fun z ↦ ((g (γ z) : GL (Fin n) E) : Matrix _ _ E) i j) :
      Continuous fun z ↦ restrictScalarsMatrix ((g (γ z) : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) :=
    continuous_restrictScalarsMatrix.comp (continuous_pi fun i ↦ continuous_pi fun j ↦ hg i j)
  refine ⟨h, γ', hh, ⟨fun i j ↦ hcont γ' ?_ i j, fun i j ↦ hcont (fun z ↦ (γ' z)⁻¹) ?_ i j,
    fun v ↦ hinj ?_, fun w ↦ hinj ?_⟩, fun z ↦ hγ' z⟩
  · simp only [hγ']
    exact ((hloc (fun g ↦ ((g⁻¹ : GL _ ℚ_[l]) : 𝕄 ℚ_[l])) _).matrix_mul
      (hR id hγc)).matrix_mul (hloc (fun g ↦ (g : 𝕄 ℚ_[l])) _)
  · have (z : ↥(pullback f f)) : (((γ' z)⁻¹ : GL _ ℤ_[l]) : 𝕄 ℤ_[l]).map
        (algebraMap ℤ_[l] ℚ_[l]) = (((h ((pullback.snd f f).base z))⁻¹ : GL _ ℚ_[l]) :
          𝕄 ℚ_[l]) * restrictScalarsMatrix (((γ z)⁻¹ : GL (Fin n) E) :
            Matrix (Fin n) (Fin n) E) * (h ((pullback.fst f f).base z) : 𝕄 ℚ_[l]) := by
      have := congrArg (fun A : GL (Fin (latticeRank E n)) ℚ_[l] ↦ (A⁻¹ : GL _ ℚ_[l]).val)
        (hmap z)
      simp only [γQ, _root_.mul_inv_rev, inv_inv] at this
      rw [← mul_assoc] at this
      exact this
    simp only [this]
    exact ((hloc (fun g ↦ ((g⁻¹ : GL _ ℚ_[l]) : 𝕄 ℚ_[l])) _).matrix_mul
      (hR (fun g ↦ g⁻¹) hγc')).matrix_mul (hloc (fun g ↦ (g : 𝕄 ℚ_[l])) _)
  · obtain ⟨h₁, h₂⟩ := diagonal_points f v
    rw [hmap, map_one]
    simp only [γQ, h₁, h₂, hγd, map_one, mul_one, inv_mul_cancel]
  · obtain ⟨e₁, e₂, e₃⟩ := tripleProduct_points f w
    rw [map_mul, hmap, hmap, hmap]
    simp only [γQ, hγco w, map_mul, e₁, e₂, e₃]
    group

end Lattice

end AlgebraicGeometry
