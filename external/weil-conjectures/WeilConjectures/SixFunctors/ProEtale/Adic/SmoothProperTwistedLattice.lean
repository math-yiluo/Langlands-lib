/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedModule
public import WeilConjectures.SixFunctors.ProEtale.Adic.Retract
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeIntegral
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeRational
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTowerExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTransition
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeBasis

/-!
# Smooth proper direct images of lisse sheaves with a lattice

Let `K` be a field, `Y` locally of finite type over `K`, `g : T ⟶ Y` smooth and proper and `F`
a lisse `ℓ`-adic sheaf on `T`, trivialised on a pro-étale cover `f₀ : V ⟶ T` with transition
cocycle `γ : V ×_T V → GL_n(E)` for a finite extension `E` of `ℚ_ℓ`. A *lattice* of `F` is a
twisted section of the cocycle `γ` acting on the discrete set of `ℤ_ℓ`-lattices in `Eⁿ`, its
compact open subgroups (`PadicAlgCl.CompactOpenLattice`). If `F` has a lattice, every
`Hᵏ(Rg_* F[0])` is lisse
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_isTwistedSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable (l : ℕ) [Fact l.Prime]

/-- The exponent `ℓᵏ` of `ℤ_ℓ ⧸ ℓᵏ` is invertible over a field of characteristic `≠ ℓ`. -/
lemma hasInvertibleExponent_towerIdeal {K : Type u} [Field K] (hK : ringChar K ≠ l) (k : ℕ) :
    HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) (Spec (.of K)) := by
  have hl : (l : K) ≠ 0 := fun h ↦ hK
    (((Nat.dvd_prime Fact.out).1 (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one)
  refine ⟨l ^ k, pow_pos (Fact.out : l.Prime).pos k, ?_, ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.subset_span rfl
  · have := (Ne.isUnit (pow_ne_zero k hl)).map (Scheme.ΓSpecIso (.of K)).inv.hom
    simpa using this

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf

variable {l : ℕ} [Fact l.Prime]

/-- **A trivialised sheaf with a lattice is a retract of the rationalised lattice.** Let
`γ : V ×_T V → GL_n(E)` have the transition matrices of `ε` as values, and let `γ'` be an integral
cocycle with `γ'(v₁, v₂) = h(v₁)⁻¹ R(γ(v₁, v₂)) h(v₂)` for a locally constant
`h : V → GL_N(ℚ_ℓ)`. Then the descent of the transition matrices of `ε` is a retract of the
descent of `γ'⁻¹`, through the matrices `h⁻¹ P` and `Q h` (`PadicAlgCl.latticeP`,
`PadicAlgCl.latticeQ`). -/
lemma nonempty_retract_descentSheaf_integralCocycleInvMatrix {T V : Scheme.{u}} (f : V ⟶ T)
    [WeaklyEtale f] {G : AdicSheaf l T} {n : ℕ}
    (ε : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V)
    {E : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] E]
    {γ : ↥(pullback f f) → GL (Fin n) E} (hγ : IsTransitionValues ε γ)
    {h : V → GL (Fin (latticeRank E n)) ℚ_[l]} (hh : IsLocallyConstant h)
    {γ' : ↥(pullback f f) → GL (Fin (latticeRank E n)) ℤ_[l]} (hγ' : IsIntegralCocycle f γ')
    (hrel : ∀ z, (γ' z).val.map (algebraMap ℤ_[l] ℚ_[l]) =
      (h ((pullback.fst f f).base z))⁻¹.val *
        restrictScalarsMatrix (γ z : Matrix (Fin n) (Fin n) E) *
          (h ((pullback.snd f f).base z)).val) :
    Nonempty (Retract (descentSheaf f (transitionMatrix ε (pullback.fst f f) (pullback.snd f f)
      pullback.condition)) (descentSheaf f (integralCocycleInvMatrix l hγ'))) := by
  set ιQ := algebraMap ℚ_[l] (PadicAlgCl l)
  set M : V → Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) (PadicAlgCl l) :=
    fun v ↦ (h v).val.map ιQ
  set Mi : V → Matrix (Fin (latticeRank E n)) (Fin (latticeRank E n)) (PadicAlgCl l) :=
    fun v ↦ (h v)⁻¹.val.map ιQ
  have hM (v : V) : M v * Mi v = 1 := by
    simp only [M, Mi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hMi (v : V) : Mi v * M v = 1 := by
    simp only [M, Mi, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  -- the values of `γ'⁻¹`
  have hinv (z : ↥(pullback f f)) :
      (γ' z)⁻¹.val.map (padicIntToPadicAlgCl l) =
        Mi ((pullback.snd f f).base z) *
          (restrictScalarsMatrix (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).map ιQ *
            M ((pullback.fst f f).base z) := by
    let φ : GL (Fin (latticeRank E n)) ℤ_[l] →* GL (Fin (latticeRank E n)) ℚ_[l] :=
      Units.map (algebraMap ℤ_[l] ℚ_[l]).mapMatrix.toMonoidHom
    have hφ : φ (γ' z) = (h ((pullback.fst f f).base z))⁻¹ * restrictScalarsGL E n (γ z) *
        h ((pullback.snd f f).base z) :=
      Units.ext (by simpa [φ, coe_restrictScalarsGL] using hrel z)
    have hφ' : φ (γ' z)⁻¹ = (h ((pullback.snd f f).base z))⁻¹ *
        restrictScalarsGL E n (γ z)⁻¹ * h ((pullback.fst f f).base z) := by
      rw [map_inv, hφ, map_inv, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    have := congrArg (fun A : GL (Fin (latticeRank E n)) ℚ_[l] ↦ A.val.map ιQ) hφ'
    simp only [Units.val_mul, Matrix.map_mul, coe_restrictScalarsGL] at this
    exact this
  set Γ₁ := transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition
  set Γ₂ := integralCocycleInvMatrix l hγ'
  set A := lfMatrixOfLocallyConstant (fun v ↦ Mi v * latticeP E n)
    (hh.comp fun g ↦ g⁻¹.val.map ιQ * latticeP E n)
  set B := lfMatrixOfLocallyConstant (fun v ↦ latticeQ E n * M v)
    (hh.comp fun g ↦ latticeQ E n * g.val.map ιQ)
  have hA : Γ₂ * A.map (locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      A.map (locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * Γ₁ := by
    refine matrix_ext_locallyFiniteFunctionsEval fun z ↦ ?_
    rw [Matrix.map_mul, Matrix.map_mul, ← hγ.inv_map z]
    change (Γ₂.map (locallyFiniteFunctionsEval z)) * (Mi ((pullback.fst f f).base z) *
      latticeP E n) = (Mi ((pullback.snd f f).base z) * latticeP E n) * _
    rw [integralCocycleInvMatrix_map_eval, hinv, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (M _), hM, Matrix.one_mul, restrictScalarsMatrix_mul_latticeP,
      Matrix.mul_assoc]
  have hB : Γ₁ * B.map (locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      B.map (locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * Γ₂ := by
    refine matrix_ext_locallyFiniteFunctionsEval fun z ↦ ?_
    rw [Matrix.map_mul, Matrix.map_mul, ← hγ.inv_map z]
    change _ * (latticeQ E n * M ((pullback.fst f f).base z)) =
      (latticeQ E n * M ((pullback.snd f f).base z)) * (Γ₂.map (locallyFiniteFunctionsEval z))
    rw [integralCocycleInvMatrix_map_eval, hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (M _),
      ← Matrix.mul_assoc (M _), hM, Matrix.one_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc (latticeQ E n), latticeQ_mul_restrictScalarsMatrix]
  have hBA : B * A = 1 := by
    refine matrix_ext_locallyFiniteFunctionsEval fun v ↦ ?_
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change (latticeQ E n * M v) * (Mi v * latticeP E n) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M v), hM, Matrix.one_mul, latticeQ_mul_latticeP]
  exact ⟨⟨descentSheafMap f Γ₁ Γ₂ A hA, descentSheafMap f Γ₂ Γ₁ B hB,
    descentSheafMap_comp_descentSheafMap f Γ₁ Γ₂ A hA hB hBA⟩⟩

/-- **Lisse direct images of lisse sheaves with a lattice.** Let `K` be a field of characteristic
`≠ ℓ`, `Y` affine and locally of finite type over `K`, `g : T ⟶ Y` smooth and proper, and `F` a
lisse `ℓ`-adic sheaf on `T`, trivialised on an affine pro-étale cover `f₀ : V ⟶ T` with transition
cocycle `γ` with values in `GL_n(E)`, together with a lattice: a twisted section `σ` of `γ`
acting on the lattices of `Eⁿ`. Then every `Hᵏ(Rg_* F[0])` is lisse.

In the coordinates of a basis of `E`, the lattice turns `γ` into an integral cocycle `γ'`
(`AlgebraicGeometry.exists_isIntegralCocycle_of_isTwistedSection`), whose étale tower of twisted
sections is an `ℓ`-adic tower of finite locally constant sheaves with limit `M`; the lattice case
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice`) applies to
`ℚ̄_ℓ ⊗ M`, the descent of `γ'⁻¹`
(`nonempty_iso_descentSheaf_integralCocycleLattice`), and `F` is a retract of `ℚ̄_ℓ ⊗ M`
(`nonempty_retract_descentSheaf_integralCocycleInvMatrix`). -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_isTwistedSection
    {K : Type u} [Field K] (hK : ringChar K ≠ l) {T Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aY] [IsAffine Y] (g : T ⟶ Y) [Smooth g] [IsProper g]
    {F : AdicSheaf l T} {V : Scheme.{u}} [IsAffine V] (f₀ : V ⟶ T) [WeaklyEtale f₀]
    [Surjective f₀] [QuasiCompact f₀] {n : ℕ}
    (ε : (f₀)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V)
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E]
    (γ : ↥(pullback f₀ f₀) → GL (Fin n) E)
    (hγ : ∀ z, ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
      (algebraMap E (PadicAlgCl l)) = (transitionMatrix ε (pullback.snd f₀ f₀)
        (pullback.fst f₀ f₀) pullback.condition.symm).map (locallyFiniteFunctionsEval z))
    (σ : ↥(pullback f₀ (𝟙 T)) → CompactOpenLattice E n)
    (hσ : IsTwistedSection f₀ (fun z L ↦ γ z • L) (𝟙 T) σ) (k : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ k).obj
      ((g)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated g
  have hγ' : IsTransitionValues ε γ := hγ
  obtain ⟨h, γ', hh, hγi, hrel⟩ := exists_isIntegralCocycle_of_isTwistedSection γ
    hγ'.continuous_apply hγ'.continuous_inv_apply hγ'.diagonal hγ'.cocycle σ hσ
  have := hasInvertibleExponent_towerIdeal.{u} l hK
  have := isFiniteLocallyConstantSheaf_levelTwistedModuleSheaf hγi
  have hlat := isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice aY g
    (integralCocycleTower γ') (integralCocycleTowerAdicTowerStructure hγi) (towerIdeal.{u} l)
    (levelTwistedModuleSheaf f₀ γ') (fun k ↦ integralCocycleTowerObjIso k) (Iso.refl _) k
  obtain ⟨e₁⟩ := nonempty_iso_descentSheaf ε
  obtain ⟨e₂⟩ := nonempty_iso_descentSheaf_integralCocycleLattice (l := l) hγi
  obtain ⟨r⟩ := nonempty_retract_descentSheaf_integralCocycleInvMatrix f₀ ε hγ' hh hγi hrel
  let r' : Retract F ((adicSheafExtendScalars T l).obj (integralCocycleLattice l hγi)) :=
    ⟨e₁.hom ≫ r.i ≫ e₂.inv, e₂.hom ≫ r.r ≫ e₁.inv, by simp⟩
  exact hlat.of_retract (r'.map (DerivedCategory.singleFunctor _ 0 ⋙
    (g)_*ᵃ[l].rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ k))

end AlgebraicGeometry.ProEtale
