/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeFrame
public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficients

/-!
# The `ℓ`-adic tower of an integral descent cocycle

Let `f : V ⟶ Y` be a morphism and `γ : V ×_Y V → GL_N(ℤ_ℓ)` a continuous cocycle
(`AlgebraicGeometry.IsIntegralCocycle`). Reducing `γ` modulo `ℓᵏ` gives linear descent cocycles
on the constant sheaves `(ℤ/ℓᵏ)ᴺ_V` (`AlgebraicGeometry.levelCocycle`), whose étale sheaves of
twisted sections form a tower `k ↦ Gₖ` of étale sheaves of `ℤ_ℓ`-modules under reduction
(`AlgebraicGeometry.integralCocycleTower`), and similarly on the pro-étale site
(`AlgebraicGeometry.proEtIntegralCocycleTower`). The comparison pullback identifies them
(`AlgebraicGeometry.comparisonUpperStarIntegralCocycleTowerIso`).

The coefficient rings are the quotients `ℤ_ℓ ⧸ ℓᵏ` of `ULift ℤ_ℓ`
(`AlgebraicGeometry.towerIdeal`), as in
`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Matrix

namespace AlgebraicGeometry

section Coefficients

variable (l : ℕ) [Fact l.Prime]

/-- The ideal `ℓᵏ` of `ULift ℤ_ℓ`. -/
noncomputable abbrev towerIdeal (k : ℕ) : Ideal (ULift.{u + 1} ℤ_[l]) :=
  Ideal.span {(l : ULift.{u + 1} ℤ_[l]) ^ k}

/-- The quotients `ℤ_ℓ ⧸ ℓᵏ` are finite. -/
instance (k : ℕ) : Finite (ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) :=
  Finite.of_equiv _ (ULift.padicIntQuotientSpanPowAddEquiv.{u + 1} l k).toEquiv.symm

/-- The reduction `ℤ_ℓ → ℤ_ℓ ⧸ ℓᵏ`. -/
noncomputable def towerReduce (k : ℕ) : ℤ_[l] →+* ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k :=
  (Ideal.Quotient.mk _).comp ULift.ringEquiv.symm.toRingHom

lemma padicIntQuotientSpanPowAddEquiv_towerReduce (k : ℕ) (x : ℤ_[l]) :
    ULift.padicIntQuotientSpanPowAddEquiv.{u + 1} l k (towerReduce.{u} l k x) =
      PadicInt.toZModPow k x :=
  rfl

/-- The reduction `ℤ_ℓ → ℤ_ℓ ⧸ ℓᵏ` is locally constant. -/
lemma isLocallyConstant_towerReduce (k : ℕ) : IsLocallyConstant (towerReduce.{u} l k) := by
  have : (towerReduce.{u} l k : ℤ_[l] → _) =
      (ULift.padicIntQuotientSpanPowAddEquiv.{u + 1} l k).symm ∘ PadicInt.toZModPow k := by
    funext x
    rw [Function.comp_apply, ← padicIntQuotientSpanPowAddEquiv_towerReduce,
      AddEquiv.symm_apply_apply]
  rw [this]
  exact (PadicInt.isLocallyConstant_toZModPow k).comp _

/-- `ℓᵏ` kills `ℤ_ℓ ⧸ ℓᵏ`. -/
lemma pow_smul_eq_zero_of_towerIdeal (k : ℕ) {M : Type*} [AddCommGroup M]
    [Module (ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) M] (x : M) :
    ((l : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) ^ k) • x = 0 := by
  have : (l : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) ^ k = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (towerIdeal.{u} l k)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [this, zero_smul]

/-- For `k' ≤ k`, the ideal `ℓᵏ` is contained in `ℓᵏ'`. -/
lemma towerIdeal_le {k k' : ℕ} (h : k' ≤ k) : towerIdeal.{u} l k ≤ towerIdeal.{u} l k' :=
  Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.mem_span_singleton.2
    (pow_dvd_pow _ h)))

/-- The reduction map `ℤ_ℓ ⧸ ℓᵏ → ℤ_ℓ ⧸ ℓᵏ'` for `k' ≤ k`. -/
noncomputable def towerFactor {k k' : ℕ} (h : k' ≤ k) :
    ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k →+* ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k' :=
  Ideal.Quotient.factor (towerIdeal_le l h)

lemma towerFactor_towerReduce {k k' : ℕ} (h : k' ≤ k) (x : ℤ_[l]) :
    towerFactor l h (towerReduce l k x) = towerReduce.{u} l k' x :=
  rfl

end Coefficients

section Matrix

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The automorphism `v ↦ A v` of `Rᴺ` of an invertible matrix `A`. -/
def glLinearEquiv (A : GL (Fin N) R) : (Fin N → R) ≃ₗ[R] (Fin N → R) where
  toFun v := (A : Matrix (Fin N) (Fin N) R) *ᵥ v
  invFun v := ((A⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ v
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

lemma glLinearEquiv_apply (A : GL (Fin N) R) (v : Fin N → R) :
    glLinearEquiv A v = (A : Matrix (Fin N) (Fin N) R) *ᵥ v :=
  rfl

lemma glLinearEquiv_one : glLinearEquiv (1 : GL (Fin N) R) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun v ↦ Matrix.one_mulVec v

lemma glLinearEquiv_mul_apply (A B : GL (Fin N) R) (v : Fin N → R) :
    glLinearEquiv (A * B) v = glLinearEquiv A (glLinearEquiv B v) :=
  (Matrix.mulVec_mulVec v _ _).symm

end Matrix

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ}

variable (f) in
/-- A *continuous integral cocycle* on `V ×_Y V`: a function `γ : V ×_Y V → GL_N(ℤ_ℓ)` with
continuous entries (and inverse entries), trivial on the diagonal and with
`γ₁₃ = γ₁₂ γ₂₃` on `V ×_Y V ×_Y V`. -/
structure IsIntegralCocycle (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]) : Prop where
  continuous (i j : Fin N) : Continuous fun z ↦ (γ z : Matrix (Fin N) (Fin N) ℤ_[l]) i j
  continuous_inv (i j : Fin N) :
    Continuous fun z ↦ ((γ z)⁻¹ : GL (Fin N) ℤ_[l]) i j
  diagonal (v : V) : γ ((pullback.diagonal f).base v) = 1
  cocycle (w : ↥(tripleProduct f)) : γ ((tripleProj₁₃ f).base w) =
    γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
      γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w)

section Level

variable (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l])

variable (l) in
/-- The module `(ℤ_ℓ ⧸ ℓᵏ)ᴺ`. -/
abbrev LevelModule (N k : ℕ) : Type (u + 1) := Fin N → ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k

/-- The reduction of `γ` modulo `ℓᵏ`, a cocycle of `ℤ_ℓ ⧸ ℓᵏ`-linear automorphisms of
`(ℤ_ℓ ⧸ ℓᵏ)ᴺ`. -/
noncomputable def levelCocycle (k : ℕ) (z : ↥(pullback f f)) :
    LevelModule l N k ≃ₗ[ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k] LevelModule l N k :=
  glLinearEquiv (Matrix.GeneralLinearGroup.map (towerReduce.{u} l k) (γ z))

/-- The reduction of `γ` modulo `ℓᵏ`, as a cocycle of `ℤ_ℓ`-linear automorphisms. -/
noncomputable def levelCocycleInt (k : ℕ) (z : ↥(pullback f f)) :
    LevelModule l N k ≃ₗ[ULift.{u + 1} ℤ_[l]] LevelModule l N k :=
  (levelCocycle γ k z).restrictScalars (ULift.{u + 1} ℤ_[l])

lemma levelCocycle_apply (k : ℕ) (z : ↥(pullback f f)) (v : LevelModule l N k) :
    levelCocycle γ k z v =
      ((γ z : Matrix (Fin N) (Fin N) ℤ_[l]).map (towerReduce.{u} l k)) *ᵥ v :=
  rfl

lemma levelCocycleInt_apply (k : ℕ) (z : ↥(pullback f f)) (v : LevelModule l N k) :
    levelCocycleInt γ k z v = levelCocycle γ k z v :=
  rfl

/-- A finite family of locally constant functions is locally constant. -/
lemma isLocallyConstant_pi {X ι : Type*} [TopologicalSpace X] [Finite ι] {A : ι → Type*}
    {g : X → ∀ i, A i} (hg : ∀ i, IsLocallyConstant fun x ↦ g x i) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have := Filter.eventually_all.2 fun i ↦ (IsLocallyConstant.iff_eventually_eq _).1 (hg i) x
  filter_upwards [this] with y hy
  exact funext hy

variable {γ}

/-- The reductions of a continuous integral cocycle are descent cocycles. -/
lemma IsIntegralCocycle.isDescentCocycle (hγ : IsIntegralCocycle f γ) (k : ℕ) :
    IsDescentCocycle f (fun z ↦ levelCocycle γ k z) where
  isLocallyConstant v := by
    refine isLocallyConstant_pi fun i ↦ ?_
    simp only [levelCocycle_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact (isLocallyConstant_pi fun j ↦ (isLocallyConstant_towerReduce l k).comp_continuous
      (hγ.continuous i j)).comp fun a ↦ ∑ j, a j * v j
  bijective z := (levelCocycle γ k z).bijective
  diagonal v := by
    funext w
    rw [levelCocycle, hγ.diagonal, map_one, glLinearEquiv_one]
    rfl
  cocycle w := by
    funext v
    rw [Function.comp_apply, levelCocycle, levelCocycle, levelCocycle, hγ.cocycle, map_mul,
      glLinearEquiv_mul_apply]

/-- The `ℤ_ℓ`-linear reductions of a continuous integral cocycle are descent cocycles. -/
lemma IsIntegralCocycle.isDescentCocycle_int (hγ : IsIntegralCocycle f γ) (k : ℕ) :
    IsDescentCocycle f (fun z ↦ levelCocycleInt γ k z) :=
  hγ.isDescentCocycle k

end Level

end AlgebraicGeometry
