/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTower

/-!
# The towers of sheaves of twisted sections of an integral cocycle

For a continuous integral cocycle `γ : V ×_Y V → GL_N(ℤ_ℓ)`
(`AlgebraicGeometry.IsIntegralCocycle`), the étale sheaves of twisted sections of its reductions
modulo `ℓᵏ` form a tower under reduction (`AlgebraicGeometry.integralCocycleTower`), and so do
the pro-étale ones (`AlgebraicGeometry.proEtIntegralCocycleTower`). The comparison pullback
identifies the two towers (`AlgebraicGeometry.comparisonUpperStarIntegralCocycleTowerIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Matrix

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ}

section LevelMaps

variable (l) in
/-- `towerReduce x * y` is the action of `x` through `ULift ℤ_ℓ`. -/
lemma towerReduce_mul (k : ℕ) (x : ℤ_[l]) (y : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) :
    towerReduce.{u} l k x * y = (ULift.up x : ULift.{u + 1} ℤ_[l]) • y := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

/-- The action of a reduced matrix through `ULift ℤ_ℓ`. -/
lemma levelCocycle_apply_eq_sum (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]) (k : ℕ)
    (z : ↥(pullback f f)) (v : LevelModule l N k) (i : Fin N) :
    levelCocycle γ k z v i =
      ∑ j, (ULift.up ((γ z : Matrix (Fin N) (Fin N) ℤ_[l]) i j) : ULift.{u + 1} ℤ_[l]) • v j := by
  rw [levelCocycle_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, towerReduce_mul]

/-- The reduction maps are `ULift ℤ_ℓ`-linear. -/
lemma towerFactor_smul {k k' : ℕ} (h : k' ≤ k) (a : ULift.{u + 1} ℤ_[l])
    (x : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) :
    towerFactor.{u} l h (a • x) = a • towerFactor.{u} l h x := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable (l N) in
/-- The reduction `(ℤ_ℓ ⧸ ℓᵏ)ᴺ → (ℤ_ℓ ⧸ ℓᵏ')ᴺ` for `k' ≤ k`. -/
noncomputable def levelReduce {k k' : ℕ} (h : k' ≤ k) :
    LevelModule l N k →ₗ[ULift.{u + 1} ℤ_[l]] LevelModule l N k' where
  toFun v i := towerFactor.{u} l h (v i)
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' a v := funext fun i ↦ towerFactor_smul h a (v i)

lemma levelReduce_apply {k k' : ℕ} (h : k' ≤ k) (v : LevelModule l N k) (i : Fin N) :
    levelReduce l N h v i = towerFactor.{u} l h (v i) :=
  rfl

lemma levelReduce_levelCocycleInt (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]) {k k' : ℕ}
    (h : k' ≤ k) (z : ↥(pullback f f)) (v : LevelModule l N k) :
    levelReduce l N h (levelCocycleInt γ k z v) =
      levelCocycleInt γ k' z (levelReduce l N h v) := by
  funext i
  rw [levelCocycleInt_apply, levelCocycleInt_apply, levelReduce_apply,
    levelCocycle_apply_eq_sum, levelCocycle_apply_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ towerFactor_smul h _ _

lemma levelReduce_id {k : ℕ} (v : LevelModule l N k) : levelReduce l N (le_refl k) v = v := by
  funext i
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (v i)
  rw [levelReduce_apply, ← hx, towerFactor, Ideal.Quotient.factor_mk]

lemma levelReduce_comp {k k' k'' : ℕ} (h : k' ≤ k) (h' : k'' ≤ k') (v : LevelModule l N k) :
    levelReduce l N h' (levelReduce l N h v) = levelReduce l N (h'.trans h) v := by
  funext i
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (v i)
  rw [levelReduce_apply, levelReduce_apply, levelReduce_apply, ← hx, towerFactor, towerFactor,
    towerFactor, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

variable (l) in
/-- The multiplication by `ℓᵐ`, `ℤ_ℓ ⧸ ℓⁿ → ℤ_ℓ ⧸ ℓⁿ⁺ᵐ`. -/
noncomputable def towerMul (n m : ℕ) :
    ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l n →ₗ[ULift.{u + 1} ℤ_[l]]
      ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l (n + m) :=
  Submodule.liftQ (towerIdeal.{u} l n)
    ((Submodule.mkQ (towerIdeal.{u} l (n + m))).comp
      (LinearMap.mulLeft (ULift.{u + 1} ℤ_[l]) ((l : ULift.{u + 1} ℤ_[l]) ^ m))) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
    ring)

lemma towerMul_mk (n m : ℕ) (a : ULift.{u + 1} ℤ_[l]) :
    towerMul.{u} l n m (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ((l : ULift.{u + 1} ℤ_[l]) ^ m * a) :=
  rfl

variable (l N) in
/-- The multiplication by `ℓᵐ`, `(ℤ_ℓ ⧸ ℓⁿ)ᴺ → (ℤ_ℓ ⧸ ℓⁿ⁺ᵐ)ᴺ`. -/
noncomputable def levelMul (n m : ℕ) :
    LevelModule l N n →ₗ[ULift.{u + 1} ℤ_[l]] LevelModule l N (n + m) :=
  LinearMap.pi fun i ↦ (towerMul.{u} l n m).comp (LinearMap.proj i)

lemma levelMul_apply (n m : ℕ) (v : LevelModule l N n) (i : Fin N) :
    levelMul l N n m v i = towerMul.{u} l n m (v i) :=
  rfl

lemma levelMul_levelCocycleInt (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]) (n m : ℕ)
    (z : ↥(pullback f f)) (v : LevelModule l N n) :
    levelMul l N n m (levelCocycleInt γ n z v) =
      levelCocycleInt γ (n + m) z (levelMul l N n m v) := by
  funext i
  rw [levelCocycleInt_apply, levelCocycleInt_apply, levelMul_apply,
    levelCocycle_apply_eq_sum, levelCocycle_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul]
  rfl

end LevelMaps

section Tower

variable (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l])

/-- **The étale tower of an integral cocycle**: the étale sheaves of twisted sections of the
reductions of `γ` modulo `ℓᵏ`, as sheaves of `ℤ_ℓ`-modules, under reduction. -/
noncomputable def integralCocycleTower :
    ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) where
  obj k := twistedModuleSheaf f (levelCocycleInt γ k.unop)
  map h := twistedModuleSheafMap (levelReduce l N (leOfHom h.unop))
    (levelReduce_levelCocycleInt γ (leOfHom h.unop))
  map_id _ := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext
    (LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ levelReduce_id _))))
  map_comp _ _ := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext
    (LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ (levelReduce_comp _ _ _).symm))))

/-- **The pro-étale tower of an integral cocycle.** -/
noncomputable def proEtIntegralCocycleTower :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) where
  obj k := proEtTwistedModuleSheaf f (levelCocycleInt γ k.unop)
  map h := proEtTwistedModuleSheafMap (levelReduce l N (leOfHom h.unop))
    (levelReduce_levelCocycleInt γ (leOfHom h.unop))
  map_id _ := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext
    (LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ levelReduce_id _))))
  map_comp _ _ := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext
    (LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ (levelReduce_comp _ _ _).symm))))

variable {γ}

/-- **The comparison pullback of the étale tower is the pro-étale tower.** -/
noncomputable def comparisonUpperStarIntegralCocycleTowerIso [QuasiCompact f] [QuasiSeparated f]
    (hγ : IsIntegralCocycle f γ) :
    integralCocycleTower γ ⋙ ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift ℤ_[l])) Y ≅
      proEtIntegralCocycleTower γ :=
  NatIso.ofComponents (fun k ↦
    @asIso _ _ _ _ (comparisonUpperStarTwistedModuleSheafHom f (levelCocycleInt γ k.unop))
      (isIso_comparisonUpperStarTwistedModuleSheafHom f (levelCocycleInt γ k.unop)
        (hγ.isDescentCocycle_int k.unop)))
    fun _ ↦ comparisonUpperStar_map_twistedModuleSheafMap_comp _ _

end Tower

end AlgebraicGeometry
