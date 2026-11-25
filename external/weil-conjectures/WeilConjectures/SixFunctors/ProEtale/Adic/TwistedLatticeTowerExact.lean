/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTowerSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeFiniteLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeFrame
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.Abelian.AdicTowerStructure
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The tower of an integral cocycle is an `ℓ`-adic tower

Let `f : V ⟶ Y` be a single-morphism pro-étale cover and `γ` a continuous integral cocycle on
`V ×_Y V` (`AlgebraicGeometry.IsIntegralCocycle`). The étale tower of twisted sections of the
reductions of `γ` (`AlgebraicGeometry.integralCocycleTower`) is an `ℓ`-adic tower
(`AlgebraicGeometry.integralCocycleTowerAdicTowerStructure`): the sequences
`0 → Gₙ --ℓᵐ--> Gₙ₊ₘ → Gₘ → 0` are exact on sections except for the surjectivity on the right,
which holds pro-étale locally, over `V`, where twisted sections are locally constant functions
(`AlgebraicGeometry.frameExt`), and hence étale locally, the comparison pullback being faithful and
identifying the étale tower with the pro-étale one. Its terms are finite locally constant sheaves
of `ℤ_ℓ ⧸ ℓᵏ`-modules (`AlgebraicGeometry.isFiniteLocallyConstantSheaf_levelTwistedModuleSheaf`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Matrix

namespace CategoryTheory

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Type*} [Ring R]

/-- A short complex of sheaves of modules which is exact on sections is exact. -/
lemma Sheaf.exact_of_sectionwise [HasSheafify J (ModuleCat.{w} R)]
    (S : ShortComplex (Sheaf J (ModuleCat.{w} R)))
    (h : ∀ U : Cᵒᵖ, (S.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj U)).Exact) : S.Exact := by
  let T := S.map (sheafToPresheaf J (ModuleCat.{w} R))
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    exact h
  have hT' := hT.map (presheafToSheaf J (ModuleCat.{w} R))
  exact ShortComplex.exact_of_iso (ShortComplex.mapNatIso S (sheafificationNatIso J _)).symm hT'

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

section Sections

variable {Y V : Scheme.{u}} {f : V ⟶ Y} {Λ : Type (u + 1)} [CommRing Λ]
  {M₁ M₂ M₃ : Type (u + 1)} [AddCommGroup M₁] [Module Λ M₁] [AddCommGroup M₂] [Module Λ M₂]
  [AddCommGroup M₃] [Module Λ M₃] {c₁ : ↥(pullback f f) → M₁ ≃ₗ[Λ] M₁}
  {c₂ : ↥(pullback f f) → M₂ ≃ₗ[Λ] M₂} {c₃ : ↥(pullback f f) → M₃ ≃ₗ[Λ] M₃}
  {φ : M₁ →ₗ[Λ] M₂} (hφ : ∀ z m, φ (c₁ z m) = c₂ z (φ m))
  {ψ : M₂ →ₗ[Λ] M₃} (hψ : ∀ z m, ψ (c₂ z m) = c₃ z (ψ m))

lemma twistedSubmoduleMap_injective (hinj : Function.Injective φ) {T : Scheme.{u}}
    (π : T ⟶ Y) : Function.Injective (twistedSubmoduleMap φ hφ π) := fun _ _ h ↦
  Subtype.ext (funext fun x ↦ hinj (congrFun (congrArg Subtype.val h) x))

/-- **Exactness of twisted sections at the middle**, for `0 → M₁ → M₂ → M₃` exact. -/
lemma exists_twistedSubmoduleMap_eq_of_exact (hinj : Function.Injective φ)
    (hex : ∀ m, ψ m = 0 → ∃ m', φ m' = m) {T : Scheme.{u}} (π : T ⟶ Y)
    (σ : twistedSubmodule f c₂ π) (hσ : twistedSubmoduleMap ψ hψ π σ = 0) :
    ∃ τ, twistedSubmoduleMap φ hφ π τ = σ := by
  classical
  let g : M₂ → M₁ := fun m ↦ if h : ψ m = 0 then (hex m h).choose else 0
  have hg (x : ↥(pullback f π)) : φ (g (σ.1 x)) = σ.1 x := by
    have h0 : ψ (σ.1 x) = 0 := congrFun (congrArg Subtype.val hσ) x
    simp only [g, dite_eq_left h0]
    exact (hex _ h0).choose_spec
  have hσ' := (mem_twistedSubmodule f c₂).1 σ.2
  refine ⟨⟨g ∘ σ.1, hσ'.1.comp g, fun w ↦ hinj ?_⟩, Subtype.ext (funext hg)⟩
  simp only [Function.comp_apply]
  rw [hφ, hg, hg]
  exact hσ'.2 w

variable [WeaklyEtale f] [Surjective f] [QuasiCompact f]

/-- **Twisted sections lift pro-étale locally along a surjection**: over the pro-étale cover
`V ×_Y W ⟶ W`, which factors through `V`, twisted sections are locally constant functions. -/
lemma isLocallySurjective_proEtTwistedModuleSheafMap
    (hc₂ : IsDescentCocycle f (fun z ↦ c₂ z)) (hsurj : Function.Surjective ψ) :
    Sheaf.IsLocallySurjective (proEtTwistedModuleSheafMap ψ hψ) := by
  refine ⟨fun {W} s ↦ ?_⟩
  let p := pullback.snd f W.hom
  let W' : Y.ProEt := Scheme.ProEt.mk (p ≫ W.hom)
  let q : W' ⟶ W := MorphismProperty.Over.homMk p rfl trivial
  have hcov : Sieve.generate (Presieve.singleton q) ∈ Scheme.ProEt.topology Y W := by
    rw [Scheme.ProEt.mem_topology_iff]
    refine ⟨Presieve.singleton q, ?_, Sieve.le_generate _⟩
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
    have : Surjective p := inferInstanceAs (Surjective (pullback.snd f W.hom))
    have : QuasiCompact p := inferInstanceAs (QuasiCompact (pullback.snd f W.hom))
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (f := p) (P := @WeaklyEtale)
      (inferInstanceAs (WeaklyEtale p))
  refine (Scheme.ProEt.topology Y).superset_covering ?_ hcov
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  have ha : pullback.fst f W.hom ≫ f = W'.hom := pullback.condition
  set s' := (proEtTwistedModuleSheaf f c₃).obj.map q.op s
  have hs' := (mem_twistedSubmodule f c₃).1 s'.2
  let τ := Function.surjInv hsurj ∘ frameEval f (pullback.fst f W.hom) ha s'.1
  have hτ : IsLocallyConstant τ := (hs'.1.comp_continuous
    (frameSection f (pullback.fst f W.hom) ha).base.hom.continuous).comp _
  refine ⟨⟨frameExt f (pullback.fst f W.hom) ha (fun z ↦ c₂ z) τ,
    (mem_twistedSubmodule f c₂).2 (isTwistedSection_frameExt _ _ hc₂ hτ)⟩, Subtype.ext ?_⟩
  change ψ ∘ frameExt f (pullback.fst f W.hom) ha (fun z ↦ c₂ z) τ = s'.1
  have : ψ ∘ frameExt f (pullback.fst f W.hom) ha (fun z ↦ c₂ z) τ =
      frameExt f (pullback.fst f W.hom) ha (fun z ↦ c₃ z)
        (frameEval f (pullback.fst f W.hom) ha s'.1) := by
    funext x
    simp only [frameExt, Function.comp_apply, hψ, τ, Function.surjInv_eq hsurj]
  rw [this, frameExt_frameEval _ _ hs']

end Sections

section Tower

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ}
  {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

lemma towerMul_injective (n m : ℕ) : Function.Injective (towerMul.{u} l n m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [towerMul_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨b, hb⟩ := hx
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  have hl : (l : ULift.{u + 1} ℤ_[l]) ^ m ≠ 0 := by
    refine pow_ne_zero m fun h ↦ (Fact.out : l.Prime).ne_zero ?_
    have := congrArg ULift.down h
    exact_mod_cast this
  refine ⟨b, mul_left_cancel₀ hl ?_⟩
  rw [← hb]
  ring


lemma levelMul_injective (n m : ℕ) : Function.Injective (levelMul.{u} l N n m) := fun _ _ h ↦
  funext fun i ↦ towerMul_injective n m (congrFun h i)

/-- The kernel of the reduction `(ℤ_ℓ ⧸ ℓⁿ⁺ᵐ)ᴺ → (ℤ_ℓ ⧸ ℓᵐ)ᴺ` is `ℓᵐ (ℤ_ℓ ⧸ ℓⁿ⁺ᵐ)ᴺ`. -/
lemma exists_levelMul_eq (n m : ℕ) (v : LevelModule.{u} l N (n + m))
    (hv : levelReduce.{u} l N (Nat.le_add_left m n) v = 0) : ∃ w, levelMul.{u} l N n m w = v := by
  have (i : Fin N) : ∃ x, towerMul.{u} l n m x = v i := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v i)
    have h0 := congrFun hv i
    rw [levelReduce_apply, ← ha] at h0
    have h1 : Ideal.Quotient.mk (towerIdeal.{u} l m) a = 0 := h0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, rfl⟩ := h1
    refine ⟨Ideal.Quotient.mk _ b, ?_⟩
    rw [towerMul_mk, ← ha, mul_comm]
  choose w hw using this
  exact ⟨w, funext hw⟩

lemma levelReduce_levelMul (n m : ℕ) (v : LevelModule.{u} l N n) :
    levelReduce.{u} l N (Nat.le_add_left m n) (levelMul.{u} l N n m v) = 0 := by
  funext i
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v i)
  rw [levelReduce_apply, levelMul_apply, ← ha, towerMul_mk]
  refine (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton'.2 ⟨a, mul_comm _ _⟩)

lemma levelMul_levelReduce (n m : ℕ) (v : LevelModule.{u} l N (n + m)) :
    levelMul.{u} l N n m (levelReduce.{u} l N (Nat.le_add_right n m) v) = (l ^ m : ℕ) • v := by
  funext i
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v i)
  rw [levelMul_apply, levelReduce_apply, ← ha, Pi.smul_apply, ← ha]
  change Ideal.Quotient.mk _ ((l : ULift.{u + 1} ℤ_[l]) ^ m * a) = _
  rw [nsmul_eq_mul, map_mul, Nat.cast_pow, map_pow, map_natCast]

lemma levelReduce_surjective {k k' : ℕ} (h : k' ≤ k) :
    Function.Surjective (levelReduce.{u} l N h) := fun v ↦ by
  have (i : Fin N) : ∃ x, towerFactor.{u} l h x = v i := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v i)
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  choose w hw using this
  exact ⟨w, funext hw⟩

variable [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f]

/-- The étale reduction maps of the tower of an integral cocycle are epimorphisms: so are the
pro-étale ones, being pro-étale locally surjective, and the comparison pullback is faithful. -/
lemma epi_integralCocycleTower_map (hγ : IsIntegralCocycle f γ) {k k' : ℕ} (h : k' ≤ k) :
    Epi ((integralCocycleTower γ).map (homOfLE h).op) := by
  have : Epi ((proEtIntegralCocycleTower γ).map (homOfLE h).op) := by
    have : Sheaf.IsLocallySurjective ((proEtIntegralCocycleTower γ).map (homOfLE h).op) :=
      isLocallySurjective_proEtTwistedModuleSheafMap
      (levelReduce_levelCocycleInt γ (leOfHom (homOfLE h)))
      (hγ.isDescentCocycle_int k) (levelReduce_surjective _)
    exact Sheaf.epi_of_isLocallySurjective _
  set e := comparisonUpperStarIntegralCocycleTowerIso hγ
  have hnat := e.hom.naturality (homOfLE h).op
  have : Epi ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift ℤ_[l])) Y).map
      ((integralCocycleTower γ).map (homOfLE h).op)) := by
    have h₁ : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift ℤ_[l])) Y).map
        ((integralCocycleTower γ).map (homOfLE h).op) =
        e.hom.app (op k) ≫ (proEtIntegralCocycleTower γ).map (homOfLE h).op ≫
          e.inv.app (op k') := by
      rw [← reassoc_of% hnat]
      simp
    rw [h₁]
    infer_instance
  exact (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift ℤ_[l])) Y).epi_of_epi_map this

/-- **The tower of an integral cocycle is an `ℓ`-adic tower.** -/
noncomputable def integralCocycleTowerAdicTowerStructure (hγ : IsIntegralCocycle f γ) :
    AdicTowerStructure (integralCocycleTower γ) l where
  ι n m := twistedModuleSheafMap (levelMul.{u} l N n m) (levelMul_levelCocycleInt γ n m)
  map_ι n m := by
    ext U σ
    refine Subtype.ext (funext fun x ↦ ?_)
    exact levelMul_levelReduce n m _
  ι_map n m := by
    ext U σ
    refine Subtype.ext (funext fun x ↦ ?_)
    exact levelReduce_levelMul n m _
  shortExact n m := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ (epi_integralCocycleTower_map hγ (Nat.le_add_left m n))
    · refine Sheaf.exact_of_sectionwise _ fun U ↦ ?_
      rw [ShortComplex.moduleCat_exact_iff]
      intro σ hσ
      exact exists_twistedSubmoduleMap_eq_of_exact (levelMul_levelCocycleInt γ n m)
        (levelReduce_levelCocycleInt γ (Nat.le_add_left m n)) (levelMul_injective n m)
        (exists_levelMul_eq n m) U.unop.hom σ hσ
    · exact Sheaf.mono_of_injective _ fun U ↦
        twistedSubmoduleMap_injective (levelMul_levelCocycleInt γ n m) (levelMul_injective n m) _

end Tower

section Level

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ}
  {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

variable (f γ) in
/-- The étale sheaf of `ℤ_ℓ ⧸ ℓᵏ`-modules of twisted sections of the reduction of `γ`. -/
noncomputable abbrev levelTwistedModuleSheaf (k : ℕ) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k)) :=
  twistedModuleSheaf f (levelCocycle γ k)

/-- The étale tower of an integral cocycle is the restriction of scalars of the sheaves of
`ℤ_ℓ ⧸ ℓᵏ`-modules of twisted sections. -/
noncomputable def integralCocycleTowerObjIso (k : ℕ) :
    (integralCocycleTower γ).obj (op k) ≅
      (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk (towerIdeal.{u} l k))).obj
        (levelTwistedModuleSheaf f γ k) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
      (X₁ := ((integralCocycleTower γ).obj (op k)).obj.obj U)
      (X₂ := ((Sheaf.restrictScalars Y.smallEtaleTopology
        (Ideal.Quotient.mk (towerIdeal.{u} l k))).obj
        (levelTwistedModuleSheaf f γ k)).obj.obj U)
      { toFun σ := ⟨σ.1, σ.2⟩
        invFun σ := ⟨σ.1, σ.2⟩
        map_add' _ _ := rfl
        map_smul' a σ := Subtype.ext (funext fun x ↦ funext fun i ↦ Algebra.smul_def a (σ.1 x i))
        left_inv _ := rfl
        right_inv _ := rfl })
      fun _ ↦ rfl)

variable [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparatedSpace Y]

/-- The sheaves of twisted sections of the reductions of an integral cocycle are finite locally
constant. -/
lemma isFiniteLocallyConstantSheaf_levelTwistedModuleSheaf (hγ : IsIntegralCocycle f γ)
    (k : ℕ) : IsFiniteLocallyConstantSheaf (levelTwistedModuleSheaf f γ k) :=
  isFiniteLocallyConstantSheaf_twistedModuleSheaf f _ (hγ.isDescentCocycle k)

end Level

end AlgebraicGeometry
