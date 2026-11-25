/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective

/-!
# Integral identifications are linear over the `ℓ`-adic closure of `ℕ`

Let `Φ` be an additive functor on abelian sheaves on `T_proét` (typically `Γ(U, p^* Rⁱg_* -)`) and
`θ : A ≃+ Φ(𝒪_{E,T})` an additive bijection from an `ℓ`-adically separated `𝒪_E`-module `A`. Then
`θ` commutes with the multiplication by every `r ∈ 𝒪_E` which is an `ℓ`-adic limit of natural
numbers (`AlgebraicGeometry.ProEtale.map_smul_of_forall_eq_natCast_add`): `θ` commutes with natural
numbers, and the defect `θ(r a) - r θ(a)` is divisible in `A` by every power of `ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}} (E : FiniteIntermediateField l)

variable (T) in
lemma padicIntegersSheafMulOfLE_natCast (n : ℕ) :
    padicIntegersSheafMulOfLE T (le_refl E.1) (n : integers l E.1) = n • 𝟙 _ := by
  ext U f
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change (n : integers l E.1) * f.down x = n • f.down x
  exact (nsmul_eq_mul n _).symm

variable (Φ : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} ⥤ Ab.{u + 1}) [Φ.Additive]
  {A : Type*} [AddCommGroup A] [Module (integers l E.1) A]
  (θ : A ≃+ Φ.obj ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicIntegersSheaf T l E.1)))

/-- **`θ` is linear over the `ℓ`-adic closure of `ℕ`**: if `A` is `ℓ`-adically separated, then
`θ (r • a) = r θ(a)` for every `r ∈ 𝒪_E` which is congruent to a natural number modulo every
power of `ℓ`. -/
theorem map_smul_of_forall_eq_natCast_add
    (hA : ∀ a : A, (∀ k : ℕ, ∃ b : A, a = l ^ k • b) → a = 0) (r : integers l E.1)
    (hr : ∀ k : ℕ, ∃ (n : ℕ) (s : integers l E.1), r = n + (l : integers l E.1) ^ k * s)
    (a : A) :
    θ (r • a) = Φ.map (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ a) := by
  let μ (o : integers l E.1) := Φ.map (padicIntegersSheafMulOfLE T (le_refl E.1) o)
  have hμ (n k : ℕ) (s : integers l E.1) (x) :
      μ (n + (l : integers l E.1) ^ k * s) x = n • x + l ^ k • μ s x := by
    have h1 : padicIntegersSheafMulOfLE T (le_refl E.1) ((l : integers l E.1) ^ k * s) =
        (l ^ k) • padicIntegersSheafMulOfLE T (le_refl E.1) s := by
      have e : (l : integers l E.1) ^ k * s =
          integersInclusion l (le_refl E.1) ((l ^ k : ℕ) : integers l E.1) * s := by
        rw [integersInclusion_refl, Nat.cast_pow]
      rw [e, ← padicIntegersSheafMulOfLE_refl_comp, padicIntegersSheafMulOfLE_natCast,
        Linear.smul_comp, Category.id_comp]
    have h2 : μ (n + (l : integers l E.1) ^ k * s) = n • 𝟙 _ + l ^ k • μ s := by
      simp only [μ, padicIntegersSheafMulOfLE_add, Functor.map_add, h1, Functor.map_nsmul,
        padicIntegersSheafMulOfLE_natCast]
      rw [CategoryTheory.Functor.map_id]
    rw [h2]
    rfl
  have hsm (n k : ℕ) (s : integers l E.1) (b : A) :
      (n + (l : integers l E.1) ^ k * s) • b = n • b + l ^ k • (s • b) := by
    rw [add_smul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [← sub_eq_zero, ← θ.symm.map_eq_zero_iff]
  refine hA _ fun k ↦ ?_
  obtain ⟨n, s, rfl⟩ := hr k
  refine ⟨s • a - θ.symm (μ s (θ a)), θ.injective ?_⟩
  rw [θ.apply_symm_apply, map_nsmul, map_sub, θ.apply_symm_apply, hμ, hsm, map_add, map_nsmul,
    map_nsmul, smul_sub]
  abel

end AlgebraicGeometry.ProEtale

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : FiniteIntermediateField l)

/-- `ℓ` is not a unit of `𝒪_E`: its norm is `ℓ⁻¹ < 1`. -/
lemma not_isUnit_natCast_integers : ¬ IsUnit ((l : ℕ) : integers l E.1) := by
  rintro ⟨u, hu⟩
  have h2 : algebraMap (integers l E.1) (PadicAlgCl l) (l : integers l E.1) *
      algebraMap (integers l E.1) (PadicAlgCl l) (u⁻¹ : (integers l E.1)ˣ) = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hv : ‖algebraMap (integers l E.1) (PadicAlgCl l) (u⁻¹ : (integers l E.1)ˣ)‖ ≤ 1 := by
    have := ((u⁻¹ : (integers l E.1)ˣ) : integers l E.1).2
    rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm] at this
    exact this
  have hl : ‖algebraMap (integers l E.1) (PadicAlgCl l) (l : integers l E.1)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends,
      Padic.norm_p]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one, hl] at h3
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have : (l : ℝ)⁻¹ * ‖algebraMap (integers l E.1) (PadicAlgCl l)
      (u⁻¹ : (integers l E.1)ˣ)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) hv) (inv_lt_one_of_one_lt₀ hl1)
  exact this.ne h3

/-- A finite `𝒪_E`-module is `ℓ`-adically separated (Krull's intersection theorem). -/
lemma eq_zero_of_forall_eq_pow_smul {M : Type*} [AddCommGroup M] [Module (integers l E.1) M]
    [Module.Finite (integers l E.1) M] (x : M) (hx : ∀ k : ℕ, ∃ y : M, x = l ^ k • y) :
    x = 0 := by
  have hI : Ideal.span {((l : ℕ) : integers l E.1)} ≠ ⊤ := fun h ↦
    not_isUnit_natCast_integers l E (Ideal.span_singleton_eq_top.1 h)
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI
  rw [← Submodule.mem_bot (R := integers l E.1), ← h, Submodule.mem_iInf]
  intro k
  obtain ⟨y, rfl⟩ := hx k
  rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ← Nat.cast_smul_eq_nsmul (integers l E.1)]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- If `ℤ_ℓ → 𝒪_E` is surjective, every `r ∈ 𝒪_E` is congruent to a natural number modulo every
power of `ℓ`. -/
lemma exists_eq_natCast_add_of_surjective
    (hκ : Function.Surjective (integersPadicIntHom l E.1)) (r : integers l E.1) (k : ℕ) :
    ∃ (n : ℕ) (s : integers l E.1), r = n + (l : integers l E.1) ^ k * s := by
  obtain ⟨z, rfl⟩ := hκ r
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k z)
  refine ⟨z.appr k, integersPadicIntHom l E.1 w, ?_⟩
  rw [← map_natCast (integersPadicIntHom l E.1), ← map_natCast (integersPadicIntHom l E.1) l,
    ← map_pow, ← map_mul, ← map_add, mul_comm, hw, add_sub_cancel]

/-- For `E = ℚ_ℓ`, the inclusion `ℤ_ℓ → 𝒪_E` is surjective. -/
lemma surjective_integersPadicIntHom_bot :
    Function.Surjective (integersPadicIntHom l (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))) := by
  intro r
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 (r : (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))).2
  have hr := r.2
  rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm] at hr
  have hq1 : ‖q‖ ≤ 1 := by
    rw [← PadicAlgCl.norm_extends]
    exact hq ▸ hr
  refine ⟨⟨q, hq1⟩, FaithfulSMul.algebraMap_injective _ (PadicAlgCl l) ?_⟩
  rw [algebraMap_integersPadicIntHom]
  exact hq

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T Y S : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
  [QuasiSeparated g] (p : S ⟶ Y) [WeaklyEtale p] (i : ℕ) (E : FiniteIntermediateField l)
  {M : Type} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  (θ : continuousMapAddSheaf S M ⟶ (p)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))

omit [QuasiCompact g] [QuasiSeparated g] [WeaklyEtale p] in
/-- **An integral identification is `𝒪_E`-linear when `𝒪_E = ℤ_ℓ`**: if `ℤ_ℓ → 𝒪_E` is
surjective (e.g. `E = ℚ_ℓ`, `PadicAlgCl.surjective_integersPadicIntHom_bot`), `M` is a finite
`𝒪_E`-module and `θ : C(-, M) ⟶ p^* Rⁱg_* 𝒪_{E,T}` is an isomorphism, then `θ` is `𝒪_E`-linear on
sections over every quasi-compact quasi-separated `U`. -/
theorem integralLattice_map_smul_of_surjective [IsIso θ]
    (hκ : Function.Surjective (integersPadicIntHom l E.1)) [Module (integers l E.1) M]
    [Module.Finite (integers l E.1) M] [TopologicalSpace (integers l E.1)]
    [ContinuousSMul (integers l E.1) M] (U : S.ProEt) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] (r : integers l E.1) (m : C(U.left, M)) :
    θ.hom.app (op U) (ULift.up (r • m)) = (upperStarRightDerivedSections g p i U).map
      (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ.hom.app (op U) (ULift.up m)) :=
  map_smul_of_forall_eq_natCast_add E (upperStarRightDerivedSections g p i U)
    (integralLatticeSectionsEquiv g p i E θ U ((ConcreteCategory.isIso_iff_bijective _).1
      (inferInstanceAs (IsIso ((((sheafToPresheaf _ _).mapIso (asIso θ)).app (op U)).hom)))))
    (fun f hf ↦ ContinuousMap.ext fun x ↦ PadicAlgCl.eq_zero_of_forall_eq_pow_smul l E (f x)
      fun k ↦ (hf k).elim fun y hy ↦ ⟨y x, congrArg (fun h : C(U.left, M) ↦ h x) hy⟩)
    r (PadicAlgCl.exists_eq_natCast_add_of_surjective l E hκ r) m

/-- **`Rⁱg_* ℚ̄_ℓ,T` is lisse**:
`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicRightDerivedLowerStarUnit`
without the `𝒪_E`-linearity hypothesis on `θ`, which is automatic when `ℤ_ℓ → 𝒪_E` is surjective
(`AlgebraicGeometry.ProEtale.integralLattice_map_smul_of_surjective`). -/
theorem isAdicLisseSheaf_adicRightDerivedLowerStarUnit_of_surjective [Surjective p]
    [QuasiCompact p] [TopologicalSpace (integers l E.1)] [IsTopologicalRing (integers l E.1)]
    (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
    {κ : ℤ_[l] →+* integers l E.1} (hκ : Continuous κ)
    (hικ : ∀ z, algebraMap (integers l E.1) (PadicAlgCl l) (κ z) =
      algebraMap ℚ_[l] _ (PadicInt.Coe.ringHom z))
    (hsurj : Function.Surjective (integersPadicIntHom l E.1))
    [Module (integers l E.1) M] [Module.Finite (integers l E.1) M]
    [ContinuousSMul (integers l E.1) M] [IsModuleTopology (integers l E.1) M] [IsIso θ]
    (hψι : ∀ (U : S.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
      integralLatticeSections g p i E θ U (f • m) = AdicSheaf.sectionAct _
        (ULift.up (AdicSheaf.ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f))
        (integralLatticeSections g p i E θ U m)) :
    IsAdicLisseSheaf (adicRightDerivedLowerStarUnit l g i) :=
  isAdicLisseSheaf_adicRightDerivedLowerStarUnit g p i E θ hι hκ hικ
    (fun U _ r m ↦ integralLattice_map_smul_of_surjective g p i E θ hsurj U r m) hψι

end AlgebraicGeometry.ProEtale
