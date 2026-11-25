/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersApproximation
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeApproximation
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIdentification

/-!
# The kernel of an integral lattice map is torsion

Let `e` identify `F` with `q^* Rⁱg_* ℚ̄_ℓ,T`, `θ : C(-, M) ≅ q^* Rⁱg_* 𝒪_{E,T}` an isomorphism of
abelian sheaves, `M` a finite `𝒪_E`-module, and `ψ_U : C(U, M) → F(U)` the induced maps
(`AlgebraicGeometry.ProEtale.integralLatticeSectionsOfIdentification`). If `ℤ_ℓ → 𝒪_E` is
surjective, a function `t` with `ψ(t) = 0` is killed by a power of `ℓ`
(`AlgebraicGeometry.ProEtale.exists_pow_smul_eq_zero_of_integralLatticeSections_eq_zero`).

Over a qcqs `W`, the vanishing of `ψ(t)` means that `ℓᵐ θ(t)` vanishes in `Γ(W, q^* Rⁱg_* 𝒪_{F,T})`
for some finite `F ⊇ E` and some `m`
(`AlgebraicGeometry.ProEtale.exists_pow_smul_map_eq_zero_of_adicConstantSheafLeg`). The inclusion
`𝒪_E ⊆ 𝒪_F` has a continuous additive retraction up to `ℓᶜ`
(`PadicAlgCl.exists_continuous_retraction`, from a `ℚ_ℓ`-linear retraction `F → ℚ_ℓ`), so that
`ℓ^{m + c} θ(t) = 0`. In general, `t` is torsion on an affine open cover, hence killed by the
bound of the torsion of `M`.
-/

@[expose] public section

universe u

namespace PadicAlgCl

open AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {E F : IntermediateField ℚ_[l] (PadicAlgCl l)}

/-- The inclusion `𝒪_E → 𝒪_F` is compatible with the inclusions of `ℤ_ℓ`. -/
lemma integersInclusion_integersPadicIntHom (h : E ≤ F) (z : ℤ_[l]) :
    integersInclusion l h (integersPadicIntHom l E z) = integersPadicIntHom l F z := by
  refine FaithfulSMul.algebraMap_injective _ (PadicAlgCl l) ?_
  rw [algebraMap_integersPadicIntHom l F z, ← algebraMap_integersPadicIntHom l E z]
  rfl

/-- **A bounded retraction `𝒪_F → 𝒪_E`** for `ℤ_ℓ → 𝒪_E` surjective and `F ⊇ E` finite over
`ℚ_ℓ`: a continuous additive map `ρ` with `ρ(x) = ℓᶜ x` for `x ∈ 𝒪_E`. -/
theorem exists_continuous_retraction [FiniteDimensional ℚ_[l] F] (h : E ≤ F)
    (hsurj : Function.Surjective (integersPadicIntHom l E)) :
    letI := normedFieldOfAlgebra l E
    letI := normedFieldOfAlgebra l F
    ∃ (c : ℕ) (ρ : integers l F →+ integers l E), Continuous ρ ∧
      ∀ x, ρ (integersInclusion l h x) = l ^ c • x := by
  let := normedFieldOfAlgebra l E
  let := normedFieldOfAlgebra l F
  let : NormedSpace ℚ_[l] F :=
    { norm_smul_le c x := by
        change ‖algebraMap F (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap F (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ_[l] F)
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ_[l] F).injective)
  let π' : F →L[ℚ_[l]] ℚ_[l] := LinearMap.toContinuousLinearMap π
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt ‖π'‖
    (show (1 : ℝ) < l by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl : (l : ℚ_[l]) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hmem (y : integers l F) : ‖(l : ℚ_[l]) ^ c * π' (y : F)‖ ≤ 1 := by
    have hy : ‖(y : F)‖ ≤ 1 := by
      have := y.2
      rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm] at this
      exact this
    have h1 := π'.le_opNorm (y : F)
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    calc ((l : ℝ) ^ c)⁻¹ * ‖π' (y : F)‖ ≤ ((l : ℝ) ^ c)⁻¹ * (l : ℝ) ^ c := by
          gcongr
          exact h1.trans ((mul_le_of_le_one_right (norm_nonneg _) hy).trans hc.le)
      _ = 1 := inv_mul_cancel₀ (pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) c).ne'
  let ρ' : integers l F →+ ℤ_[l] :=
    { toFun y := ⟨(l : ℚ_[l]) ^ c * π' (y : F), hmem y⟩
      map_zero' := PadicInt.ext (by simp)
      map_add' y y' := PadicInt.ext (by simp [mul_add]) }
  have hρ' : Continuous ρ' := Continuous.subtype_mk
    (f := fun y : integers l F ↦ (l : ℚ_[l]) ^ c * π' (y : F))
    (continuous_const.mul (π'.continuous.comp continuous_subtype_val)) _
  refine ⟨c, (integersPadicIntHom l E).toAddMonoidHom.comp ρ',
    (continuous_integersPadicIntHom l E).comp hρ', fun x ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hsurj x
  change integersPadicIntHom l E (ρ' (integersInclusion l h (integersPadicIntHom l E z))) = _
  rw [integersInclusion_integersPadicIntHom, nsmul_eq_mul,
    ← map_natCast (integersPadicIntHom l E), ← map_mul]
  congr 1
  refine PadicInt.ext ?_
  change (l : ℚ_[l]) ^ c * π ((integersPadicIntHom l F z : F)) = _
  have : ((integersPadicIntHom l F z : F)) = Algebra.linearMap ℚ_[l] F (z : ℚ_[l]) := rfl
  rw [this, ← LinearMap.comp_apply, hπ]
  push_cast
  rfl

end PadicAlgCl

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u})

/-- Postcomposition with a continuous additive map `ρ : T →+ T'`, as a morphism of the abelian
sheaves of continuous maps. -/
noncomputable def continuousMapAbSheafAddMap {T T' : Type} [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T'] (ρ : T →+ T')
    (hρ : Continuous ρ) : continuousMapAbSheaf X T ⟶ continuousMapAbSheaf X T' where
  hom :=
    { app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((ρ.compLeftContinuous U.unop.left hρ).comp AddEquiv.ulift.toAddMonoidHom))
      naturality _ _ _ := rfl }

variable {l : ℕ} [Fact l.Prime]

variable {X} in
/-- The bounded retraction `𝒪_{F,X} ⟶ 𝒪_{E,X}` composed with the inclusion is `ℓᶜ`. -/
lemma exists_padicIntegersSheafMapOfLE_comp_eq_smul {E F : IntermediateField ℚ_[l] (PadicAlgCl l)}
    [FiniteDimensional ℚ_[l] F] (h : E ≤ F)
    (hsurj : Function.Surjective (integersPadicIntHom l E)) :
    ∃ (c : ℕ) (r : (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntegersSheaf X l F) ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf X l E)),
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (padicIntegersSheafMapOfLE X l h) ≫ r = l ^ c • 𝟙 _ := by
  let := normedFieldOfAlgebra l E
  let := normedFieldOfAlgebra l F
  have := isTopologicalRing_integers l E
  have := isTopologicalRing_integers l F
  obtain ⟨c, ρ, hρ, hρx⟩ := exists_continuous_retraction h hsurj
  refine ⟨c, continuousMapAbSheafAddMap X ρ hρ, ?_⟩
  ext U f
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change ρ (integersInclusion l h (f.down x)) = _
  rw [hρx]
  rfl


variable {T Y S : Scheme.{u}} {g : T ⟶ Y} {i : ℕ} {q : S ⟶ Y} {F : AdicSheaf l S}
  (e : AdicAbIdentification g i F q) (E : FiniteIntermediateField l)
  {M : Type} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  (θ : continuousMapAddSheaf S M ⟶ (q)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))

include e in
/-- **The kernel of `ψ_W` is torsion over a qcqs `W`**, for `ℤ_ℓ → 𝒪_E` surjective and `θ` an
isomorphism: a function `t` with `ψ(t) = 0` is killed by a power of `ℓ`. -/
theorem exists_pow_smul_eq_zero_of_integralLatticeSections_eq_zero_of_qcqs
    [QuasiCompact g] [QuasiSeparated g] [IsIso θ]
    (hsurj : Function.Surjective (integersPadicIntHom l E.1))
    (W : S.ProEt) [CompactSpace W.left] [QuasiSeparatedSpace W.left] (t : C(W.left, M))
    (ht : integralLatticeSectionsOfIdentification e E θ W t = 0) :
    ∃ n : ℕ, l ^ n • t = 0 := by
  let Φ := upperStarRightDerivedSections g q i W
  have hy : Φ.map (adicConstantSheafLeg T l E 0) (θ.hom.app (op W) (ULift.up t)) = 0 := by
    rw [← iso_hom_integralLatticeSectionsOfIdentification, ht, map_zero]
  obtain ⟨F', h, m, hm⟩ := exists_pow_smul_map_eq_zero_of_adicConstantSheafLeg g q i W l _ hy
  have := F'.2
  obtain ⟨c, r, hr⟩ := exists_padicIntegersSheafMapOfLE_comp_eq_smul (X := T) h hsurj
  have hθ : Function.Bijective (θ.hom.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      ((((sheafToPresheaf _ _).mapIso (asIso θ)).app (op W)).hom)))
  refine ⟨m + c, ULift.up_injective (hθ.1 ?_)⟩
  have h1 := congrArg (Φ.map r) hm
  rw [map_nsmul, ← ConcreteCategory.comp_apply, ← Φ.map_comp, hr, Functor.map_nsmul,
    CategoryTheory.Functor.map_id, map_zero] at h1
  have h2 (y : Φ.obj _) : (l ^ c • 𝟙 (Φ.obj ((sheafCompose _ (forget₂ RingCat.{u + 1}
      Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))) : Φ.obj _ ⟶ Φ.obj _) y = l ^ c • y := rfl
  rw [h2] at h1
  change θ.hom.app (op W) (l ^ (m + c) • ULift.up t) = θ.hom.app (op W) 0
  rw [map_zero, map_nsmul, pow_add, mul_smul]
  exact h1


include e in
/-- **The kernel of `ψ_U` is torsion**, for `ℤ_ℓ → 𝒪_E` surjective, `M` a finite `𝒪_E`-module
and `θ` an isomorphism: a function `t` with `ψ(t) = 0` is killed by a power of `ℓ`. -/
theorem exists_pow_smul_eq_zero_of_integralLatticeSections_eq_zero
    [QuasiCompact g] [QuasiSeparated g] [IsIso θ]
    (hsurj : Function.Surjective (integersPadicIntHom l E.1)) [Module (integers l E.1) M]
    [Module.Finite (integers l E.1) M] (U : S.ProEt) (t : C(U.left, M))
    (ht : integralLatticeSectionsOfIdentification e E θ U t = 0) :
    ∃ n : ℕ, l ^ n • t = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_mem_powTorsion E (M := M)
  refine ⟨N, ContinuousMap.ext fun x ↦ hN _ ?_⟩
  obtain ⟨R, f, hf, ⟨y, hy⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := U.left) (x := x) (U := ⊤) trivial
  let V := Scheme.ProEt.ofOpenImmersion U f
  have : CompactSpace V.left := inferInstanceAs (CompactSpace (Spec R))
  have : QuasiSeparatedSpace V.left := inferInstanceAs (QuasiSeparatedSpace (Spec R))
  have hV : integralLatticeSectionsOfIdentification e E θ V
      (t.comp (Scheme.ProEt.ofOpenImmersionHom U f).left.base.hom) = 0 := by
    rw [AdicSheaf.sectionsOfHom_comp, ht, map_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_smul_eq_zero_of_integralLatticeSections_eq_zero_of_qcqs e E θ hsurj
      V _ hV
  refine ⟨n, ?_⟩
  have := congrArg (fun h : C(V.left, M) ↦ h y) hn
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.zero_apply] at this
  rw [← hy]
  exact this

end AlgebraicGeometry.ProEtale
