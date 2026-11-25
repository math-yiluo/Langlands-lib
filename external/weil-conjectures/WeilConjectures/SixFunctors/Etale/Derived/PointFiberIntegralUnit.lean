/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegralBase

/-!
# Integral constructible complexes over a geometric point: constant sheaves

Auxiliary results for `WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral`: over a
separably closed field `k`, the constant sheaf `Λ` on `Spec k` placed in degree `0` lies in the
integral stage `Dᵇc(Spec k, Λ)`, and the constant sheaves in degree `0` lying in the integral
stage satisfy the two-out-of-three property along short exact sequences.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] essentiallySmall_etale_pointFiberIntegral

section IntegralPoint

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsSepClosed k]

variable [IsNoetherianRing Λ] [Finite (Λ ⧸ I)]

/-! ### Bounded constructible complexes lie in the integral stage -/

omit [IsNoetherianRing Λ] in
/-- A constant sheaf on a finitely generated module is constructible on `Spec k`. -/
lemma isConstructibleSheaf_constantSheaf_of_isSepClosed (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    IsConstructibleSheaf
      ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  rw [isConstructibleSheaf_iff_moduleFinite_pointSections]
  exact Module.Finite.equiv (M := M)
    ((constantSheafEquivalenceOfIsSepClosed Λ (k := k)).unitIso.app M).toLinearEquiv

variable [IsAdicComplete I Λ]

omit [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] in
include hϖ hI in
/-- The constant sheaf `Λ` on `Spec k`, placed in degree `0`, is derived complete: it is the
homotopy limit of the constant sheaves `Λ/Iⁿ`, as `Λ` is for `Λ`-modules
(`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`), and those are killed by `ϖⁿ`. -/
lemma derivedComplete_unitSingle :
    _root_.DerivedCategory.derivedComplete (Spec (.of k)).smallEtaleTopology I
      (unitSingle Λ k 0) := by
  have hϖI : ϖ ∈ I := hI ▸ Ideal.mem_span_singleton_self ϖ
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI]
  intro Y f hY
  -- the homotopy limit `Λ = R lim Λ/Iⁿ` for modules
  let T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
    Ideal.quotPowFunctor I ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0
  let c := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapCone (Ideal.quotPowCone I)
  have hc : IsLimit c := isLimitOfPreserves _ (Ideal.isLimitQuotPowCone I)
  have hT (n : ℕ) (i : ℤ) : Epi ((T.map (homOfLE n.le_succ).op).f i) := by
    by_cases hi : i = 0
    · subst hi
      change Epi (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        ((Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op)).f 0)
      rw [HomologicalComplex.single_map_f_self]
      have : Epi ((Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op) := by
        rw [ModuleCat.epi_iff_surjective]
        exact Submodule.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).epi _
  have hQ := DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi hT hc
  -- transported to sheaves on `Spec k`
  have : (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).IsEquivalence :=
    (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).isEquivalence_functor
  have : (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).Additive :=
    additive_constantSheaf Λ _
  let G :=
    (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategory
  have hG := hQ.map G
  let eG (M : ModuleCat.{u + 1} Λ) : G.obj (DerivedCategory.Q.obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    G.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
      ((constantSheaf _ _).mapDerivedCategorySingleFunctor 0).app M
  have hkill (Z : _root_.DerivedCategory
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hZ : _root_.DerivedCategory.smulInvertible _ ϖ Z) (n : ℕ)
      (g : Z ⟶ (T ⋙ DerivedCategory.Q ⋙ G).obj (op n)) : g = 0 := by
    rw [← cancel_mono (eG _).hom, Limits.zero_comp]
    exact hZ.hom_eq_zero
      (_root_.DerivedCategory.smul_id_quotPowFunctor_obj _ hϖI n) _
  have h0 := hG.hom_ext_zero (hkill Y hY) (hkill _ (ObjectProperty.le_shift _ 1 Y hY))
    (f ≫ (eG _).inv)
  rwa [← cancel_mono (eG _).inv, Limits.zero_comp]

omit [IsSepClosed k] [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [IsAdicComplete I Λ] in
include hϖ hI in
/-- The reductions `Λ ⊗ᴸ Λ/Iⁿ` of the constant sheaf `Λ` are the constant sheaves `Λ/Iⁿ`. -/
lemma nonempty_iso_reductionModIdeal_unitSingle (n : ℕ) :
    Nonempty ((reductionModIdeal Λ (Spec (.of k)) (I ^ n)).obj (unitSingle Λ k 0) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ I ^ n)))) := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_reductionModIdeal hϖ hI (unitSingle Λ k 0) n
  have hT' :=
    _root_.DerivedCategory.quotPowTriangle_distinguished (Spec (.of k)).smallEtaleTopology hϖ hI n
  obtain ⟨e, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ hT hT'
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      rw [_root_.DerivedCategory.quotPowTriangle_mor₁]
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Arrow.mk_hom]
      rfl))
  exact ⟨Triangle.π₃.mapIso e⟩

omit [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [IsAdicComplete I Λ] in
include hϖ hI in
/-- The constant sheaf `Λ/Iⁿ` on `Spec k`, placed in degree `0`, is bounded constructible of
Tor amplitude in `[-1, 0]`: it is the cone of `ϖⁿ : Λ ⟶ Λ`, and `Λ` is flat. -/
lemma boundedConstructible_torAmplitudeIn_single_quot (n : ℕ) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ I ^ n)))) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (Spec (.of k)) (-1) 0
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ I ^ n)))) := by
  have := isConstructibleSheaf_constantSheaf_of_isSepClosed (k := k)
    (ModuleCat.of Λ (Λ ⧸ I ^ n))
  refine ⟨DerivedCategory.boundedConstructible_singleFunctor_obj _ 0, ?_⟩
  have hT :=
    _root_.DerivedCategory.quotPowTriangle_distinguished (Spec (.of k)).smallEtaleTopology hϖ hI n
  have hU : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (Spec (.of k)) 0 0
      ((DerivedCategory.singleFunctor _ 0).obj
        (MonoidalCategory.tensorUnit
          (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :=
    _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (ObjectProperty.flat_of_isDualizable isDualizable_unit)
  have h := DerivedCategory.torAmplitudeIn_obj₂ (ModuleCat.{u + 1} Λ) (rot_of_distTriang _ hT)
    hU (DerivedCategory.torAmplitudeIn.shift hU 1)
  exact h.mono (by simp) (by simp)

omit [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] in
include hϖ hI in
/-- The constant sheaf `Λ` on `Spec k`, placed in degree `0`, lies in the integral stage. -/
lemma boundedConstructibleIntegral_unitSingle :
    DerivedCategory.boundedConstructibleIntegral I (Spec (.of k)) (unitSingle Λ k 0) := by
  refine ⟨derivedComplete_unitSingle hϖ hI, -1, 0, fun n ↦ ?_⟩
  obtain ⟨e⟩ := nonempty_iso_reductionModIdeal_unitSingle (k := k) hϖ hI (n + 1)
  obtain ⟨h₁, h₂⟩ := boundedConstructible_torAmplitudeIn_single_quot (k := k) hϖ hI (n + 1)
  exact ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso e.symm h₁,
    (DerivedCategory.torAmplitudeIn _ _ _ _).prop_of_iso e.symm h₂⟩

omit [IsAdicComplete I Λ] in
include hϖ hI in
/-- The constant sheaves `M` on `Spec k` placed in degree `0` which lie in the integral stage
satisfy the two-out-of-three property along short exact sequences of `Λ`-modules. -/
lemma boundedConstructibleIntegral_single_of_shortExact {S : ShortComplex (ModuleCat.{u + 1} Λ)}
    (hS : S.ShortExact) :
    let P : ModuleCat.{u + 1} Λ → Prop := fun M ↦
      DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
    (P S.X₁ → P S.X₂ → P S.X₃) ∧ (P S.X₁ → P S.X₃ → P S.X₂) := by
  intro P
  have : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ}) := ⟨⟨ϖ, hϖ, hI⟩⟩
  have := DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
    (X := Spec (.of k)) hϖ hI
  have hS' := hS.map_of_exact (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).functor
  have hT := hS'.singleTriangle_distinguished
  refine ⟨fun h₁ h₂ ↦ ?_, fun h₁ h₃ ↦ ?_⟩
  · exact
      (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).ext_of_isTriangulatedClosed₂
      _ (rot_of_distTriang _ hT) h₂
      ((DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).le_shift 1 _ h₁)
  · exact
      (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).ext_of_isTriangulatedClosed₂
      _ hT h₁ h₃

end IntegralPoint

end Etale

end AlgebraicGeometry
