/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTowerDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleInduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegersPowShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.TraceFormula.OpenCover

/-!
# Bounded constructible `𝒪_E`-complexes are derived complete

On a noetherian scheme `X`, every bounded constructible complex of `𝒪_{E,X}`-module objects is
derived complete (`ProEtale.derivedCompleteIntegers_of_boundedConstructible`, part of blueprint
`proposition-integral-constructibility-criterion`).

By dévissage along the truncation triangles, it suffices to treat a constructible module object
`M` placed in one degree. For it, derived completeness follows from the bijectivity of
`1 - ϖ · shift : ∏ₙ M ⟶ ∏ₙ M`, which is checked after pullback to finitely many affine members
of pro-étale covers of the strata (the pullbacks preserve countable products), where `M` is
finitely presented. A finitely presented module is a cokernel of a map of finite free modules,
and the bijectivity passes to cokernels by the snake lemma; for `𝒪_{E,V}` itself it is the
`ϖ`-adic completeness of the rings `C(V, 𝒪_E)` of sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-! ### Derived complete complexes form a triangulated subcategory -/

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Derived complete complexes are closed under isomorphisms. -/
lemma derivedCompleteIntegers_of_iso {X : Scheme.{u}}
    {K K' : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (e : K ≅ K') : derivedCompleteIntegers ℓ E X K' := by
  intro Z hZ f
  rw [← cancel_mono e.inv, hK hZ (f ≫ e.inv), zero_comp]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Zero objects are derived complete. -/
lemma derivedCompleteIntegers_of_isZero {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : IsZero K) : derivedCompleteIntegers ℓ E X K :=
  fun _ _ _ ↦ hK.eq_of_tgt _ _

/-! ### Constructible module objects -/

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Let `M` be an `𝒪_{E,X}`-module whose sheaf pullback along `j : Z ⟶ X` becomes finitely
presented after further pullback along `h : Y ⟶ Z`. Then the pullback of `M` along `k ≫ h ≫ j` is
finitely presented, for every `k : W ⟶ Y`. -/
lemma isFinitelyPresented_upperStar_comp_comp_padicIntegers {X Y Z W : Scheme.{u}} (j : Z ⟶ X)
    (h : Y ⟶ Z) (k : W ⟶ Y)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hM : Mod.IsFinitelyPresented ((h)^*[Ab.{u + 1}].obj ((j)^*[Ab.{u + 1}].obj
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
      (((h)^*[Ab.{u + 1}].mapMod ((j)^*[Ab.{u + 1}].obj
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))).obj
        (((j)^*[Ab.{u + 1}].mapMod
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).obj M))) :
    Mod.IsFinitelyPresented _ ((k ≫ h ≫ j)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M) :=
  (IsFinitelyPresented.upperStar _ k (isFinitelyPresented_upperStar_of_comap_iso _ h
    (condensedPullbackHom _ j) (comapUpperStarObjIso _ j M) hM)).of_iso
    ((k)^*⟦_⟧.mapIso ((CondensedRing.upperStarComp _ h j).app M).symm ≪≫
      ((CondensedRing.upperStarComp _ k (h ≫ j)).app M).symm)

/-- **Constructible `𝒪_{E,X}`-modules are complete with respect to `ϖ ∈ 𝔪_E`**, on a noetherian
scheme: on the countable power of a constructible `𝒪_{E,X}`-module `M`,
`(xₙ)ₙ ↦ (xₙ - ϖ x_{n+1})ₙ` is an isomorphism. This is checked after pullback along finitely many
quasi-compact jointly surjective morphisms `g : W ⟶ X` from affine schemes along which `M`
becomes finitely presented; the pullbacks preserve countable products and the action of `ϖ`. -/
theorem isIso_sub_powShift_padicIntegersCenter_of_isConstructible {X : Scheme.{u}}
    [IsNoetherian X] {ϖ : integers ℓ E} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (integers ℓ E))
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (hM : IsConstructibleModuleObject _ M) :
    IsIso (𝟙 _ - powShift ((padicIntegersCenter X ℓ E ϖ).app M)) := by
  obtain ⟨S, hS⟩ := hM
  choose 𝒰 h𝒰 using hS
  -- the strata are quasi-compact
  have hc (a : Fin S.n) : CompactSpace (S.domain a) := by
    have := (S.immersion a).isEmbedding.isInducing.noetherianSpace
    infer_instance
  -- finitely many affine opens of members of the covers cover each stratum
  have hqc (a : Fin S.n) : QuasiCompactCover (𝒰 a).toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact (show _ ∈ propQCPrecoverage @WeaklyEtale _ from (𝒰 a).mem₀).1
  have hfin (a : Fin S.n) := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (𝒰 a).toPreZeroHypercover (U := ⊤) (by simpa using isCompact_univ)
  choose N j W hW hcov using hfin
  have hW' (a : Fin S.n) (i : Fin (N a)) : IsAffine (W a i) := hW a i
  obtain ⟨g, hg_eq⟩ : ∃ g : ∀ p : Σ a : Fin S.n, Fin (N a), (W p.1 p.2).toScheme ⟶ X,
      ∀ p, g p = (W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1 := ⟨_, fun _ ↦ rfl⟩
  have hg : ∀ x, ∃ p : Σ a : Fin S.n, Fin (N a), x ∈ Set.range (g p).base := by
    intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, rfl⟩ := ha
    have hy : y ∈ ⋃ i, (𝒰 a).f (j a i) '' (W a i) := by
      rw [hcov a]
      trivial
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨w, rfl⟩ : z ∈ Set.range (W a i).ι := by
      rw [Scheme.Opens.range_ι]
      exact hz
    refine ⟨⟨a, i⟩, w, ?_⟩
    rw [hg_eq]
    rfl
  have hfp (p : Σ a : Fin S.n, Fin (N a)) :
      Mod.IsFinitelyPresented _ ((g p)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M) := by
    rw [hg_eq]
    exact isFinitelyPresented_upperStar_comp_comp_padicIntegers (S.immersion p.1)
      ((𝒰 p.1).f (j p.1 p.2)) (W p.1 p.2).ι (h𝒰 p.1 (j p.1 p.2))
  have hqcg (p : Σ a : Fin S.n, Fin (N a)) : QuasiCompact (g p) := by
    rw [hg_eq]
    have := hW' p.1 p.2
    exact quasiCompact_of_compactSpace _
  have (p : Σ a : Fin S.n, Fin (N a)) : PreservesLimit (Discrete.functor fun _ : ℕ ↦ M)
      ((g p)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) := by
    have := hW' p.1 p.2
    infer_instance
  have key (p : Σ a : Fin S.n, Fin (N a)) : IsIso (𝟙 _ - powShift
      (((g p)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).map
        ((padicIntegersCenter X ℓ E ϖ).app M))) := by
    rw [upperStar_map_padicIntegersCenter_app]
    exact isIso_sub_powShift_padicIntegersCenter_of_isFinitelyPresented _ ℓ E hϖ (hfp p)
  exact isIso_sub_powShift_of_jointlyReflectIsomorphisms
    (jointlyReflectIsomorphisms_upperStar_of_cover _ g hg) _ key


/-- On a noetherian scheme, **bounded constructible `𝒪_E`-complexes are derived complete**
(part of blueprint `proposition-integral-constructibility-criterion`). -/
theorem derivedCompleteIntegers_of_boundedConstructible {X : Scheme.{u}} [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) K) :
    derivedCompleteIntegers ℓ E X K := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  refine prop_of_boundedConstructible (derivedCompleteIntegers ℓ E X)
    (fun _ h ↦ derivedCompleteIntegers_of_isZero h) derivedCompleteIntegers_of_iso
    (fun n h ↦ derivedCompleteIntegers_shift h n) derivedCompleteIntegers_ext₂ (fun M hM ↦ ?_) hK
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ]
  exact isCenterComplete_singleFunctor_of_isIso _ M
    (isIso_sub_powShift_padicIntegersCenter_of_isConstructible
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ) M hM)

end AlgebraicGeometry.ProEtale
