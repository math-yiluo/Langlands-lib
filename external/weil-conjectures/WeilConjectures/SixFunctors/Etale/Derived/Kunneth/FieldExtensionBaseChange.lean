/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PerfectSeparable
public import WeilConjectures.FieldTheory.SeparableSmoothColimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.BaseChangeUniversalHomeomorphism

/-!
# Higher direct images commute with base change along field extensions

Let `L/K` be a field extension and `g : T ⟶ S` a quasi-compact quasi-separated morphism of
schemes over `K`. For every sheaf `F` on `T` whose geometric stalks are torsion of orders
invertible in `K`, the base-change map `R^q g_* F |_{S_L} ⟶ R^q g_{L,*} (F|_{T_L})` is an
isomorphism (blueprint `corollary-open-direct-image-over-field--2`, Stacks 0F1C). After passing to
perfect closures (a universal homeomorphism does not change the étale sites) the extension is
separable, hence a filtered colimit of smooth algebras, and smooth base change along limits
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth`) applies.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`

## References

- Stacks Project, Lemma 59.89.4, <https://stacks.math.columbia.edu/tag/0F1C>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Being torsion of orders invertible on `S` passes to any `S'` mapping to `S`. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.of_hom {S S' T : Scheme.{u}} (b : S' ⟶ S)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hF : Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S' F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨n, hn, hu, hx⟩ := hF.exists_isUnit_nsmul_eq_zero Ω s x
    exact ⟨n, hn, by simpa using hu.map b.appTop.hom, hx⟩

/-- **Base change along a separable field extension.** Let `L / K` be a separable field
extension and `g : T ⟶ S` a quasi-compact quasi-separated morphism of schemes over `K`. Then the
base-change map of the square `T_L = T ×_S S_L` is an isomorphism in every degree, at every sheaf
on `T` with torsion stalks of orders invertible in `K`. Indeed `L` is the filtered colimit of
its smooth finite type `K`-subalgebras (blueprint `corollary-open-direct-image-over-field--2`), so
`S_L` is the limit of the smooth `S`-schemes `S ×_K Spec A`, and blueprint
`corollary-open-direct-image-over-field--2` applies. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isSeparableExtension {K L : Type u} [Field K]
    [Field L] [Algebra K L] (hKL : Algebra.IsSeparableExtension K L) {S T S' T' : Scheme.{u}}
    (σ : S ⟶ Spec (.of K)) (g : T ⟶ S) [QuasiCompact g] [QuasiSeparated g] (p : S' ⟶ S)
    (σ' : S' ⟶ Spec (.of L))
    (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {e : T' ⟶ T} {h : T' ⟶ S'} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let 𝒜 := {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}
  obtain ⟨hne, hdir, -, -, ⟨hD₀⟩, -, -⟩ :=
    FieldTheory.separable_extension_is_filtered_colimit_smooth hKL
  have : IsDirected 𝒜 (· ≤ ·) := ⟨hdir⟩
  have : IsFiltered 𝒜 := isFiltered_of_directed_le_nonempty 𝒜
  let D₀ : 𝒜ᵒᵖ ⥤ Scheme.{u} :=
    (FieldTheory.smoothSubalgebraDiagram K L).op ⋙ Scheme.Spec
  let π : D₀ ⟶ (Functor.const 𝒜ᵒᵖ).obj (Spec (.of K)) :=
    { app A := Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1))
      naturality A B f := by
        simp only [D₀, Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [Scheme.Spec_map, ← Spec.map_comp]
        rfl }
  have hP (A : 𝒜ᵒᵖ) :
      (Scheme.Spec.mapCone (FieldTheory.smoothSubalgebraCocone K L).op).π.app A ≫ π.app A =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    simp only [Functor.mapCone_π_app, Cocone.op_π, NatTrans.op_app, Scheme.Spec_map, π]
    rw [← Spec.map_comp]
    rfl
  let X := baseChangeOverDiagram D₀ π σ
  let c := baseChangeOverCone D₀ π
    (Scheme.Spec.mapCone (FieldTheory.smoothSubalgebraCocone K L).op)
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) (fun A ↦ (hP A).symm) σ
  have hc : IsLimit c := isLimitBaseChangeOverCone D₀ π _ _ (fun A ↦ (hP A).symm) σ hD₀
  let c' := c.extend hS.isoPullback.hom
  have hc' : IsLimit c' := hc.ofIsoLimit (Cone.extendIso c hS.isoPullback.symm)
  let pX : X ⟶ (Functor.const 𝒜ᵒᵖ).obj S :=
    { app A := pullback.fst σ (π.app A)
      naturality A B f := by simp [X] }
  have : ∀ A, Smooth (π.app A) := fun A ↦ by
    have : Algebra.Smooth K A.unop.1 := A.unop.2.1
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap K A.unop.1))).2
      ((RingHom.smooth_algebraMap (R := K) (S := A.unop.1)).2 this)
  have : ∀ A, QuasiCompact (π.app A) := fun A ↦
    (inferInstance : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1))))
  have : ∀ A, QuasiSeparated (π.app A) := fun A ↦
    (inferInstance : QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1))))
  have : ∀ A, Smooth (pX.app A) := fun A ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ (π.app A)).flip inferInstance
  have : ∀ A, QuasiCompact (pX.app A) := fun A ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ (π.app A)).flip inferInstance
  have : ∀ A, QuasiSeparated (pX.app A) := fun A ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ (π.app A)).flip inferInstance
  have : ∀ {A B : 𝒜ᵒᵖ} (f : A ⟶ B), IsAffineHom (D₀.map f) := fun f ↦
    (inferInstance : IsAffineHom (Spec.map _))
  have : Scheme.IsTorsionSheafOfInvertibleOrder S F :=
    Scheme.IsTorsionSheafOfInvertibleOrder.of_hom Λ σ F
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth' Λ g X pX hc' p
    (fun A ↦ by simp [c', c, pX]) sq q F

/-- Blueprint `corollary-open-direct-image-over-field--2`: Direct image commutes with base change
along field extensions.

Let `L/K` be a field extension, `σ : S ⟶ Spec K` a scheme over `K` and `g : T ⟶ S` a
quasi-compact quasi-separated morphism. Let `S' = S ×_K L` (the Cartesian square `hS`) and
`T' = T ×_S S'` (the Cartesian square `sq`). For every sheaf `F` of `Λ`-modules on `T` whose
geometric stalks are torsion of orders invertible in `K`, the base-change map
`R^q g_* F |_{S'} ⟶ R^q h_* (F|_{T'})` is an isomorphism in every degree `q`. -/
@[stacks 0F1C]
theorem Etale.isIso_baseChangeHomologyMap_of_fieldExtension {K L : Type u} [Field K] [Field L]
    [Algebra K L] {S T S' T' : Scheme.{u}} (σ : S ⟶ Spec (.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (p : S' ⟶ S) (σ' : S' ⟶ Spec (.of L))
    (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {e : T' ⟶ T} {h : T' ⟶ S'} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  -- the perfect closures `K'` of `K` and `L'` of `L` inside an algebraic closure of `L`
  let K' := perfectClosure K (AlgebraicClosure L)
  let L' := perfectClosure L (AlgebraicClosure L)
  let _ : Algebra K' L' := (perfectClosureAlgebraicClosureHom K L).toRingHom.toAlgebra
  have hsep : Algebra.IsSeparableExtension K' L' :=
    Algebra.isSeparableExtension_of_perfectField K' L'
  let πK : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  let πL : Spec (.of L') ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom (algebraMap L L'))
  let ι : Spec (.of L') ⟶ Spec (.of K') := Spec.map (CommRingCat.ofHom (algebraMap K' L'))
  have : IsUniversalHomeomorphism πK :=
    Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism
  have : IsUniversalHomeomorphism πL :=
    Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism
  have hcomm : πL ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = ι ≫ πK := by
    simp only [πL, πK, ι, ← Spec.map_comp]
    congr 1
  -- the base changes `S₁ = S_{K'}` and `S₂ = S'_{L'}`
  let p₁ := pullback.fst σ πK
  let σ₁ := pullback.snd σ πK
  let p₂ := pullback.fst σ' πL
  let σ₂ := pullback.snd σ' πL
  have : IsUniversalHomeomorphism p₁ :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ πK).flip inferInstance
  have : IsUniversalHomeomorphism p₂ :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ' πL).flip inferInstance
  let r : pullback σ' πL ⟶ pullback σ πK := pullback.lift (p₂ ≫ p) (σ₂ ≫ ι) (by
    rw [Category.assoc, hS.w, ← Category.assoc, pullback.condition, Category.assoc, hcomm,
      Category.assoc])
  have hr₁ : r ≫ p₁ = p₂ ≫ p := pullback.lift_fst _ _ _
  have hS₁ : IsPullback r σ₂ σ₁ ι := by
    have big := (IsPullback.of_hasPullback σ' πL).paste_horiz hS
    rw [hcomm, ← hr₁] at big
    exact IsPullback.of_right big (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback σ πK)
  -- the base changes of `g`
  let e₁ := pullback.fst g p₁
  let g₁ := pullback.snd g p₁
  have sq₁ : IsPullback e₁ g₁ g p₁ := IsPullback.of_hasPullback g p₁
  have : QuasiCompact g₁ := MorphismProperty.of_isPullback sq₁ inferInstance
  have : QuasiSeparated g₁ := MorphismProperty.of_isPullback sq₁ inferInstance
  let a₂ := pullback.fst h p₂
  let b₂ := pullback.snd h p₂
  have sq₃ : IsPullback a₂ b₂ h p₂ := IsPullback.of_hasPullback h p₂
  have sqC : IsPullback (a₂ ≫ e) b₂ g (p₂ ≫ p) := sq₃.paste_horiz sq
  let c₂ : pullback h p₂ ⟶ pullback g p₁ := pullback.lift (a₂ ≫ e) (b₂ ≫ r) (by
    rw [sqC.w, Category.assoc, hr₁])
  have sq₂ : IsPullback c₂ b₂ g₁ r := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) sq₁
    rw [pullback.lift_fst, hr₁]
    exact sqC
  -- the composite square over `p₂ ≫ p = r ≫ p₁` has an invertible base-change map
  have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K'))
      (((e₁)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    Scheme.IsTorsionSheafOfInvertibleOrder.upperStar Λ πK e₁ F
  have hC : IsIso (Etale.baseChangeHomologyMap Λ sqC q F) :=
    Etale.isIso_baseChangeHomologyMap_of_paste_horiz Λ sq₁ sq₂ sqC (pullback.lift_fst _ _ _)
      hr₁ q F (Etale.baseChangeProperty_of_isUniversalHomeomorphism Λ p₁ q g e₁ g₁ sq₁ F)
      (Etale.isIso_baseChangeHomologyMap_of_isSeparableExtension Λ hsep σ₁ g₁ r σ₂ hS₁
        sq₂ q _)
  -- cancel the base change along the universal homeomorphism `p₂`
  rw [Etale.isIso_baseChangeHomologyMap_iff] at hC ⊢
  rw [Etale.baseChange_app_paste_horiz Λ sq.toCommSq sq₃.toCommSq sqC.toCommSq] at hC
  simp only [Functor.map_comp] at hC
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₃.toCommSq).app
        (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    have := Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism
      (ModuleCat.{u + 1} Λ) sq₃
    infer_instance
  rw [isIso_comp_left_iff, isIso_comp_right_iff] at hC
  have h₅ : IsIso (((p₂)^*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :=
    (NatIso.isIso_map_iff (((p₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      q) _).2 hC
  have := Etale.isEquivalence_upperStar (ModuleCat.{u + 1} Λ) p₂
  exact isIso_of_reflects_iso _ ((p₂)^*[ModuleCat.{u + 1} Λ])

end AlgebraicGeometry
