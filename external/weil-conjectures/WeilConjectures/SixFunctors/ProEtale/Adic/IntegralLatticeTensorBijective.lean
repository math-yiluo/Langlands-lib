/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStageMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeSections

/-!
# `p^* Rⁱg_* ℚ̄_ℓ,T = ℚ̄_ℓ ⊗_{𝒪_E} C(-, M)` from an integral identification

Let `g : T ⟶ Y` be quasi-compact and quasi-separated, `p : S ⟶ Y` weakly étale, `E` a finite
extension of `ℚ_ℓ` inside `ℚ̄_ℓ` and `θ : C(-, M) ⟶ p^* Rⁱg_* 𝒪_{E,T}` a morphism of abelian
sheaves (an integral identification, for an `𝒪_E`-module `M`). Composing with
`p^* Rⁱg_* 𝒪_{E,T} ⟶ p^* Rⁱg_* ℚ̄_ℓ,T` gives maps
`ψ_U : C(U, M) → (p^* Rⁱg_* ℚ̄_ℓ,T)(U)` (`AlgebraicGeometry.ProEtale.integralLatticeSections`).

- `AlgebraicGeometry.ProEtale.bijective_tensorSections_integralLatticeSections`: if `θ` is
  bijective and `𝒪_E`-linear on sections over a quasi-compact quasi-separated `W`, then
  `ℚ̄_ℓ ⊗_{𝒪_E} C(W, M) → (p^* Rⁱg_* ℚ̄_ℓ,T)(W)`, `c ⊗ m ↦ c • ψ(m)`, is bijective. Both sides are
  the colimit of the `ℓ⁻ⁿ (𝒪_F ⊗_{𝒪_E} C(W, M))` (`PadicAlgCl.bijective_of_integersSubalgebra`,
  `AlgebraicGeometry.ProEtale.exists_sections_adicConstantSheafLeg_eq_of_le`), compatibly:
  `𝒪_F ⊗_{𝒪_E} C(W, M) = Γ(W, p^* Rⁱg_* 𝒪_{F,T})` (`AlgebraicGeometry.ProEtale.bijective_stageMap`)
  and the `ℚ̄_ℓ`-structure of the sections is the one induced by functoriality
  (`AlgebraicGeometry.ProEtale.adicUpperStarRightDerivedLowerStarUnitAbIso_hom_smul`).
- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicRightDerivedLowerStarUnit`: hence
  `Rⁱg_* ℚ̄_ℓ,T` is lisse when `p` is moreover surjective and quasi-compact, `θ` is an
  isomorphism, `𝒪_E`-linear on affine objects, `M` is finite over `𝒪_E` and the maps `ψ_U` are
  `C(U, 𝒪_E)`-semilinear.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl TensorProduct

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T Y S : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
  [QuasiSeparated g] (p : S ⟶ Y) [WeaklyEtale p] (i : ℕ) (E : FiniteIntermediateField l)
  {M : Type} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  (θ : continuousMapAddSheaf S M ⟶ (p)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))

/-- The morphism `C(-, M) ⟶ p^* Rⁱg_* 𝒪_{E,T} ⟶ p^* Rⁱg_* ℚ̄_ℓ,T` of abelian sheaves attached to an
integral identification `θ`. -/
noncomputable def integralLatticeHom :
    continuousMapAddSheaf S M ⟶ (sheafCompose (Scheme.ProEt.topology S)
      (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        ((p)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)).X :=
  θ ≫ (p)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
    (adicConstantSheafLeg T l E 0)) ≫ (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).inv

/-- The maps `ψ_U : C(U, M) → (p^* Rⁱg_* ℚ̄_ℓ,T)(U)` attached to an integral identification `θ`. -/
noncomputable abbrev integralLatticeSections (U : S.ProEt) :
    C(U.left, M) →+ ((p)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)).X.obj.obj (op U) :=
  AdicSheaf.sectionsOfHom _ (integralLatticeHom g p i E θ) U

omit [QuasiCompact g] [QuasiSeparated g] in
lemma adicUpperStarRightDerivedLowerStarUnitAbIso_hom_integralLatticeSections (U : S.ProEt)
    (m : C(U.left, M)) :
    (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op U)
        (integralLatticeSections g p i E θ U m) =
      ((p)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
        (adicConstantSheafLeg T l E 0))).hom.app (op U) (θ.hom.app (op U) (ULift.up m)) := by
  have h : integralLatticeHom g p i E θ ≫
      (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom =
      θ ≫ (p)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
        (adicConstantSheafLeg T l E 0)) := by
    simp [integralLatticeHom]
  have h := congrArg (fun φ ↦ φ.hom.app (op U)) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  rw [AdicSheaf.sectionsOfHom_apply, ← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]

omit [QuasiCompact g] [QuasiSeparated g] in
lemma adicUpperStarRightDerivedLowerStarUnitAbIso_hom_app_smul (U : S.ProEt)
    (c : ULift.{u + 1} (PadicAlgCl l))
    (x : ((p)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)).X.obj.obj (op U)) :
    (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op U) (c • x) =
      ((p)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
        ((weilCoefficientsForgetAb l T).map
          ((weilSmulNatTrans l T c).app (adicConstantSheaf l T))))).hom.app (op U)
        ((adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op U) x) := by
  have h := congrArg (fun φ ↦ φ.hom.app (op U))
    (adicUpperStarRightDerivedLowerStarUnitAbIso_hom_smul l g p i c)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  have h2 := ConcreteCategory.congr_hom h x
  exact h2.trans rfl

section Bijective

variable (W : S.ProEt) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
  [TopologicalSpace (integers l E.1)] [Module (integers l E.1) M]
  [ContinuousSMul (integers l E.1) M]
  (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
  (hθW : Function.Bijective (θ.hom.app (op W)))
  (hθ : ∀ (r : integers l E.1) (m : C(W.left, M)),
    θ.hom.app (op W) (ULift.up (r • m)) = (upperStarRightDerivedSections g p i W).map
      (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ.hom.app (op W) (ULift.up m)))
  (hψι : ∀ (U : S.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
    integralLatticeSections g p i E θ U (f • m) = AdicSheaf.sectionAct _
      (ULift.up (AdicSheaf.ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f))
      (integralLatticeSections g p i E θ U m))

/-- The sections of the integral identification over `W`, as an additive equivalence
`C(W, M) ≃ Γ(W, p^* Rⁱg_* 𝒪_{E,T})`. -/
noncomputable abbrev integralLatticeSectionsEquiv :
    C(W.left, M) ≃+ (upperStarRightDerivedSections g p i W).obj
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1)) :=
  AddEquiv.ofBijective ((θ.hom.app (op W)).hom.comp
      (AddEquiv.ulift.{u, u + 1} (α := C(W.left, M))).symm.toAddMonoidHom)
    ⟨hθW.1.comp ULift.up_injective, fun y ↦ by
      obtain ⟨⟨x⟩, hx⟩ := hθW.2 y
      exact ⟨x, hx⟩⟩

omit [Module (integers l E.1) M] [ContinuousSMul (integers l E.1) M]
  [TopologicalSpace (integers l E.1)] [CompactSpace W.left] [QuasiSeparatedSpace W.left]
  [QuasiCompact g] [QuasiSeparated g] in
lemma adicUpperStarRightDerivedLowerStarUnitAbIso_hom_integralLatticeSections' (m : C(W.left, M)) :
    (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op W)
        (integralLatticeSections g p i E θ W m) =
      (upperStarRightDerivedSections g p i W).map (adicConstantSheafLeg T l E 0)
        (θ.hom.app (op W) (ULift.up m)) :=
  adicUpperStarRightDerivedLowerStarUnitAbIso_hom_integralLatticeSections g p i E θ W m

omit [QuasiCompact g] [QuasiSeparated g] [TopologicalSpace (integers l E.1)]
  [CompactSpace W.left] [QuasiSeparatedSpace W.left] in
lemma adicUpperStarRightDerivedLowerStarUnitAbIso_hom_app_smul' (c : ULift.{u + 1} (PadicAlgCl l))
    (x : ((p)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)).X.obj.obj (op W)) :
    (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op W) (c • x) =
      (upperStarRightDerivedSections g p i W).map ((weilCoefficientsForgetAb l T).map
        ((weilSmulNatTrans l T c).app (adicConstantSheaf l T)))
        ((adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op W) x) :=
  adicUpperStarRightDerivedLowerStarUnitAbIso_hom_app_smul g p i W c x

include hθ in
omit [CompactSpace W.left] [QuasiSeparatedSpace W.left] [QuasiCompact g] [QuasiSeparated g] in
/-- **Compatibility of `tensorSections` with the stages**: `ψ(ℓ⁻ⁿ o ⊗ m)` corresponds to the
image of `o ⊗ m ∈ 𝒪_F ⊗ C(W, M) = Γ(W, p^* Rⁱg_* 𝒪_{F,T})` under `ℓ⁻ⁿ : 𝒪_{F,T} ⟶ ℚ̄_ℓ,T`. -/
lemma tensorSections_stageTensorMap (F : FiniteIntermediateFieldOver l E.1) (n : ℕ)
    (τ : integersSubalgebraFamily l E.1 F ⊗[integers l E.1] C(W.left, M)) :
    (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op W)
        (AdicSheaf.tensorSections _ hι (algebraMap_integers_mem l E.1)
          (integralLatticeSections g p i E θ) hψι W
          (Subalgebra.stageTensorMap (l : integers l E.1) (integersSubalgebraFamily l E.1) F n
            τ)) =
      (upperStarRightDerivedSections g p i W).map (adicConstantSheafLeg T l F.1 n)
        (stageMap _ E (integralLatticeSectionsEquiv g p i E θ W hθW) hθ F τ) := by
  induction τ using TensorProduct.inductionOn with
  | add τ τ' hτ hτ' => simp only [map_add, hτ, hτ']
  | tmul o m =>
    simp only [Subalgebra.stageTensorMap_tmul, AdicSheaf.tensorSections_tmul,
      adicUpperStarRightDerivedLowerStarUnitAbIso_hom_app_smul']
    refine (congrArg (fun y ↦ (upperStarRightDerivedSections g p i W).map
      ((weilCoefficientsForgetAb l T).map ((weilSmulNatTrans l T _).app
        (adicConstantSheaf l T))) y)
      (adicUpperStarRightDerivedLowerStarUnitAbIso_hom_integralLatticeSections' g p i E θ W
        m)).trans ?_
    rewrite [stageMap_tmul]
    rewrite [algebraMap_natCast_pow_inv_mul_eq]
    have key := congrArg (fun φ ↦ (upperStarRightDerivedSections g p i W).map φ
      (θ.hom.app (op W) (ULift.up m)))
      (padicIntegersSheafMulOfLE_comp_adicConstantSheafLeg (X := T) (E := E) (F := F.1) F.2
        (integersSubalgebraFamilyEquiv E F o) n)
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at key
    exact key.symm

include hθ hθW in
/-- **`ℚ̄_ℓ ⊗_{𝒪_E} C(W, M) = Γ(W, p^* Rⁱg_* ℚ̄_ℓ,T)`** for `W` quasi-compact and
quasi-separated: the map `c ⊗ m ↦ c • ψ(m)` attached to an `𝒪_E`-linear integral identification
`θ : C(-, M) ≅ p^* Rⁱg_* 𝒪_{E,T}` is bijective. -/
theorem bijective_tensorSections_integralLatticeSections :
    Function.Bijective (AdicSheaf.tensorSections _ hι (algebraMap_integers_mem l E.1)
      (integralLatticeSections g p i E θ) hψι W) := by
  let Φ := upperStarRightDerivedSections g p i W
  let θW := integralLatticeSectionsEquiv g p i E θ W hθW
  have hB : Function.Bijective
      ((adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      ((((sheafToPresheaf _ _).mapIso (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i)).app
        (op W)).hom)))
  refine (hB.of_comp_iff' _).1 ?_
  refine bijective_of_integersSubalgebra (E := E.1)
    ((ConcreteCategory.hom ((adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom.hom.app
      (op W))).comp (AdicSheaf.tensorSections _ hι (algebraMap_integers_mem l E.1)
        (integralLatticeSections g p i E θ) hψι W)) (fun b ↦ ?_) (fun F n τ hτ ↦ ?_)
  · obtain ⟨F₀, hle, n, y, rfl⟩ := exists_sections_adicConstantSheafLeg_eq_of_le g p i W l E b
    obtain ⟨τ, rfl⟩ := (bijective_stageMap Φ E θW hθ ⟨F₀, hle⟩).2 y
    exact ⟨⟨F₀, hle⟩, n, τ, tensorSections_stageTensorMap g p i E θ W hι hθW hθ hψι _ n τ⟩
  · have hτ' := (tensorSections_stageTensorMap g p i E θ W hι hθW hθ hψι F n τ).symm.trans hτ
    have key := exists_pow_smul_map_eq_zero_of_adicConstantSheafLeg g p i W l
      (E := F.1) (n := n) (stageMap (upperStarRightDerivedSections g p i W) E
        (integralLatticeSectionsEquiv g p i E θ W hθW) hθ F τ)
    have hτ'' : (upperStarRightDerivedSections g p i W).map (adicConstantSheafLeg T l F.1 n)
        (stageMap (upperStarRightDerivedSections g p i W) E
          (integralLatticeSectionsEquiv g p i E θ W hθW) hθ F τ) = 0 := hτ'
    have key2 := key hτ''
    refine key2.elim fun F'' hF ↦ hF.elim fun h hm' ↦ hm'.elim fun m hm ↦ ?_
    let F' : FiniteIntermediateFieldOver l E.1 := ⟨F'', F.2.trans h⟩
    have hs : integersSubalgebraFamily l E.1 F ≤ integersSubalgebraFamily l E.1 F' :=
      integersSubalgebra_mono F.2 h
    refine ⟨F', hs, m, (bijective_stageMap Φ E θW hθ F').1 ?_⟩
    have e1 : ((l : integers l E.1) ^ m) •
        (Subalgebra.inclusion hs).toLinearMap.rTensor C(W.left, M) τ =
          (l ^ m) • (Subalgebra.inclusion hs).toLinearMap.rTensor C(W.left, M) τ :=
      natCast_pow_smul_eq_nsmul _ _ _
    refine (congrArg _ e1).trans ((map_nsmul _ _ _).trans ?_)
    exact (congrArg _ (stageMap_rTensor Φ E θW hθ h hs τ)).trans (hm.trans (map_zero _).symm)

end Bijective

/-- **`Rⁱg_* ℚ̄_ℓ,T` is lisse** as soon as its pullback to a weakly étale surjective quasi-compact
`p : S ⟶ Y` has an `𝒪_E`-linear integral identification `θ : C(-, M) ≅ p^* Rⁱg_* 𝒪_{E,T}` with `M`
a finite `𝒪_E`-module, whose induced maps `ψ_U : C(U, M) → (p^* Rⁱg_* ℚ̄_ℓ,T)(U)` are
`C(U, 𝒪_E)`-semilinear. -/
theorem isAdicLisseSheaf_adicRightDerivedLowerStarUnit [Surjective p] [QuasiCompact p]
    [TopologicalSpace (integers l E.1)] [IsTopologicalRing (integers l E.1)]
    (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
    {κ : ℤ_[l] →+* integers l E.1} (hκ : Continuous κ)
    (hικ : ∀ z, algebraMap (integers l E.1) (PadicAlgCl l) (κ z) =
      algebraMap ℚ_[l] _ (PadicInt.Coe.ringHom z))
    [Module (integers l E.1) M] [Module.Finite (integers l E.1) M]
    [ContinuousSMul (integers l E.1) M] [IsModuleTopology (integers l E.1) M] [IsIso θ]
    (hθ : ∀ (U : S.ProEt) [IsAffine U.left] (r : integers l E.1) (m : C(U.left, M)),
      θ.hom.app (op U) (ULift.up (r • m)) = (upperStarRightDerivedSections g p i U).map
        (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ.hom.app (op U) (ULift.up m)))
    (hψι : ∀ (U : S.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
      integralLatticeSections g p i E θ U (f • m) = AdicSheaf.sectionAct _
        (ULift.up (AdicSheaf.ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f))
        (integralLatticeSections g p i E θ U m)) :
    IsAdicLisseSheaf (adicRightDerivedLowerStarUnit l g i) :=
  IsAdicLisseSheaf.of_bijective_tensorSections p hι (algebraMap_integers_mem l E.1) hκ hικ
    (integralLatticeSections g p i E θ) (fun _ _ f m ↦ AdicSheaf.sectionsOfHom_comp _ _ f m) hψι
    fun U _ ↦ bijective_tensorSections_integralLatticeSections g p i E θ U hι
      ((ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
        ((((sheafToPresheaf _ _).mapIso (asIso θ)).app (op U)).hom)))) (hθ U) hψι

end AlgebraicGeometry.ProEtale
