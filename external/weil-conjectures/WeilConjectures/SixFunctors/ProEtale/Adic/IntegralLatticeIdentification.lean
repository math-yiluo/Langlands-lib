/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective

/-!
# Lisse sheaves from integral identifications along arbitrary morphisms

This file generalises `WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective`
from `p^* Rⁱg_* ℚ̄_ℓ,T`, `p` weakly étale, to any sheaf `F` of `ℚ̄_ℓ`-modules on `S` with an
identification `e` of its underlying abelian sheaf with `q^* Rⁱg_* ℚ̄_ℓ,T` for an arbitrary
`q : S ⟶ Y`, compatible with the scalars (`AlgebraicGeometry.ProEtale.AdicAbIdentification`).
The typical case is `F = p^* j^* Rⁱg_* ℚ̄_ℓ,T` and `q = p ≫ j` for a stratum `j` and a weakly étale
cover `p` of `S` (`AlgebraicGeometry.ProEtale.AdicAbIdentification.upperStar`).

Given an integral identification `θ : C(-, M) ⟶ q^* Rⁱg_* 𝒪_{E,T}`, the maps
`ψ_U : C(U, M) → F(U)` are `θ` followed by `q^* Rⁱg_* 𝒪_{E,T} ⟶ q^* Rⁱg_* ℚ̄_ℓ,T ≅ F`
(`AlgebraicGeometry.ProEtale.integralLatticeSectionsOfIdentification`), and:

- `AlgebraicGeometry.ProEtale.bijective_tensorSections_integralLatticeSectionsOfIdentification`:
  if `θ` is bijective and `𝒪_E`-linear on sections over a qcqs `W`, then
  `ℚ̄_ℓ ⊗_{𝒪_E} C(W, M) → F(W)` is bijective;
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_integralLatticeIdentification`: a sheaf `F₀`
  whose pullback along a weakly étale surjective quasi-compact `p` has such an identification,
  with `θ` an isomorphism and `M` finite over `𝒪_E`, is lisse, provided the maps `ψ_U` are
  `C(U, 𝒪_E)`-semilinear.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl TensorProduct

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T Y S : Scheme.{u}} {g : T ⟶ Y} {i : ℕ} {q : S ⟶ Y}
  {F : AdicSheaf l S} (e : AdicAbIdentification g i F q) (E : FiniteIntermediateField l)
  {M : Type} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  (θ : continuousMapAddSheaf S M ⟶ (q)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))

/-- The morphism `C(-, M) ⟶ q^* Rⁱg_* 𝒪_{E,T} ⟶ q^* Rⁱg_* ℚ̄_ℓ,T ≅ F` of abelian sheaves attached
to an integral identification `θ` and an identification `e`. -/
noncomputable def integralLatticeHomOfIdentification :
    continuousMapAddSheaf S M ⟶ (sheafCompose (Scheme.ProEt.topology S)
      (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj F.X :=
  θ ≫ (q)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
    (adicConstantSheafLeg T l E 0)) ≫ e.iso.inv

/-- The maps `ψ_U : C(U, M) → F(U)` attached to an integral identification `θ`. -/
noncomputable abbrev integralLatticeSectionsOfIdentification (U : S.ProEt) :
    C(U.left, M) →+ F.X.obj.obj (op U) :=
  AdicSheaf.sectionsOfHom _ (integralLatticeHomOfIdentification e E θ) U

lemma iso_hom_integralLatticeSectionsOfIdentification (U : S.ProEt) (m : C(U.left, M)) :
    e.iso.hom.hom.app (op U) (integralLatticeSectionsOfIdentification e E θ U m) =
      (upperStarRightDerivedSections g q i U).map (adicConstantSheafLeg T l E 0)
        (θ.hom.app (op U) (ULift.up m)) := by
  have h : integralLatticeHomOfIdentification e E θ ≫ e.iso.hom =
      θ ≫ (q)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
        (adicConstantSheafLeg T l E 0)) := by
    simp [integralLatticeHomOfIdentification]
  have h := congrArg (fun φ ↦ φ.hom.app (op U)) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  rw [AdicSheaf.sectionsOfHom_apply, ← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]
  rfl

include e in
lemma AdicAbIdentification.iso_hom_app_smul (U : S.ProEt) (c : ULift.{u + 1} (PadicAlgCl l))
    (x : F.X.obj.obj (op U)) :
    e.iso.hom.hom.app (op U) (c • x) =
      (upperStarRightDerivedSections g q i U).map ((weilCoefficientsForgetAb l T).map
        ((weilSmulNatTrans l T c).app (adicConstantSheaf l T)))
        (e.iso.hom.hom.app (op U) x) := by
  have h := congrArg (fun φ ↦ φ.hom.app (op U)) (e.hom_smul c)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  exact (ConcreteCategory.congr_hom h x).trans rfl

section Bijective

variable [QuasiCompact g] [QuasiSeparated g]
  (W : S.ProEt) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
  [TopologicalSpace (integers l E.1)] [Module (integers l E.1) M]
  [ContinuousSMul (integers l E.1) M]
  (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
  (hθW : Function.Bijective (θ.hom.app (op W)))
  (hθ : ∀ (r : integers l E.1) (m : C(W.left, M)),
    θ.hom.app (op W) (ULift.up (r • m)) = (upperStarRightDerivedSections g q i W).map
      (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ.hom.app (op W) (ULift.up m)))
  (hψι : ∀ (U : S.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
    integralLatticeSectionsOfIdentification e E θ U (f • m) = AdicSheaf.sectionAct _
      (ULift.up (AdicSheaf.ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f))
      (integralLatticeSectionsOfIdentification e E θ U m))

include hθ in
omit [QuasiCompact g] [QuasiSeparated g] [CompactSpace W.left] [QuasiSeparatedSpace W.left] in
/-- `ψ(ℓ⁻ⁿ o ⊗ m)` corresponds to the image of `o ⊗ m ∈ 𝒪_F ⊗ C(W, M) = Γ(W, q^* Rⁱg_* 𝒪_{F,T})`
under `ℓ⁻ⁿ : 𝒪_{F,T} ⟶ ℚ̄_ℓ,T`. -/
lemma tensorSections_stageTensorMap_ofIdentification (F' : FiniteIntermediateFieldOver l E.1)
    (n : ℕ) (τ : integersSubalgebraFamily l E.1 F' ⊗[integers l E.1] C(W.left, M)) :
    e.iso.hom.hom.app (op W)
        (AdicSheaf.tensorSections _ hι (algebraMap_integers_mem l E.1)
          (integralLatticeSectionsOfIdentification e E θ) hψι W
          (Subalgebra.stageTensorMap (l : integers l E.1) (integersSubalgebraFamily l E.1) F' n
            τ)) =
      (upperStarRightDerivedSections g q i W).map (adicConstantSheafLeg T l F'.1 n)
        (stageMap _ E (integralLatticeSectionsEquiv g q i E θ W hθW) hθ F' τ) := by
  induction τ using TensorProduct.inductionOn with
  | add τ τ' hτ hτ' => simp only [map_add, hτ, hτ']
  | tmul o m =>
    rw [Subalgebra.stageTensorMap_tmul, AdicSheaf.tensorSections_tmul,
      AdicAbIdentification.iso_hom_app_smul e]
    refine (congrArg (fun y ↦ (upperStarRightDerivedSections g q i W).map
      ((weilCoefficientsForgetAb l T).map ((weilSmulNatTrans l T _).app
        (adicConstantSheaf l T))) y)
      (iso_hom_integralLatticeSectionsOfIdentification e E θ W m)).trans ?_
    rw [stageMap_tmul, algebraMap_natCast_pow_inv_mul_eq]
    have key := congrArg (fun φ ↦ (upperStarRightDerivedSections g q i W).map φ
      (θ.hom.app (op W) (ULift.up m)))
      (padicIntegersSheafMulOfLE_comp_adicConstantSheafLeg (X := T) (E := E) (F := F'.1) F'.2
        (integersSubalgebraFamilyEquiv E F' o) n)
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at key
    exact key.symm

include hθ hθW in
/-- **`ℚ̄_ℓ ⊗_{𝒪_E} C(W, M) = F(W)`** for `W` quasi-compact and quasi-separated: the map
`c ⊗ m ↦ c • ψ(m)` attached to an `𝒪_E`-linear integral identification
`θ : C(-, M) ≅ q^* Rⁱg_* 𝒪_{E,T}` is bijective. -/
theorem bijective_tensorSections_integralLatticeSectionsOfIdentification :
    Function.Bijective (AdicSheaf.tensorSections _ hι (algebraMap_integers_mem l E.1)
      (integralLatticeSectionsOfIdentification e E θ) hψι W) := by
  let Φ := upperStarRightDerivedSections g q i W
  let θW := integralLatticeSectionsEquiv g q i E θ W hθW
  have hB : Function.Bijective (e.iso.hom.hom.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      ((((sheafToPresheaf _ _).mapIso e.iso).app (op W)).hom)))
  refine (hB.of_comp_iff' _).1 ?_
  refine bijective_of_integersSubalgebra (E := E.1)
    ((ConcreteCategory.hom (e.iso.hom.hom.app (op W))).comp
      (AdicSheaf.tensorSections _ hι (algebraMap_integers_mem l E.1)
        (integralLatticeSectionsOfIdentification e E θ) hψι W)) (fun b ↦ ?_)
    (fun F' n τ hτ ↦ ?_)
  · obtain ⟨F₀, hle, n, y, rfl⟩ := exists_sections_adicConstantSheafLeg_eq_of_le g q i W l E b
    obtain ⟨τ, rfl⟩ := (bijective_stageMap Φ E θW hθ ⟨F₀, hle⟩).2 y
    exact ⟨⟨F₀, hle⟩, n, τ,
      tensorSections_stageTensorMap_ofIdentification e E θ W hι hθW hθ hψι _ n τ⟩
  · have hτ' := (tensorSections_stageTensorMap_ofIdentification e E θ W hι hθW hθ hψι F' n
      τ).symm.trans hτ
    have key := exists_pow_smul_map_eq_zero_of_adicConstantSheafLeg g q i W l
      (E := F'.1) (n := n) (stageMap Φ E θW hθ F' τ)
    have hτ'' : Φ.map (adicConstantSheafLeg T l F'.1 n) (stageMap Φ E θW hθ F' τ) = 0 := hτ'
    refine (key hτ'').elim fun F'' hF ↦ hF.elim fun h hm' ↦ hm'.elim fun m hm ↦ ?_
    let F₁ : FiniteIntermediateFieldOver l E.1 := ⟨F'', F'.2.trans h⟩
    have hs : integersSubalgebraFamily l E.1 F' ≤ integersSubalgebraFamily l E.1 F₁ :=
      integersSubalgebra_mono F'.2 h
    refine ⟨F₁, hs, m, (bijective_stageMap Φ E θW hθ F₁).1 ?_⟩
    have e1 : ((l : integers l E.1) ^ m) •
        (Subalgebra.inclusion hs).toLinearMap.rTensor C(W.left, M) τ =
          (l ^ m) • (Subalgebra.inclusion hs).toLinearMap.rTensor C(W.left, M) τ :=
      natCast_pow_smul_eq_nsmul _ _ _
    refine (congrArg _ e1).trans ((map_nsmul _ _ _).trans ?_)
    exact (congrArg _ (stageMap_rTensor Φ E θW hθ h hs τ)).trans (hm.trans (map_zero _).symm)

end Bijective

/-- **A sheaf whose pullback to a cover is identified with `q^* Rⁱg_* ℚ̄_ℓ,T` is lisse**, as soon
as there is an `𝒪_E`-linear integral identification `θ : C(-, M) ≅ q^* Rⁱg_* 𝒪_{E,T}` with `M` a
finite `𝒪_E`-module, whose induced maps `ψ_U : C(U, M) → (p^* F₀)(U)` are
`C(U, 𝒪_E)`-semilinear. Here `p : S ⟶ S₀` is weakly étale, surjective and quasi-compact, and
`q : S ⟶ Y` is arbitrary. -/
theorem IsAdicLisseSheaf.of_integralLatticeIdentification [QuasiCompact g] [QuasiSeparated g]
    {S₀ : Scheme.{u}} (p : S ⟶ S₀) [WeaklyEtale p] [Surjective p] [QuasiCompact p]
    {F₀ : AdicSheaf l S₀} (e : AdicAbIdentification g i ((p)^*ᵃ[l].obj F₀) q)
    (θ : continuousMapAddSheaf S M ⟶ (q)^*[Ab.{u + 1}].obj
      (((g)_*[Ab.{u + 1}].rightDerived i).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))
    [TopologicalSpace (integers l E.1)] [IsTopologicalRing (integers l E.1)]
    (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
    {κ : ℤ_[l] →+* integers l E.1} (hκ : Continuous κ)
    (hικ : ∀ z, algebraMap (integers l E.1) (PadicAlgCl l) (κ z) =
      algebraMap ℚ_[l] _ (PadicInt.Coe.ringHom z))
    [Module (integers l E.1) M] [Module.Finite (integers l E.1) M]
    [ContinuousSMul (integers l E.1) M] [IsModuleTopology (integers l E.1) M] [IsIso θ]
    (hθ : ∀ (U : S.ProEt) [IsAffine U.left] (r : integers l E.1) (m : C(U.left, M)),
      θ.hom.app (op U) (ULift.up (r • m)) = (upperStarRightDerivedSections g q i U).map
        (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ.hom.app (op U) (ULift.up m)))
    (hψι : ∀ (U : S.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
      integralLatticeSectionsOfIdentification e E θ U (f • m) = AdicSheaf.sectionAct _
        (ULift.up (AdicSheaf.ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f))
        (integralLatticeSectionsOfIdentification e E θ U m)) :
    IsAdicLisseSheaf F₀ :=
  IsAdicLisseSheaf.of_bijective_tensorSections p hι (algebraMap_integers_mem l E.1) hκ hικ
    (integralLatticeSectionsOfIdentification e E θ)
    (fun _ _ f m ↦ AdicSheaf.sectionsOfHom_comp _ _ f m) hψι
    fun U _ ↦ bijective_tensorSections_integralLatticeSectionsOfIdentification e E θ U hι
      ((ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
        ((((sheafToPresheaf _ _).mapIso (asIso θ)).app (op U)).hom)))) (hθ U) hψι

end AlgebraicGeometry.ProEtale
