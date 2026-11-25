/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import all WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenOrdinaryScalarComparison
/-! # Restriction of the actual scalar tensor construction
Source: Stacks Project, sites-cohomology.tex, Tag 06YY.
(blueprint: lem-sf-clopen-scalar-raw-restriction-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open SheafOfModules SheafOfModules.StrictScalarHom
open ProEt.ClopenScalar ProEt.ClopenData
open scoped ChangeOfRings
attribute [local instance 20000] SheafOfModules.systemRingHasDerived
  SheafOfModules.instAbelian

private instance (priority := 20000) sfScalarSiteSmall (Z : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} Z.ProEt := essentiallySmallSelf _

private instance (priority := 20000) sfScalarAbSheafify (Z : Scheme.{t}) :
    HasSheafify (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} Z
private instance (priority := 20000) sfScalarAbLocallyBijective (Z : Scheme.{t}) :
    (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} Z

private theorem sfSystemTensor_eq
    {Z : Scheme.{t}} {R S : Sheaf (ProEt.topology Z) CommRingCat.{max u (t + 1)}}
    {a : R ⟶ S} (A : SystemScalarModel.{t + 1, t, max u (t + 1)} a)
    (M : SheafOfModules.{max u (t + 1)}
      (derivedChangeRingIndependentCoefficients (ProEt.topology Z) R))
    (V : Z.ProEtᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    systemModelTmul A.model M V s x =
      (eqToHom (A.model.obj_eq M).symm).val.app V
        (SheafOfModules.SuccessiveDerivedQuotient.pure a M V s x) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1}
    (𝟙 (derivedChangeRingIndependentCoefficients (ProEt.topology Z) S).obj)).unit.app
      (changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} (J := ProEt.topology Z) a M)
  change s • (eqToHom (A.model.obj_eq M).symm).val.app V
      (η.app V ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) =
    (eqToHom (A.model.obj_eq M).symm).val.app V
      (η.app V (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))
  rw [← ((eqToHom (A.model.obj_eq M).symm).val.app V).hom.map_smul]
  rw [← (η.app V).hom.map_smul]
  congr 2
  change (s * 1) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x =
    s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x
  rw [mul_one]

private def sfOrdinaryRestrictionBack
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (G : clopenTensorModules.{t, u} R ⥤ clopenTensorModules.{t, u} S)
    (hobj : ∀ M, G.obj M = changeOfRings a M)
    (hmap : ∀ {M Q} (f : M ⟶ Q), G.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom a M f ≫ eqToHom (hobj Q).symm)
    (H : clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R) ⥤
      clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj S))
    (kobj : ∀ M, H.obj M = changeOfRings ((clopenTensorRings.{t, u} j).map a) M)
    (kmap : ∀ {M Q} (f : M ⟶ Q), H.map f =
      eqToHom (kobj M) ≫ changeOfRingsHom ((clopenTensorRings.{t, u} j).map a) M f ≫
        eqToHom (kobj Q).symm) :
    clopenTensorRestriction.{t, u} j R ⋙ H ≅ G ⋙ clopenTensorRestriction.{t, u} j S := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    (integralCoefficientAbSheafify.{t, u} X).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
    (integralCoefficientAbSheafify.{t, u} Y).isRightAdjoint
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (ProEt.topology Y) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let L := clopenTensorRestriction.{t, u} j R
  let N := clopenTensorRestriction.{t, u} j S
  let back (M : clopenTensorModules.{t, u} R) :
      H.obj (L.obj M) ≅ N.obj (G.obj M) :=
    eqToIso (kobj (L.obj M)) ≪≫
      oldScalarBackIso (J₀ := ProEt.topology Y) F a M ≪≫
        N.mapIso (eqToIso (hobj M).symm)
  refine NatIso.ofComponents back ?_
  intro M Q g
  dsimp only [back, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  change H.map (L.map g) ≫ eqToHom (kobj (L.obj Q)) ≫
      (oldScalarBackIso (J₀ := ProEt.topology Y) F a Q).hom ≫
      N.map (eqToHom (hobj Q).symm) =
    (eqToHom (kobj (L.obj M)) ≫
      (oldScalarBackIso (J₀ := ProEt.topology Y) F a M).hom ≫
      N.map (eqToHom (hobj M).symm)) ≫
        N.map (G.map g)
  rw [kmap, hmap]
  have h := oldScalarBackIso_natural (J₀ := ProEt.topology Y) F a g
  simp only [Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  simp only [← Functor.map_comp_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have ht := congrArg (fun z ↦ eqToHom (kobj (L.obj M)) ≫ z ≫
    N.map (eqToHom (hobj Q).symm)) h
  dsimp only [moduleRestrictionF, clopenTensorRestriction, ProEt.clopenModuleRestriction,
    pullRing, clopenTensorRings, F, L, N] at ht ⊢
  simpa only [Category.assoc] using ht

private theorem sfOrdinaryRestrictionBack_tensor
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (G : clopenTensorModules.{t, u} R ⥤ clopenTensorModules.{t, u} S)
    (hobj : ∀ M, G.obj M = changeOfRings a M)
    (hmap : ∀ {M Q} (f : M ⟶ Q), G.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom a M f ≫ eqToHom (hobj Q).symm)
    (H : clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R) ⥤
      clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj S))
    (kobj : ∀ M, H.obj M = changeOfRings ((clopenTensorRings.{t, u} j).map a) M)
    (kmap : ∀ {M Q} (f : M ⟶ Q), H.map f =
      eqToHom (kobj M) ≫ changeOfRingsHom ((clopenTensorRings.{t, u} j).map a) M f ≫
        eqToHom (kobj Q).symm)
    (M : clopenTensorModules.{t, u} R) (V : Y.ProEtᵒᵖ)
    (s : S.obj.obj ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).op.obj V))
    (x : M.val.obj ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).op.obj V)) :
    ((sfOrdinaryRestrictionBack.{t, u} j a G hobj @hmap H kobj @kmap).hom.app M).val.app V
      ((eqToHom (kobj ((clopenTensorRestriction.{t, u} j R).obj M)).symm).val.app V
        (SheafOfModules.SuccessiveDerivedQuotient.pure ((clopenTensorRings.{t, u} j).map a)
          ((clopenTensorRestriction.{t, u} j R).obj M) V s x)) =
      (eqToHom (hobj M).symm).val.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj V)
          (SheafOfModules.SuccessiveDerivedQuotient.pure a M
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj V) s x) := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    (integralCoefficientAbSheafify.{t, u} X).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
    (integralCoefficientAbSheafify.{t, u} Y).isRightAdjoint
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (ProEt.topology Y) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let L := clopenTensorRestriction.{t, u} j R
  let N := clopenTensorRestriction.{t, u} j S
  unfold sfOrdinaryRestrictionBack
  dsimp only [NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, eqToIso.hom]
  let hq := kobj (L.obj M)
  have hc := congrArg (fun f ↦ f.val.app V
    (SheafOfModules.SuccessiveDerivedQuotient.pure ((clopenTensorRings.{t, u} j).map a)
      (L.obj M) V s x)) (eqToHom_trans hq.symm hq)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at hc
  change (N.map (eqToHom (hobj M).symm)).val.app V
    ((oldScalarBackIso (J₀ := ProEt.topology Y) F a M).hom.val.app V
      ((eqToHom hq).val.app V ((eqToHom hq.symm).val.app V
        (SheafOfModules.SuccessiveDerivedQuotient.pure
          ((clopenTensorRings.{t, u} j).map a) (L.obj M) V s x)))) = _
  rw [hc]
  exact congrArg (fun z ↦ (N.map (eqToHom (hobj M).symm)).val.app V z)
    (oldScalarBackIso_pure (J₀ := ProEt.topology Y) F a M V s x)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private def sfClopenScalarRawBack
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens) (n : ℕ)
    (A : SystemScalarModel.{t + 1, t, max u (t + 1)} (J := ProEt.topology U.toScheme)
      ((clopenTensorRings.{t, u} U.ι).map
        (completedIntegralCommRingProjectionUnrestricted l E T n))) :
    clopenTensorRestriction.{t, u} U.ι
        (completedIntegralCommRingSheafUnrestricted l E T) ⋙ A.model.E ≅
      scalarReductionExtension l E T n ⋙
        clopenTensorRestriction.{t, u} U.ι (integralCoefficientCommRingSheaf l E T n) := by
  exact sfOrdinaryRestrictionBack.{t, u} U.ι
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (scalarReductionExtension l E T n)
    (scalarReductionExistence l E T n).choose_spec.choose
    (scalarReductionExistence l E T n).choose_spec.choose_spec.choose
    A.model.E A.model.obj_eq A.model.map_eq

private theorem sfClopenScalarRawBack_tensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens) (n : ℕ)
    (A : SystemScalarModel.{t + 1, t, max u (t + 1)} (J := ProEt.topology U.toScheme)
      ((clopenTensorRings.{t, u} U.ι).map
        (completedIntegralCommRingProjectionUnrestricted l E T n)))
    (M : scalarReductionSource l E T) (V : U.toScheme.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E T n).obj.obj
      ((sfClopenSiteInclusion U).op.obj V))
    (x : M.val.obj ((sfClopenSiteInclusion U).op.obj V)) :
    (((sfClopenScalarRawBack.{t, u} l E T U n A).hom.app M).val.app V)
      (systemModelTmul A.model
        ((clopenTensorRestriction.{t, u} U.ι
          (completedIntegralCommRingSheafUnrestricted l E T)).obj M) V s x) =
      unrestrictedTowerTensorSection l E T n M ((sfClopenSiteInclusion U).op.obj V) s x := by
  rw [sfSystemTensor_eq.{t, u}]
  exact sfOrdinaryRestrictionBack_tensor.{t, u} U.ι
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (scalarReductionExtension l E T n)
    (scalarReductionExistence l E T n).choose_spec.choose
    (scalarReductionExistence l E T n).choose_spec.choose_spec.choose
    A.model.E A.model.obj_eq A.model.map_eq M V s x

attribute [local irreducible] sfClopenScalarRawBack

/-- Restriction of a sheafified scalar tensor, transported through the recorded model.

Source: Stacks Project, sites-modules.tex, Tags 03EL and 03CY.
(blueprint: lem-sf-clopen-scalar-raw-restriction-comparison).

Proof: cocontinuity identifies the restriction of the tensor-presheaf sheafification
with the sheafification of the restricted tensor presheaf. Transport the comparison
through the two functors' object and map equations. The sheafification-unit equation
sends each pure tensor to the same pure tensor. Naturality follows from the tensor
map equations; the inverse comes from the inverse sheafification comparison. -/
theorem sf_clopen_scalar_raw_restriction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens) (n : ℕ)
    (A : SystemScalarModel.{t + 1, t, max u (t + 1)} (J := ProEt.topology U.toScheme)
      ((clopenTensorRings.{t, u} U.ι).map
        (completedIntegralCommRingProjectionUnrestricted l E T n))) :
    ∃ back :
    clopenTensorRestriction.{t, u} U.ι
        (completedIntegralCommRingSheafUnrestricted l E T) ⋙ A.model.E ≅
      scalarReductionExtension l E T n ⋙
        clopenTensorRestriction.{t, u} U.ι (integralCoefficientCommRingSheaf l E T n),
      ∀ (M : scalarReductionSource l E T) (V : U.toScheme.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E T n).obj.obj
          ((sfClopenSiteInclusion U).op.obj V))
        (x : M.val.obj ((sfClopenSiteInclusion U).op.obj V)),
      ((back.hom.app M).val.app V)
        (systemModelTmul A.model
          ((clopenTensorRestriction.{t, u} U.ι
            (completedIntegralCommRingSheafUnrestricted l E T)).obj M) V s x) =
        unrestrictedTowerTensorSection l E T n M ((sfClopenSiteInclusion U).op.obj V)
          s x := by
  let back := sfClopenScalarRawBack.{t, u} l E T U n A
  refine ⟨back, ?_⟩
  intro M V s x
  exact sfClopenScalarRawBack_tensor.{t, u} l E T U n A M V s x

end WeilConjectures
