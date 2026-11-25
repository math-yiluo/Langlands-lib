/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi

import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Composition of rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469 (blueprint: lem-weil-scalar-extension-composition).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u r v

open CategoryTheory

namespace WeilConjectures

section ScalarProofContext

attribute [-instance] integralOperationsCommHasDerivedCategory
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralScalarExtension

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

private instance scalarSiteSmall : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private instance scalarSiteSheafify :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  inferInstance

private instance scalarSiteLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := inferInstance

private theorem quotientScalar_id (n : ℕ) :
    integralScalarQuotientSheafMap.{u, u} l E E (AlgHom.id (Padic l) E) Y n = 𝟙 _ := by
  unfold integralScalarQuotientSheafMap integralCoefficientCommRingSheaf
  rw [← (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))]
  congr 1
  ext x
  obtain ⟨x⟩ := x
  induction x using Quotient.inductionOn' with
  | h x => rfl

private theorem completedScalar_id :
    integralCompletedScalarMap l E E (AlgHom.id (Padic l) E) Y = 𝟙 _ := by
  apply (integralCompletedScalarMap_existsUnique l E E (AlgHom.id (Padic l) E) Y).unique
  · exact (integralCompletedScalarMap_existsUnique l E E
      (AlgHom.id (Padic l) E) Y).exists.choose_spec
  · intro n
    simp only [Category.id_comp, integralScalarRho, quotientScalar_id, Category.comp_id]

private theorem quotientScalar_comp
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (j : L →ₐ[Padic l] M) (n : ℕ) :
    integralScalarQuotientSheafMap.{u, u} l E L ι Y n ≫
      integralScalarQuotientSheafMap.{u, u} l L M j Y n =
        integralScalarQuotientSheafMap.{u, u} l E M (j.comp ι) Y n := by
  unfold integralScalarQuotientSheafMap
  rw [← Functor.map_comp]
  congr 1
  ext x
  obtain ⟨x⟩ := x
  induction x using Quotient.inductionOn' with
  | h x => rfl

private theorem completedScalar_comp
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (j : L →ₐ[Padic l] M) :
    integralCompletedScalarMap l E L ι Y ≫ integralCompletedScalarMap l L M j Y =
      integralCompletedScalarMap l E M (j.comp ι) Y := by
  apply (integralCompletedScalarMap_existsUnique l E M (j.comp ι) Y).unique
  · intro n
    have hLM : integralCompletedScalarMap l L M j Y ≫
        completedIntegralCommRingProjectionUnrestricted l M Y n =
        integralScalarRho l L M j Y n :=
      (integralCompletedScalarMap_existsUnique l L M j Y).exists.choose_spec n
    have hEL : integralCompletedScalarMap l E L ι Y ≫
        completedIntegralCommRingProjectionUnrestricted l L Y n =
        integralScalarRho l E L ι Y n :=
      (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec n
    rw [Category.assoc, hLM]
    unfold integralScalarRho
    rw [← Category.assoc, hEL]
    unfold integralScalarRho
    rw [Category.assoc, quotientScalar_comp]
  · exact (integralCompletedScalarMap_existsUnique l E M (j.comp ι) Y).exists.choose_spec

/-- The sheafified pure tensor in the ordinary finite free scalar extension.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryTensorSection
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U) (x : N.val.obj U) :
    ((integralOrdinaryScalar l E L ι Y).obj N).val.obj U :=
  (eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose N).symm).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (integralCompletedScalarMap l E L ι Y) N).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))

attribute [local irreducible] integralOrdinaryScalar

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

section OrdinaryCoherence
attribute [local irreducible] integralCompletedScalarMap integralOrdinaryTensorSection
section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
variable
  (F : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
  (hm : ∀ {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N'), F.map f = eqToHom (h N) ≫
    SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (h N').symm)
private noncomputable def tensorSection
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :=
  (eqToHom (h N).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
private theorem tensorSection_ext
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (f g : F.obj N ⟶ T)
    (he : ∀ (U : Cᵒᵖ) (x : N.val.obj U),
      f.val.app U (tensorSection φ F h N U 1 x) =
        g.val.app U (tensorSection φ F h N U 1 x)) : f = g := by
  let e := eqToIso (h N)
  apply (cancel_epi e.inv).mp
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  ext1 U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact he U x

include hm in
private theorem tensorSection_map
    {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N') (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : N.val.obj U) :
    (F.map f).val.app U (tensorSection φ F h N U s x) =
      tensorSection φ F h N' U s (f.val.app U x) := by
  let a : SheafOfModules.changeOfRingsPresheaf φ N ⟶
      SheafOfModules.changeOfRingsPresheaf φ N' :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ N f }
  have hn := congrArg (fun t ↦ t.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
    (CategoryTheory.toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map a))
  rw [hm]
  change (eqToHom (h N').symm).val.app U
    ((SheafOfModules.changeOfRingsHom φ N f).val.app U
      ((eqToHom (h N)).val.app U (tensorSection φ F h N U s x))) = _
  dsimp only [tensorSection]
  have hc {A B : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
      (e : A = B) (z : B.val.obj U) :
      (eqToHom e).val.app U ((eqToHom e.symm).val.app U z) = z := by
    cases e
    rfl
  rw [hc]
  congr 1
  exact hn.symm

private theorem tensorSection_smul
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (c b : S.obj.obj U) (x : N.val.obj U) :
    tensorSection φ F h N U (c * b) x = c • tensorSection φ F h N U b x := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf φ N)
  have ht := (ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom
    (M := N.val.obj U) c b x).symm
  have hη := (η.app U).hom.map_smul c (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := ((eqToHom (h N).symm).val.app U).hom.map_smul c
    ((η.app U) (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  unfold tensorSection
  with_unfolding_all
    exact (congrArg (fun z ↦ (eqToHom (h N).symm).val.app U z)
      ((congrArg (fun z ↦ (η.app U) z) ht).trans hη)).trans he

include hm in
private noncomputable def tensorPresentation [EssentiallySmall.{r} C] :
    F ≅ CategoryTheory.CochainPullback.extensionFunctor φ :=
  NatIso.ofComponents (fun N ↦ eqToIso (h N)) (by
    intro N N' f
    rw [hm]
    simp [CategoryTheory.CochainPullback.extensionFunctor])

private theorem tensorAdjunction_unit [EssentiallySmall.{r} C]
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : N.val.obj U) :
    ((((CategoryTheory.CochainPullback.extensionAdjunction φ).ofNatIsoLeft
      (tensorPresentation φ F h hm).symm).unit.app N).val.app U x) =
        tensorSection φ F h N U 1 x := by
  have hunit := (Classical.choose_spec
    (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique φ)).1 N U x
  rw [Adjunction.ofNatIsoLeft_unit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    tensorPresentation, Iso.symm_hom, NatIso.ofComponents_inv_app, eqToIso.inv]
  change (eqToHom (h N).symm).val.app U
    (((CategoryTheory.CochainPullback.extensionAdjunction φ).unit.app N).val.app U x) = _
  erw [hunit]
  unfold CategoryTheory.CochainPullback.extensionTmul tensorSection
  have hη := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
    (SheafOfModules.changeOfRingsPresheaf φ N)
  with_unfolding_all exact congrArg (fun f ↦ (eqToHom (h N).symm).val.app U
    (f.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) hη

attribute [local irreducible] tensorSection

private theorem tensorSection_pentagon
    {T V : Sheaf J CommRingCat.{r}}
    (ψ : S ⟶ T) (ξ : T ⟶ V) (κ : R ⟶ T) (ζ : S ⟶ V) (μ : R ⟶ V)
    (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (H : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj V))
    (FG : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (GH : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj V))
    (FGH : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj V))
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings ψ N)
    (hH : ∀ N, H.obj N = SheafOfModules.changeOfRings ξ N)
    (hFG : ∀ N, FG.obj N = SheafOfModules.changeOfRings κ N)
    (hGH : ∀ N, GH.obj N = SheafOfModules.changeOfRings ζ N)
    (hFGH : ∀ N, FGH.obj N = SheafOfModules.changeOfRings μ N)
    (hmH : ∀ {N N'} (f : N ⟶ N'), H.map f = eqToHom (hH N) ≫
      SheafOfModules.changeOfRingsHom ξ N f ≫ eqToHom (hH N').symm)
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (ha : ∀ N U s x, (a.inv.app N).val.app U (tensorSection κ FG hFG N U s x) =
      tensorSection ψ G hG _ U s (tensorSection φ F h N U 1 x))
    (hb : ∀ N U s x, (b.inv.app N).val.app U (tensorSection μ FGH hFGH N U s x) =
      tensorSection ξ H hH _ U s (tensorSection κ FG hFG N U 1 x))
    (hc : ∀ N U s x, (c.inv.app N).val.app U (tensorSection ζ GH hGH N U s x) =
      tensorSection ξ H hH _ U s (tensorSection ψ G hG N U 1 x))
    (hd : ∀ N U s x, (d.inv.app N).val.app U (tensorSection μ FGH hFGH N U s x) =
      tensorSection ζ GH hGH _ U s (tensorSection φ F h N U 1 x)) :
    Functor.isoWhiskerRight a H ≪≫ b = Functor.isoWhiskerLeft F c ≪≫ d := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply NatTrans.ext
  funext N
  apply tensorSection_ext μ FGH hFGH
  intro U x
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change (H.map (a.inv.app N)).val.app U
    ((b.inv.app N).val.app U (tensorSection μ FGH hFGH N U 1 x)) = _
  rw [hb, tensorSection_map ξ H hH hmH, ha]
  change _ = (c.inv.app (F.obj N)).val.app U
    ((d.inv.app N).val.app U (tensorSection μ FGH hFGH N U 1 x))
  rw [hd, hc]
  rfl

private theorem tensorSection_one
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    tensorSection φ F h N U s x = s • tensorSection φ F h N U 1 x := by
  simpa only [mul_one] using tensorSection_smul φ F h N U s 1 x

private theorem tensorComp_existsUnique
    {T : Sheaf J CommRingCat.{r}} (ψ : S ⟶ T) (κ : R ⟶ T)
    (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (H : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings ψ N)
    (hH : ∀ N, H.obj N = SheafOfModules.changeOfRings κ N)
    (adjG : G ⊣ CategoryTheory.CochainPullback.restrictionFunctor ψ)
    (hu : ∀ N U x, ((adjG.unit.app N).val.app U x) = tensorSection ψ G hG N U 1 x)
    (a : F ⋙ G ≅ H)
    (ha : ∀ N U x, (a.hom.app N).val.app U
      (tensorSection ψ G hG _ U 1 (tensorSection φ F h N U 1 x)) =
        tensorSection κ H hH N U 1 x) :
    ∃! a : F ⋙ G ≅ H, ∀ N U (c : T.obj.obj U) (b : S.obj.obj U) (x : N.val.obj U),
      (a.hom.app N).val.app U
        (tensorSection ψ G hG _ U c (tensorSection φ F h N U b x)) =
          tensorSection κ H hH N U (c * ψ.hom.app U b) x := by
  have hall (N : SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
      (c : T.obj.obj U)
      (b : S.obj.obj U) (x : N.val.obj U) :
      (a.hom.app N).val.app U
        (tensorSection ψ G hG _ U c
          (tensorSection φ F h N U b x)) =
        tensorSection κ H hH N U
          (c * ψ.hom.app U b) x := by
    rw [tensorSection_one ψ G hG _ U c,
      tensorSection_one φ F h N U b x]
    have hb : tensorSection ψ G hG _ U 1
        (b • tensorSection φ F h N U 1 x) =
        ψ.hom.app U b •
          tensorSection ψ G hG _ U 1
            (tensorSection φ F h N U 1 x) := by
      conv_lhs => rw [← hu]
      conv_rhs => rw [← hu]
      change _ = b •
        ((adjG.unit.app
          (F.obj N)).val.app U
            (tensorSection φ F h N U 1 x))
      exact map_smul
        ((adjG.unit.app
          (F.obj N)).val.app U).hom b _
    rw [hb]
    rw [map_smul, map_smul, ha, smul_smul,
      ← tensorSection_one κ H hH]
  refine ⟨a, hall, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply tensorSection_ext ψ
    G hG
  intro U y
  have hinner :
      (adjG.unit.app
        (F.obj N)) ≫
          (CategoryTheory.CochainPullback.restrictionFunctor
            ψ).map (a'.hom.app N) =
      (adjG.unit.app
        (F.obj N)) ≫
          (CategoryTheory.CochainPullback.restrictionFunctor
            ψ).map (a.hom.app N) := by
    apply tensorSection_ext φ
      F h
    intro V x
    change (a'.hom.app N).val.app V
      ((adjG.unit.app
        (F.obj N)).val.app V
          (tensorSection φ F h N V 1 x)) = _
    have hu := hu
      (F.obj N) V
        (tensorSection φ F h N V 1 x)
    exact (congrArg (fun z ↦ (a'.hom.app N).val.app V z) hu).trans
      ((ha' N V 1 1 x).trans ((hall N V 1 1 x).symm.trans
        (congrArg (fun z ↦ (a.hom.app N).val.app V z) hu.symm)))
  have hinner' := congrArg (fun f ↦ f.val.app U y) hinner
  change (a'.hom.app N).val.app U
    ((adjG.unit.app
      (F.obj N)).val.app U y) = _ at hinner'
  have hu := hu
    (F.obj N) U y
  exact (congrArg (fun z ↦ (a'.hom.app N).val.app U z) hu.symm).trans
    (hinner'.trans (congrArg (fun z ↦ (a.hom.app N).val.app U z) hu))

end

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
private theorem scalar_obj : ∀ N : integralTowerModules.{u, u} l E Y,
    (integralOrdinaryScalar l E L ι Y).obj N = SheafOfModules.changeOfRings
      (integralCompletedScalarMap l E L ι Y) N := by
  unfold integralOrdinaryScalar
  exact (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose

private theorem tensorSection_eq (N : integralTowerModules.{u, u} l E Y)
    (U : Y.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : N.val.obj U) :
    tensorSection (integralCompletedScalarMap l E L ι Y)
      (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y) N U s x =
      integralOrdinaryTensorSection l E L ι Y N U s x := by
  unfold tensorSection integralOrdinaryTensorSection integralOrdinaryScalar
  rfl

private theorem scalar_map {N N' : integralTowerModules.{u, u} l E Y} (f : N ⟶ N') :
    (integralOrdinaryScalar l E L ι Y).map f =
      eqToHom (scalar_obj l E L ι Y N) ≫
        SheafOfModules.changeOfRingsHom (integralCompletedScalarMap l E L ι Y) N f ≫
          eqToHom (scalar_obj l E L ι Y N').symm := by
  unfold integralOrdinaryScalar
  exact (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose f

private theorem scalar_map_tensor {N N' : integralTowerModules.{u, u} l E Y}
    (f : N ⟶ N') (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : N.val.obj U) :
    ((integralOrdinaryScalar l E L ι Y).map f).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U s x) =
      integralOrdinaryTensorSection l E L ι Y N' U s (f.val.app U x) := by
  have ht := tensorSection_map (integralCompletedScalarMap l E L ι Y)
      (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y)
      (scalar_map l E L ι Y) f U s x
  rw [tensorSection_eq, tensorSection_eq] at ht
  exact ht

variable
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

end OrdinaryCoherence

private theorem scalar_tensor_smul
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
    (c b : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : N.val.obj U) :
    integralOrdinaryTensorSection l E L ι Y N U (c * b) x =
      c • integralOrdinaryTensorSection l E L ι Y N U b x := by
  rw [← tensorSection_eq, ← tensorSection_eq]
  exact tensorSection_smul (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y) N U c b x

private theorem scalar_tensor_one
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : N.val.obj U) :
    integralOrdinaryTensorSection l E L ι Y N U b x =
      b • integralOrdinaryTensorSection l E L ι Y N U 1 x := by
  simpa only [mul_one] using scalar_tensor_smul l E L ι Y N U b 1 x

private noncomputable def scalarPresentation :
    integralOrdinaryScalar l E L ι Y ≅
      CategoryTheory.CochainPullback.extensionFunctor.{u + 1, u + 1, u}
        (integralCompletedScalarMap l E L ι Y) :=
  tensorPresentation (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y) (scalar_map l E L ι Y)

private noncomputable def scalarAdjunction :
    integralOrdinaryScalar l E L ι Y ⊣
      CategoryTheory.CochainPullback.restrictionFunctor.{u + 1, u + 1, u, u + 1}
        (integralCompletedScalarMap l E L ι Y) :=
  (CategoryTheory.CochainPullback.extensionAdjunction.{u + 1, u + 1, u}
    (integralCompletedScalarMap l E L ι Y)).ofNatIsoLeft (scalarPresentation l E L ι Y).symm

private theorem scalarAdjunction_unit
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ) (x : N.val.obj U) :
    ((scalarAdjunction l E L ι Y).unit.app N).val.app U x =
      integralOrdinaryTensorSection l E L ι Y N U 1 x := by
  rw [← tensorSection_eq]
  exact tensorAdjunction_unit (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y)
    (scalar_map l E L ι Y) N U x

private noncomputable def restrictionCompIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J CommRingCat.{r}}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (φ : R ⟶ S) (ψ : S ⟶ T) (κ : R ⟶ T) (h : φ ≫ ψ = κ) :
    CategoryTheory.CochainPullback.restrictionFunctor.{r, u, v, r} ψ ⋙
      CategoryTheory.CochainPullback.restrictionFunctor.{r, u, v, r} φ ≅
        CategoryTheory.CochainPullback.restrictionFunctor.{r, u, v, r} κ :=
  NatIso.ofComponents (fun N ↦
    { hom := { val := {
        app := fun U ↦ (ModuleCat.restrictScalarsComp'App
          (φ.hom.app U).hom
          (ψ.hom.app U).hom
          (κ.hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) h.symm)
          (N.val.obj U)).inv
        naturality := by intros; ext; rfl } }
      inv := { val := {
        app := fun U ↦ (ModuleCat.restrictScalarsComp'App
          (φ.hom.app U).hom
          (ψ.hom.app U).hom
          (κ.hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) h.symm)
          (N.val.obj U)).hom
        naturality := by intros; ext; rfl } }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }) (by intros; ext; rfl)

private noncomputable def restrictionUnitIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{r}}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (φ : R ⟶ R) (h : φ = 𝟙 R) :
    CategoryTheory.CochainPullback.restrictionFunctor.{r, u, v, r} φ ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom := { val := {
        app := fun U ↦ (ModuleCat.restrictScalarsId'App
          (φ.hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) h)
          (N.val.obj U)).hom
        naturality := by intros; ext; rfl } }
      inv := { val := {
        app := fun U ↦ (ModuleCat.restrictScalarsId'App
          (φ.hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) h)
          (N.val.obj U)).inv
        naturality := by intros; ext; rfl } }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }) (by intros; ext; rfl)

private noncomputable def scalarRestrictionComp :
    CategoryTheory.CochainPullback.restrictionFunctor.{u + 1, u + 1, u, u + 1}
        (integralCompletedScalarMap l L M j Y) ⋙
      CategoryTheory.CochainPullback.restrictionFunctor.{u + 1, u + 1, u, u + 1}
        (integralCompletedScalarMap l E L ι Y) ≅
      CategoryTheory.CochainPullback.restrictionFunctor.{u + 1, u + 1, u, u + 1}
        (integralCompletedScalarMap l E M (j.comp ι) Y) :=
  restrictionCompIso (integralCompletedScalarMap l E L ι Y)
    (integralCompletedScalarMap l L M j Y)
    (integralCompletedScalarMap l E M (j.comp ι) Y) (completedScalar_comp l E L ι Y M j)

private noncomputable def scalarRestrictionUnit :
    CategoryTheory.CochainPullback.restrictionFunctor.{u + 1, u + 1, u, u + 1}
      (integralCompletedScalarMap l E E (AlgHom.id (Padic l) E) Y) ≅ 𝟭 _ :=
  restrictionUnitIso (integralCompletedScalarMap l E E (AlgHom.id (Padic l) E) Y)
    (completedScalar_id l E Y)

attribute [local irreducible] integralCompletedScalarMap integralOrdinaryTensorSection

/-- The uniquely normalized ordinary tensor associator.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: the completed ring inclusions compose since all finite quotient projections
agree on the integer inclusions. Send c⊗(b⊗x) to c*j(b)⊗x, and send c⊗x to c⊗(1⊗x)
for the inverse. The balanced relations prove these formulas well defined and mutually
inverse. They commute with restrictions and module maps. Sheafification gives the
natural isomorphism, and local tensor generation proves its uniqueness. -/
theorem integralOrdinaryScalarComp_existsUnique :
    ∃! a : integralOrdinaryScalar l E L ι Y ⋙ integralOrdinaryScalar l L M j Y ≅
        integralOrdinaryScalar l E M (j.comp ι) Y,
      ∀ (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
        (c : (completedIntegralCommRingSheafUnrestricted l M Y).obj.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralOrdinaryTensorSection l L M j Y _ U c
            (integralOrdinaryTensorSection l E L ι Y N U b x)) =
          integralOrdinaryTensorSection l E M (j.comp ι) Y N U
            (c * (integralCompletedScalarMap l L M j Y).hom.app U b) x := by
  let a := Adjunction.leftAdjointCompIso (scalarAdjunction l E L ι Y)
    (scalarAdjunction l L M j Y) (scalarAdjunction l E M (j.comp ι) Y)
    (scalarRestrictionComp l E L ι Y M j)
  have ha (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
      (x : N.val.obj U) :
      (a.hom.app N).val.app U
        (integralOrdinaryTensorSection l L M j Y _ U 1
          (integralOrdinaryTensorSection l E L ι Y N U 1 x)) =
        integralOrdinaryTensorSection l E M (j.comp ι) Y N U 1 x := by
    have h := unit_conjugateEquiv_symm
      (scalarAdjunction l E M (j.comp ι) Y)
      ((scalarAdjunction l E L ι Y).comp (scalarAdjunction l L M j Y))
      (scalarRestrictionComp l E L ι Y M j).inv N
    have h' := congrArg (fun f ↦ f.val.app U x) h
    change ((scalarAdjunction l E M (j.comp ι) Y).unit.app N).val.app U x =
      (a.hom.app N).val.app U
        (((scalarAdjunction l L M j Y).unit.app
          ((integralOrdinaryScalar l E L ι Y).obj N)).val.app U
          (((scalarAdjunction l E L ι Y).unit.app N).val.app U x)) at h'
    simpa only [scalarAdjunction_unit] using h'.symm
  have h := tensorComp_existsUnique
    (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y)
    (integralCompletedScalarMap l L M j Y)
    (integralCompletedScalarMap l E M (j.comp ι) Y)
    (integralOrdinaryScalar l L M j Y) (integralOrdinaryScalar l E M (j.comp ι) Y)
    (scalar_obj l L M j Y) (scalar_obj l E M (j.comp ι) Y)
    (scalarAdjunction l L M j Y)
    (fun N U x ↦ (scalarAdjunction_unit l L M j Y N U x).trans
      (tensorSection_eq l L M j Y N U 1 x).symm) a
    (by intros; simpa only [tensorSection_eq] using ha _ _ _)
  simpa only [tensorSection_eq] using h

/-- Tensor associativity, fixed on all pure tensor sections.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryScalarComp :
    integralOrdinaryScalar l E L ι Y ⋙ integralOrdinaryScalar l L M j Y ≅
      integralOrdinaryScalar l E M (j.comp ι) Y :=
  (integralOrdinaryScalarComp_existsUnique l E L ι Y M j).exists.choose

/-- The tensor identity comparison is uniquely fixed by multiplication on generators.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: the completed identity inclusion is the identity by its projections. Thus the
balanced map s⊗x↦s*x and inverse x↦1⊗x are natural inverse maps. Sheafification and
local generation give the uniquely specified natural isomorphism. -/
theorem integralOrdinaryScalarUnit_existsUnique :
    ∃! a : integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (integralTowerModules.{u, u} l E Y),
      ∀ (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U s x) = s • x := by
  let a := Adjunction.leftAdjointIdIso
    (scalarAdjunction l E E (AlgHom.id (Padic l) E) Y) (scalarRestrictionUnit l E Y)
  have ha (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ) (x : N.val.obj U) :
      (a.hom.app N).val.app U
        (integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U 1 x) = x := by
    have h := unit_conjugateEquiv_symm Adjunction.id
      (scalarAdjunction l E E (AlgHom.id (Padic l) E) Y)
      (scalarRestrictionUnit l E Y).inv N
    have h' := congrArg (fun f ↦ f.val.app U x) h
    change x = (a.hom.app N).val.app U
      (((scalarAdjunction l E E (AlgHom.id (Padic l) E) Y).unit.app N).val.app U x) at h'
    simpa only [scalarAdjunction_unit] using h'.symm
  have hall (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U)
      (x : N.val.obj U) :
      (a.hom.app N).val.app U
        (integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U s x) = s • x := by
    rw [scalar_tensor_one, map_smul, ha]
  refine ⟨a, hall, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply tensorSection_ext (integralCompletedScalarMap l E E (AlgHom.id (Padic l) E) Y)
    (integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y)
    (scalar_obj l E E (AlgHom.id (Padic l) E) Y)
  intro U x
  rw [tensorSection_eq, ha', hall]

/-- The identity tensor comparison.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryScalarUnit :
    integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y ≅
      𝟭 (integralTowerModules.{u, u} l E Y) :=
  (integralOrdinaryScalarUnit_existsUnique l E Y).exists.choose

/-- The associator induced on the canonical derived localizations.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryDerivedScalarComp :
    integralOrdinaryDerivedScalar l E L ι Y ⋙ integralOrdinaryDerivedScalar l L M j Y ≅
      integralOrdinaryDerivedScalar l E M (j.comp ι) Y :=
  (Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L ι Y)
    (integralOrdinaryScalar l L M j Y)) ≪≫
    Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarComp l E L ι Y M j)

/-- The ordinary derived tensor unit, through the fixed derived localization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryDerivedScalarUnit :
    integralOrdinaryDerivedScalar l E E (AlgHom.id (Padic l) E) Y ≅
      𝟭 (DerivedCategory (integralTowerModules.{u, u} l E Y)) :=
  Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarUnit l E Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

section OrdinaryCoherence
attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryScalarUnit
private theorem scalar_comp_inv_tensor
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l M Y).obj.obj U)
    (x : N.val.obj U) :
    ((integralOrdinaryScalarComp l E L ι Y M j).inv.app N).val.app U
      (integralOrdinaryTensorSection l E M (j.comp ι) Y N U s x) =
    integralOrdinaryTensorSection l L M j Y _ U s
      (integralOrdinaryTensorSection l E L ι Y N U 1 x) := by
  let a := integralOrdinaryScalarComp l E L ι Y M j
  let z := integralOrdinaryTensorSection l L M j Y _ U s
    (integralOrdinaryTensorSection l E L ι Y N U 1 x)
  have hz : (a.hom.app N).val.app U z =
      integralOrdinaryTensorSection l E M (j.comp ι) Y N U s x := by
    simpa only [a, z, integralOrdinaryScalarComp] using
    ((integralOrdinaryScalarComp_existsUnique l E L ι Y M j).exists.choose_spec
      N U s 1 x).trans (by rw [map_one, mul_one])
  calc
    _ = (a.inv.app N).val.app U ((a.hom.app N).val.app U z) :=
      congrArg (fun y ↦ (a.inv.app N).val.app U y) hz.symm
    _ = z := congrArg (fun t ↦ t.val.app U z) (a.hom_inv_id_app N)

private theorem scalar_unit_inv_tensor
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ) (x : N.val.obj U) :
    ((integralOrdinaryScalarUnit l E Y).inv.app N).val.app U x =
      integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U 1 x := by
  let a := integralOrdinaryScalarUnit l E Y
  let z := integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U 1 x
  have hz : (a.hom.app N).val.app U z = x := by
    simpa only [a, z, integralOrdinaryScalarUnit] using
    ((integralOrdinaryScalarUnit_existsUnique l E Y).exists.choose_spec N U 1 x).trans
      (one_smul _ _)
  calc
    _ = (a.inv.app N).val.app U ((a.hom.app N).val.app U z) :=
      congrArg (fun y ↦ (a.inv.app N).val.app U y) hz.symm
    _ = z := congrArg (fun t ↦ t.val.app U z) (a.hom_inv_id_app N)

private theorem ordinary_source_unit :
    integralOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι =
      Functor.isoWhiskerRight (integralOrdinaryScalarUnit l E Y)
        (integralOrdinaryScalar l E L ι Y) ≪≫
      Functor.leftUnitor (integralOrdinaryScalar l E L ι Y) := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply NatTrans.ext
  funext N
  apply tensorSection_ext (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y)
    (scalar_obj l E L ι Y)
  intro U x
  rw [tensorSection_eq]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app]
  change ((integralOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι).inv.app N).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x) =
    ((integralOrdinaryScalar l E L ι Y).map
      ((integralOrdinaryScalarUnit l E Y).inv.app N)).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x)
  erw [scalar_comp_inv_tensor]
  erw [scalar_map_tensor]
  change _ = integralOrdinaryTensorSection l E L ι Y _ U 1
    (((integralOrdinaryScalarUnit l E Y).inv.app N).val.app U x)
  rw [scalar_unit_inv_tensor]

private theorem ordinary_target_unit :
    integralOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L) =
      Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι Y)
        (integralOrdinaryScalarUnit l L Y) ≪≫
      Functor.rightUnitor (integralOrdinaryScalar l E L ι Y) := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply NatTrans.ext
  funext N
  apply tensorSection_ext (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y)
    (scalar_obj l E L ι Y)
  intro U x
  rw [tensorSection_eq]
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app]
  change ((integralOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L)).inv.app N).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x) =
    ((integralOrdinaryScalarUnit l L Y).inv.app
      ((integralOrdinaryScalar l E L ι Y).obj N)).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x)
  erw [scalar_comp_inv_tensor, scalar_unit_inv_tensor]

private theorem ordinary_pentagon
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (k : M →ₐ[Padic l] N) :
    Functor.isoWhiskerRight (integralOrdinaryScalarComp l E L ι Y M j)
        (integralOrdinaryScalar l M N k Y) ≪≫
      integralOrdinaryScalarComp l E M (j.comp ι) Y N k =
    Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι Y)
        (integralOrdinaryScalarComp l L M j Y N k) ≪≫
      integralOrdinaryScalarComp l E L ι Y N (k.comp j) := by
  apply tensorSection_pentagon
    (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y)
    (integralCompletedScalarMap l L M j Y)
    (integralCompletedScalarMap l M N k Y)
    (integralCompletedScalarMap l E M (j.comp ι) Y)
    (integralCompletedScalarMap l L N (k.comp j) Y)
    (integralCompletedScalarMap l E N (k.comp (j.comp ι)) Y)
    (integralOrdinaryScalar l L M j Y) (integralOrdinaryScalar l M N k Y)
    (integralOrdinaryScalar l E M (j.comp ι) Y)
    (integralOrdinaryScalar l L N (k.comp j) Y)
    (integralOrdinaryScalar l E N (k.comp (j.comp ι)) Y)
    (scalar_obj l L M j Y) (scalar_obj l M N k Y)
    (scalar_obj l E M (j.comp ι) Y) (scalar_obj l L N (k.comp j) Y)
    (scalar_obj l E N (k.comp (j.comp ι)) Y) (scalar_map l M N k Y)
  all_goals
    intros
    simp only [tensorSection_eq]
    apply scalar_comp_inv_tensor

end OrdinaryCoherence

attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryScalarUnit
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategory

section DerivedCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (T : A ⥤ A) (F : A ⥤ B)
  [T.Additive] [F.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (u : T ≅ 𝟭 A) (a : T ⋙ F ≅ F)
  (ha : a = Functor.isoWhiskerRight u F ≪≫ Functor.leftUnitor F)
include ha in
private theorem derived_source_unit :
    (Functor.mapDerivedCategoryCompIso T F ≪≫
      Functor.mapDerivedCategoryNatIso a).hom =
    Functor.whiskerRight
      (Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso A).hom
      F.mapDerivedCategory := by
  have h := Functor.mapDerivedCategoryNatIso_isoWhiskerRight u F
  have hu := Functor.mapDerivedCategoryCompIso_id_comp F
  have ha' : a = Functor.isoWhiskerRight u F := by
    apply Iso.ext
    ext X
    have hx := congrArg (fun e ↦ e.hom.app X) ha
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app] at hx
    erw [Category.comp_id] at hx
    exact hx
  rw [ha']
  apply (cancel_mono (Functor.mapDerivedCategoryCompIso (𝟭 A) F).inv).mp
  simp only [Iso.trans_hom, Category.assoc,
    Functor.whiskerRight_comp]
  rw [h]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hu' : Functor.whiskerRight (Functor.mapDerivedCategoryIdIso A).hom
      F.mapDerivedCategory ≫ (Functor.mapDerivedCategoryCompIso (𝟭 A) F).inv = 𝟙 _ := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 A) F).inv).mp
    rw [← Category.assoc, hu]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  rw [Category.assoc, hu', Category.comp_id]

end

section
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) (T : B ⥤ B)
  [T.Additive] [F.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (u : T ≅ 𝟭 B) (a : F ⋙ T ≅ F)
  (ha : a = Functor.isoWhiskerLeft F u ≪≫ Functor.rightUnitor F)
include ha in
private theorem derived_target_unit :
    (Functor.mapDerivedCategoryCompIso F T ≪≫
      Functor.mapDerivedCategoryNatIso a).hom =
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso B).hom := by
  have h := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F u
  have hu := Functor.mapDerivedCategoryCompIso_comp_id F
  have ha' : a = Functor.isoWhiskerLeft F u := by
    apply Iso.ext
    ext X
    have hx := congrArg (fun e ↦ e.hom.app X) ha
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_hom_app] at hx
    erw [Category.comp_id] at hx
    exact hx
  rw [ha']
  apply (cancel_mono (Functor.mapDerivedCategoryCompIso F (𝟭 B)).inv).mp
  simp only [Iso.trans_hom, Category.assoc,
    Functor.whiskerLeft_comp]
  rw [h]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hu' : Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryIdIso B).hom ≫
      (Functor.mapDerivedCategoryCompIso F (𝟭 B)).inv = 𝟙 _ := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso F (𝟭 B)).inv).mp
    rw [← Category.assoc, hu]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  rw [Category.assoc, hu', Category.comp_id]

end

end DerivedCoherence

private theorem ordinary_derived_source_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y)) :
    (integralOrdinaryDerivedScalarComp l E E (AlgHom.id (Padic l) E) Y L ι).hom.app K =
      (integralOrdinaryDerivedScalar l E L ι Y).map
        ((integralOrdinaryDerivedScalarUnit l E Y).hom.app K) := by
  exact congrArg (fun t ↦ t.app K)
    (derived_source_unit
      (integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y)
      (integralOrdinaryScalar l E L ι Y) (integralOrdinaryScalarUnit l E Y)
      (integralOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι)
      (ordinary_source_unit l E L ι Y))

private theorem ordinary_derived_target_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y)) :
    (integralOrdinaryDerivedScalarComp l E L ι Y L (AlgHom.id (Padic l) L)).hom.app K =
      (integralOrdinaryDerivedScalarUnit l L Y).hom.app
        ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  exact congrArg (fun t ↦ t.app K)
    (derived_target_unit
      (integralOrdinaryScalar l E L ι Y)
      (integralOrdinaryScalar l L L (AlgHom.id (Padic l) L) Y)
      (integralOrdinaryScalarUnit l L Y)
      (integralOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L))
      (ordinary_target_unit l E L ι Y))

private theorem derived_pentagon
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    (FG : A ⥤ C) (GH : B ⥤ D) (FGH : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (h : Functor.isoWhiskerRight a H ≪≫ b = Functor.isoWhiskerLeft F c ≪≫ d)
    (K : DerivedCategory A) :
    H.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso F G ≪≫
          Functor.mapDerivedCategoryNatIso a).hom.app K) ≫
      (Functor.mapDerivedCategoryCompIso FG H ≪≫
        Functor.mapDerivedCategoryNatIso b).hom.app K =
    (Functor.mapDerivedCategoryCompIso G H ≪≫
        Functor.mapDerivedCategoryNatIso c).hom.app (F.mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategoryCompIso F GH ≪≫
        Functor.mapDerivedCategoryNatIso d).hom.app K :=
  Functor.mapDerivedCategoryCompNatIso_cocycle a b c d
    (fun X ↦ congrArg (fun e ↦ e.hom.app X) h) K

private theorem ordinary_derived_pentagon
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (j : L →ₐ[Padic l] M)
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (k : M →ₐ[Padic l] N)
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y)) :
    (integralOrdinaryDerivedScalar l M N k Y).map
        ((integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K) ≫
      (integralOrdinaryDerivedScalarComp l E M (j.comp ι) Y N k).hom.app K =
    (integralOrdinaryDerivedScalarComp l L M j Y N k).hom.app
        ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
      (integralOrdinaryDerivedScalarComp l E L ι Y N (k.comp j)).hom.app K := by
  exact derived_pentagon
    (integralOrdinaryScalar l E L ι Y)
    (integralOrdinaryScalar l L M j Y)
    (integralOrdinaryScalar l M N k Y)
    (integralOrdinaryScalar l E M (j.comp ι) Y)
    (integralOrdinaryScalar l L N (k.comp j) Y)
    (integralOrdinaryScalar l E N (k.comp (j.comp ι)) Y)
    (integralOrdinaryScalarComp l E L ι Y M j)
    (integralOrdinaryScalarComp l E M (j.comp ι) Y N k)
    (integralOrdinaryScalarComp l L M j Y N k)
    (integralOrdinaryScalarComp l E L ι Y N (k.comp j))
    (ordinary_pentagon l E L ι Y M j N k) K

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Restriction of the fixed derived associator to the full integral subcategories.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: all three functors preserve the stated full subcategories. Their inclusion is
fully faithful, so the ambient derived associator and its inverse lift uniquely. -/
theorem integralConstructibleScalarComp_existsUnique :
    ∃! a : integralConstructibleScalarExtension D l hl E L ι Y ⋙
        integralConstructibleScalarExtension D l hl L M j Y ≅
        integralConstructibleScalarExtension D l hl E M (j.comp ι) Y,
      ∀ K, (a.hom.app K).hom =
        (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj := by
  let a : integralConstructibleScalarExtension D l hl E L ι Y ⋙
      integralConstructibleScalarExtension D l hl L M j Y ≅
      integralConstructibleScalarExtension D l hl E M (j.comp ι) Y := NatIso.ofComponents
    (fun K ↦ { hom := ⟨(integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj⟩
               inv := ⟨(integralOrdinaryDerivedScalarComp l E L ι Y M j).inv.app K.obj⟩
               hom_inv_id := by ext; exact
                 (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom_inv_id_app K.obj
               inv_hom_id := by ext; exact
                 (integralOrdinaryDerivedScalarComp l E L ι Y M j).inv_hom_id_app K.obj })
    (fun f ↦ by ext; exact
      (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.naturality f.hom)
  refine ⟨a, fun _ ↦ rfl, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  ext
  exact ha' K

/-- The restricted canonical associator.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralConstructibleScalarComp :=
  (integralConstructibleScalarComp_existsUnique l E L ι Y M j D hl).exists.choose

/-- Restriction of the fixed derived unit to the full integral subcategory.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: the full inclusion uniquely lifts the ambient derived tensor unit and inverse. -/
theorem integralConstructibleScalarUnit_existsUnique :
    ∃! a : integralConstructibleScalarExtension D l hl E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y),
      ∀ K, (a.hom.app K).hom =
        (integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj := by
  let a : integralConstructibleScalarExtension D l hl E E (AlgHom.id (Padic l) E) Y ≅
      𝟭 (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
    NatIso.ofComponents
    (fun K ↦ { hom := ⟨(integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj⟩
               inv := ⟨(integralOrdinaryDerivedScalarUnit l E Y).inv.app K.obj⟩
               hom_inv_id := by ext; exact
                 (integralOrdinaryDerivedScalarUnit l E Y).hom_inv_id_app K.obj
               inv_hom_id := by ext; exact
                 (integralOrdinaryDerivedScalarUnit l E Y).inv_hom_id_app K.obj })
    (fun f ↦ by ext; exact
      (integralOrdinaryDerivedScalarUnit l E Y).hom.naturality f.hom)
  refine ⟨a, fun _ ↦ rfl, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  ext
  exact ha' K

/-- The restricted canonical tensor unit.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralConstructibleScalarUnit :=
  (integralConstructibleScalarUnit_existsUnique l E Y D hl).exists.choose

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    simp [c]
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.inductionOn with
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
        (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
      dsimp [c]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      simpa only [ScalarLocalization.localization, Category.assoc] using
        congrArg (fun z :
          (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
            eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

private instance rationalOrdinary_additive :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).Additive where
  map_add := by
    intro K K' f g
    exact (rationalScalarHom D l hl E Y L ι K.obj K'.obj).map_add f g

private theorem rationalOrdinary_map
    {K K' : rationalConstructibleCategory D l hl E Y}
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (f : K.obj ⟶ K'.obj) :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).map (a ⊗ₜ f) =
      rationalCoefficientMap l E L ι a ⊗ₜ
        (integralConstructibleScalarExtension D l hl E L ι Y).map f :=
  (rationalScalarHom_existsUnique D l hl E Y L ι K.obj K'.obj).exists.choose_spec a f

private theorem rationalCoefficientMap_comp
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    rationalCoefficientMap l L M j (rationalCoefficientMap l E L ι a) =
      rationalCoefficientMap l E M (j.comp ι) a := by
  simp [rationalCoefficientMap]

private theorem integral_comp_component
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    ((integralConstructibleScalarComp l E L ι Y M j D hl).hom.app K).hom =
      (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj :=
  (integralConstructibleScalarComp_existsUnique l E L ι Y M j D hl).exists.choose_spec K

private theorem integral_unit_component
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    ((integralConstructibleScalarUnit l E Y D hl).hom.app K).hom =
      (integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj :=
  (integralConstructibleScalarUnit_existsUnique l E Y D hl).exists.choose_spec K

/-- The localized associator, uniquely fixed by the integral tensor associator.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: tensor each component and inverse with one. The integral naturality equation
extends to pure rational tensors by scalar compatibility and to sums by additivity.
Inverse equations persist. Equality of hom components determines a natural isomorphism. -/
theorem rationalOrdinaryScalarComp_existsUnique :
    ∃! a : rationalOrdinaryScalarExtension D l hl E Y L ι ⋙
        rationalOrdinaryScalarExtension D l hl L Y M j ≅
        rationalOrdinaryScalarExtension D l hl E Y M (j.comp ι),
      ∀ K, a.hom.app K =
        1 ⊗ₜ (integralConstructibleScalarComp l E L ι Y M j D hl).hom.app K.obj := by
  have h := localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l M)
    (rationalCoefficientMap l E M (j.comp ι))
    (integralConstructibleScalarExtension D l hl E L ι Y ⋙
      integralConstructibleScalarExtension D l hl L M j Y)
    (integralConstructibleScalarExtension D l hl E M (j.comp ι) Y)
    (integralConstructibleScalarComp l E L ι Y M j D hl)
    (rationalOrdinaryScalarExtension D l hl E Y L ι ⋙
      rationalOrdinaryScalarExtension D l hl L Y M j)
    (rationalOrdinaryScalarExtension D l hl E Y M (j.comp ι))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (by
    intro K K' f a
    apply heq_of_eq
    change (rationalOrdinaryScalarExtension D l hl L Y M j).map
      ((rationalOrdinaryScalarExtension D l hl E Y L ι).map (a ⊗ₜ f)) = _
    rw [rationalOrdinary_map, rationalOrdinary_map, rationalCoefficientMap_comp]
    rfl
  ) (by
    intro K K' f a
    exact heq_of_eq (rationalOrdinary_map l E M (j.comp ι) Y D hl a f)
  )
  simpa only [heq_iff_eq, ScalarLocalization.localization] using h

/-- The rational scalar associator with the specified integral normalization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalOrdinaryScalarComp :=
  (rationalOrdinaryScalarComp_existsUnique l E L ι Y M j D hl).exists.choose

/-- The localized unit, uniquely fixed by the integral tensor unit.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: tensor both components of the integral unit with one. Naturality on pure
tensors, additivity and the integral inverse equations give the unique unit isomorphism. -/
theorem rationalOrdinaryScalarUnit_existsUnique :
    ∃! a : rationalOrdinaryScalarExtension D l hl E Y E (AlgHom.id (Padic l) E) ≅
        𝟭 (rationalConstructibleCategory D l hl E Y),
      ∀ K, a.hom.app K =
        1 ⊗ₜ (integralConstructibleScalarUnit l E Y D hl).hom.app K.obj := by
  have h := localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l E)
    id (integralConstructibleScalarExtension D l hl E E (AlgHom.id (Padic l) E) Y)
    (𝟭 _) (integralConstructibleScalarUnit l E Y D hl)
    (rationalOrdinaryScalarExtension D l hl E Y E (AlgHom.id (Padic l) E)) (𝟭 _)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (by
    intro K K' f a
    apply heq_of_eq
    rw [rationalOrdinary_map]
    change (rationalCoefficientEquiv l E).symm (rationalCoefficientEquiv l E a) ⊗ₜ _ =
      a ⊗ₜ _
    rw [AlgEquiv.symm_apply_apply]
  ) (by
    intro K K' f a
    rfl
  )
  simpa only [heq_iff_eq, ScalarLocalization.localization] using h

/-- The rational scalar unit with the specified integral normalization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalOrdinaryScalarUnit :=
  (rationalOrdinaryScalarUnit_existsUnique l E Y D hl).exists.choose

private theorem rational_comp_component (K : rationalConstructibleCategory D l hl E Y) :
    (rationalOrdinaryScalarComp l E L ι Y M j D hl).hom.app K =
      1 ⊗ₜ (integralConstructibleScalarComp l E L ι Y M j D hl).hom.app K.obj :=
  (rationalOrdinaryScalarComp_existsUnique l E L ι Y M j D hl).exists.choose_spec K

private theorem rational_unit_component (K : rationalConstructibleCategory D l hl E Y) :
    (rationalOrdinaryScalarUnit l E Y D hl).hom.app K =
      1 ⊗ₜ (integralConstructibleScalarUnit l E Y D hl).hom.app K.obj :=
  (rationalOrdinaryScalarUnit_existsUnique l E Y D hl).exists.choose_spec K

attribute [local irreducible] rationalScalarHom rationalCoefficientMap

attribute [local irreducible] integralOrdinaryDerivedScalarComp
  integralOrdinaryDerivedScalarUnit integralConstructibleScalarComp
  integralConstructibleScalarUnit rationalOrdinaryScalarComp rationalOrdinaryScalarUnit

/-- Tensor units and associators obey both unit laws and the pentagon.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: first check the ordinary sheaf tensor generators. Both unit maps multiply
1⊗x to x. Both paths around the pentagon multiply the same three coefficients, so
associativity in the largest completed coefficient ring gives equality. Local tensor
generation gives the natural transformation equalities. Canonical derived localization,
full-subcategory restriction, and tensoring Hom maps with one preserve these equations. -/
theorem rationalOrdinaryScalar_coherence :
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι D hl).hom.app K =
        (rationalOrdinaryScalarExtension D l hl E Y L ι).map
          ((rationalOrdinaryScalarUnit l E Y D hl).hom.app K)) ∧
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L) D hl).hom.app K =
        (rationalOrdinaryScalarUnit l L Y D hl).hom.app
          ((rationalOrdinaryScalarExtension D l hl E Y L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : rationalConstructibleCategory D l hl E Y),
      (rationalOrdinaryScalarExtension D l hl M Y N k).map
          ((rationalOrdinaryScalarComp l E L ι Y M j D hl).hom.app K) ≫
        (rationalOrdinaryScalarComp l E M (j.comp ι) Y N k D hl).hom.app K =
      (rationalOrdinaryScalarComp l L M j Y N k D hl).hom.app
          ((rationalOrdinaryScalarExtension D l hl E Y L ι).obj K) ≫
        (rationalOrdinaryScalarComp l E L ι Y N (k.comp j) D hl).hom.app K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K
    rw [rational_comp_component, rational_unit_component]
    rw [rationalOrdinary_map, map_one]
    congr 1
    apply (boundedConstructibleDerivedCompleteIntegral D l hl L Y).ι.map_injective
    change ((integralConstructibleScalarComp l E E
      (AlgHom.id (Padic l) E) Y L ι D hl).hom.app K.obj).hom =
      (integralOrdinaryDerivedScalar l E L ι Y).map
        (((integralConstructibleScalarUnit l E Y D hl).hom.app K.obj).hom)
    rw [integral_comp_component, integral_unit_component]
    exact ordinary_derived_source_unit l E L ι Y K.obj.obj
  · intro K
    rw [rational_comp_component, rational_unit_component]
    congr 1
    apply (boundedConstructibleDerivedCompleteIntegral D l hl L Y).ι.map_injective
    change ((integralConstructibleScalarComp l E L ι Y L
      (AlgHom.id (Padic l) L) D hl).hom.app K.obj).hom =
      ((integralConstructibleScalarUnit l L Y D hl).hom.app
        ((integralConstructibleScalarExtension D l hl E L ι Y).obj K.obj)).hom
    rw [integral_comp_component, integral_unit_component]
    exact ordinary_derived_target_unit l E L ι Y K.obj.obj
  · intro N _ _ _ k K
    rw [rational_comp_component, rational_comp_component,
      rational_comp_component, rational_comp_component, rationalOrdinary_map, map_one]
    change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ _) (1 ⊗ₜ _) =
      ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ _) (1 ⊗ₜ _)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
    congr 1
    apply (boundedConstructibleDerivedCompleteIntegral D l hl N Y).ι.map_injective
    change (integralOrdinaryDerivedScalar l M N k Y).map
      (((integralConstructibleScalarComp l E L ι Y M j D hl).hom.app K.obj).hom) ≫
      ((integralConstructibleScalarComp l E M (j.comp ι) Y N k D hl).hom.app K.obj).hom =
      ((integralConstructibleScalarComp l L M j Y N k D hl).hom.app
        ((integralConstructibleScalarExtension D l hl E L ι Y).obj K.obj)).hom ≫
      ((integralConstructibleScalarComp l E L ι Y N (k.comp j) D hl).hom.app K.obj).hom
    rw [integral_comp_component, integral_comp_component,
      integral_comp_component, integral_comp_component]
    exact ordinary_derived_pentagon l E L ι Y M j N k K.obj.obj

attribute [local irreducible] rationalScalarExtension rationalOrdinaryScalarExtension
  rationalOrdinaryComparison

/-- The canonical associator of the published rational scalar extensions.
It is ordinary balanced tensor associativity conjugated by the normalized quotient
completion comparisons, so it retains the tensor-generator characterization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalConstructibleScalarComp :
    rationalScalarExtension D l hl E Y L ι ⋙ rationalScalarExtension D l hl L Y M j ≅
      rationalScalarExtension D l hl E Y M (j.comp ι) :=
  Functor.isoWhiskerRight (rationalOrdinaryComparison D l hl E Y L ι).symm
      (rationalScalarExtension D l hl L Y M j) ≪≫
    Functor.isoWhiskerLeft (rationalOrdinaryScalarExtension D l hl E Y L ι)
      (rationalOrdinaryComparison D l hl L Y M j).symm ≪≫
    rationalOrdinaryScalarComp l E L ι Y M j D hl ≪≫
    rationalOrdinaryComparison D l hl E Y M (j.comp ι)

/-- The identity-extension comparison, with its actual completeness-unit normalization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalConstructibleScalarUnit :
    rationalScalarExtension D l hl E Y E (AlgHom.id (Padic l) E) ≅
      𝟭 (rationalConstructibleCategory D l hl E Y) :=
  (rationalOrdinaryComparison D l hl E Y E (AlgHom.id (Padic l) E)).symm ≪≫
    rationalOrdinaryScalarUnit l E Y D hl

private theorem conj_unit_left {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (I : A ⥤ B) (J : C ⥤ D)
    (T : A ⥤ A) (F : A ⥤ C) (T₀ : B ⥤ B) (F₀ : B ⥤ D)
    (c : I ⋙ T₀ ≅ T ⋙ I) (d : I ⋙ F₀ ≅ F ⋙ J)
    (u₀ : T₀ ≅ 𝟭 B) (u : T ≅ 𝟭 A)
    (hu' : ∀ K, I.map (u.hom.app K) = c.inv.app K ≫ u₀.hom.app (I.obj K))
    (K : A) :
    d.inv.app (T.obj K) ≫ F₀.map (c.inv.app K) ≫
      F₀.map (u₀.hom.app (I.obj K)) ≫ d.hom.app K =
      J.map (F.map (u.hom.app K)) := by
  rw [← F₀.map_comp_assoc, ← hu']
  have hn := d.hom.naturality (u.hom.app K)
  change F₀.map (I.map (u.hom.app K)) ≫ d.hom.app K =
    d.hom.app (T.obj K) ≫ J.map (F.map (u.hom.app K)) at hn
  rw [hn, Iso.inv_hom_id_app_assoc]
private theorem conj_unit_right {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (I : A ⥤ B) (J : C ⥤ D)
    (T : C ⥤ C) (F : A ⥤ C) (T₀ : D ⥤ D) (F₀ : B ⥤ D)
    (c : J ⋙ T₀ ≅ T ⋙ J) (d : I ⋙ F₀ ≅ F ⋙ J)
    (u₀ : T₀ ≅ 𝟭 D) (K : A) :
    c.inv.app (F.obj K) ≫ T₀.map (d.inv.app K) ≫
      u₀.hom.app (F₀.obj (I.obj K)) ≫ d.hom.app K =
      c.inv.app (F.obj K) ≫ u₀.hom.app (J.obj (F.obj K)) := by
  rw [reassoc_of% (u₀.hom.naturality (d.inv.app K))]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem conj_comp {A B C D A₀ B₀ C₀ D₀ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    (I : A ⥤ A₀) (J : B ⥤ B₀) (K : C ⥤ C₀) (L : D ⥤ D₀)
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    (FG : A ⥤ C) (GH : B ⥤ D) (FGH : A ⥤ D)
    (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ C₀) (H₀ : C₀ ⥤ D₀)
    (FG₀ : A₀ ⥤ C₀) (GH₀ : B₀ ⥤ D₀) (FGH₀ : A₀ ⥤ D₀)
    (cF : I ⋙ F₀ ≅ F ⋙ J) (cG : J ⋙ G₀ ≅ G ⋙ K)
    (cH : K ⋙ H₀ ≅ H ⋙ L) (cFG : I ⋙ FG₀ ≅ FG ⋙ K)
    (cGH : J ⋙ GH₀ ≅ GH ⋙ L) (cFGH : I ⋙ FGH₀ ≅ FGH ⋙ L)
    (a₀ : F₀ ⋙ G₀ ≅ FG₀) (b₀ : FG₀ ⋙ H₀ ≅ FGH₀)
    (c₀ : G₀ ⋙ H₀ ≅ GH₀) (d₀ : F₀ ⋙ GH₀ ≅ FGH₀)
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (ha : ∀ X, K.map (a.hom.app X) = cG.inv.app (F.obj X) ≫
      G₀.map (cF.inv.app X) ≫ a₀.hom.app (I.obj X) ≫ cFG.hom.app X)
    (hb : ∀ X, L.map (b.hom.app X) = cH.inv.app (FG.obj X) ≫
      H₀.map (cFG.inv.app X) ≫ b₀.hom.app (I.obj X) ≫ cFGH.hom.app X)
    (hc : ∀ X, L.map (c.hom.app X) = cH.inv.app (G.obj X) ≫
      H₀.map (cG.inv.app X) ≫ c₀.hom.app (J.obj X) ≫ cGH.hom.app X)
    (hd : ∀ X, L.map (d.hom.app X) = cGH.inv.app (F.obj X) ≫
      GH₀.map (cF.inv.app X) ≫ d₀.hom.app (I.obj X) ≫ cFGH.hom.app X)
    (h₀ : ∀ X, H₀.map (a₀.hom.app X) ≫ b₀.hom.app X =
      c₀.hom.app (F₀.obj X) ≫ d₀.hom.app X) (X : A) :
    L.map (H.map (a.hom.app X) ≫ b.hom.app X) =
      L.map (c.hom.app (F.obj X) ≫ d.hom.app X) := by
  have hn := cH.hom.naturality (a.hom.app X)
  have hm : L.map (H.map (a.hom.app X)) =
      cH.inv.app (G.obj (F.obj X)) ≫ H₀.map (K.map (a.hom.app X)) ≫
        cH.hom.app (FG.obj X) := by
    have hn' : H₀.map (K.map (a.hom.app X)) ≫ cH.hom.app (FG.obj X) =
        cH.hom.app (G.obj (F.obj X)) ≫ L.map (H.map (a.hom.app X)) := hn
    rw [hn']
    simp only [Iso.inv_hom_id_app_assoc]
  rw [L.map_comp, L.map_comp, hm, ha, hb, hc, hd]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  have hcanc : H₀.map (cFG.hom.app X) ≫ H₀.map (cFG.inv.app X) = 𝟙 _ := by
    rw [← H₀.map_comp, Iso.hom_inv_id_app, H₀.map_id]
  rw [← Category.assoc (H₀.map (cFG.hom.app X)) (H₀.map (cFG.inv.app X)), hcanc]
  erw [Category.id_comp]
  have hn' := c₀.hom.naturality (cF.inv.app X)
  change H₀.map (G₀.map (cF.inv.app X)) ≫ c₀.hom.app (F₀.obj (I.obj X)) =
    c₀.hom.app (J.obj (F.obj X)) ≫ GH₀.map (cF.inv.app X) at hn'
  calc
    _ = cH.inv.app (G.obj (F.obj X)) ≫ H₀.map (cG.inv.app (F.obj X)) ≫
        H₀.map (G₀.map (cF.inv.app X)) ≫
        (H₀.map (a₀.hom.app (I.obj X)) ≫ b₀.hom.app (I.obj X)) ≫
        cFGH.hom.app X := by simp only [Category.assoc]
    _ = _ := by rw [h₀]; simp only [Category.assoc]; rw [reassoc_of% hn']

private theorem conjugate_comp_formula {A B C : Type*}
    [Category A] [Category B] [Category C]
    (F₀ F : A ⥤ B) (G₀ G : B ⥤ C) (FG₀ FG : A ⥤ C)
    (cF : F₀ ≅ F) (cG : G₀ ≅ G) (cFG : FG₀ ≅ FG) (a₀ : F₀ ⋙ G₀ ≅ FG₀)
    (X : A) :
    (Functor.isoWhiskerRight cF.symm G ≪≫ Functor.isoWhiskerLeft F₀ cG.symm ≪≫
      a₀ ≪≫ cFG).hom.app X =
    cG.inv.app (F.obj X) ≫ G₀.map (cF.inv.app X) ≫ a₀.hom.app X ≫ cFG.hom.app X := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [← reassoc_of% (cG.inv.naturality (cF.inv.app X))]

private theorem completed_comp_formula
    (K : rationalConstructibleCategory D l hl E Y) :
    (rationalConstructibleScalarComp l E L ι Y M j D hl).hom.app K =
      (rationalOrdinaryComparison D l hl L Y M j).inv.app
          ((rationalScalarExtension D l hl E Y L ι).obj K) ≫
        (rationalOrdinaryScalarExtension D l hl L Y M j).map
          ((rationalOrdinaryComparison D l hl E Y L ι).inv.app K) ≫
        (rationalOrdinaryScalarComp l E L ι Y M j D hl).hom.app K ≫
        (rationalOrdinaryComparison D l hl E Y M (j.comp ι)).hom.app K := by
  exact conjugate_comp_formula
    (rationalOrdinaryScalarExtension D l hl E Y L ι)
    (rationalScalarExtension D l hl E Y L ι)
    (rationalOrdinaryScalarExtension D l hl L Y M j)
    (rationalScalarExtension D l hl L Y M j)
    (rationalOrdinaryScalarExtension D l hl E Y M (j.comp ι))
    (rationalScalarExtension D l hl E Y M (j.comp ι))
    (rationalOrdinaryComparison D l hl E Y L ι)
    (rationalOrdinaryComparison D l hl L Y M j)
    (rationalOrdinaryComparison D l hl E Y M (j.comp ι))
    (rationalOrdinaryScalarComp l E L ι Y M j D hl) K

private theorem completed_unit_formula (K : rationalConstructibleCategory D l hl E Y) :
    (rationalConstructibleScalarUnit l E Y D hl).hom.app K =
      (rationalOrdinaryComparison D l hl E Y E (AlgHom.id (Padic l) E)).inv.app K ≫
        (rationalOrdinaryScalarUnit l E Y D hl).hom.app K := rfl

attribute [local irreducible] rationalConstructibleScalarComp
  rationalConstructibleScalarUnit

/-- Tensor units and associators obey both unit laws and the pentagon.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: first check the ordinary sheaf tensor generators. Both unit maps multiply
1⊗x to x. Both paths around the pentagon multiply the same three coefficients, so
associativity in the largest completed coefficient ring gives equality. Local tensor
generation gives the natural transformation equalities. Canonical derived localization,
full-subcategory restriction, and tensoring Hom maps with one preserve these equations.
For the published completed functors, expand the conjugations by the normalized
quotient completion comparisons. Naturality cancels adjacent inverse comparisons,
leaving the same ordinary tensor equation on both sides. -/
theorem rationalConstructibleScalar_coherence :
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalConstructibleScalarComp l E E (AlgHom.id (Padic l) E) Y L ι D hl).hom.app K =
        (rationalScalarExtension D l hl E Y L ι).map
          ((rationalConstructibleScalarUnit l E Y D hl).hom.app K)) ∧
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalConstructibleScalarComp l E L ι Y L (AlgHom.id (Padic l) L) D hl).hom.app K =
        (rationalConstructibleScalarUnit l L Y D hl).hom.app
          ((rationalScalarExtension D l hl E Y L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : rationalConstructibleCategory D l hl E Y),
      (rationalScalarExtension D l hl M Y N k).map
          ((rationalConstructibleScalarComp l E L ι Y M j D hl).hom.app K) ≫
        (rationalConstructibleScalarComp l E M (j.comp ι) Y N k D hl).hom.app K =
      (rationalConstructibleScalarComp l L M j Y N k D hl).hom.app
          ((rationalScalarExtension D l hl E Y L ι).obj K) ≫
        (rationalConstructibleScalarComp l E L ι Y N (k.comp j) D hl).hom.app K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K
    rw [completed_comp_formula,
      (rationalOrdinaryScalar_coherence l E L ι Y M j D hl).1]
    exact conj_unit_left (𝟭 _) (𝟭 _)
      (rationalScalarExtension D l hl E Y E (AlgHom.id (Padic l) E))
      (rationalScalarExtension D l hl E Y L ι)
      (rationalOrdinaryScalarExtension D l hl E Y E (AlgHom.id (Padic l) E))
      (rationalOrdinaryScalarExtension D l hl E Y L ι)
      (rationalOrdinaryComparison D l hl E Y E (AlgHom.id (Padic l) E))
      (rationalOrdinaryComparison D l hl E Y L ι)
      (rationalOrdinaryScalarUnit l E Y D hl) (rationalConstructibleScalarUnit l E Y D hl)
      (fun K ↦ completed_unit_formula l E Y D hl K) K
  · intro K
    rw [completed_comp_formula,
      (rationalOrdinaryScalar_coherence l E L ι Y M j D hl).2.1,
      completed_unit_formula]
    exact conj_unit_right (𝟭 _) (𝟭 _)
      (rationalScalarExtension D l hl L Y L (AlgHom.id (Padic l) L))
      (rationalScalarExtension D l hl E Y L ι)
      (rationalOrdinaryScalarExtension D l hl L Y L (AlgHom.id (Padic l) L))
      (rationalOrdinaryScalarExtension D l hl E Y L ι)
      (rationalOrdinaryComparison D l hl L Y L (AlgHom.id (Padic l) L))
      (rationalOrdinaryComparison D l hl E Y L ι)
      (rationalOrdinaryScalarUnit l L Y D hl) K
  · intro N _ _ _ k K
    exact conj_comp (𝟭 _) (𝟭 _) (𝟭 _) (𝟭 _)
      (rationalScalarExtension D l hl E Y L ι)
      (rationalScalarExtension D l hl L Y M j)
      (rationalScalarExtension D l hl M Y N k)
      (rationalScalarExtension D l hl E Y M (j.comp ι))
      (rationalScalarExtension D l hl L Y N (k.comp j))
      (rationalScalarExtension D l hl E Y N (k.comp (j.comp ι)))
      (rationalOrdinaryScalarExtension D l hl E Y L ι)
      (rationalOrdinaryScalarExtension D l hl L Y M j)
      (rationalOrdinaryScalarExtension D l hl M Y N k)
      (rationalOrdinaryScalarExtension D l hl E Y M (j.comp ι))
      (rationalOrdinaryScalarExtension D l hl L Y N (k.comp j))
      (rationalOrdinaryScalarExtension D l hl E Y N (k.comp (j.comp ι)))
      (rationalOrdinaryComparison D l hl E Y L ι)
      (rationalOrdinaryComparison D l hl L Y M j)
      (rationalOrdinaryComparison D l hl M Y N k)
      (rationalOrdinaryComparison D l hl E Y M (j.comp ι))
      (rationalOrdinaryComparison D l hl L Y N (k.comp j))
      (rationalOrdinaryComparison D l hl E Y N (k.comp (j.comp ι)))
      (rationalOrdinaryScalarComp l E L ι Y M j D hl)
      (rationalOrdinaryScalarComp l E M (j.comp ι) Y N k D hl)
      (rationalOrdinaryScalarComp l L M j Y N k D hl)
      (rationalOrdinaryScalarComp l E L ι Y N (k.comp j) D hl)
      (rationalConstructibleScalarComp l E L ι Y M j D hl)
      (rationalConstructibleScalarComp l E M (j.comp ι) Y N k D hl)
      (rationalConstructibleScalarComp l L M j Y N k D hl)
      (rationalConstructibleScalarComp l E L ι Y N (k.comp j) D hl)
      (completed_comp_formula l E L ι Y M j D hl)
      (completed_comp_formula l E M (j.comp ι) Y N k D hl)
      (completed_comp_formula l L M j Y N k D hl)
      (completed_comp_formula l E L ι Y N (k.comp j) D hl)
      ((rationalOrdinaryScalar_coherence l E L ι Y M j D hl).2.2 N k) K

end ScalarProofContext

end WeilConjectures
