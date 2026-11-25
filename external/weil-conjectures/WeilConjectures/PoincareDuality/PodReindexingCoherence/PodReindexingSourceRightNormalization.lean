/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingSourceModelFactors

/-! # Right-route normalization of the source-shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
This computes the right composite on K-injective Hom models.
(blueprint: lem-pod-reindexing-source-right-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

/-- Naturality and shift compatibility transport a normalized model composite.
Source: the functorial localization calculation in Stacks 08JA.
(blueprint: lem-pod-reindexing-source-right-normalization) -/
private theorem right_model_calculus
    {CY DY CX DX : Type*} [Category CY] [Category DY] [Category CX] [Category DX]
    [HasShift CY ℤ] [HasShift DY ℤ] [HasShift CX ℤ] [HasShift DX ℤ]
    (QY : CY ⥤ DY) (QX : CX ⥤ DX) (Fc : CY ⥤ CX) (F : DY ⥤ DX)
    [QY.CommShift ℤ] [QX.CommShift ℤ] [Fc.CommShift ℤ] [F.CommShift ℤ]
    (θ : QY ⋙ F ≅ Fc ⋙ QX) [NatTrans.CommShift θ.hom ℤ]
    (A B : CY) (C : CX) (V : DY) (W : DX) (b : ℤ)
    (e : B ⟶ A⟦b⟧) (i : QY.obj B ⟶ V⟦b⟧) (k : QY.obj A ≅ V)
    (d : F.obj V ⟶ W) (o : W ≅ QX.obj C) (f : Fc.obj A ⟶ C)
    (hi : i = QY.map e ≫ (QY.commShiftIso b).hom.app A ≫ k.hom⟦b⟧')
    (hm : F.map k.hom ≫ d ≫ o.hom = θ.hom.app A ≫ QX.map f) :
    F.map i ≫ (F.commShiftIso b).hom.app V ≫ d⟦b⟧' ≫ o.hom⟦b⟧' =
      θ.hom.app B ≫ QX.map (Fc.map e ≫ (Fc.commShiftIso b).hom.app A ≫ f⟦b⟧') ≫
        (QX.commShiftIso b).hom.app C := by
  have ht := NatTrans.shift_app_comm θ.hom b A
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at ht
  rw [hi]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [F.commShiftIso_hom_naturality_assoc]
  rw [← (shiftFunctor DX b).map_comp_assoc, ← (shiftFunctor DX b).map_comp]
  rw [Category.assoc, hm]
  simp only [CategoryTheory.Functor.map_comp]
  rw [reassoc_of% ht]
  have he := θ.hom.naturality e
  simp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [QX.commShiftIso_hom_naturality]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The right route of the source-shift square on localized Hom models.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.

Proof:

1. Write F,K,Q,alpha,beta,kappa as in the model-factor definitions. Apply the source-site
LeftNormalization at source QP with representative P and identity representative isomorphism.
Uniqueness of LeftFormula identifies the chosen chain isomorphism with eY. Invert the equation to
obtain kappa_(P[a],I)^(-1) followed by Hom(Q shift(a)^(-1),id) followed by sourceShift.inv =
Q(eY.inv) followed by Q shift(-a) followed by kappa_(P,I)^(-1)[-a].

2. Apply F to this equation. Naturality of F shift(-a) moves F of the shifted kappa inverse to the
shifted F(kappa inverse). Shifted functoriality groups it with c.derived and the first part of
beta. Comparison.derived_model at (P,I) identifies that grouped composite with
localizationFactors(Hom(P,I)) followed by Q(c.chain(P,I)); all kappa and Hom-factor inverses
cancel.

3. Use shift compatibility of localizationFactors at Hom(P,I), then naturality of that factor
along eY.inv. Finally naturality of Q shift(-a) along c.chain(P,I) moves Q shift to the far right.
The remaining composite is localizationFactors(Hom(P[a],I)), Q of K(eY.inv) followed by
complexShift(-a) followed by c.chain(P,I)[-a], and Q shift(-a) at Hom(KP,KI), as claimed.

This calculates one route, independently of the chain square and of the other route.
(blueprint: lem-pod-reindexing-source-right-normalization) -/
theorem source_right_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (a : ℤ)
    [I.IsKInjective] [CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I)]
    (eY : (hom l E Y s P I)⟦-a⟧ ≅ hom l E Y s (P⟦a⟧) I)
    (hY : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology Y) (podReindexingRing l E Y s) P I a eY) :
    (sourceModelInput l E g s P I a).hom ≫
      ((podReindexingDerivedFunctor l E g s).map
      ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s) ((podReindexingQ l E Y s).obj P)
          a).inv.app ((podReindexingQ l E Y s).obj I)) ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso (-a)).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op ((podReindexingQ l E Y s).obj P),
          ((podReindexingQ l E Y s).obj I))) ≫
      (c.derived.hom.app (op ((podReindexingQ l E Y s).obj P), ((podReindexingQ l E Y s).obj
          I)))⟦-a⟧') ≫
      (sourceModelOutput l E g s P I a).hom =
    (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s (P⟦a⟧) I) ≫
      (podReindexingQ l E X s).map
        ((podReindexingComplexFunctor l E g s).map eY.inv ≫
          (complexShift l E g s (-a)).hom.app (hom l E Y s P I) ≫
          ((c.chain P I).hom)⟦-a⟧') ≫
      ((podReindexingQ l E X s).commShiftIso (-a)).hom.app
        (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I)) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  have hn := (CategoryTheory.RingedHomUniverses.leftShift_existsUnique.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (podReindexingRing l E Y s)).exists.choose_spec
  obtain ⟨e, he, hn⟩ := hn ((podReindexingQ l E Y s).obj P) P I
    (Iso.refl _) a
  have heq : e = eY := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro k
    apply homComplex_hom_ext
    intro p q hpq
    exact (he k p q hpq).trans (hY k p q hpq).symm
  subst e
  have hk (L : K l E Y s) :
      CategoryTheory.ringedSiteOrdinaryHomComparison.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s) L I =
      (podReindexingHomModel l E Y s L I).inv := by
    unfold CategoryTheory.ringedSiteOrdinaryHomComparison
      CategoryTheory.ringedSiteHomComplexMap
    rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]
    erw [Category.id_comp]
    rfl
  simp only [Iso.refl_inv, op_id, ← prod_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp, hk] at hn
  let QY := podReindexingQ l E Y s
  let HY := podReindexingDerivedHom l E Y s
  let k := podReindexingHomModel l E Y s P I
  let kA := podReindexingHomModel l E Y s (P⟦a⟧) I
  let v := HY.mapIso (((QY.commShiftIso a).app P).symm.op.prod
    (Iso.refl (QY.obj I)))
  let σ := CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (podReindexingRing l E Y s) (QY.obj P) a
  change (QY.commShiftIso (-a)).hom.app (hom l E Y s P I) ≫ k.inv⟦-a⟧' ≫
    σ.hom.app (QY.obj I) = QY.map eY.hom ≫ kA.inv ≫ v.hom at hn
  have hi : kA.inv ≫ v.hom ≫ σ.inv.app (QY.obj I) =
      QY.map eY.inv ≫ (QY.commShiftIso (-a)).hom.app (hom l E Y s P I) ≫
        k.inv⟦-a⟧' := by
    apply (cancel_epi (QY.map eY.hom)).mp
    simp only [← QY.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [← reassoc_of% hn]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
  let F := podReindexingDerivedFunctor l E g s
  let Fc := podReindexingComplexFunctor l E g s
  let QX := podReindexingQ l E X s
  let HX := podReindexingDerivedHom l E X s
  let θ := podReindexingDerivedFactors l E g s
  let kX := podReindexingHomModel l E X s (Fc.obj P) (Fc.obj I)
  let t := HX.mapIso (((θ.app P).symm.op.prod (θ.app I)))
  let o := t ≪≫ kX
  let d := c.derived.hom.app (op (QY.obj P), QY.obj I)
  have hm : F.map k.inv ≫ d ≫ o.hom =
      θ.hom.app (hom l E Y s P I) ≫ QX.map (c.chain P I).hom := by
    obtain ⟨hFI, hc⟩ := c.derived_model P I inferInstance
    change d = F.map k.hom ≫ θ.hom.app (hom l E Y s P I) ≫
      QX.map (c.chain P I).hom ≫ kX.inv ≫ t.inv at hc
    rw [hc]
    dsimp only [o]
    simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      ← F.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    erw [Category.comp_id]
  have h := right_model_calculus QY QX Fc F θ (hom l E Y s P I)
    (hom l E Y s (P⟦a⟧) I) (hom l E X s (Fc.obj P) (Fc.obj I))
    _ _ (-a) eY.inv (kA.inv ≫ v.hom ≫ σ.inv.app (QY.obj I)) k.symm
    d o (c.chain P I).hom hi hm
  change F.map (kA.inv ≫ v.hom) ≫
      (F.map (σ.inv.app (QY.obj I)) ≫ (F.commShiftIso (-a)).hom.app _ ≫ d⟦-a⟧') ≫
        o.hom⟦-a⟧' =
    θ.hom.app (hom l E Y s (P⟦a⟧) I) ≫
      QX.map (Fc.map eY.inv ≫ (Fc.commShiftIso (-a)).hom.app (hom l E Y s P I) ≫
        ((c.chain P I).hom)⟦-a⟧') ≫ (QX.commShiftIso (-a)).hom.app _
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h

end WeilConjectures.PodReindexingCoherence
