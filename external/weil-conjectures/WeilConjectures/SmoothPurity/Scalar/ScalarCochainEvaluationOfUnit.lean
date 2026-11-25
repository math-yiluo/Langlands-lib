/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement

/-! # Scalar cochain counits from the ordinary unit square

Source: Stacks 03D7, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
private theorem counit_square
    {X Y x y : Type*} [Category X] [Category Y] [Category x] [Category y]
    {L : X ⥤ Y} {R : Y ⥤ X} {l : x ⥤ y} {r : y ⥤ x}
    (adj : L ⊣ R) (level : l ⊣ r) (E : X ⥤ x) (F : Y ⥤ y)
    (δ : R ⋙ E ≅ F ⋙ r) (γ : L ⋙ F ≅ E ⋙ l)
    (ht : ∀ (P : X) (N : Y) (f : L.obj P ⟶ N),
      E.map ((adj.homEquiv _ _) f) ≫ δ.hom.app N =
        (level.homEquiv _ _) (γ.inv.app P ≫ F.map f))
    (P : X) (N : Y) (P₀ : x) (N₀ : y)
    (a : E.obj P ⟶ P₀) (b : F.obj N ⟶ N₀)
    (f : L.obj P ⟶ N) (g : l.obj P₀ ⟶ N₀)
    (hu : E.map ((adj.homEquiv _ _) f) ≫ δ.hom.app N ≫ r.map b =
      a ≫ (level.homEquiv _ _) g) :
    F.map f ≫ b = γ.hom.app P ≫ l.map a ≫ g := by
  apply (cancel_epi (γ.inv.app P)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (level.homEquiv _ _).injective
  rw [← Category.assoc, level.homEquiv_naturality_right,
    ← ht, level.homEquiv_naturality_left]
  simpa only [Category.assoc] using hu

section LocalizationSquare
universe a b c d va vb vc vd wa wb wc wd
variable {X : Type a} {Y : Type b} {Z : Type c} {V : Type d}
  [Category.{va} X] [Category.{vb} Y] [Category.{vc} Z] [Category.{vd} V]
  [Abelian X] [Abelian Y] [Abelian Z] [Abelian V]
  [HasDerivedCategory.{wa} X] [HasDerivedCategory.{wb} Y]
  [HasDerivedCategory.{wc} Z] [HasDerivedCategory.{wd} V]
  (R : X ⥤ Y) (E : Y ⥤ V) (F : X ⥤ Z) (S : Z ⥤ V)
  [R.Additive] [E.Additive] [F.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

private theorem localization_square (δ : R ⋙ E ≅ F ⋙ S)
    (P : CochainComplex X ℤ) :
    ((Functor.mapDerivedCategoryCompIso R E) ≪≫
        Functor.mapDerivedCategoryNatIso δ ≪≫
        (Functor.mapDerivedCategoryCompIso F S).symm).hom.app (DerivedCategory.Q.obj P) ≫
        S.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        S.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      E.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        E.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  have h₁ := Functor.mapDerivedCategoryCompIso_fac F S P
  have h₂ := Functor.mapDerivedCategoryCompIso_fac R E P
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ S))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  have hj : (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ E))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  erw [hi, CategoryTheory.Functor.map_id, Category.comp_id] at h₁
  erw [hj, CategoryTheory.Functor.map_id, Category.comp_id] at h₂
  erw [h₁, Functor.mapDerivedCategoryNatIso_fac]
  erw [← h₂]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end LocalizationSquare

section ScalarUnit
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{r}}
  {φ : R ⟶ S} (A : SemilinearSections.ScalarData.{c, v, r} φ)

private theorem scalar_cochain_unit
    (P : CochainComplex (SemilinearSections.Mod J R) ℤ) :
    (A.adjunction.homEquiv _ _) (A.model.ε.app P) ≫
        (SemilinearSections.res φ).mapDerivedCategoryFactors.hom.app
          ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((A.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  let U := SemilinearSections.res φ
  let EC := A.model.E.mapHomologicalComplex (.up ℤ)
  let ν : DerivedCategory.Q ⟶ EC ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q A.adjunction.unit ≫
      Functor.whiskerRight A.model.ε U.mapDerivedCategory ≫
      Functor.whiskerLeft EC U.mapDerivedCategoryFactors.hom
  let η : DerivedCategory.Q ⟶ EC ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight
      (A.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit DerivedCategory.Q
  have hν (K : CochainComplex (SemilinearSections.Mod J R) ℤ)
      (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
      ν.app K = η.app K := by
    have h := A.transpose_model K (EC.obj K) hK (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at h
    simpa only [ν, η, EC, U, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Adjunction.homEquiv_unit, Category.assoc] using h
  obtain ⟨K, q, hK, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  have : QuasiIso q := hq
  have : IsIso (DerivedCategory.Q.map q) := by infer_instance
  rw [Adjunction.homEquiv_unit, Category.assoc]
  change ν.app P = η.app P
  apply (cancel_epi (DerivedCategory.Q.map q)).1
  rw [ν.naturality, η.naturality, hν K hK]

end ScalarUnit

section Ordinary
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
set_option backward.defeqAttrib.useBackward true
universe c v r
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B F : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
  (α : ∀ n, B n ⟶ F n) (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)
  (A : SemilinearSections.ScalarSystems.{c, v, r} J B τ F σ α hα)

/-- An ordinary scalar evaluation comparison preserving the actual units also
preserves the universal cochain counits.
Source: Stacks 06YY and 07A6
(blueprint: stage3-pur-scalar-cochain-unit-descent).
Proof: for each scalar datum, its normalized transpose formula gives the cochain
unit formula on K-flat complexes. Both sides are natural transformations out of
localization Q. Resolve an arbitrary source complex by a K-flat complex and
cancel its localized augmentation to obtain the unit formula on all complexes.
The exact-functor localization identities identify the derived restriction square
with its ordinary cochain square. The assumed ordinary unit equation holds in
each cochain degree. Localize it and apply the supplied derived transpose identity
and the two cochain unit formulas. The finite derived adjunction Hom bijection
then gives the counit equation. No faithfulness of evaluation, coefficient
flatness, or preservation of K-flatness by evaluation is assumed. -/
theorem scalarCochainEvaluation_of_unit (n : ℕ)
    (ρ : A.scalar.model.E ⋙ SemilinearSections.evaluation J F σ n ≅
      SemilinearSections.evaluation J B τ n ⋙ (A.levels n).model.E)
    (hρ : ∀ M,
      (SemilinearSections.evaluation J B τ n).map
          (A.scalar.ordinaryAdjunction.unit.app M) ≫
        (SemilinearSections.restrictionEvaluation_existsUnique
          J B τ F σ α hα n).exists.choose.hom.app (A.scalar.model.E.obj M) ≫
        (SemilinearSections.res (α n)).map (ρ.hom.app M) =
      (A.levels n).ordinaryAdjunction.unit.app
        ((SemilinearSections.evaluation J B τ n).obj M))
    (P : CochainComplex (SemilinearSections.Systems J B τ) ℤ) :
    (SemilinearSections.e J F σ n).map (A.scalar.model.ε.app P) ≫
        (SemilinearSections.evaluation J F σ n).mapDerivedCategoryFactors.hom.app
          ((A.scalar.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ρ (.up ℤ)).hom.app P) =
      (A.evaluation n).hom.app (DerivedCategory.Q.obj P) ≫
        (A.levels n).T.map
          ((SemilinearSections.evaluation J B τ n).mapDerivedCategoryFactors.hom.app P) ≫
        (A.levels n).model.ε.app
          (((SemilinearSections.evaluation J B τ n).mapHomologicalComplex (.up ℤ)).obj P) := by
  let eE := SemilinearSections.evaluation J B τ n
  let eL := SemilinearSections.evaluation J F σ n
  let rs := SemilinearSections.res (SemilinearSections.systemMap J B τ F σ α hα)
  let rf := SemilinearSections.res (α n)
  let es := A.scalar.model.E.mapHomologicalComplex (.up ℤ)
  let ef := (A.levels n).model.E.mapHomologicalComplex (.up ℤ)
  let ev := eE.mapHomologicalComplex (.up ℤ)
  let d := (SemilinearSections.restrictionEvaluation_existsUnique
    J B τ F σ α hα n).exists.choose
  let p := (NatIso.mapHomologicalComplex ρ (.up ℤ)).hom.app P
  have hchain :
      ev.map ((A.scalar.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app (es.obj P) ≫
        (rf.mapHomologicalComplex (.up ℤ)).map p =
      ((A.levels n).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app
        (ev.obj P) := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact hρ (P.X i)
  apply counit_square A.scalar.adjunction (A.levels n).adjunction
    eE.mapDerivedCategory eL.mapDerivedCategory
    (SemilinearSections.restrictionEvaluation J B τ F σ α hα n)
    (A.evaluation n) (A.transpose_evaluation n)
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj (es.obj P))
    (DerivedCategory.Q.obj (ev.obj P)) (DerivedCategory.Q.obj (ef.obj (ev.obj P)))
    (eE.mapDerivedCategoryFactors.hom.app P)
    (eL.mapDerivedCategoryFactors.hom.app (es.obj P) ≫ DerivedCategory.Q.map p)
    (A.scalar.model.ε.app P) ((A.levels n).model.ε.app (ev.obj P))
  apply (cancel_mono (rf.mapDerivedCategoryFactors.hom.app (ef.obj (ev.obj P)))).1
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality]
  have hl := localization_square rs eE eL rf d (es.obj P)
  change (SemilinearSections.restrictionEvaluation J B τ F σ α hα n).hom.app
      (DerivedCategory.Q.obj (es.obj P)) ≫
        rf.mapDerivedCategory.map (eL.mapDerivedCategoryFactors.hom.app (es.obj P)) ≫
        rf.mapDerivedCategoryFactors.hom.app
          ((eL.mapHomologicalComplex (.up ℤ)).obj (es.obj P)) = _ at hl
  erw [reassoc_of% hl]
  erw [← CategoryTheory.Functor.map_comp_assoc, scalar_cochain_unit]
  erw [CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [scalar_cochain_unit]
  erw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp, hchain]
  rfl

end Ordinary
end WeilConjectures
