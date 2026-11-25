/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Restriction comparison on complexes

Source: Stacks Project, Tag 0D6D.
(blueprint: lem-sf-scalar-restriction-complex-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard SheafOfModules.monoidalCategory Functor.leftAdjoint
  proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingRestrictionDirectImage proEtaleRingRestrictionDerivedDirectImage

/-- The canonical cochain computation unit for a right derived functor.
Source: Mathlib right-derived comparison unit
(blueprint: lem-sf-scalar-restriction-complex-normalization). -/
def coefficientDirectComplexUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

private theorem cancel_isomorphism_square {C : Type*} [Category C]
    {A B X Y : C} (e : A ≅ B) (d : X ≅ Y) (f : A ⟶ X) (g : B ⟶ Y)
    (h : f ≫ d.hom = e.hom ≫ g) : e.inv ≫ f = g ≫ d.inv := by
  apply e.inv_comp_eq.mpr
  simpa only [Category.assoc] using d.eq_comp_inv.mpr h

/-- Termwise restriction/direct-image comparison, with its composition identifications.
Source: Stacks Tag 0D6D (blueprint: lem-sf-scalar-restriction-complex-normalization). -/
def scalarRestrictionComplex {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U)
      (S.pull g)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcRestrict (a.map V)).mapHomologicalComplex (.up ℤ) ≅
      (pbcRestrict (a.map U)).mapHomologicalComplex (.up ℤ) ⋙
        (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U)
          (R.pull g)).mapHomologicalComplex (.up ℤ) :=
  let d := proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  Functor.mapHomologicalComplexCompIso d (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcRestrict (a.map U) ⋙
        proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))) (.up ℤ)).symm

/-- The inverse restriction/direct-image comparison has its complex-unit normalization.
Source: Stacks Tag 0D6D (blueprint: lem-sf-scalar-restriction-complex-normalization).
Proof: start with the defining unit equation of the derived comparison. Cancel the
exact restriction factorization isomorphisms on its two sides. The general
isomorphism-square cancellation identity gives the forward square; invert the
ordinary and derived comparison isomorphisms to obtain this inverse square. -/
theorem scalarRestriction_complex_normalization
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (K : CochainComplex (pbcModules U (S.ring U)) ℤ) :
    (coefficientDirectComplexUnit (proEtaleRingModuleDirectImage g
      (R.ring V) (R.ring U) (R.pull g))).app
        (((pbcRestrict (a.map U)).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
        ((pbcRestrict (a.map U)).mapDerivedCategoryFactors.inv.app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage g
        (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv.app
          (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map ((scalarRestrictionComplex a g).inv.app K) ≫
      (pbcRestrict (a.map V)).mapDerivedCategoryFactors.inv.app
        (((proEtaleRingModuleDirectImage g (S.ring V) (S.ring U)
          (S.pull g)).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (pbcDerivedRestrict (a.map V)).map
        ((coefficientDirectComplexUnit (proEtaleRingModuleDirectImage g
          (S.ring V) (S.ring U) (S.pull g))).app K) := by
  let d := proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let dd := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let dc := scalarRestrictionComplex a g
  let qr := coefficientDirectComplexUnit (proEtaleRingModuleDirectImage g
    (R.ring V) (R.ring U) (R.pull g))
  let qs := coefficientDirectComplexUnit (proEtaleRingModuleDirectImage g
    (S.ring V) (S.ring U) (S.pull g))
  let qv := (pbcRestrict (a.map V)).mapDerivedCategoryFactors.inv
  let qu := (pbcRestrict (a.map U)).mapDerivedCategoryFactors.inv
  let rr := proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)
  let rv := pbcDerivedRestrict (a.map V)
  change qr.app _ ≫ rr.map (qu.app K) ≫ dd.inv.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map (dc.inv.app K) ≫ qv.app _ ≫ rv.map (qs.app K)
  have hn := (Classical.choose_spec
    (proEtaleRingRestrictionDerivedDirectImage_existsUnique g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))).1 K
  have hdc : dc.hom.app K =
      (NatIso.mapHomologicalComplex d (.up ℤ)).hom.app K := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hf : qv.app _ ≫ rv.map (qs.app K) ≫
      dd.hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map (dc.hom.app K) ≫
      qr.app (((pbcRestrict (a.map U)).mapHomologicalComplex (.up ℤ)).obj K) ≫
        rr.map (qu.app K) := by
    as_aux_lemma =>
      have hn' : (rv.map (qs.app K) ≫ dd.hom.app (DerivedCategory.Q.obj K)) ≫
          rr.map ((pbcRestrict (a.map U)).mapDerivedCategoryFactors.hom.app K) =
        (pbcRestrict (a.map V)).mapDerivedCategoryFactors.hom.app _ ≫
          (DerivedCategory.Q.map (dc.hom.app K) ≫ qr.app _) := by
        dsimp only [rv, rr, qr, qs, dd, d, coefficientDirectComplexUnit, pbcDerivedRestrict,
          pbcRestrict, proEtaleRingDerivedDirectImage, Functor.comp_obj]
        rw [hdc]
        unfold proEtaleRingRestrictionDerivedDirectImage
        convert hn using 1
        all_goals first
          | rfl
          | repeat' erw [Category.assoc]
            rfl
      have hc := cancel_isomorphism_square
        ((pbcRestrict (a.map V)).mapDerivedCategoryFactors.app _)
        (rr.mapIso ((pbcRestrict (a.map U)).mapDerivedCategoryFactors.app K))
        (rv.map (qs.app K) ≫ dd.hom.app (DerivedCategory.Q.obj K))
        (DerivedCategory.Q.map (dc.hom.app K) ≫ qr.app _)
        (by
          dsimp only [Functor.comp_obj, rv, pbcDerivedRestrict] at hn' ⊢
          simpa only [Functor.mapIso, Iso.app] using hn')
      simpa only [qv, qu, Functor.mapIso, Iso.app, Category.assoc] using hc
  dsimp only [Functor.comp_obj, rv, pbcDerivedRestrict, pbcRestrict,
    proEtaleRingDerivedDirectImage] at hf ⊢
  erw [← Category.assoc]
  apply (Iso.comp_inv_eq (dd.app (DerivedCategory.Q.obj K))).2
  erw [Category.assoc]
  simpa only [qr, coefficientDirectComplexUnit, Functor.rightDerivedFunctorUnitQ,
    Functor.mapIso, Iso.app, Category.assoc] using
      (Iso.eq_inv_comp (DerivedCategory.Q.mapIso (dc.app K))).2 hf.symm

end WeilConjectures.PurCompactSupport
