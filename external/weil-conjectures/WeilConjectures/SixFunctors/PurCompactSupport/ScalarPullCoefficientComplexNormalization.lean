/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarComplexAdjunctionNormalization
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarRestrictionComplexNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # The coefficient square on complexes

Source: Stacks Project, Tags 07A6 and 0D6D.
(blueprint: lem-sf-scalar-pull-coefficient-complex-normalization).
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
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction scalarPull
  HasDerivedCategory.standard SheafOfModules.monoidalCategory Functor.leftAdjoint
  proEtaleRingModulePullback proEtaleRingModuleDirectImage
  pbcExtensionCounit pbcComplexCounit
  reductionChange reductionDerivedChange proEtaleRingRestrictionDirectImage
  proEtaleRingRestrictionDerivedDirectImage

/-- The ordinary coefficient comparison, conjugate to identity on direct-image sections.
Source: Stacks 07A6 (blueprint: lem-sf-scalar-pull-coefficient-complex-normalization). -/
def scalarPullModule {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    pbcExtend (a.map V) ⋙ proEtaleRingModulePullback g (S.ring V) (S.ring U) (S.pull g) ≅
      proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g) ⋙
        pbcExtend (a.map U) :=
  ((((proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g)).comp
    (pbcScalarAdjunction (a.map U))).ofNatIsoRight
      (proEtaleRingRestrictionDirectImage g
        (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).symm).leftAdjointUniq
          ((pbcScalarAdjunction (a.map V)).comp
            (proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g)))).symm

attribute [local irreducible] scalarPullModule

/-- The termwise coefficient comparison with the canonical composition identifications.
Source: Stacks 07A6 (blueprint: lem-sf-scalar-pull-coefficient-complex-normalization). -/
def scalarPullComplex {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    (pbcExtend (a.map V)).mapHomologicalComplex (.up ℤ) ⋙
        (proEtaleRingModulePullback g (S.ring V) (S.ring U)
          (S.pull g)).mapHomologicalComplex (.up ℤ) ≅
      (proEtaleRingModulePullback g (R.ring V) (R.ring U)
        (R.pull g)).mapHomologicalComplex (.up ℤ) ⋙
          (pbcExtend (a.map U)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcExtend (a.map V) ⋙
        proEtaleRingModulePullback g (S.ring V) (S.ring U) (S.pull g))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (scalarPullModule a g) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g) ⋙
        pbcExtend (a.map U))) (.up ℤ)).symm

attribute [local irreducible] scalarPullComplex

private theorem scalarComplexCounit_eq {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules W R) ℤ) :
    pbcComplexCounit φ P = (pbcExtensionCounit φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  simp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors]
  erw [(pbcDerivedExtend φ).map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id]
  exact Category.comp_id _

private def scalarComplexCounit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedExtend φ ⟶
      (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app := pbcComplexCounit φ
  naturality := by
    intro P K f
    rw [scalarComplexCounit_eq, scalarComplexCounit_eq]
    exact (pbcExtensionCounit φ).naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map f)

private theorem geometric_complexTranspose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : CochainComplex C ℤ) (K : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        G.rightDerivedFunctorUnitQ K := by
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj P)
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj P)) = _ at hu
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors] at hu
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id] at hu
  erw [Category.comp_id] at hu
  erw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hu, Category.assoc]
  have hn := G.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map f)
  dsimp only [Functor.comp_map] at hn
  erw [← hn, ← Category.assoc, ← Functor.map_comp]
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The derived coefficient comparison has the ordinary complex normalization.
This is a single-variable comparison and contains no tensor product.

Source: Stacks 07A6 and 0D6D, comparison of the derived adjunctions
(blueprint: lem-sf-scalar-pull-coefficient-complex-normalization).

Proof: transpose through the two composite scalar/geometric adjunctions.
The ordinary comparison was defined by the restriction/direct-image isomorphism
which is identity on sections. The derived restriction/direct-image comparison
is its unique extension compatible with the direct-image computation unit.
The scalar adjunction and geometric adjunction have their canonical derived
unit/counit normalization. Their composite transpose therefore identifies both
sides with the same restriction/direct-image comparison followed by its unit.
Naturality of the universal derived counits moves the ordinary comparison
through the quotient. Injectivity of the composite adjunction bijection gives
the displayed equality. This argument uses the universal counits, rather than
inverting them, and therefore applies to arbitrary complexes and nonflat changes. -/
theorem scalarPull_complex_normalization
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (P : CochainComplex (pbcModules V (R.ring V)) ℤ) :
    (scalarPull a g).inv.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedExtend (a.map U)).map
        ((proEtaleRingDerivedPullbackFactors g (R.ring V) (R.ring U)
          (R.pull g)).hom.app P) ≫
      pbcComplexCounit (a.map U)
        (((proEtaleRingModulePullback g (R.ring V) (R.ring U)
          (R.pull g)).mapHomologicalComplex (.up ℤ)).obj P) =
    (pull S g).map (pbcComplexCounit (a.map V) P) ≫
      (proEtaleRingDerivedPullbackFactors g (S.ring V) (S.ring U)
        (S.pull g)).hom.app (((pbcExtend (a.map V)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((scalarPullComplex a g).hom.app P) := by
  let r := proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g)
  let s := proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g)
  let v := pbcScalarAdjunction (a.map V)
  let u := pbcScalarAdjunction (a.map U)
  let rd := proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)
  let sd := proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)
  let vd := pbcDerivedScalarAdjunction (a.map V)
  let ud := pbcDerivedScalarAdjunction (a.map U)
  let rc := r.mapHomologicalComplex (.up ℤ)
  let sc := s.mapHomologicalComplex (.up ℤ)
  let vc := v.mapHomologicalComplex (.up ℤ)
  let uc := u.mapHomologicalComplex (.up ℤ)
  let d := proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let dd := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let dc := scalarRestrictionComplex a g
  let er := (proEtaleRingModulePullback g (R.ring V) (R.ring U)
    (R.pull g)).mapDerivedCategoryFactors.hom
  let es := (proEtaleRingModulePullback g (S.ring V) (S.ring U)
    (S.pull g)).mapDerivedCategoryFactors.hom
  let ev := scalarComplexCounit (a.map V)
  let eu := scalarComplexCounit (a.map U)
  let qr := coefficientDirectComplexUnit (proEtaleRingModuleDirectImage g
    (R.ring V) (R.ring U) (R.pull g))
  let qs := coefficientDirectComplexUnit (proEtaleRingModuleDirectImage g
    (S.ring V) (S.ring U) (S.pull g))
  let qv := (pbcRestrict (a.map V)).mapDerivedCategoryFactors.inv
  let qu := (pbcRestrict (a.map U)).mapDerivedCategoryFactors.inv
  have hrc := geometric_complexTranspose r
  have hsc := geometric_complexTranspose s
  have hvc := scalarComplexTranspose (a.map V)
  have huc := scalarComplexTranspose (a.map U)
  have hleft := normalizedAdjunction_composition rc uc rd ud er eu qr qu
    (by simpa only [rd, proEtaleRingDerivedAdjunction, er, qr,
      coefficientDirectComplexUnit] using hrc)
    huc
  have hright := normalizedAdjunction_composition vc sc vd sd ev es qv qs hvc
    (by simpa only [sd, proEtaleRingDerivedAdjunction, es, qs,
      coefficientDirectComplexUnit] using hsc)
  have hν (K : CochainComplex (pbcModules V (R.ring V)) ℤ) :
      (rc.comp uc).homEquiv _ _ ((scalarPullComplex a g).inv.app K) ≫
        dc.inv.app _ = (vc.comp sc).unit.app K := by
    as_aux_lemma =>
      apply HomologicalComplex.hom_ext
      intro i
      dsimp only [dc]
      unfold scalarPullComplex scalarPullModule scalarRestrictionComplex
      change (r.comp u).homEquiv _ _
        ((((r.comp u).ofNatIsoRight d.symm).leftAdjointUniq (v.comp s)).hom.app
          (K.X i)) ≫ d.inv.app _ = (v.comp s).unit.app (K.X i)
      simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom] using
        Adjunction.homEquiv_leftAdjointUniq_hom_app
          ((r.comp u).ofNatIsoRight d.symm) (v.comp s) (K.X i)
  let rr := proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)
  let rv := pbcDerivedRestrict (a.map V)
  have hρ (K : CochainComplex (pbcModules U (S.ring U)) ℤ) :
      qr.app _ ≫ rr.map (qu.app K) ≫ dd.inv.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map (dc.inv.app K) ≫ qv.app _ ≫ rv.map (qs.app K) := by
    simpa only [qr, qs, qv, qu, rr, rv, dc, dd] using
      scalarRestriction_complex_normalization a g K
  have he := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    (rc.comp uc) (vc.comp sc) (rd.comp ud) (vd.comp sd)
    (fun K ↦ (pbcDerivedExtend (a.map U)).map (er.app K) ≫ eu.app _)
    (fun K ↦ (pull S g).map (ev.app K) ≫ es.app _)
    (fun K ↦ qr.app _ ≫ rr.map (qu.app K))
    (fun K ↦ qv.app _ ≫ rv.map (qs.app K))
    (fun K L f ↦ by simpa only [Category.assoc] using hleft K L f)
    (fun K L f ↦ by
      dsimp only [Functor.comp_obj, rv, pbcDerivedRestrict, pull] at hright ⊢
      simpa only [Category.assoc] using hright K L f)
    dc.symm dd.symm (fun K ↦ (scalarPullComplex a g).inv.app K) hν
    (fun K ↦ by
      have hp := hρ K
      dsimp only [Functor.comp_obj, rv, pbcDerivedRestrict, pbcRestrict] at hp ⊢
      convert hp using 1 <;> first | rfl | simp only [Category.assoc, Iso.symm_hom]) P
  have he' : (scalarPull a g).hom.app (DerivedCategory.Q.obj P) ≫
    ((pull S g).map (pbcComplexCounit (a.map V) P) ≫
      (proEtaleRingDerivedPullbackFactors g (S.ring V) (S.ring U)
        (S.pull g)).hom.app _) =
    ((pbcDerivedExtend (a.map U)).map
      ((proEtaleRingDerivedPullbackFactors g (R.ring V) (R.ring U)
        (R.pull g)).hom.app P) ≫ pbcComplexCounit (a.map U) _) ≫
      DerivedCategory.Q.map ((scalarPullComplex a g).inv.app P) := by
    as_aux_lemma =>
      unfold scalarPull
      dsimp only [rd, ud, vd, sd, dd, er, es, eu, ev,
        scalarComplexCounit, proEtaleRingDerivedPullbackFactors, pull,
        Functor.comp_obj] at he ⊢
      convert he using 1
      rfl
  have ht := congrArg (fun f ↦ (scalarPull a g).inv.app (DerivedCategory.Q.obj P) ≫
    f ≫ DerivedCategory.Q.map ((scalarPullComplex a g).hom.app P)) he'
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at ht
  dsimp only [Functor.comp_obj] at ht
  erw [DerivedCategory.Q.map_id, Category.comp_id] at ht
  exact ht.symm

end WeilConjectures.PurCompactSupport
