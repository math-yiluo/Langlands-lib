/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Target-shift square for normalized reindexing

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: lem-pod-reindexing-derived-target-shift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme SheafOfModules
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  homComplexFunctor homComplexπ WeilConjectures.podReindexingCoefficient

set_option allowUnsafeReducibility true in
attribute [local reducible] homComplex CochainComplex.shiftFunctor Functor.mapHomologicalComplex

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_shift_pasting
    {CY CX DY DX : Type*} [Category* CY] [Category* CX] [Category* DY] [Category* DX]
    [HasShift CY ℤ] [HasShift CX ℤ] [HasShift DY ℤ] [HasShift DX ℤ]
    (QY : CY ⥤ DY) (QX : CX ⥤ DX) (Fc : CY ⥤ CX) (F : DY ⥤ DX)
    [QY.CommShift ℤ] [QX.CommShift ℤ] [Fc.CommShift ℤ] [F.CommShift ℤ]
    (UY : CY ⥤ CY) (UX : CX ⥤ CX) (HY : DY ⥤ DY) (HX : DX ⥤ DX)
    [HY.CommShift ℤ] [HX.CommShift ℤ]
    (θ : QY ⋙ F ≅ Fc ⋙ QX) [NatTrans.CommShift θ.hom ℤ]
    (AY : UY ⋙ QY ⟶ QY ⋙ HY) (AX : UX ⋙ QX ⟶ QX ⋙ HX)
    (d : HY ⋙ F ⟶ F ⋙ HX) (I : CY) (b : ℤ)
    (ey : (UY.obj I)⟦b⟧ ≅ UY.obj (I⟦b⟧))
    (ex : (UX.obj (Fc.obj I))⟦b⟧ ≅ UX.obj ((Fc.obj I)⟦b⟧))
    (k : Fc.obj (UY.obj I) ⟶ UX.obj (Fc.obj I))
    (ks : Fc.obj (UY.obj (I⟦b⟧)) ⟶ UX.obj (Fc.obj (I⟦b⟧)))
    [IsIso (AY.app (I⟦b⟧))]
    (hY : QY.map ey.hom ≫ AY.app (I⟦b⟧) ≫
        HY.map ((QY.commShiftIso b).hom.app I) ≫
        (HY.commShiftIso b).hom.app (QY.obj I) =
      (QY.commShiftIso b).hom.app (UY.obj I) ≫ (AY.app I)⟦b⟧')
    (hX : QX.map ex.hom ≫ AX.app ((Fc.obj I)⟦b⟧) ≫
        HX.map ((QX.commShiftIso b).hom.app (Fc.obj I)) ≫
        (HX.commShiftIso b).hom.app (QX.obj (Fc.obj I)) =
      (QX.commShiftIso b).hom.app (UX.obj (Fc.obj I)) ≫ (AX.app (Fc.obj I))⟦b⟧')
    (hc : Fc.map ey.hom ≫ ks ≫ UX.map ((Fc.commShiftIso b).hom.app I) =
      (Fc.commShiftIso b).hom.app (UY.obj I) ≫ k⟦b⟧' ≫ ex.hom)
    (hm : F.map (AY.app I) ≫ d.app (QY.obj I) ≫ HX.map (θ.hom.app I) =
      θ.hom.app (UY.obj I) ≫ QX.map k ≫ AX.app (Fc.obj I))
    (hms : F.map (AY.app (I⟦b⟧)) ≫ d.app (QY.obj (I⟦b⟧)) ≫
        HX.map (θ.hom.app (I⟦b⟧)) =
      θ.hom.app (UY.obj (I⟦b⟧)) ≫ QX.map ks ≫ AX.app (Fc.obj (I⟦b⟧))) :
    d.app ((QY.obj I)⟦b⟧) ≫ HX.map ((F.commShiftIso b).hom.app (QY.obj I)) ≫
        (HX.commShiftIso b).hom.app (F.obj (QY.obj I)) =
      F.map ((HY.commShiftIso b).hom.app (QY.obj I)) ≫
        (F.commShiftIso b).hom.app (HY.obj (QY.obj I)) ≫ (d.app (QY.obj I))⟦b⟧' := by
  have ht (J : CY) := NatTrans.shift_app_comm θ.hom b J
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at ht
  have hd := d.naturality ((QY.commShiftIso b).hom.app I)
  have ha := AX.naturality ((Fc.commShiftIso b).hom.app I)
  have he := θ.hom.naturality ey.hom
  simp only [Functor.comp_map] at hd ha he
  apply (cancel_epi (F.map (QY.map ey.hom ≫ AY.app (I⟦b⟧) ≫
    HY.map ((QY.commShiftIso b).hom.app I)))).mp
  apply (cancel_mono ((HX.map (θ.hom.app I))⟦b⟧')).mp
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hd, ← HX.commShiftIso_hom_naturality]
  simp only [← HX.map_comp_assoc]
  rw [ht I]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hms, ← reassoc_of% ha, reassoc_of% he]
  simp only [← QX.map_comp_assoc]
  rw [hc]
  simp only [QX.map_comp, Category.assoc]
  simp only [Functor.comp_obj]
  rw [hX, QX.commShiftIso_hom_naturality_assoc, ← reassoc_of% (ht (UY.obj I))]
  have hy := congrArg F.map hY
  simp only [CategoryTheory.Functor.map_comp] at hy
  rw [reassoc_of% hy, F.commShiftIso_hom_naturality_assoc]
  simp only [← (shiftFunctor DX b).map_comp]
  rw [hm]

private theorem model_inv (W : Scheme.{u}) (s : Option ℕ)
    (P I : K l E W s) [I.IsKInjective] :
    (podReindexingHomModel l E W s P I).inv =
      ringedSiteOrdinaryHomComparison.{u + 1, u, u, u + 2}
        (ProEt.topology W) (podReindexingRing l E W s) P I := by
  simp only [podReindexingHomModel, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    ringedSiteOrdinaryHomComparison, ringedSiteHomComplexMap, op_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

private abbrev fixedHom (W : Scheme.{u}) (s : Option ℕ)
    (M : podReindexingDerived l E W s) :=
  (Functor.curry.obj (podReindexingDerivedHom l E W s)).obj (op M)

private def ordinaryToFixed (W : Scheme.{u}) (s : Option ℕ)
    (M : podReindexingDerived l E W s) (P : K l E W s)
    (eM : (podReindexingQ l E W s).obj P ≅ M) :
    (podReindexingHom l E W s).obj (op P) ⋙ podReindexingQ l E W s ⟶
      podReindexingQ l E W s ⋙ fixedHom l E W s M where
  app I := ringedSiteOrdinaryHomComparison.{u + 1, u, u, u + 2}
    (ProEt.topology W) (podReindexingRing l E W s) P I ≫
      (podReindexingDerivedHom l E W s).map (Prod.mkHom eM.inv.op (𝟙 _))
  naturality {I J} f := by
    have h := (CategoryTheory.RingedHomUniverses.ordinaryComparison.{u + 1, u, u, u + 2}
      (ProEt.topology W) (podReindexingRing l E W s)).naturality
        (Prod.mkHom (𝟙 (op P)) f)
    simp only [CategoryTheory.RingedHomUniverses.ordinaryComparison_app,
      CategoryTheory.RingedHomUniverses.ordinaryBifunctor, Functor.uncurry_obj_map,
      unop_id, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      Functor.comp_map, Functor.prod_map, Functor.op_map] at h
    dsimp only [fixedHom, Functor.comp_map, Functor.curry_obj_obj_map]
    rw [← Category.assoc, h]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id]
    congr 3
    exact Category.id_comp eM.inv.op

private theorem normalized_fixed_shift (W : Scheme.{u}) (s : Option ℕ)
    (M : podReindexingDerived l E W s) (P I : K l E W s)
    (eM : (podReindexingQ l E W s).obj P ≅ M) (b : ℤ) :
    ∃ e : (hom l E W s P I)⟦b⟧ ≅ hom l E W s P (I⟦b⟧),
      CategoryTheory.RingedHomUniverses.RightFormula.{u + 1, u, u}
        (ProEt.topology W) (podReindexingRing l E W s) P I b e ∧
      (podReindexingQ l E W s).map e.hom ≫
          (ordinaryToFixed l E W s M P eM).app (I⟦b⟧) ≫
          (fixedHom l E W s M).map (((podReindexingQ l E W s).commShiftIso b).hom.app I) ≫
          ((fixedHom l E W s M).commShiftIso b).hom.app
            ((podReindexingQ l E W s).obj I) =
        ((podReindexingQ l E W s).commShiftIso b).hom.app (hom l E W s P I) ≫
          ((ordinaryToFixed l E W s M P eM).app I)⟦b⟧' := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W s)
  obtain ⟨e, he, h⟩ :=
    (CategoryTheory.RingedHomUniverses.rightShift_existsUnique.{u + 1, u, u, u + 2}
      (ProEt.topology W) (podReindexingRing l E W s)).exists.choose_spec M P I eM b
  refine ⟨e, he, ?_⟩
  simpa only [ordinaryToFixed, fixedHom, Functor.curry_obj_obj_map,
    Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, prod_comp,
    Category.id_comp, Category.comp_id] using h

private lemma complexShift_hom_f {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (s : Option ℕ) (b : ℤ) (P : K l E Y s) (r : ℤ) :
    ((complexShift l E g s b).hom.app P).f r = 𝟙 _ := by
  rfl

private lemma chain_projection' {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) {SX : Closed l E X s} {SY : Closed l E Y s}
    {TX : Models l E X s SX} {TY : Models l E Y s SY}
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s)
    (n p q : ℤ) (h : p + n = q) (U : X.ProEtᵒᵖ) (V : (Over U.unop)ᵒᵖ)
    (z : ((hom l E Y s P I).X n).val.obj
      (op ((proEtaleIsoPostcompose g).obj U.unop)))
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj V.unop.left))) :
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) n p q h).val.app U
        (((c.chain P I).hom.f n).val.app U z)).app V).hom x =
      (((proj l E Y s P I n p q h).val.app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) z).app
          (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom)))).hom x := by
  subst q
  exact c.chain_projection P I n p U.unop V.unop.left V.unop.hom z x

private theorem chain_target_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (b : ℤ)
    (eY : (hom l E Y s P I)⟦b⟧ ≅ hom l E Y s P (I⟦b⟧))
    (eX : (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I))⟦b⟧ ≅
      hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
        (((podReindexingComplexFunctor l E g s).obj I)⟦b⟧))
    (hY : CategoryTheory.RingedHomUniverses.RightFormula.{u + 1, u, u}
      (ProEt.topology Y) (podReindexingRing l E Y s) P I b eY)
    (hX : CategoryTheory.RingedHomUniverses.RightFormula.{u + 1, u, u}
      (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) b eX) :
    (podReindexingComplexFunctor l E g s).map eY.hom ≫
        (c.chain P (I⟦b⟧)).hom ≫
        ((podReindexingHom l E X s).obj
          (op ((podReindexingComplexFunctor l E g s).obj P))).map
            ((complexShift l E g s b).hom.app I) =
      (complexShift l E g s b).hom.app (hom l E Y s P I) ≫
        ((c.chain P I).hom)⟦b⟧' ≫ eX.hom := by
  apply HomologicalComplex.hom_ext
  intro r
  apply homComplex_hom_ext
  intro p q hpq
  subst q
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    complexShift_hom_f,
    Category.assoc]
  erw [Category.id_comp, hX r p (p + r) rfl]
  have hmap := homComplexFunctor_obj_map_f_π (R := podReindexingRing l E X s)
    (L := (podReindexingComplexFunctor l E g s).obj P)
    (((complexShift l E g s b).hom.app I)) r p (p + r) rfl
  erw [hmap]
  simp only [complexShift_hom_f]
  have hid := SheafOfModules.homObjMap_id (R := podReindexingRing l E X s)
    (M := ((podReindexingComplexFunctor l E g s).obj P).X p)
    (N := ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧)).X (p + r))
  erw [hid, Category.comp_id]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧)) r p (p + r) rfl).val.app U
        (((c.chain P (I⟦b⟧)).hom.f r).val.app U
          ((((podReindexingComplexFunctor l E g s).map eY.hom).f r).val.app U z))).app V).hom x =
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) (r + b) p (p + r + b)
        (by omega)).val.app U (((c.chain P I).hom.f (r + b)).val.app U z)).app V).hom x
  rw [chain_projection', chain_projection']
  have hy := congrArg
    (fun f ↦ ((f.val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) z).app
      (op (Over.mk ((proEtaleIsoPostcompose g).map V.unop.hom)))).hom x)
    (hY r p (p + r) rfl)
  exact hy

set_option allowUnsafeReducibility true in
attribute [local semireducible] Functor.mapHomologicalComplex

private theorem model_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) [hI : I.IsKInjective] :
    (podReindexingDerivedFunctor l E g s).map
        ((ordinaryToFixed l E Y s ((podReindexingQ l E Y s).obj P) P (Iso.refl _)).app I) ≫
      c.derived.hom.app (op ((podReindexingQ l E Y s).obj P),
        (podReindexingQ l E Y s).obj I) ≫
      (fixedHom l E X s ((podReindexingDerivedFunctor l E g s).obj
        ((podReindexingQ l E Y s).obj P))).map
          ((podReindexingDerivedFactors l E g s).hom.app I) =
    (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s P I) ≫
      (podReindexingQ l E X s).map (c.chain P I).hom ≫
      (ordinaryToFixed l E X s
        ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj P))
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingDerivedFactors l E g s).app P).symm).app
          ((podReindexingComplexFunctor l E g s).obj I) := by
  obtain ⟨hFI, h⟩ := c.derived_model P I hI
  let := hFI
  simp only [ordinaryToFixed, Iso.refl_inv, op_id, ← prod_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← model_inv, h]
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, Iso.symm_hom,
    fixedHom, Functor.curry_obj_obj_map, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← CategoryTheory.Functor.map_comp, prod_comp,
    Category.id_comp, Iso.symm_inv]
  rw [model_inv]
  congr 5
  all_goals simp only [Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app]
  · exact Category.comp_id _
  · rfl

private def comparisonAt {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (M : podReindexingDerived l E Y s) :
    fixedHom l E Y s M ⋙ podReindexingDerivedFunctor l E g s ≅
      podReindexingDerivedFunctor l E g s ⋙
        fixedHom l E X s ((podReindexingDerivedFunctor l E g s).obj M) :=
  NatIso.ofComponents (fun N ↦ c.derived.app (op M, N)) (by
    intro N N' f
    have h := c.derived.hom.naturality (Prod.mkHom (𝟙 (op M)) f)
    change (podReindexingDerivedFunctor l E g s).map
        ((podReindexingDerivedHom l E Y s).map (Prod.mkHom (𝟙 (op M)) f)) ≫
          c.derived.hom.app (op M, N') =
      c.derived.hom.app (op M, N) ≫ (podReindexingDerivedHom l E X s).map
        (Prod.mkHom ((podReindexingDerivedFunctor l E g s).map (𝟙 M)).op
          ((podReindexingDerivedFunctor l E g s).map f)) at h
    have hid : ((podReindexingDerivedFunctor l E g s).map (𝟙 M)).op =
        𝟙 (op ((podReindexingDerivedFunctor l E g s).obj M)) :=
      congrArg Quiver.Hom.op ((podReindexingDerivedFunctor l E g s).map_id M)
    rw [hid] at h
    exact h)

/--
The target-shift square for the normalized comparison on localized
representatives.  Resolve the second representative by a K-injective complex,
expand `Comparison.derived_model` at the two pairs, and compare every
Hom-product projection after unsigned target reindexing.  The fixed
`chain_projection` field identifies the projections, so product extensionality
and localization yield the displayed equation.  This is the representative
step of the target-shift argument; the passage to arbitrary objects is a
separate descent theorem.
Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: lem-pod-reindexing-derived-target-shift).
-/
private theorem derived_target_shift_model
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (P I : K l E Y s) (hI : I.IsKInjective) (b : ℤ) :
    c.derived.hom.app
        (op ((podReindexingQ l E Y s).obj P),
          ((podReindexingQ l E Y s).obj I)⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (𝟙 (op ((podReindexingDerivedFunctor l E g s).obj
          ((podReindexingQ l E Y s).obj P))))
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app
            ((podReindexingQ l E Y s).obj I))) ≫
      ((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingDerivedFunctor l E g s).obj
          ((podReindexingQ l E Y s).obj P))).commShiftIso b).hom.app
            ((podReindexingDerivedFunctor l E g s).obj
              ((podReindexingQ l E Y s).obj I)) =
    (podReindexingDerivedFunctor l E g s).map
      (((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s)
        ((podReindexingQ l E Y s).obj P)).commShiftIso b).hom.app
          ((podReindexingQ l E Y s).obj I)) ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app
        ((podReindexingDerivedHom l E Y s).obj
          (op ((podReindexingQ l E Y s).obj P),
            ((podReindexingQ l E Y s).obj I))) ≫
      (c.derived.hom.app
        (op ((podReindexingQ l E Y s).obj P),
          ((podReindexingQ l E Y s).obj I)) )⟦b⟧' := by
  let := hI
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let QY := podReindexingQ l E Y s
  let QX := podReindexingQ l E X s
  let Fc := podReindexingComplexFunctor l E g s
  let F := podReindexingDerivedFunctor l E g s
  let θ := podReindexingDerivedFactors l E g s
  let UY := (podReindexingHom l E Y s).obj (op P)
  let UX := (podReindexingHom l E X s).obj (op (Fc.obj P))
  let HY := fixedHom l E Y s (QY.obj P)
  let HX := fixedHom l E X s (F.obj (QY.obj P))
  let AY := ordinaryToFixed l E Y s (QY.obj P) P (Iso.refl _)
  let AX := ordinaryToFixed l E X s (F.obj (QY.obj P)) (Fc.obj P) (θ.app P).symm
  let d := comparisonAt l E g s SX SY TX TY c (QY.obj P)
  obtain ⟨ey, hey, hy⟩ := normalized_fixed_shift l E Y s (QY.obj P) P I (Iso.refl _) b
  obtain ⟨ex, hex, hx⟩ := normalized_fixed_shift l E X s (F.obj (QY.obj P))
    (Fc.obj P) (Fc.obj I) (θ.app P).symm b
  have : IsIso (AY.app (I⟦b⟧)) := by
    dsimp only [AY, ordinaryToFixed, Iso.refl_inv]
    rw [← model_inv]
    change IsIso ((podReindexingHomModel l E Y s P (I⟦b⟧)).inv ≫
      (podReindexingDerivedHom l E Y s).map (𝟙 (op (QY.obj P), QY.obj (I⟦b⟧))))
    rw [(podReindexingDerivedHom l E Y s).map_id, Category.comp_id]
    infer_instance
  exact normalized_shift_pasting QY QX Fc F UY UX HY HX θ AY AX d.hom I b
    ey ex (c.chain P I).hom (c.chain P (I⟦b⟧)).hom hy hx
    (chain_target_square l E g s SX SY TX TY c P I b ey ex hey hex)
    (model_square l E g s SX SY TX TY c P I)
    (model_square l E g s SX SY TX TY c P (I⟦b⟧))

/-- Reindexing respects the normalized target shift of derived internal Hom.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: lem-pod-reindexing-derived-target-shift).

Proof: represent the source by a complex and resolve the target by a K-injective
complex. Its target shift is again K-injective. Expand `Comparison.derived_model`
at the two pairs. The `RightNormalization` characterization of `homCommShift`
identifies the vertical arrows with unsigned target reindexing on Hom products.
The `chain_projection` field makes these maps commute with sectionwise
reindexing on each factor; product extensionality proves their chain square.
Localize and use naturality of the localization factors. Cancel the comparison
isomorphisms and transport along the representative isomorphisms to obtain the
square for arbitrary M and N. -/
theorem derived_target_shift_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (M N : podReindexingDerived l E Y s) (b : ℤ) :
    c.derived.hom.app (op M, N⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (𝟙 (op ((podReindexingDerivedFunctor l E g s).obj M)))
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app N)) ≫
      ((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingDerivedFunctor l E g s).obj M)).commShiftIso b).hom.app
          ((podReindexingDerivedFunctor l E g s).obj N) =
    (podReindexingDerivedFunctor l E g s).map
      (((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s) M).commShiftIso b).hom.app N) ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
      (c.derived.hom.app (op M, N))⟦b⟧' := by
  let W := HomologicalComplex.quasiIso (podReindexingModules l E Y s) (.up ℤ)
  obtain ⟨P, rfl⟩ := (Localization.Construction.objEquiv W).surjective M
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (podReindexingRing l E Y s)).1
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  let F := podReindexingDerivedFunctor l E g s
  let M := (podReindexingQ l E Y s).obj P
  let HY := fixedHom l E Y s M
  let HX := fixedHom l E X s (F.obj M)
  let lhs := Functor.whiskerLeft (shiftFunctor _ b)
      (comparisonAt l E g s SX SY TX TY c M).hom ≫
    Functor.whiskerRight (F.commShiftIso b).hom HX ≫
    Functor.whiskerLeft F (HX.commShiftIso b).hom
  let rhs := Functor.whiskerRight (HY.commShiftIso b).hom F ≫
    Functor.whiskerLeft HY (F.commShiftIso b).hom ≫
    Functor.whiskerRight (comparisonAt l E g s SX SY TX TY c M).hom
      (shiftFunctor _ b)
  change lhs.app N = rhs.app N
  have hrep : lhs.app ((podReindexingQ l E Y s).obj I) =
      rhs.app ((podReindexingQ l E Y s).obj I) := by
    exact derived_target_shift_model l E g s SX SY TX TY c P I hI b
  have hl := lhs.naturality e.hom
  have hr := rhs.naturality e.hom
  rw [hrep] at hl
  exact (cancel_mono _).mp (hl.symm.trans hr)

end WeilConjectures.PodReindexingCoherence
