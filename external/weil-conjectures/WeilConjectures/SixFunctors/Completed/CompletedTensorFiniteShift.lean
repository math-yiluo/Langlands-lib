/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # The finite tensor tower and right shifts

Source: Stacks Project, Tags 011G, 012Z and 03EK.
(blueprint: lem-sf-completed-tensor-finite-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
universe a b c d e f
section FiniteShiftHelpers
variable {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type c} [Category.{d} B] [Preadditive B]
  {C : Type e} [Category.{f} C] [Preadditive C]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
  (T : B ⥤ B ⥤ B) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).Additive]
  [∀ X Y : CochainComplex B ℤ, CochainComplex.HasMapBifunctor X Y T]
private noncomputable def levelIso (P Q : CochainComplex A ℤ) (r : ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj (Q⟦r⟧)) T) ≅
    ((G.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) T))⟦r⟧ :=
  (G.mapHomologicalComplex (.up ℤ)).mapIso
    ((T.map₂CochainComplex.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).mapIso
      ((F.mapCochainComplexShiftIso r).app Q) ≪≫
      CochainComplex.mapBifunctorShift₂Iso
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) T r) ≪≫
    (G.mapCochainComplexShiftIso r).app _

private theorem levelIso_ι (P Q : CochainComplex A ℤ) (r i j : ℤ) :
    G.map (CochainComplex.ιMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj (Q⟦r⟧)) T i j (i + j) rfl) ≫
        (levelIso F G T P Q r).hom.f (i + j) =
    (i * r).negOnePow • G.map (CochainComplex.ιMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) T i (j + r) (i + (j + r)) rfl) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((G.mapHomologicalComplex (.up ℤ)).obj
            (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
              ((F.mapHomologicalComplex (.up ℤ)).obj Q) T))
          r (i + j) (i + (j + r)) (by omega)).inv := by
  let P' := (F.mapHomologicalComplex (.up ℤ)).obj P
  let Q' := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have hm := HomologicalComplex.ι_mapBifunctorMap (𝟙 P')
    ((F.mapCochainComplexShiftIso r).hom.app Q) T (.up ℤ) i j (i + j) rfl
  dsimp only [HomologicalComplex.id_f,
    Functor.mapCochainComplexShiftIso_hom_app_f] at hm
  change _ = (T.map (𝟙 (F.obj (P.X i)))).app (F.obj (Q.X (j + r))) ≫
    (T.obj (F.obj (P.X i))).map (𝟙 (F.obj (Q.X (j + r)))) ≫ _ at hm
  rw [T.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp] at hm
  have hs := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    P' Q' T r i j (i + j) rfl (j + r) (i + (j + r)) rfl (by omega)
  change _ = (i * r).negOnePow • (T.obj (F.obj (P.X i))).map
    (𝟙 (F.obj (Q.X (j + r)))) ≫ _ at hs
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hs
  have hc := congrArg (fun k ↦ G.map k) ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ (CochainComplex.mapBifunctorShift₂Iso P' Q' T r).hom.f
      (i + j)) hm).trans hs))
  dsimp only [Functor.comp_obj] at hc
  convert hc using 1 <;>
    simp only [levelIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapCochainComplexShiftIso_hom_app_f, Iso.app_hom,
    Functor.map_comp, Category.assoc,
    Functor.map_units_smul, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq,
    P', Q',
    eqToIso.inv, eqToHom_map]
  · rfl
  · change _ ≫ _ ≫ _ ≫ 𝟙 _ = _ ≫ _ ≫ _
    exact congrArg₂ (fun f g ↦ f ≫ g) rfl
      (congrArg₂ (fun f g ↦ f ≫ g) rfl (Category.comp_id _))

section Natural
variable [T.Additive]
private noncomputable def tensorShiftIso (r : ℤ) :
    ((𝟭 (CochainComplex B ℤ)).prod (shiftFunctor _ r)) ⋙
        Functor.uncurry.obj T.map₂CochainComplex ≅
      Functor.uncurry.obj T.map₂CochainComplex ⋙ shiftFunctor _ r :=
  NatIso.ofComponents
    (fun X ↦ CochainComplex.mapBifunctorShift₂Iso X.1 X.2 T r) (by
      intro X Y f
      change ((T.map₂CochainComplex.map f.1).app (X.2⟦r⟧) ≫
        (T.map₂CochainComplex.obj Y.1).map (f.2⟦r⟧')) ≫
          ((T.map₂CochainComplex.obj Y.1).commShiftIso r).hom.app Y.2 = _
      rw [Category.assoc, Functor.commShiftIso_hom_naturality,
        ← Category.assoc, ← NatTrans.shift_app_comm]
      simp only [Functor.uncurry_obj_map, Functor.comp_map, Functor.map_comp, Category.assoc]
      rfl)

private noncomputable def levelNatIso (r : ℤ) :
    ((𝟭 (CochainComplex A ℤ)).prod (shiftFunctor _ r)) ⋙
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj T.map₂CochainComplex ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj T.map₂CochainComplex ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
      shiftFunctor _ r :=
  isoWhiskerRight
    (NatIso.prod (Iso.refl (F.mapHomologicalComplex (.up ℤ)))
      (F.mapCochainComplexShiftIso r))
    (Functor.uncurry.obj T.map₂CochainComplex ⋙ G.mapHomologicalComplex (.up ℤ)) ≪≫
  isoWhiskerLeft
    ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)))
    (isoWhiskerRight (tensorShiftIso T r) (G.mapHomologicalComplex (.up ℤ))) ≪≫
  isoWhiskerLeft
    ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj T.map₂CochainComplex)
    (G.mapCochainComplexShiftIso r)

private theorem levelNatIso_app (P Q : CochainComplex A ℤ) (r : ℤ) :
    (levelNatIso F G T r).app (P, Q) = levelIso F G T P Q r := by
  apply Iso.ext
  dsimp only [levelNatIso, Iso.app_hom, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    NatIso.prod_hom, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.uncurry_obj_map]
  change (G.mapHomologicalComplex (.up ℤ)).map
    ((T.map₂CochainComplex.map (𝟙 _)).app _ ≫
      (T.map₂CochainComplex.obj _).map _) ≫ _ ≫ _ = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  simp only [levelIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, tensorShiftIso, NatIso.ofComponents_hom_app]
  rfl
end Natural

end FiniteShiftHelpers

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] levelIso CategoryTheory.constantSheaf
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.unrestrictedIntegralReductionExistence
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
universe t u
open WeilConjectures
section SectionEval
universe v w z
variable {D : Type v} [Category.{w} D] {J : GrothendieckTopology D}
  {R : Sheaf J RingCat.{z}}
private theorem restriction_apply {S : Sheaf J RingCat.{z}} (α : R ⟶ S)
    {M N : SheafOfModules.{z} S} (f : M ⟶ N) (U : Dᵒᵖ) (x : M.val.obj U) :
    (((SheafOfModules.restrictScalars α).map f).val.app U) x = (f.val.app U) x := rfl

private theorem section_signed_apply {X Y X' Y' : SheafOfModules.{z} R}
    (a : X ⟶ Y) (b : Y ⟶ Y') (c : X ⟶ X') (d : X' ⟶ Y')
    (s : ℤˣ) (h : a ≫ b = s • (c ≫ d)) (U : Dᵒᵖ) (x : X.val.obj U) :
    b.val.app U (a.val.app U x) = d.val.app U (s • c.val.app U x) := by
  let H := SheafOfModules.evaluation (R := R) U
  have : H.Additive := inferInstanceAs
    ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U).Additive)
  have he := congrArg (fun k ↦ H.map k x) h
  simp only [Units.smul_def, Functor.map_comp, Functor.map_zsmul, ModuleCat.comp_apply] at he
  change b.val.app U (a.val.app U x) = (s : ℤ) • d.val.app U (c.val.app U x) at he
  simpa only [Units.smul_def, _root_.map_zsmul] using he
private theorem reindex_section {X Y : CochainComplex (SheafOfModules.{z} R) ℤ}
    (f : X ⟶ Y) {i j : ℤ} (h : i = j) (U : Dᵒᵖ)
    (x : (X.X j).val.obj U) (y : (Y.X j).val.obj U)
    (hxy : (f.f i).val.app U (((X.XIsoOfEq h).inv.val.app U) x) =
      ((Y.XIsoOfEq h).inv.val.app U) y) : (f.f j).val.app U x = y := by
  subst j
  exact hxy
end SectionEval
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteTensorAdditive
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) :
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).obj M).Additive :=
  SheafOfModules.tensorLeft_additive_independent
    (integralCoefficientCommRingSheaf l E W n) M

private noncomputable def finiteShiftIso (W : AlgebraicGeometry.Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) (n : ℕ) :
    (integralOperationsTensorLevel l E W n).obj (P, Q⟦r⟧) ≅
      ((integralOperationsTensorLevel l E W n).obj (P, Q))⟦r⟧ := by
  letI := finiteTensorAdditive l E W n
  exact levelIso (unrestrictedIntegralReductionFunctor l E W n)
    (SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E W n)))
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)) P Q r

private theorem finiteShiftFormula (W : AlgebraicGeometry.Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) (n : ℕ)
    (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (j + r)).val.obj U) :
    (((finiteShiftIso l E W P Q r n).hom.f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) (i + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow •
        integralOperationsTotalTensorSection l E W n P Q i (j + r) U x y) := by
  let := finiteTensorAdditive l E W n
  let F := unrestrictedIntegralReductionFunctor l E W n
  let G := SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
  let T := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)
  have h := levelIso_ι F G T P Q r i j
  have he := section_signed_apply _ _ _ _ (i * r).negOnePow h U
    (integralOperationsTensorSection l E W n _ _ U x y)
  dsimp only [finiteShiftIso, integralOperationsTensorLevel, integralOperationsRestrict,
    unrestrictedIntegralFiniteComplex, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, integralOperationsTotalTensorSection,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  dsimp only [F, G, T] at he
  dsimp only [Functor.mapHomologicalComplex_obj_X, CochainComplex.shiftFunctor_obj_X'] at he
  simp only [restriction_apply] at he
  simp only [Int.mul_comm, Functor.mapHomologicalComplex_obj_X,
    CochainComplex.shiftFunctor_obj_X', CochainComplex.mapBifunctor] at he ⊢
  convert he using 1 <;> with_unfolding_all rfl

private theorem finiteTensorAdditiveFirst
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).Additive := by
  refine ⟨?_⟩
  intro X Y f g
  apply NatTrans.ext
  funext N
  exact (CategoryTheory.tensorRight_additive_reconstruction
    (integralCoefficientCommRingSheaf l E W n) N).map_add

private noncomputable def finiteShiftNatIso (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) :
    ((𝟭 (CochainComplex (integralTowerModules l E W) ℤ)).prod
      (shiftFunctor _ r)) ⋙ integralOperationsTensorLevel l E W n ≅
      integralOperationsTensorLevel l E W n ⋙ shiftFunctor _ r := by
  let := finiteTensorAdditive l E W n
  let := finiteTensorAdditiveFirst l E W n
  exact levelNatIso (unrestrictedIntegralReductionFunctor l E W n)
    (SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E W n)))
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)) r

private theorem finiteShiftNatIso_app (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (finiteShiftNatIso l E W r n).app (P, Q) = finiteShiftIso l E W P Q r n := by
  let := finiteTensorAdditive l E W n
  let := finiteTensorAdditiveFirst l E W n
  apply levelNatIso_app

private noncomputable def unshiftedTransition (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) : integralOperationsTensorLevel l E W (n + 1) ⟶
      integralOperationsTensorLevel l E W n := by
  let A := CochainComplex (integralTowerModules l E W) ℤ
  let S := shiftFunctor A r
  let H := (whiskeringRight (A × A) A A).obj S
  let V := (𝟭 A).prod S
  exact H.preimage ((finiteShiftNatIso l E W r (n + 1)).inv ≫
    whiskerLeft V (integralOperationsTensorTransition l E W n) ≫
      (finiteShiftNatIso l E W r n).hom)

private theorem unshiftedTransition_shift (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) :
    whiskerRight (unshiftedTransition l E W r n) (shiftFunctor _ r) =
      (finiteShiftNatIso l E W r (n + 1)).inv ≫
        whiskerLeft ((𝟭 _).prod (shiftFunctor _ r))
          (integralOperationsTensorTransition l E W n) ≫
        (finiteShiftNatIso l E W r n).hom := by
  exact Functor.map_preimage ((whiskeringRight _ _ _).obj (shiftFunctor _ r)) _

private theorem reductionTransition_f (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
    ((unrestrictedIntegralTransition l E W n).app P).f i =
      unrestrictedModuleStep l E W n (P.X i) := by
  let τ : unrestrictedIntegralComplexFunctor l E W (n + 1) ⟶
      unrestrictedIntegralComplexFunctor l E W n :=
    { app := fun P ↦
        { f := fun i ↦ unrestrictedModuleStep l E W n (P.X i)
          comm' := fun i j _ ↦
            (unrestrictedModuleStep_naturality l E W n (P.d i j)).symm }
      naturality := fun P Q a ↦ by
        apply HomologicalComplex.hom_ext
        intro i
        exact unrestrictedModuleStep_naturality l E W n (a.f i) }
  have hτ : ∀ P i U s x, ((τ.app P).f i).val.app U
      (unrestrictedIntegralTensorSection l E W (n + 1) (P.X i) U s x) =
      unrestrictedIntegralTensorSection l E W n (P.X i) U
        ((integralCoefficientSheafTransition l E W n).hom.app U s) x :=
    fun P i U s x ↦ unrestrictedModuleStep_tmul l E W n (P.X i) U s x
  have h : unrestrictedIntegralTransition l E W n = τ :=
    (unrestrictedIntegralTransition_existsUnique l E W n).unique
      (unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec hτ
  exact congrArg (fun a ↦ (a.app P).f i) h

private theorem reductionTransition_shift (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) (r i : ℤ) :
    ((unrestrictedIntegralTransition l E W n).app (P⟦r⟧)).f i =
      ((unrestrictedIntegralTransition l E W n).app P).f (i + r) := by
  rw [reductionTransition_f, reductionTransition_f]
  rfl

private theorem finiteShiftNatIso_hom_app (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (finiteShiftNatIso l E W r n).hom.app (P, Q) =
      (finiteShiftIso l E W P Q r n).hom :=
  congrArg Iso.hom (finiteShiftNatIso_app l E W r n P Q)

private theorem unshiftedTransition_square (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) :
    (finiteShiftNatIso l E W r (n + 1)).hom ≫
        whiskerRight (unshiftedTransition l E W r n) (shiftFunctor _ r) =
      whiskerLeft ((𝟭 _).prod (shiftFunctor _ r))
        (integralOperationsTensorTransition l E W n) ≫
          (finiteShiftNatIso l E W r n).hom := by
  rw [unshiftedTransition_shift]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

attribute [local implicit_reducible] integralOperationsTensorLevel integralOperationsRestrict
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj CategoryTheory.Functor.map₂HomologicalComplex
  integralCoefficientCommRingSheaf completedIntegralCommRingSheafUnrestricted
  integralCoefficientSheaf
  CategoryTheory.sheafCompose ModuleCat.restrictScalars

private theorem unshiftedTransition_generator (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q).X q).val.obj U) :
    (((unshiftedTransition l E W r n).app (P, Q)).f (p + q)).val.app U
        (integralOperationsTotalTensorSection l E W (n + 1) P Q p q U x y) =
      integralOperationsTotalTensorSection l E W n P Q p q U
        ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
        ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, q = j + r := ⟨q - r, by omega⟩
  have he := congrArg
    (fun k ↦ (((k.app (P, Q)).f (p + j)).val.app U)
      (integralOperationsTotalTensorSection l E W (n + 1) P (Q⟦r⟧) p j U x y))
    (unshiftedTransition_square l E W r n)
  dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, whiskerLeft_app, whiskerRight_app] at he
  rw [finiteShiftNatIso_hom_app, finiteShiftNatIso_hom_app] at he
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply, Functor.prod_obj,
    Functor.id_obj] at he
  have hleft := congrArg
    (fun z ↦ (((((shiftFunctor _ r).map
      ((unshiftedTransition l E W r n).app (P, Q))).f (p + j)).val.app U) z))
    (finiteShiftFormula l E W P Q r (n + 1) p j U x y)
  have ht := (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
    P (Q⟦r⟧) p j U x y
  have hright := congrArg
    (fun z ↦ (((finiteShiftIso l E W P Q r n).hom.f (p + j)).val.app U) z) ht
  have hs := finiteShiftFormula l E W P Q r n p j U
    ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
    ((((unrestrictedIntegralTransition l E W n).app Q).f (j + r)).val.app U y)
  have hred := reductionTransition_shift l E W n Q r j
  rw [hred] at hright
  have hcomb := hleft.symm.trans (he.trans (hright.trans hs))
  simp only [CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
    at hcomb
  have hresult := reindex_section ((unshiftedTransition l E W r n).app (P, Q))
    (show p + j + r = p + (j + r) by omega) U _ _ hcomb
  apply smul_left_cancel (r * p).negOnePow
  simpa only [Units.smul_def, _root_.map_zsmul] using hresult

private theorem unshiftedTransition_eq (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) : unshiftedTransition l E W r n =
      integralOperationsTensorTransition l E W n :=
  (integralOperationsTensorTransition_existsUnique l E W n).unique
    (unshiftedTransition_generator l E W r n)
    (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec

private theorem finiteShift_transition (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (n : ℕ) :
    whiskerLeft ((𝟭 _).prod (shiftFunctor _ r))
      (integralOperationsTensorTransition l E W n) ≫
        (finiteShiftNatIso l E W r n).hom =
      (finiteShiftNatIso l E W r (n + 1)).hom ≫
        whiskerRight (integralOperationsTensorTransition l E W n) (shiftFunctor _ r) := by
  exact (unshiftedTransition_square l E W r n).symm.trans
    (congrArg (fun τ ↦ (finiteShiftNatIso l E W r (n + 1)).hom ≫
      whiskerRight τ (shiftFunctor _ r)) (unshiftedTransition_eq l E W r n))

private noncomputable abbrev towerShiftIso (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r :=
  NatIso.ofComponents (fun n ↦ finiteShiftIso l E W P Q r n.unop) (by
    intro n m f
    let η : (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ⟶
        (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r :=
      NatTrans.ofOpSequence (fun n ↦ (finiteShiftIso l E W P Q r n).hom) (by
        intro n
        have h := congrArg (fun τ ↦ τ.app (P, Q))
          (finiteShift_transition l E W r n)
        simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
          Functor.prod_obj, Functor.id_obj, finiteShiftNatIso_hom_app,
          integralOperationsTensorTowerFunctor, Functor.flip_obj_map,
          Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] using h)
    exact η.naturality f)

private noncomputable abbrev towerShiftNatIso (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    ((𝟭 (CochainComplex (integralTowerModules l E W) ℤ)).prod (shiftFunctor _ r)) ⋙
      integralOperationsTensorTowerFunctor l E W ≅
    integralOperationsTensorTowerFunctor l E W ⋙
      (whiskeringRight ℕᵒᵖ (CochainComplex (integralTowerModules l E W) ℤ)
        (CochainComplex (integralTowerModules l E W) ℤ)).obj (shiftFunctor _ r) :=
  NatIso.ofComponents (fun X ↦ towerShiftIso l E W r X.1 X.2) (by
    intro X Y f
    apply NatTrans.ext
    funext n
    rcases X with ⟨P, Q⟩
    rcases Y with ⟨P', Q'⟩
    have h := (finiteShiftNatIso l E W r n.unop).hom.naturality f
    simp only [finiteShiftNatIso_hom_app] at h
    convert h using 1 <;> with_unfolding_all rfl)

/-- The signed right shift isomorphism of the strict finite tensor towers.
Source: Stacks Project, Tags 011G, 012Z and 03EK; steps 1 and 3 of
`lem-sf-completed-tensor-shift-right`
(blueprint: lem-sf-completed-tensor-finite-shift).

Proof: ordinary reduction and scalar restriction act termwise, so their shift
comparisons are the identities on the reindexed terms. Between them use the
right total-bifunctor shift isomorphism: its (i,j)-summand map is multiplication
by (-1)^(ri). The first differential raises i, contributing the additional
(-1)^r from shifting the total; the second differential has the usual (-1)^i
and the shift of Q contributes (-1)^r. These are precisely the two chain-map
identities. The inverse has the same signs. All comparisons are natural in
both complexes. The quotient transition sends a tensor x tensor y to the
tensor of the two reductions; reduction is termwise and preserves degree and
integer multiplication. Thus each transition square commutes. This can also
be deduced from the existing uniqueness characterization of the tensor
transition by conjugating with the shift isomorphisms. The component
isomorphisms therefore form a natural isomorphism of tower-valued functors.
The total-bifunctor injection formula, followed by evaluation on a sheafified
pure tensor, is the displayed equality. The argument includes r=0, negative
shifts, zero complexes, and the empty site. -/
theorem integralCompletedTensorFiniteShift (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    ∃ β : ((𝟭 (CochainComplex (integralTowerModules l E W) ℤ)).prod
        (shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r)) ⋙
        integralOperationsTensorTowerFunctor l E W ≅
      integralOperationsTensorTowerFunctor l E W ⋙
        (whiskeringRight ℕᵒᵖ (CochainComplex (integralTowerModules l E W) ℤ)
          (CochainComplex (integralTowerModules l E W) ℤ)).obj
            (shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r),
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (i j : ℤ)
        (U : W.ProEtᵒᵖ)
        (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i).val.obj U)
        (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (j + r)).val.obj U),
        ((((β.app (P, Q)).hom.app (op n)).f (i + j)).val.app U)
          (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) i j U x y) =
        ((CochainComplex.shiftFunctorObjXIso
          ((integralOperationsTensorLevel l E W n).obj (P, Q))
            r (i + j) (i + (j + r)) (by omega)).inv.val.app U)
          ((r * i).negOnePow •
            integralOperationsTotalTensorSection l E W n P Q i (j + r) U x y) := by
  refine ⟨towerShiftNatIso l E W r, ?_⟩
  intro P Q n i j U x y
  exact finiteShiftFormula l E W P Q r n i j U x y

end WeilConjectures
