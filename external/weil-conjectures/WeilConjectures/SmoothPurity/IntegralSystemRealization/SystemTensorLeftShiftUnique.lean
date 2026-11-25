/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.SliceTensorIntegerShiftCompatibility
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Prod

/-! # Unique normalized shift in the unsigned strict-system first slot -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

set_option synthInstance.maxSize 4096
open CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
attribute [local irreducible] SheafOfModules.monoidalCategory
  WeilConjectures.coefficientSequenceCommRingSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.CoefficientClosedStructure.tensor
attribute [local instance 2000] SheafOfModules.cochainModulesPreadditive
attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

private theorem localizationIso_app
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ B) (V : MorphismProperty A) [L.IsLocalization V]
    (F G : B ⥤ D) (e : L ⋙ F ≅ L ⋙ G) (X : A) :
    (Localization.liftNatIso L V _ _ F G e).hom.app (L.obj X) = e.hom.app X := by
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]

section AbstractDescent

variable {A D : Type*} [Category A] [Category D] [HasShift A ℤ] [HasShift D ℤ]
    (P : ObjectProperty A) (q : A ⥤ D) [q.CommShift ℤ]
    (B : A × A ⥤ A) (T : D × D ⥤ D) (r : ℤ)
    (hshift : ∀ X, P X → P ((shiftFunctor A r).obj X))
    (c : (shiftFunctor A r).prod (𝟭 A) ⋙ B ≅ B ⋙ shiftFunctor A r)
    (e : P.ι.prod P.ι ⋙ B ⋙ q ≅ (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ T)

private def abstractModelShift :
    (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ (shiftFunctor D r).prod (𝟭 D) ⋙ T ≅
      (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ T ⋙ shiftFunctor D r := by
  let s := (ObjectProperty.lift P (P.ι ⋙ shiftFunctor A r)
    (fun X ↦ hshift X.obj X.property)).prod (𝟭 P.FullSubcategory)
  let a : (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ (shiftFunctor D r).prod (𝟭 D) ≅
      s ⋙ (P.ι ⋙ q).prod (P.ι ⋙ q) :=
    NatIso.prod (isoWhiskerLeft P.ι (q.commShiftIso r)).symm (Iso.refl (P.ι ⋙ q))
  let b : s ⋙ (P.ι.prod P.ι ⋙ B ⋙ q) ≅
      (P.ι.prod P.ι ⋙ B ⋙ q) ⋙ shiftFunctor D r :=
    isoWhiskerRight (isoWhiskerLeft (P.ι.prod P.ι) c) q ≪≫
      isoWhiskerLeft (P.ι.prod P.ι ⋙ B) (q.commShiftIso r)
  exact isoWhiskerRight a T ≪≫ isoWhiskerLeft s e.symm ≪≫ b ≪≫
    isoWhiskerRight e (shiftFunctor D r)

attribute [local irreducible] abstractModelShift

private theorem abstractModelShift_app (X Y : P.FullSubcategory) :
    (abstractModelShift P q B T r hshift c e).hom.app (X, Y) =
      T.map ((q.commShiftIso r).inv.app X.obj, 𝟙 (q.obj Y.obj)) ≫
      e.inv.app (⟨(shiftFunctor A r).obj X.obj, hshift X.obj X.property⟩, Y) ≫
      q.map (c.hom.app (X.obj, Y.obj)) ≫
      (q.commShiftIso r).hom.app (B.obj (X.obj, Y.obj)) ≫
      (shiftFunctor D r).map (e.hom.app (X, Y)) := by
  simp only [abstractModelShift, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.prod_hom, NatTrans.prod,
    Iso.symm_hom, Iso.refl_hom, NatTrans.id_app, Category.assoc,
    isoWhiskerLeft_inv, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    ObjectProperty.ι_obj, ObjectProperty.lift]

end AbstractDescent

private theorem firstShift_app {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (P Q : CochainComplex D ℤ), CochainComplex.HasMapBifunctor P Q F]
    (P Q : CochainComplex D ℤ) (r : ℤ) :
    (CategoryTheory.tensorFirstShiftIso F.map₂CochainComplex r).hom.app (P, Q) =
      (CochainComplex.mapBifunctorShift₁Iso P Q F r).hom := by
  simp only [CategoryTheory.tensorFirstShiftIso, NatIso.ofComponents_hom_app,
    Iso.app_hom, Functor.commShiftIso_map₂CochainComplex_flip_hom_app]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev Mods (W : Scheme.{u}) := coefficientSequenceModules l E W

private theorem totalBifunctor (W : Scheme.{u})
    (P Q : CochainComplex (Mods l E W) ℤ) :
    CochainComplex.HasMapBifunctor P Q (curriedTensor (Mods l E W)) := by
  infer_instance

attribute [local instance 10000] totalBifunctor

private abbrev FlatComplex (W : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (systemKFlat l E W)

private theorem flatLocalization (W : Scheme.{u}) :
    (coefficientKFlatInclusion.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (Mods l E W) (.up ℤ)).inverseImage
        (coefficientKFlatInclusion.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))) :=
  CategoryTheory.RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2} _ _

attribute [local instance 10000] flatLocalization

private def cochainLeftNat (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (CochainComplex (Mods l E W) ℤ) r ⋙ systemTotalTensor l E W ≅
      systemTotalTensor l E W ⋙ shiftFunctor _ r :=
  CategoryTheory.tensorFirstShiftIso (curriedTensor (Mods l E W)).map₂CochainComplex r

private def cochainLeft (W : Scheme.{u})
    (P Q : CochainComplex (Mods l E W) ℤ) (r : ℤ) :
    (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧ :=
  (cochainLeftNat l E W r).app (P, Q)

attribute [local irreducible] cochainLeft
private theorem cochainLeft_formula (W : Scheme.{u})
    (P Q : CochainComplex (Mods l E W) ℤ) (r : ℤ) :
    systemTensorLeftFormula l E W P Q r (cochainLeft l E W P Q r) := by
  intro i j U x y
  have h := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f P Q (curriedTensor _) r
    i j (i + j) rfl (i + r) ((i + r) + j) rfl (by omega)
  change _ = ((curriedTensor _).map (𝟙 (P.X (i + r)))).app (Q.X j) ≫
    HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ)
      (i + r) j ((i + r) + j) rfl ≫ _ at h
  erw [(curriedTensor (Mods l E W)).map_id, NatTrans.id_app, Category.id_comp] at h
  let R := coefficientSequenceCommRingSheaf l E W
  let J := coefficientSequenceTopology (Scheme.ProEt.topology W)
  let z := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
        ((P.X (i + r)).val ⊗ (Q.X j).val) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := R)
        (P.X (i + r)) (Q.X j)).inv.val).app U (x ⊗ₜ[R.obj.obj U] y))
  unfold cochainLeft cochainLeftNat
  simp only [Iso.app_hom, firstShift_app]
  change ((HomologicalComplex.ιMapBifunctor (P⟦r⟧) Q (curriedTensor _) (.up ℤ)
    i j (i + j) rfl ≫
    (CochainComplex.mapBifunctorShift₁Iso P Q (curriedTensor _) r).hom.f (i + j)).val.app U)
      z = ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ)
        (i + r) j ((i + r) + j) rfl ≫
          (CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mapBifunctor P Q (curriedTensor _)) r (i + j) ((i + r) + j)
            (by omega)).inv).val.app U) z
  exact congrArg (fun f ↦ f.val.app U z) h

private theorem flat_shift (W : Scheme.{u})
    (P : CochainComplex (Mods l E W) ℤ) (hP : systemKFlat l E W P) (r : ℤ) :
    systemKFlat l E W (P⟦r⟧) := by
  intro F hF
  have ht := hP F hF
  have hs : (CochainComplex.mapBifunctor F P (curriedTensor _)⟦r⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (Mods l E W)).le_shift r _ ht
  intro i
  exact (hs i).of_iso (CochainComplex.mapBifunctorShift₂Iso F P (curriedTensor _) r).symm

private theorem total_ext (W : Scheme.{u}) (P Q I : CochainComplex (Mods l E W) ℤ)
    (f g : (systemTotalTensor l E W).obj (P, Q) ⟶ I)
    (h : ∀ (a b : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U),
      (f.f (a + b)).val.app U
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q a b (a + b) rfl U x y) =
      (g.f (a + b)).val.app U
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q a b (a + b) rfl U x y)) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = k at hab
  subst k
  let R := coefficientSequenceCommRingSheaf l E W
  let J := coefficientSequenceTopology (Scheme.ProEt.topology W)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification
    (R := R) (P.X a) (Q.X b)).inv).1
  apply ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).homEquiv
      ((P.X a).val ⊗ (Q.X b).val) (I.X (a + b))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h a b U

attribute [local irreducible] cochainLeftNat coefficientTotalTensor

private def modelShift (W : Scheme.{u}) (r : ℤ) :
    let i := coefficientKFlatInclusion.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
    ((i ⋙ DerivedCategory.Q).prod (i ⋙ DerivedCategory.Q)) ⋙
        (tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor) ≅
      ((i ⋙ DerivedCategory.Q).prod (i ⋙ DerivedCategory.Q)) ⋙
        ((calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) := by
  exact abstractModelShift (systemKFlat l E W) DerivedCategory.Q
    (systemTotalTensor l E W) (calculus l E W).systemClosed.tensor r
    (fun P hP ↦ flat_shift l E W P hP r) (cochainLeftNat l E W r)
    (calculus l E W).systemTensorModel.comparison

attribute [local irreducible] modelShift

private theorem modelShift_app (W : Scheme.{u}) (r : ℤ)
    (P Q : CochainComplex (Mods l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q) :
    (modelShift l E W r).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (calculus l E W).systemClosed.tensor.map
        ((DerivedCategory.Q.commShiftIso r).inv.app P, 𝟙 (DerivedCategory.Q.obj Q)) ≫
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P⟦r⟧) Q (flat_shift l E W P hP r) hQ).inv ≫
      DerivedCategory.Q.map (cochainLeft l E W P Q r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom) := by
  have h := abstractModelShift_app (systemKFlat l E W) DerivedCategory.Q
    (systemTotalTensor l E W) (calculus l E W).systemClosed.tensor r
    (fun P hP ↦ flat_shift l E W P hP r) (cochainLeftNat l E W r)
    (calculus l E W).systemTensorModel.comparison ⟨P, hP⟩ ⟨Q, hQ⟩
  unfold modelShift cochainLeft
  convert h using 1 <;> rfl

private def derivedLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r := by
  let J := coefficientSequenceTopology (Scheme.ProEt.topology W)
  let R := coefficientSequenceCommRingSheaf l E W
  let i := coefficientKFlatInclusion.{u, u + 1, u} J R
  let L := i ⋙ DerivedCategory.Q
  let W₀ := (HomologicalComplex.quasiIso (Mods l E W) (.up ℤ)).inverseImage i
  let := CategoryTheory.RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2} J R
  let F := tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor
  let G := (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r
  let : Localization.Lifting (L.prod L) (W₀.prod W₀) ((L.prod L) ⋙ F) F :=
    ⟨Iso.refl _⟩
  let : Localization.Lifting (L.prod L) (W₀.prod W₀) ((L.prod L) ⋙ G) G :=
    ⟨Iso.refl _⟩
  exact Localization.liftNatIso (L.prod L) (W₀.prod W₀) _ _ F G (modelShift l E W r)

attribute [local irreducible] derivedLeft

private theorem derivedLeft_app (W : Scheme.{u}) (r : ℤ)
    (P Q : FlatComplex l E W) :
    (derivedLeft l E W r).hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      (modelShift l E W r).hom.app (P, Q) := by
  unfold derivedLeft
  exact localizationIso_app _ _ _ _ _ (P, Q)

private theorem derivedLeft_property (W : Scheme.{u}) (r : ℤ) :
    systemTensorLeftProperty l E W r (derivedLeft l E W r) := by
  intro P Q hP hQ
  refine ⟨flat_shift l E W P hP r, cochainLeft l E W P Q r,
    cochainLeft_formula l E W P Q r, ?_⟩
  erw [derivedLeft_app l E W r ⟨P, hP⟩ ⟨Q, hQ⟩, modelShift_app]
  let e : (DerivedCategory.Q.obj (P⟦r⟧), DerivedCategory.Q.obj Q) ≅
      ((DerivedCategory.Q.obj P)⟦r⟧, DerivedCategory.Q.obj Q) :=
    ((DerivedCategory.Q.commShiftIso r).app P).prod (Iso.refl _)
  have he := (calculus l E W).systemClosed.tensor.map_comp e.hom e.inv
  have hh : (calculus l E W).systemClosed.tensor.map e.hom ≫
      (calculus l E W).systemClosed.tensor.map e.inv = 𝟙 _ :=
    he.symm.trans (congrArg _ e.hom_inv_id) |>.trans ((calculus l E W).systemClosed.tensor.map_id _)
  let g := ((calculus l E W).systemTensorModel.iso
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
    (P⟦r⟧) Q (flat_shift l E W P hP r) hQ).inv ≫
    DerivedCategory.Q.map (cochainLeft l E W P Q r).hom ≫
    (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
    (shiftFunctor (System l E W) r).map
      (((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        P Q hP hQ).hom)
  simpa only [e, Iso.prod_hom, Iso.prod_inv, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, Category.assoc, Category.id_comp] using
      congrArg (fun f ↦ f ≫ g) hh

private theorem resolving_ext (W : Scheme.{u})
    {F G : System l E W × System l E W ⥤ System l E W} (f g : F ⟶ G)
    (h : ∀ (P Q : CochainComplex (Mods l E W) ℤ)
      (_hP : systemKFlat l E W P) (_hQ : systemKFlat l E W Q),
      f.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        g.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : f = g := by
  have hres (X : System l E W) :
      ∃ P : CochainComplex (Mods l E W) ℤ, systemKFlat l E W P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let K := DerivedCategory.Q.objPreimage X
    obtain ⟨P, p, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) K
    have : QuasiIso p := hq
    exact ⟨P, hp, ⟨asIso (DerivedCategory.Q.map p) ≪≫
      DerivedCategory.Q.objObjPreimageIso X⟩⟩
  apply NatTrans.ext
  funext X
  obtain ⟨P, hP, ⟨eP⟩⟩ := hres X.1
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hres X.2
  let e := eP.prod eQ
  apply (cancel_epi (F.map e.hom)).1
  rw [f.naturality, g.naturality, h P Q hP hQ]

private theorem normalized_unique (W : Scheme.{u}) (r : ℤ)
    (σ τ : tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r)
    (hσ : systemTensorLeftProperty l E W r σ)
    (hτ : systemTensorLeftProperty l E W r τ) : σ = τ := by
  apply Iso.ext
  apply resolving_ext l E W
  intro P Q hP hQ
  obtain ⟨hS, α, hα, eα⟩ := hσ P Q hP hQ
  obtain ⟨hS', β, hβ, eβ⟩ := hτ P Q hP hQ
  have hab : α.hom = β.hom := by
    apply total_ext l E W (P⟦r⟧) Q _
    intro a b U x y
    exact (hα a b U x y).trans (hβ a b U x y).symm
  let e := ((DerivedCategory.Q.commShiftIso r).app P).prod
    (Iso.refl (DerivedCategory.Q.obj Q))
  apply (cancel_epi ((calculus l E W).systemClosed.tensor.map e.hom)).1
  exact eα.trans ((congrArg (fun f ↦ _ ≫ DerivedCategory.Q.map f ≫ _) hab).trans eβ.symm)

/-- Existence and uniqueness for the unsigned strict-system first slot.
Source: Stacks 011G, 012Z, 014E, 06YU, 0941; blueprint purity transport, Step 2
(blueprint: lem-pur-system-tensor-left-shift-unique).

Proof: Reindex the direct sum defining total tensor by (i,j) ↦ (i+r,j).
The differential on the shifted first factor and the shifted total differential
have the same signs, so coefficient one defines a chain isomorphism. Its inverse
uses the inverse reindexing. These maps commute with section restriction and
coefficient transitions, and are natural in both complexes. Shifts preserve
K-flatness, so the K-flat tensor models descend this comparison to the derived
bifunctor and give the displayed property on every K-flat pair. For uniqueness,
the pure tensor generators determine each total cochain map. The normalization
then determines the derived component on each K-flat pair, and every derived
object has a K-flat representative. Naturality transports this equality along
the representative isomorphisms to every pair of derived objects. Natural
isomorphism extensionality proves uniqueness. -/
theorem systemTensorLeftShift_existsUnique (W : Scheme.{u}) (r : ℤ) :
    ∃! σ : tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r,
      systemTensorLeftProperty l E W r σ := by
  refine ⟨derivedLeft l E W r, derivedLeft_property l E W r, ?_⟩
  intro σ hσ
  exact normalized_unique l E W r σ (derivedLeft l E W r) hσ
    (derivedLeft_property l E W r)

end WeilConjectures.IntegralSystemRealization
