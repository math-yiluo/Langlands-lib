/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option linter.privateModule false

/-! # Normalized descent of the strict scalar shift

Source: Stacks Project, Tags 011G, 014E, 06YS, 06YT and 08TC.
(blueprint: lem-weil-completed-scalar-shift-descent)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private lemma acyclic_shift {A : Type*} [Category A] [Abelian A]
    (K : CochainComplex A ℤ) (hK : K.Acyclic) (m : ℤ) : (K⟦m⟧).Acyclic := by
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
  apply (HomotopyCategory.subcategoryAcyclic A).prop_of_iso
    ((HomotopyCategory.quotient A (.up ℤ)).commShiftIso m |>.app K).symm
  exact (HomotopyCategory.subcategoryAcyclic A).le_shift m _
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr hK)

private lemma acyclic_of_iso {A : Type*} [Category A] [Abelian A]
    {K K' : CochainComplex A ℤ} (e : K ≅ K') (hK : K.Acyclic) : K'.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Limits.IsZero.of_iso (hK i).isZero_homology
    ((HomologicalComplex.homologyFunctor A (.up ℤ) i).mapIso e).symm

private lemma good_shift (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (m : ℤ) :
    integralOperationsGoodComplex l E Y (P⟦m⟧) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have (M : SheafOfModules ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).obj R)) : (MonoidalCategory.tensorLeft M).Additive :=
    SheafOfModules.tensorLeft_additive_independent R M
  refine ⟨?_, ?_⟩
  · intro F hF
    exact acyclic_of_iso
      (CochainComplex.mapBifunctorShift₂Iso F P (MonoidalCategory.curriedTensor _) m).symm
      (acyclic_shift _ (hP.1 F hF) m)
  · intro i
    exact hP.2 (i + m)

private lemma conj_naturality {D B : Type*} [Category D] [Category B] (F G : D ⥤ B)
    {a b a' b' : D} (u : a ⟶ b) (v : a' ⟶ b') (ea : a ≅ a') (eb : b ≅ b')
    (hq : u ≫ eb.hom = ea.hom ≫ v) (ta : F.obj a' ⟶ G.obj a') (tb : F.obj b' ⟶ G.obj b')
    (h : F.map v ≫ tb = ta ≫ G.map v) :
    F.map u ≫ F.map eb.hom ≫ tb ≫ G.map eb.inv =
      (F.map ea.hom ≫ ta ≫ G.map ea.inv) ≫ G.map u := by
  have hq' : ea.inv ≫ u = v ≫ eb.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [← F.map_comp_assoc, hq, F.map_comp_assoc, reassoc_of% h, Category.assoc,
    Category.assoc, ← G.map_comp, ← G.map_comp, hq']

private lemma conj_app_eq {D B : Type*} [Category D] [Category B] {F G : D ⥤ B}
    (p : F ⟶ G) {a a' : D} (e : a ≅ a') (t : F.obj a' ⟶ G.obj a')
    (h : p.app a = F.map e.hom ≫ t ≫ G.map e.inv) : p.app a' = t := by
  rw [← cancel_epi (F.map e.hom), p.naturality, h, Category.assoc, Category.assoc,
    ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id]

private theorem good_whisker_full (Z : Type*) [Category Z] :
    ((Functor.whiskeringLeft _ _ Z).obj
      (integralOperationsGoodLocalization l E Y)).Full := by
  obtain ⟨P, hP, ⟨H, hH, ⟨eH⟩⟩, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{_, _, _, _, 0, 0}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
  let A := SheafOfModules.{max u (t + 1)} ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat RingCat)).obj (completedIntegralCommRingSheafUnrestricted l E Y))
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  let Lg := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ _)
  have : H.IsEquivalence := hH
  have : V.Q.IsLocalization V := inferInstance
  have : Lg.IsLocalization V := by
    have : (V.Q ⋙ H).IsLocalization V := inferInstance
    exact Functor.IsLocalization.of_iso V eH
  refine ⟨?_⟩
  intro F G τ
  let eX (X : P.FullSubcategory) : Lg.obj X ≅
      (integralOperationsGoodLocalization l E Y).obj ⟨X.obj.as, (hP X.obj).mp X.property⟩ :=
    (DerivedCategory.quotientCompQhIso A).app X.obj.as
  let τh : Lg ⋙ F ⟶ Lg ⋙ G :=
    { app := fun X ↦ F.map (eX X).hom ≫ τ.app ⟨X.obj.as, (hP X.obj).mp X.property⟩ ≫
        G.map (eX X).inv
      naturality := by
        intro X X' f
        have h := τ.naturality (ObjectProperty.homMk f.hom.out :
          (⟨X.obj.as, (hP X.obj).mp X.property⟩ :
            (integralOperationsGoodComplex l E Y).FullSubcategory) ⟶
          ⟨X'.obj.as, (hP X'.obj).mp X'.property⟩)
        have hq : Lg.map f ≫ (eX X').hom = (eX X).hom ≫ DerivedCategory.Q.map f.hom.out := by
          have hh := DerivedCategory.quotientCompQhIso_hom_naturality f.hom.out
          rw [HomotopyCategory.quotient_map_out] at hh
          exact hh
        change F.map (DerivedCategory.Q.map f.hom.out) ≫ _ =
          _ ≫ G.map (DerivedCategory.Q.map f.hom.out) at h
        exact conj_naturality F G _ _ _ _ hq _ _ h }
  let ff := Localization.fullyFaithfulWhiskeringLeft Lg V Z
  refine ⟨ff.preimage τh, ?_⟩
  ext X
  let X₀ : P.FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ (.up ℤ)).obj X.obj, (hP _).mpr X.property⟩
  have h := congrArg (fun a ↦ a.app X₀) (ff.map_preimage τh)
  exact conj_app_eq (ff.preimage τh) (eX X₀) (τ.app X) h

private theorem goodLocalization_essSurj :
    (integralOperationsGoodLocalization l E Y).EssSurj := by
  obtain ⟨P, hP, ⟨H, hH, ⟨eH⟩⟩, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{_, _, _, _, 0, 0}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
  let A := SheafOfModules.{max u (t + 1)}
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).obj (completedIntegralCommRingSheafUnrestricted l E Y))
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  let Lg := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ _)
  have : H.IsEquivalence := hH
  have : Lg.IsLocalization V := by
    have : (V.Q ⋙ H).IsLocalization V := inferInstance
    exact Functor.IsLocalization.of_iso V eH
  have : Lg.EssSurj := Localization.essSurj Lg V
  constructor
  intro K
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Lg K
  exact ⟨⟨X.obj.as, (hP X.obj).mp X.property⟩,
    ⟨((DerivedCategory.quotientCompQhIso A).app X.obj.as).symm ≪≫ e⟩⟩

private theorem whiskeringLeft_faithful
    {C D B : Type*} [Category C] [Category D] [Category B]
    (Q : C ⥤ D) [Q.EssSurj] :
    ((Functor.whiskeringLeft C D B).obj Q).Faithful where
  map_injective := by
    intro F G α β h
    ext K
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q K
    apply (cancel_epi (F.map e.hom)).mp
    rw [α.naturality, β.naturality]
    exact congrArg (· ≫ G.map e.hom) (NatTrans.congr_app h X)

private theorem descentShift
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] (H : C ⥤ B) [H.CommShift ℤ]
    (F : D ⥤ B) (e : Q ⋙ F ≅ H)
    (ff : ((Functor.whiskeringLeft C D B).obj Q).FullyFaithful) :
    ∃ s : F.CommShift ℤ, ∀ (a : ℤ) (X : C),
      (Functor.commShiftIso F (self := s) a).hom.app (Q.obj X) ≫
        (e.hom.app X)⟦a⟧' =
      F.map ((Q.commShiftIso a).inv.app X) ≫ e.hom.app (X⟦a⟧) ≫
        (H.commShiftIso a).hom.app X := by
  let j (a : ℤ) : Q ⋙ shiftFunctor D a ⋙ F ≅ Q ⋙ F ⋙ shiftFunctor B a :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Q.commShiftIso a).symm F ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ Functor.isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _
  let i (a : ℤ) : shiftFunctor D a ⋙ F ≅ F ⋙ shiftFunctor B a :=
    ff.preimageIso (j a)
  have hi (a : ℤ) (X : C) :
      (i a).hom.app (Q.obj X) =
        F.map ((Q.commShiftIso a).inv.app X) ≫ e.hom.app (X⟦a⟧) ≫
          (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' := by
    have h := NatTrans.congr_app (ff.map_preimage (j a).hom) X
    exact h.trans (by simp [j])
  let s : F.CommShift ℤ :=
    { commShiftIso := i
      commShiftIso_zero := by
        ext1
        apply ff.map_injective
        ext X
        dsimp
        simp only [hi, Functor.comp_obj, Functor.commShiftIso_zero,
          Functor.CommShift.isoZero_inv_app, Functor.map_comp,
          Functor.CommShift.isoZero_hom_app, Category.assoc,
          ← NatTrans.naturality_assoc, ← NatTrans.naturality]
        dsimp
        simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
          Iso.inv_hom_id_app, Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp,
          Iso.hom_inv_id_app_assoc]
      commShiftIso_add a b := by
        ext1
        apply ff.map_injective
        ext X
        dsimp
        simp only [hi, Functor.comp_obj, Functor.commShiftIso_add,
          Functor.CommShift.isoAdd_inv_app, Functor.map_comp,
          Functor.CommShift.isoAdd_hom_app, Category.assoc]
        congr 1
        rw [← cancel_epi (F.map ((shiftFunctor D b).map ((Q.commShiftIso a).hom.app X))),
          ← F.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
        conv_lhs =>
          erw [← NatTrans.naturality_assoc]
          dsimp
          rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
            ← Functor.map_comp, Iso.inv_hom_id_app]
          dsimp
          rw [CategoryTheory.Functor.map_id, Category.comp_id, ← NatTrans.naturality]
          dsimp
        conv_rhs =>
          erw [← NatTrans.naturality_assoc]
          dsimp
          rw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
          dsimp
          rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, hi,
            Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
            Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] }
  refine ⟨s, ?_⟩
  intro a X
  change (i a).hom.app (Q.obj X) ≫ _ = _
  rw [hi]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem good_stable :
    (integralOperationsGoodComplex l E Y).IsStableUnderShift ℤ where
  isStableUnderShiftBy m := ⟨fun P hP ↦ good_shift l E Y P hP m⟩

end WeilConjectures
