/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement

/-! # Shift compatibility of the compact-support restriction square

Source: Stacks Tag 07A6; the restriction square used by the scalar mate
(blueprint: lem-pur-compact-support-restriction-shift).

The proof is split from the ambient coefficient comparison: the restriction
square is built from the exact open restriction comparison and the canonical
proper direct-image restriction comparison. Both pieces commute with integer
shifts by their normalized derived adjunctions; the pasted square therefore
commutes with shifts. This auxiliary statement records exactly that lower step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

private theorem properRestriction_shift {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    NatTrans.CommShift (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
      (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).hom ℤ := by
  let ar := proEtaleRingDerivedAdjunction g (R.ring Y) (R.ring X) (R.pull g)
  let as' := proEtaleRingDerivedAdjunction g (S.ring Y) (S.ring X) (S.pull g)
  let : ar.CommShift ℤ := canonicalRightDerivedAdjunctionShift _
  let : as'.CommShift ℤ := canonicalRightDerivedAdjunctionShift _
  let b := proEtaleRingRestrictionDerivedPullback g
    (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
    (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)
  have hb : NatTrans.CommShift b.hom ℤ := by
    dsimp only [b, proEtaleRingRestrictionDerivedPullback, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let := hb
  let m := (mateEquiv as' ar (TwoSquare.mk _ _ _ _ b.inv))
  have hm : NatTrans.CommShift m ℤ := NatTrans.CommShift.mateEquiv as' ar _
  have heq : m = (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
      (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).hom := by
    ext N
    have h := (proEtaleRingSheafChangeAdjunction g
      (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
      (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).2.2
        ((proEtaleRingDerivedDirectImage g (S.ring Y) (S.ring X) (S.pull g)).obj N) N
        (as'.counit.app N)
    dsimp only [as'] at h
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
      Adjunction.right_triangle_components, CategoryTheory.Functor.map_id,
      Category.id_comp] at h
    simpa only [m, ar, as', b, mateEquiv_apply, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id, Category.assoc] using h
  exact heq ▸ hm

/-- The compact-support restriction square commutes with the canonical integer shifts.
The restriction functors have their exact derived shifts, and compact support has
exact open shifts followed by canonical K-injective direct-image shifts.
Source: Stacks Tag 07A6; the normalized open/proper scalar square.
(blueprint: lem-pur-compact-support-restriction-shift).
Proof: the open comparison is induced by an isomorphism of exact functors, hence
commutes with the exact derived shifts. The proper comparison is the mate of the
exact inverse-image comparison under the canonical derived geometric adjunctions.
The latter commute with shifts. Whiskering the open square by proper image and
composing with the inverse proper square gives the asserted compatibility. -/
theorem restriction_commShift {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    letI : (pbcDerivedRestrict (a.map X)).CommShift ℤ :=
      inferInstanceAs ((pbcRestrict (a.map X)).mapDerivedCategory.CommShift ℤ)
    letI : (image R c).CommShift ℤ :=
      inferInstanceAs (((openExtension R c.i).mapDerivedCategory ⋙ push R c.g).CommShift ℤ)
    letI : (image S c).CommShift ℤ :=
      inferInstanceAs (((openExtension S c.i).mapDerivedCategory ⋙ push S c.g).CommShift ℤ)
    letI : (pbcDerivedRestrict (a.map Y)).CommShift ℤ :=
      inferInstanceAs ((pbcRestrict (a.map Y)).mapDerivedCategory.CommShift ℤ)
    NatTrans.CommShift (restriction a c).hom ℤ := by
  let : (pbcDerivedRestrict (a.map X)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (a.map X)).mapDerivedCategory.CommShift ℤ)
  let : (pbcDerivedRestrict (a.map c.Z)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (a.map c.Z)).mapDerivedCategory.CommShift ℤ)
  let : (pbcDerivedRestrict (a.map Y)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (a.map Y)).mapDerivedCategory.CommShift ℤ)
  have ho : NatTrans.CommShift (openRestriction a c.i).hom ℤ := by
    dsimp only [openRestriction, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let := ho
  have hp := properRestriction_shift a c.g
  let := hp
  let e := (Functor.associator (pbcDerivedRestrict (a.map X))
      (openExtension R c.i).mapDerivedCategory (push R c.g)).symm ≪≫
    Functor.isoWhiskerRight (openRestriction a c.i) (push R c.g) ≪≫
    Functor.associator (openExtension S c.i).mapDerivedCategory
      (pbcDerivedRestrict (a.map c.Z)) (push R c.g) ≪≫
    Functor.isoWhiskerLeft (openExtension S c.i).mapDerivedCategory
      (proEtaleRingRestrictionDerivedDirectImage c.g
        (R.ring Y) (S.ring Y) (R.ring c.Z) (S.ring c.Z)
        (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g) (a.square c.g)).symm ≪≫
    (Functor.associator (openExtension S c.i).mapDerivedCategory
      (push S c.g) (pbcDerivedRestrict (a.map Y))).symm
  have he : e.hom = (restriction a c).hom := by
    ext M
    simp only [e, restriction, push, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj]
    erw [Category.id_comp, Category.comp_id, Category.id_comp]
  rw [← he]
  dsimp only [e, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

-- The caller's scalar mate must use the same canonical restriction shifts.
-- This private normalization argument follows PbcScalarAmbientShift's proof.
private theorem restrictionScalarAdjunction_complexUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : L ⊣ R) (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (d : LD ⊣ R.mapDerivedCategory)
    (hd : ∀ H, d.unit.app (DerivedCategory.Qh.obj H) ≫ R.mapDerivedCategory.map (ε.app H) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj H) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app H))
    (P : CochainComplex A ℤ) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map
          (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
            ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
            DerivedCategory.Qh.map
              ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
            (DerivedCategory.quotientCompQhIso _).hom.app
              ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
  have hp := hd ((HomotopyCategory.quotient _ _).obj P)
  change d.unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
    R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
    R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient B (.up ℤ)).obj
      ((L.mapHomologicalComplex (.up ℤ)).obj P)) = _ at hp
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, Functor.map_id,
    Category.id_comp, Category.comp_id] at hp ⊢
  erw [LD.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [R.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id,
    Category.comp_id] at hp
  erw [Category.comp_id]
  erw [Category.id_comp] at hp
  exact hp

attribute [local irreducible] pbcDerivedScalarAdjunction in
private theorem restrictionScalarAdjunction_shift {T : Scheme.{u}}
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : A ⟶ B)
    [(pbcDerivedExtend φ).CommShift ℤ] [NatTrans.CommShift (pbcExtensionCounit φ) ℤ] :
    letI : (pbcDerivedRestrict φ).CommShift ℤ :=
      inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)
    (pbcDerivedScalarAdjunction φ).CommShift ℤ := by
  let : (pbcDerivedRestrict φ).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let L := pbcExtend φ
  let R := pbcRestrict φ
  let LD := pbcDerivedExtend φ
  let ε := pbcExtensionCounit φ
  let adj := pbcScalarAdjunction φ
  have hLD := pbcDerivedExtension_universal φ
  have hr (X : HomotopyCategory (pbcModules T (A))
      (.up ℤ)) :
      ∃ (K : HomotopyCategory (pbcModules T (A))
          (.up ℤ)) (f : K ⟶ X),
        IsIso (ε.app K) ∧ HomotopyCategory.quasiIso _ (.up ℤ) f := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, f, hK, hf⟩ :=
      ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
        (J := ProEt.topology T) (O := A) P
    exact ⟨_, (HomotopyCategory.quotient _ _).map f,
      pbcExtensionCounit_isIso φ K hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  obtain ⟨d, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    L R adj LD ε hLD hr
  have hn (P : CochainComplex (pbcModules T (A)) ℤ) :
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
    exact restrictionScalarAdjunction_complexUnit L R adj LD ε d hd P
  have he : d = pbcDerivedScalarAdjunction φ := by
    unfold pbcDerivedScalarAdjunction
    exact (pbcDerivedScalarAdjunction_exists φ).unique
      (fun P _ ↦ hn P) (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec
  have : LD.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LD ε
      (HomotopyCategory.quasiIso _ (.up ℤ))
  have hu : NatTrans.CommShift d.unit ℤ := by
    apply CategoryTheory.normalized_unit_commShift DerivedCategory.Qh DerivedCategory.Qh
      (L.mapHomotopyCategory (.up ℤ)) (R.mapHomotopyCategory (.up ℤ))
      LD R.mapDerivedCategory (adj.mapHomotopyCategory (.up ℤ)) d
      ε R.mapDerivedCategoryFactorsh.inv
    intro H
    apply (cancel_mono (R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj H))).mp
    simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id] using hd H
  rw [he] at hu
  exact Adjunction.CommShift.mk' _ ℤ hu

end WeilConjectures.PurCompactSupport
