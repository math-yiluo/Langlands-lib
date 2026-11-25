/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SmoothPurity.PurStrictScalar.NativeReductionCounitKFlat

/-! # Universal whole-cochain scalar reduction counit

Source: Stacks 06YY and 0940--0941; the whole-sequence derived balancing construction.
(blueprint: lem-pur-scalar-target-counit-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.reductionChange
  HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower

-- A computing comparison on a resolving class is already universal.
private theorem kanOfResolving
    {A B H : Type*} [Category A] [Category B] [Category H]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (Q : A ⥤ B) [Q.IsLocalization W] (P : A → Prop)
    (res : ∀ X, ∃ Y, ∃ s : Y ⟶ X, P Y ∧ W s)
    (T : B ⥤ H) (F : A ⥤ H) (ε : Q ⋙ T ⟶ F)
    (computes : ∀ X, P X → IsIso (ε.app X)) : T.IsRightKanExtension ε := by
  classical
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W H
  have extension (V : B ⥤ H) (η : Q ⋙ V ⟶ F) :
      ∃ γ : V ⟶ T, Functor.whiskerLeft Q γ ≫ ε = η := by
    let α (X : A) (hX : P X) : (Q ⋙ V).obj X ⟶ (Q ⋙ T).obj X :=
      letI := computes X hX
      η.app X ≫ inv (ε.app X)
    have hα (X Y : A) (hX : P X) (hY : P Y) (s : X ⟶ Y) :
        (Q ⋙ V).map s ≫ α Y hY = α X hX ≫ (Q ⋙ T).map s := by
      have := computes X hX
      have := computes Y hY
      apply (cancel_mono (ε.app Y)).1
      simp only [α, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [ε.naturality s, IsIso.inv_hom_id_assoc]
      exact η.naturality s
    have hV : W.IsInvertedBy (Q ⋙ V) := by
      intro X Y s hs
      have := Localization.inverts Q W s hs
      exact V.map_isIso (Q.map s)
    obtain ⟨β, hβ⟩ := exists_natTrans_from_resolvingClass W P res
      (Q ⋙ V) (Q ⋙ T) hV α hα
    let γ := ff.preimage β
    have hγ : Functor.whiskerLeft Q γ = β := ff.map_preimage β
    refine ⟨γ, ?_⟩
    ext X
    obtain ⟨Y, s, hY, hs⟩ := res X
    have := Localization.inverts Q W s hs
    apply (cancel_epi (V.map (Q.map s))).1
    change (Q ⋙ V).map s ≫ (γ.app (Q.obj X) ≫ ε.app X) =
      (Q ⋙ V).map s ≫ η.app X
    rw [η.naturality s]
    have hb := congr_app hγ X
    change γ.app (Q.obj X) = β.app X at hb
    rw [hb, ← Category.assoc, β.naturality s, Category.assoc,
      ε.naturality s, ← Category.assoc, hβ Y hY]
    have := computes Y hY
    simp [α]
  have unique (V : B ⥤ H) (γ γ' : V ⟶ T)
      (h : Functor.whiskerLeft Q γ ≫ ε = Functor.whiskerLeft Q γ' ≫ ε) : γ = γ' := by
    apply Localization.natTrans_ext Q W
    intro X
    obtain ⟨Y, s, hY, hs⟩ := res X
    have := Localization.inverts Q W s hs
    have := computes Y hY
    have he : γ.app (Q.obj Y) = γ'.app (Q.obj Y) := by
      apply (cancel_mono (ε.app Y)).1
      exact congr_app h Y
    apply (cancel_epi (V.map (Q.map s))).1
    rw [γ.naturality, γ'.naturality, he]
  choose lift fac using extension
  constructor
  refine ⟨IsTerminal.ofUniqueHom
    (fun X ↦ CostructuredArrow.homMk (lift X.left X.hom) (fac X.left X.hom)) ?_⟩
  intro X m
  apply CostructuredArrow.hom_ext
  exact unique X.left m.left _ ((CostructuredArrow.w m).trans (fac X.left X.hom).symm)

private theorem cochainKanOfResolving
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ X, ∃ Y, ∃ s : Y ⟶ X, good Y ∧ QuasiIso s)
    (computes : ∀ X, good X → IsIso (ε.app X)) : T.IsRightKanExtension ε := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α : q ⋙ (Q ⋙ T) ⟶ q ⋙ F := Functor.whiskerRight i.hom T ≫ ε ≫ j.inv
  let H := (Functor.whiskeringLeft _ _ (DerivedCategory B)).obj q
  let δ := H.preimage α
  have hδ : Functor.whiskerLeft q δ = α := H.map_preimage α
  let P : HomotopyCategory A (.up ℤ) → Prop := fun X ↦
    ∃ Y, good Y ∧ q.obj Y = X
  have hres : ∀ X, ∃ Y, ∃ s : Y ⟶ X, P Y ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, s, hY, hs⟩ := res X
    exact ⟨q.obj Y, q.map s, ⟨Y, hY, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hcomp : ∀ X, P X → IsIso (δ.app X) := by
    rintro X ⟨Y, hY, rfl⟩
    have := computes Y hY
    have he := congr_app hδ Y
    change δ.app (q.obj Y) = α.app Y at he
    rw [he]
    dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have := kanOfResolving (HomotopyCategory.quasiIso A (.up ℤ)) Q P hres T F δ hcomp
  have := AlgebraicGeometry.Scheme.kan_precomp_quotient q Q F T δ
  have hkan := AlgebraicGeometry.Scheme.kan_change_iso T i j
    ((Functor.associator q Q T).hom ≫ Functor.whiskerLeft q δ)
  have he : Functor.whiskerRight i.inv T ≫
      ((Functor.associator q Q T).hom ≫ Functor.whiskerLeft q δ) ≫ j.hom = ε := by
    rw [hδ]
    ext X
    simp only [α, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id,
      ← T.map_comp_assoc, Iso.inv_hom_id_app, T.map_id, Category.id_comp]
  rwa [he] at hkan

private def cochainCounit
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := reductionComplexCounit E T ε P
  naturality := by
    intro P Q f
    have h := (AlgebraicGeometry.Scheme.complexCounitNat E T ε).naturality f
    simpa only [AlgebraicGeometry.Scheme.complexCounitNat_app] using h

private theorem cochainCounit_app
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    (cochainCounit E T ε).app P = reductionComplexCounit E T ε P := rfl

private theorem cochainCounit_formula
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    (cochainCounit E T ε).app P =
      T.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) := rfl

private theorem pbcCochainCounit_app (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules W R) ℤ) :
    (cochainCounit (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ)).app P =
      pbcComplexCounit φ P := rfl

private def pbcCochainCounit (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedExtend φ ⟶
      (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := pbcComplexCounit φ P
  naturality := by
    intro P Q f
    simpa only [pbcCochainCounit_app] using
      (cochainCounit (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ)).naturality f

attribute [local irreducible] cochainCounit

-- Keep composition bookkeeping abstract when applying it to large coefficient categories.
private def pasteCounit
    {A B C : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] (U : DerivedCategory B ⥤ DerivedCategory C)
    (β : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (T ⋙ U) ⟶
      (E ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  { app := fun P ↦ U.map (α.app P) ≫ β.app ((E.mapHomologicalComplex (.up ℤ)).obj P)
    naturality := by
      intro P Q f
      dsimp only [Functor.comp_map]
      erw [← U.map_comp_assoc, α.naturality, U.map_comp, Category.assoc, β.naturality]
      rw [← Category.assoc]
      rfl }

private theorem pasteCounit_app
    {A B C : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] (U : DerivedCategory B ⥤ DerivedCategory C)
    (β : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex A ℤ) :
    (pasteCounit E T α F U β).app P =
      U.map (α.app P) ≫ β.app ((E.mapHomologicalComplex (.up ℤ)).obj P) := by rfl

private theorem pasteCounit_computes
    {A B C : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] (U : DerivedCategory B ⥤ DerivedCategory C)
    (β : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex A ℤ) [IsIso (α.app P)]
    [IsIso (β.app ((E.mapHomologicalComplex (.up ℤ)).obj P))] :
    IsIso ((pasteCounit E T α F U β).app P) := by
  rw [pasteCounit_app]
  infer_instance

attribute [local irreducible] pasteCounit

private theorem tripleCounitUniversal
    {A B C H : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    [Category H] [Abelian H] [HasDerivedCategory H]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] (U : DerivedCategory B ⥤ DerivedCategory C)
    (β : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G : C ⥤ H) [G.Additive] (V : DerivedCategory C ⥤ DerivedCategory H)
    (γ : DerivedCategory.Q ⋙ V ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ X, ∃ Y, ∃ s : Y ⟶ X, good Y ∧ QuasiIso s)
    (hα : ∀ P, good P → IsIso (α.app P))
    (hβ : ∀ P, good P → IsIso (β.app ((E.mapHomologicalComplex (.up ℤ)).obj P)))
    [IsIso γ] :
    ∃ δ : DerivedCategory.Q ⋙ (T ⋙ U ⋙ V) ⟶
        (E ⋙ F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      (∀ P, δ.app P = V.map (U.map (α.app P)) ≫
        V.map (β.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        γ.app ((F.mapHomologicalComplex (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P))) ∧
      (T ⋙ U ⋙ V).IsRightKanExtension δ := by
  let ε := pasteCounit F U β G V γ
  let δ := pasteCounit E T α (F ⋙ G) (U ⋙ V) ε
  refine ⟨δ, ?_, ?_⟩
  · intro P
    rw [pasteCounit_app, pasteCounit_app]
    rfl
  · apply cochainKanOfResolving (E ⋙ F ⋙ G) (T ⋙ U ⋙ V) δ good res
    intro P hP
    have := hα P hP
    have := hβ P hP
    have : IsIso (ε.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) :=
      pasteCounit_computes _ _ _ _ _ _ _
    exact pasteCounit_computes _ _ _ _ _ _ _

private theorem fourCounitUniversal
    {A B C H J : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    [Category H] [Abelian H] [HasDerivedCategory H]
    [Category J] [Abelian J] [HasDerivedCategory J]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] (U : DerivedCategory B ⥤ DerivedCategory C)
    (β : DerivedCategory.Qh ⋙ U ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (G : C ⥤ H) [G.Additive] (V : DerivedCategory C ⥤ DerivedCategory H)
    (γ : DerivedCategory.Q ⋙ V ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : H ⥤ J) [K.Additive] (L : DerivedCategory H ⥤ DerivedCategory J)
    (κ : DerivedCategory.Q ⋙ L ⟶ K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [IsIso γ] [IsIso κ]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ X, ∃ Y, ∃ s : Y ⟶ X, good Y ∧ QuasiIso s)
    (hα : ∀ P, good P → IsIso (α.app P))
    (hβ : ∀ P, good P → IsIso (β.app ((HomotopyCategory.quotient _ _).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj P)))) :
    let O := F ⋙ G
    let c (P : CochainComplex B ℤ) :=
      U.map ((DerivedCategory.quotientCompQhIso B).inv.app P) ≫
        β.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
    let d (P : CochainComplex B ℤ) :=
      V.map (c P) ≫ γ.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ∃ ε : DerivedCategory.Q ⋙ (T ⋙ (U ⋙ V) ⋙ L) ⟶
        (E ⋙ O ⋙ K).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      (∀ P, ε.app P = L.map ((U ⋙ V).map (α.app P)) ≫
        L.map (d ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        κ.app ((O.mapHomologicalComplex (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P))) ∧
      (T ⋙ (U ⋙ V) ⋙ L).IsRightKanExtension ε := by
  let c := cochainCounit F U β
  let d := pasteCounit F U c G V γ
  have hd (P) (hP : good P) : IsIso (d.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
    have := hβ P hP
    have : IsIso (c.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [cochainCounit_app]
      dsimp only [reductionComplexCounit]
      infer_instance
    exact pasteCounit_computes _ _ _ _ _ _ _
  obtain ⟨ε, hε, hkan⟩ := tripleCounitUniversal E T α (F ⋙ G) (U ⋙ V) d K L κ
    good res hα hd
  refine ⟨ε, ?_, hkan⟩
  intro P
  rw [hε]
  dsimp only [d, c]
  rw [pasteCounit_app, cochainCounit_formula]

namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem scalarExtensionComputes (W : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    IsIso (pbcCochainCounit W (completedCoefficientMap l E F i W) |>.app P) := by
  dsimp only [pbcCochainCounit, pbcComplexCounit]
  have := pbcExtensionCounit_isIso (completedCoefficientMap l E F i W) P hP
  infer_instance

private theorem scalarExtensionKFlat (W : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l F W)
      (((pbcExtend (completedCoefficientMap l E F i W)).mapHomologicalComplex (.up ℤ)).obj P) :=
  SheafOfModules.changeOfRings_isKFlat_independentCoefficients
    (completedCoefficientMap l E F i W) P _
    (reductionChange_obj_eq W (completedCoefficientMap l E F i W))
    (reductionChange_map_eq W (completedCoefficientMap l E F i W)) hP

/-- Completed scalar extension followed by native reduction and arithmetic
restriction has its universal composite cochain counit.
Source: Stacks 06YY (derived tensor composition), 0940--0941 (ringed sequence systems).
Proof: choose a K-flat resolution of the completed E-module complex. Its extension
to completed F coefficients is K-flat: restriction of scalars is exact, and the
tensor adjunction tests acyclicity against arbitrary acyclic coefficient complexes.
Compute native F quotient extension on this replacement. Derived tensor
associativity identifies this with the left derived functor of the composite
ordinary extensions. The mate defining the native reduction counit is the
universal counit by its normalized derived-limit adjunction. Exact restriction to
constant integral scalars followed by arithmetic restriction of strict diagrams
preserves the calculation, since both operate on the underlying whole sequence
complex and compute cohomology pointwise. Pasting the scalar-extension counit,
reduction counit and exact-localization factor yields exactly the formula below.
This construction is natural on all complexes, and its universal property
identifies maps into the resulting derived functor with maps into the ordinary
composite after Q. Hence it is the asserted right Kan extension. The index e=1
is the identity subsequence, and the same argument applies to the zero complex
and the empty site object.
(blueprint: lem-pur-scalar-target-counit-universal). -/
theorem scalarTargetCounit_universal (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l F W) (e : ℕ) :
    letI := ordinaryReduction_additive l F W
    letI := systemRestriction_additive l F W
    let O := ordinaryReduction l F W ⋙ systemRestriction l F W
    letI : O.Additive := inferInstanceAs
      ((ordinaryReduction l F W ⋙ systemRestriction l F W).Additive)
    let γ (P : CochainComplex (scalarReductionSource l F W) ℤ) :=
      S.reduction.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        (systemReductionCounit l F W S).app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map
          (((ordinaryReduction l F W).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((ordinaryReduction l F W).mapHomologicalComplex (.up ℤ)).obj P)
    let δ (P : CochainComplex (scalarReductionSource l F W) ℤ) :
        (reduction l F W S).obj (DerivedCategory.Q.obj P) ⟶
          DerivedCategory.Q.obj ((O.mapHomologicalComplex (.up ℤ)).obj P) :=
      (systemU l F W).map (γ P) ≫
        (systemRestriction l F W).mapDerivedCategoryFactors.hom.app
          (((ordinaryReduction l F W).mapHomologicalComplex (.up ℤ)).obj P)
    let r := CategoryTheory.StrictTowerArithmetic.restriction
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) e
    let R := CategoryTheory.StrictTowerArithmetic.derivedRestriction
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) e
    let C := pbcExtend (completedCoefficientMap l E F i W)
    letI : (C ⋙ O ⋙ r).Additive := inferInstance
    let D := pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙ reduction l F W S ⋙ R
    ∃ α : DerivedCategory.Q ⋙ D ⟶
        ((C ⋙ O ⋙ r).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q,
      (∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
        α.app P = R.map
            ((reduction l F W S).map (pbcComplexCounit (completedCoefficientMap l E F i W) P)) ≫
          R.map (δ ((C.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          r.mapDerivedCategoryFactors.hom.app
            ((O.mapHomologicalComplex (.up ℤ)).obj
              ((C.mapHomologicalComplex (.up ℤ)).obj P))) ∧
      D.IsRightKanExtension α := by
  intro O γ₀ δ₀ r R C D
  have := ordinaryReduction_additive l F W
  have := systemRestriction_additive l F W
  have : O.Additive := inferInstanceAs
    ((ordinaryReduction l F W ⋙ systemRestriction l F W).Additive)
  have : r.Additive := inferInstance
  have : (O ⋙ r).Additive := inferInstance
  have : C.Additive := inferInstanceAs
    ((pbcExtend (completedCoefficientMap l E F i W)).Additive)
  have : (C ⋙ O ⋙ r).Additive := inferInstance
  let LC := pbcDerivedExtend (completedCoefficientMap l E F i W)
  let εC := pbcCochainCounit W (completedCoefficientMap l E F i W)
  let good (P : CochainComplex (scalarReductionSource l E W) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P
  have res (X : CochainComplex (scalarReductionSource l E W) ℤ) :
      ∃ P, ∃ s : P ⟶ X, good P ∧ QuasiIso s := by
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E W) X
    exact ⟨P, s, hP, hs⟩
  have hεC (P) (hP : good P) : IsIso (εC.app P) :=
    scalarExtensionComputes l E F i W P hP
  have hγ (P) (hP : good P) := nativeReductionCounit_kFlat l F W S
    ((C.mapHomologicalComplex (.up ℤ)).obj P) (scalarExtensionKFlat l E F i W P hP)
  exact fourCounitUniversal C LC εC
    (ordinaryReduction l F W) S.reduction (systemReductionCounit l F W S)
    (systemRestriction l F W) (systemU l F W)
    (systemRestriction l F W).mapDerivedCategoryFactors.hom
    r R r.mapDerivedCategoryFactors.hom good res hεC hγ

end WeilConjectures.PurStrictScalar
