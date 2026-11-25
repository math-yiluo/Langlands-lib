/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Comparison of the two strict Roos functor presentations -/
@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace WeilConjectures
universe a b t u v w s
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The explicit cofiber and cone constructions give the same strict Roos map.
Source: Stacks 0941 and the two-coordinate Roos calculation.
(blueprint: lem-pod-native-roos-functor-comparison-s8).
Proof: both shifted cone maps induce the componentwise product map on each
coordinate. Extensionality for maps out of the cofiber proves equality. -/
theorem podNativeRoosMap_eq
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') :
    integralOperationsRoosFunctor.map
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) = roosF.map f := by
  change (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom (roosU N) (roosU N')
        (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
        (Arrow.homMk (roosPmap f) (roosPmap f) (roosU_natural f).symm)) =
    (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
      (CochainComplex.mappingCone.map (roosU N) (roosU N')
        (roosPmap f) (roosPmap f) (roosU_natural f))
  exact congrArg ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
    (CategoryTheory.RoosConeCalculus.cofiberMap_eq_coneMap (roosU N) (roosU N')
      (roosPmap f) (roosPmap f) (roosU_natural f))

/-- Identity on Roos objects, identifying the two induced strict maps.
Source: Stacks 0941, the explicit shifted cone model
(blueprint: lem-pod-native-roos-functor-comparison-s8). -/
def podNativeRoosIso : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    integralOperationsRoosFunctor (A := A) ≅ roosF :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro N N' f
    simp only [Iso.refl_hom]
    dsimp only [Functor.comp_obj]
    erw [Category.comp_id, Category.id_comp]
    exact podNativeRoosMap_eq f)

section Pasting
variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₅] [Category C₆]
  (Q : C₁ ⥤ C₂) (L : C₂ ⥤ C₃) (H : C₁ ⥤ C₄) (Q' : C₄ ⥤ C₃)
  (T : C₃ ⥤ C₅) (K : C₄ ⥤ C₆) (Q'' : C₆ ⥤ C₅)

@[irreducible] private def pasteComparison
    (e : Q ⋙ L ≅ H ⋙ Q') (k : Q' ⋙ T ≅ K ⋙ Q'') :
    Q ⋙ (L ⋙ T) ≅ (H ⋙ K) ⋙ Q'' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e T ≪≫
    Functor.associator H Q' T ≪≫ Functor.isoWhiskerLeft H k ≪≫
    (Functor.associator H K Q'').symm

variable [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
  [HasShift C₄ ℤ] [HasShift C₅ ℤ] [HasShift C₆ ℤ]
  [Q.CommShift ℤ] [L.CommShift ℤ] [H.CommShift ℤ] [Q'.CommShift ℤ]
  [T.CommShift ℤ] [K.CommShift ℤ] [Q''.CommShift ℤ]

private theorem pasteComparison_commShift
    (e : Q ⋙ L ≅ H ⋙ Q') (k : Q' ⋙ T ≅ K ⋙ Q'')
    [NatTrans.CommShift e.hom ℤ] [NatTrans.CommShift k.hom ℤ] :
    NatTrans.CommShift (pasteComparison Q L H Q' T K Q'' e k).hom ℤ := by
  unfold pasteComparison
  change NatTrans.CommShift
    ((Functor.associator Q L T).inv ≫ Functor.whiskerRight e.hom T ≫
      (Functor.associator H Q' T).hom ≫ Functor.whiskerLeft H k.hom ≫
      (Functor.associator H K Q'').inv) ℤ
  infer_instance
end Pasting

section Generic

private theorem native_shift_asFunctor
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    (podNativeRoosShift.comparison C.asFunctor r).hom =
      (Functor.commShiftIso roosF
        (self := CategoryTheory.RoosConeCalculus.roosCommShift) r).hom.app C := by
  rfl

private theorem native_shift_Q [HasDerivedCategory A]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    DerivedCategory.Q.map ((Functor.commShiftIso roosF
        (self := CategoryTheory.RoosConeCalculus.roosCommShift) r).hom.app C) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app (roosF.obj C) =
    DerivedCategory.Q.map (podNativeRoosShift.comparison C.asFunctor r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app (integralOperationsRoos C.asFunctor) := by
  rfl

omit [HasCountableProducts A] in
private theorem hom_ext_of_decomposition {P Q R Z : A}
    (v : P ⟶ Q) (w : P ⟶ R) (i : Q ⟶ P) (j : R ⟶ P)
    (h : v ≫ i + w ≫ j = 𝟙 P) {a b : Z ⟶ P}
    (hv : a ≫ v = b ≫ v) (hw : a ≫ w = b ≫ w) : a = b := by
  calc
    a = (a ≫ v) ≫ i + (a ≫ w) ≫ j := by
      rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, h, Category.comp_id]
    _ = (b ≫ v) ≫ i + (b ≫ w) ≫ j := by rw [hv, hw]
    _ = b := by
      rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, h, Category.comp_id]

private theorem roosShift_hom_ext (S S' : WeilConjectures.PodSignedRoosShift A)
    (hS : S.Laws) (hS' : S'.Laws)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    (S.comparison C r).hom = (S'.comparison C r).hom := by
  have hf := (hS.1 C r).trans (hS'.1 C r).symm
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun f ↦ f.f i) hf
  simp only [HomologicalComplex.comp_f] at hfi
  erw [CochainComplex.shiftFunctor_map_f'] at hfi
  have hs := (hS.2 C r i).trans (hS'.2 C r i).symm
  have hid := CochainComplex.mappingCocone.id_X (WeilConjectures.podRoosBoundary C)
    (i + r) (i - 1 + r) (by omega)
  exact hom_ext_of_decomposition _ _ _ _ hid hfi hs

attribute [local instance] CategoryTheory.RoosConeCalculus.levelCommShift

private theorem nativeRoos_laws : (podNativeRoosShift (A := A)).Laws := by
  constructor
  · intro C r
    apply HomologicalComplex.hom_ext
    intro i
    have h := CategoryTheory.RoosConeCalculus.roosShift_v (towerAsComplex C) r i
    change (podNativeRoosShift.comparison C r).hom.f i ≫
        𝟙 _ ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C)).f (i + r) =
      (CochainComplex.mappingCocone.fst (podRoosBoundary (podShiftTower C r))).f i ≫
        (ProductShift.productShiftIso
          (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
          (towerAsComplex C) r).hom.f i at h
    erw [Category.id_comp, podProductShift] at h
    erw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      HomologicalComplex.comp_f]
    exact h
  · intro C r i
    have h := CategoryTheory.RoosConeCalculus.roosShift_u (towerAsComplex C) r i
    change (podNativeRoosShift.comparison C r).hom.f i ≫ 𝟙 _ ≫
        (CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
          (i + r) (i - 1 + r) (by omega) =
      r.negOnePow • ((CochainComplex.mappingCocone.snd
        (podRoosBoundary (podShiftTower C r))).v i (i - 1) (by omega) ≫
        (ProductShift.productShiftIso
          (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
          (towerAsComplex C) r).hom.f (i - 1)) at h
    erw [Category.id_comp, podProductShift] at h
    exact h

private theorem roosShift_eq (S S' : PodSignedRoosShift A)
    (hS : S.Laws) (hS' : S'.Laws) : S = S' := by
  cases S with
  | mk f =>
    cases S' with
    | mk g =>
      congr 1
      funext C r
      apply Iso.ext
      exact roosShift_hom_ext _ _ hS hS' C r

/-- The additive structure already captured by canonical derived shifts.
This explicit choice avoids expanding module-sheaf operations when specializing
cochain shift formulas. It is registered only locally in the proof modules.
Source: Mathlib's abelian instance for module sheaves
(blueprint: lem-pod-native-roos-functor-comparison-s8). -/
abbrev podSheafCanonicalPreadditive
    {T : Type v} [Category.{w} T] {J : GrothendieckTopology T}
    (M : Sheaf J RingCat.{s})
    [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] :
    Preadditive (SheafOfModules.{a} M) := (SheafOfModules.instAbelian M).toPreadditive

attribute [local instance 50000] podSheafCanonicalPreadditive

-- Match the zero morphisms carried by the abelian sheaf category.
private abbrev sheafTowerComplex
    {T : Type v} [Category.{w} T] {J : GrothendieckTopology T}
    (M : Sheaf J RingCat.{s})
    [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] :=
  CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{a} M) ℤ

private theorem roosShift_hom_ext_sheaf
    {T : Type v} [Category.{w} T] {J : GrothendieckTopology T}
    (M : Sheaf J RingCat.{s})
    [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
    [HasCountableProducts (SheafOfModules.{a} M)]
    (S S' : PodSignedRoosShift (SheafOfModules.{a} M))
    (hS : S.Laws) (hS' : S'.Laws)
    (C : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{a} M) ℤ) (r : ℤ) :
    (S.comparison C r).hom = (S'.comparison C r).hom := by
  exact roosShift_hom_ext S S' hS hS' C r

attribute [local instance] CategoryTheory.RoosConeCalculus.roosCommShift

private theorem roosShift_hom_ext_complex_sheaf
    {T : Type v} [Category.{w} T] {J : GrothendieckTopology T}
    (M : Sheaf J RingCat.{s})
    [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
    [HasCountableProducts (SheafOfModules.{a} M)]
    (S : PodSignedRoosShift (SheafOfModules.{a} M)) (hS : S.Laws)
    (C : sheafTowerComplex M) (r : ℤ) :
    (Functor.commShiftIso roosF r).hom.app C = (S.comparison C.asFunctor r).hom := by
  have h := roosShift_hom_ext_sheaf M S podNativeRoosShift hS nativeRoos_laws C.asFunctor r
  rw [native_shift_asFunctor] at h
  convert h.symm using 1
  rfl

end Generic

end WeilConjectures
