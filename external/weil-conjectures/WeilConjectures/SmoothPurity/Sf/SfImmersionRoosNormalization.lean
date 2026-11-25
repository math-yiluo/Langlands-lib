/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.ExactAdjointTowerModels.ExactAdjointTowerModels
import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Uniqueness and normalization of the strict Roos comparison

Source: localization Step 6, the strict Roos model of derived inverse limit.
The comparison is determined on K-injectives and extended by naturality along
functorial K-injective resolutions. The remaining private helpers transport the
existing exact-products comparison to the positive-difference convention.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
attribute [local irreducible] CategoryTheory.Limits.limit HasDerivedCategory.standard

universe u uA vA w

private theorem component_iso_eqToIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (h : F = G) (hobj : ∀ X, F.obj X = G.obj X)
    (hn : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (eqToIso (hobj Y)).hom = (eqToIso (hobj X)).hom ≫ G.map f) :
    NatIso.ofComponents (fun X ↦ eqToIso (hobj X)) hn = eqToIso h := by
  cases h
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rfl

private theorem exact_left_derived_iso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G F : A ⥤ B) [G.Additive] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))]
    (μ : G ≅ F) :
    ∃! e : L ≅ F.mapDerivedCategory,
      whiskerLeft DerivedCategory.Qh e.hom ≫ F.mapDerivedCategoryFactorsh.hom =
        ε ≫ whiskerRight (NatTrans.mapHomotopyCategory μ.hom (.up ℤ))
          DerivedCategory.Qh := by
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let m : G.mapHomotopyCategory (.up ℤ) ≅ F.mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory μ.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory μ.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  let τ := isoWhiskerRight m DerivedCategory.Qh
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactorsh
  let e : L ≅ F.mapDerivedCategory := Functor.leftDerivedNatIso L F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom W τ
  have he : whiskerLeft DerivedCategory.Qh e.hom ≫ F.mapDerivedCategoryFactorsh.hom =
      ε ≫ τ.hom := Functor.leftDerivedNatTrans_fac L F.mapDerivedCategory ε
        F.mapDerivedCategoryFactorsh.hom W τ.hom
  exact ⟨e, he, fun e' he' ↦ Iso.ext
    (Functor.leftDerived_ext F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom W L
      e'.hom e.hom (he'.trans he.symm))⟩

-- This generic certificate identifies the canonical product comparison with the
-- original projection formula, for any proof of evaluation compatibility.
private theorem roos_product_comparison_formula
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (h : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).obj (M.asFunctor.obj (op n)) =
      ((roosTowerAction F).obj M).asFunctor.obj (op n)) :
    Pi.lift (f := fun n : ℕ ↦ ((roosTowerAction F).obj M).asFunctor.obj (op n))
      (fun n : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) ≫ eqToHom (h n)) =
      roosProductComparison F M := by
  apply Pi.hom_ext
  intro n
  simp only [roosProductComparison, piComparison, Pi.lift_comp_π,
    eqToHom_refl, Category.comp_id]
  change (F.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) =
    (Pi.lift (fun k : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun j : ℕ ↦ M.asFunctor.obj (op j)) k))) ≫
        Pi.π (fun k : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).obj
          (M.asFunctor.obj (op k))) n
  rw [Pi.lift_comp_π]

private theorem roos_iso_unique
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃! e : (F.mapHomologicalComplex (.up ℤ)).obj (strictRoosComplex M) ≅
        strictRoosComplex
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates
            ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj M)
            p).hom =
        F.map (strictRoosCoordinates M p).hom ≫ biprodComparison F _ _ ≫
          biprod.map ((roosProductComparison F M).f p)
            ((roosProductComparison F M).f (p + 1)) := by
  have := roosAdditiveComparison_isIso F M
  refine ⟨asIso (roosAdditiveComparison F M), ?_, ?_⟩
  · exact fun p ↦ roosAdditiveComparison_coordinates F M p
  · intro e he
    apply Iso.ext
    ext k : 1
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    apply (cancel_mono (strictRoosCoordinates
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj M)
      p).hom).1
    exact (he p).trans (roosAdditiveComparison_coordinates F M p).symm

namespace AlgebraicGeometry.Scheme.ImmersionCompletedPullback

private theorem normalized_exact_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (he : F = G) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : L ≅ G.mapDerivedCategory)
    (hnorm : whiskerLeft DerivedCategory.Qh e.hom ≫ G.mapDerivedCategoryFactorsh.hom =
      ε ≫ whiskerRight (NatTrans.mapHomotopyCategory (eqToIso he).hom (.up ℤ))
        DerivedCategory.Qh)
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P) :
    ExactDerivedCounitNormalization F G L
      (Functor.leftDerivedCounitOnComplex F L ε) hp e := by
  cases he
  intro P
  have h := congr_app hnorm ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.mapHomotopyCategory_id,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, NatTrans.id_app,
    DerivedCategory.Qh.map_id] at h
  erw [Category.comp_id] at h
  have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso C).inv.app P)
  simp only [eqToIso_refl, Iso.refl_hom, DerivedCategory.Q.map_id, Category.comp_id]
  dsimp only [Functor.leftDerivedCounitOnComplex]
  rw [← h, F.mapDerivedCategoryFactorsh_hom_app]
  simp only [← Category.assoc]
  erw [hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.Scheme.ImmersionCompletedPullback
