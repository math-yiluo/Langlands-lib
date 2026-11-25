/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceSectionsLimit
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections

/-! # Normalized sections and inverse limit for constant-coefficient towers

Source: Stacks 0941 and 0D6E. The ordinary sections functor may be any additive
limit-preserving functor to abelian groups.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe a av d dt w sep
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace WeilConjectures.CoefficientSectionsCoreComparison

variable {A : Type a} [Category.{av} A] [Abelian A]
  [HasDerivedCategory.{d} A]
  [Abelian.HasKInjectiveResolutions A]

/-- The existing total right-derived functor with its actual cochain unit.
Source: Stacks 079P; the universal comparison is invertible on K-injectives.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
@[reducible] def standardPair {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] : SequenceSectionsDerivedPair F where
  functor := F.rightDerivedFunctor
  unit :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  universal := by
    have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
        (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
      intro X Y f hf
      have : X.obj.IsKInjective := X.property
      have : Y.obj.IsKInjective := Y.property
      have : QuasiIso f.hom := hf
      obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
        (inferInstance : QuasiIso f.hom)
      have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
        rw [← he]
        exact (F.mapHomotopyEquiv e).quasiIso_hom
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
      infer_instance
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (F.rightDerivedFunctorUnitQ I.obj)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  computes I hI := by
    have := hI
    change IsIso (F.rightDerivedFunctorUnitQ I)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance

section Tower

variable [HasDerivedCategory.{dt} (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{w})]
  [IsGrothendieckAbelian.{sep} A] [HasLimitsOfShape ℕᵒᵖ A]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
  [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive]
  (G : A ⥤ AddCommGrpCat.{w}) [G.Additive] [PreservesLimitsOfShape ℕᵒᵖ G]

/-- The constant-tower sections/limit comparison with its actual universal units.
Source: Stacks 0941 and 0D6E. Limit preserves K-injectives by the exact constant-tower
left adjoint. In the other order the sections of a K-injective tower are limit-acyclic
by the existing split-transition Roos calculation. The two composite universal derived
pairs are thus isomorphic, with the displayed unit equation, by right-derived uniqueness.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
theorem comparison_exists :
    ∃ κ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        G.rightDerivedFunctorUnitQ
            (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          G.rightDerivedFunctor.map
            ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ X) ≫
          κ.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (preservesLimitNatIso G (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
          (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctorUnitQ
            (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
              (.up ℤ)).obj X) ≫
          (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor.map
            (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ
              X) := by
  let L := standardPair (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  let P := standardPair G
  let T := standardPair ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)
  let R := standardPair (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let α := SheafOfModules.sectionsCompositeUnit _ _ L P
  let β := SheafOfModules.sectionsCompositeUnit _ _ T R
  have hα := SheafOfModules.sectionsCompositeDerived _ _ L P (fun I hI ↦ by
    have := hI
    exact P.computes _ inferInstance)
  have hβ := SheafOfModules.sectionsCompositeDerived _ _ T R
    (fun I hI ↦ SheafOfModules.sectionsTowerImageAcyclic G R I hI)
  let τ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
    (preservesLimitNatIso G (J := ℕᵒᵖ)) (.up ℤ)) DerivedCategory.Q
  let κ := Functor.rightDerivedNatIso _ _ α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) τ
  refine ⟨κ, ?_⟩
  intro X
  have h := Functor.rightDerivedNatTrans_app _ _ α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) τ.hom X
  change α.app X ≫ κ.hom.app (DerivedCategory.Q.obj X) = τ.hom.app X ≫ β.app X at h
  simpa only [α, β, L, P, T, R, SheafOfModules.sectionsCompositeUnit, τ, standardPair,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc] using h

omit [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{w})]
  [IsGrothendieckAbelian.{sep} A]
  [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive] in
/-- A projection characterized on K-injectives satisfies its unit equation on every complex.
Source: Stacks 079P and 0941. Derive the ordinary projection by the universal property.
Its unit equation holds on all complexes. On K-injectives, cancellation of the invertible
unit identifies it with the prescribed projection. Naturality extends equality to all
objects, since every derived object has a K-injective representative.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
theorem projection_unit (n : ℕ)
    (p : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⟶
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory)
    (hp : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
      p.app (DerivedCategory.Q.obj I) ≫
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I =
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (lim.π (op n)) (.up ℤ)).app I))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K ≫
      p.app (DerivedCategory.Q.obj K) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app K =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (lim.π (op n)) (.up ℤ)).app K) := by
  obtain ⟨q, hq⟩ := SheafOfModules.sectionsProjections
    (standardPair (lim : (ℕᵒᵖ ⥤ A) ⥤ A))
  have heq : p = q n := by
    apply SheafOfModules.sectionsNatTransExt
    intro I hI
    have := hI
    apply (cancel_mono
      (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I)).mp
    apply (cancel_epi ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).inv).mp
    rw [hp I, Iso.inv_hom_id_assoc]
    simpa only [standardPair, Functor.rightDerivedFunctorUnitQ_eq] using (hq I n).symm
  rw [heq]
  exact hq K n

omit [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{w})]
  [IsGrothendieckAbelian.{sep} A] [HasLimitsOfShape ℕᵒᵖ A]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
  [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive]
  [PreservesLimitsOfShape ℕᵒᵖ G] in
/-- Derived termwise sections and exact evaluation have normalized comparisons.
Source: Stacks 0941. Apply the existing normalized tower comparison to the actual
right-derived pairs. Evaluation preserves K-injectives by its exact left adjoint, and
uniqueness of the derived comparison gives precisely the displayed normalization.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
theorem evaluation_exists :
    ∃ β : ∀ n : ℕ,
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor ⋙
        ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ G.rightDerivedFunctor,
      ∀ (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
        ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategoryFactors.inv.app
            (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
              (.up ℤ)).obj I) ≫
          ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory.map
            (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ
              I) ≫
          (β n).hom.app (DerivedCategory.Q.obj I) ≫ G.rightDerivedFunctor.map
            (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I) =
        G.rightDerivedFunctorUnitQ
          ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj I) := by
  have enough (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a := by
    obtain ⟨I, hI, a, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, hq⟩
  obtain ⟨β, hβ, _⟩ := SheafOfModules.coefficientTowerComparison G (standardPair G)
    (standardPair ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)) enough
  exact ⟨fun n ↦ β (op n), fun n I _ ↦ hβ (op n) I⟩

omit [IsGrothendieckAbelian.{sep} A] in
/-- Transport the normalized comparison along a morphism of derived towers.
Source: Stacks 079P and 0941. Compose the unit equation with the image of the
morphism on the right and use naturality of the comparison to move that image
across the comparison. Keeping this calculation abstract avoids repeatedly
unfolding the coefficient site's derived functors.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
theorem comparison_morphism
    (κ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hκ : G.rightDerivedFunctorUnitQ
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ X) ≫
        κ.hom.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (preservesLimitNatIso G (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctorUnitQ
          (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ X))
    {M : DerivedCategory (ℕᵒᵖ ⥤ A)} (f : DerivedCategory.Q.obj X ⟶ M) :
    G.rightDerivedFunctorUnitQ
        (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
      G.rightDerivedFunctor.map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ X) ≫
      G.rightDerivedFunctor.map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map f) ≫
      κ.hom.app M =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (preservesLimitNatIso G (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctorUnitQ
        (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
          (.up ℤ)).obj X) ≫
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor.map
        (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ X) ≫
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor.map
        (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor.map f) := by
  have hn := κ.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  have hfirst := congrArg (fun z ↦ G.rightDerivedFunctorUnitQ
    (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
    G.rightDerivedFunctor.map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ X) ≫ z) hn
  have h := congrArg (fun z ↦ z ≫
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor.map
      (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor.map f)) hκ
  exact hfirst.trans (by simpa only [Functor.comp_obj, Category.assoc] using h)

omit [IsGrothendieckAbelian.{sep} A] in
/-- Universal-unit normalization determines the actual finite projections.
Source: Stacks 0941 and 0D6E. On a K-injective tower, precompose with the invertible
composite unit and postcompose with the exact evaluation factorization. Naturality of
the derived projection, the evaluation-unit equation, the ordinary limit projection
equation and the two projection-unit equations reduce both sides to the same map.
Naturality against K-injective representatives then proves the result on every object.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
theorem comparison_projection
    (pA : ∀ n : ℕ, (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⟶
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory)
    (pB : ∀ n : ℕ,
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor ⟶
        ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory)
    (β : ∀ n : ℕ,
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor ⋙
        ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (κ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor)
    (hpA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ X ≫
        (pA n).app (DerivedCategory.Q.obj X) ≫
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X))
    (hpB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ) (n : ℕ),
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctorUnitQ X ≫
        (pB n).app (DerivedCategory.Q.obj X) ≫
        ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategoryFactors.hom.app X =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X))
    (hβ : ∀ (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
      ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategoryFactors.inv.app
          (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
        ((evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ I) ≫
        (β n).hom.app (DerivedCategory.Q.obj I) ≫ G.rightDerivedFunctor.map
          (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I) =
      G.rightDerivedFunctorUnitQ
        ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj I))
    (hκ : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      G.rightDerivedFunctorUnitQ
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ X) ≫
        κ.hom.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (preservesLimitNatIso G (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctorUnitQ
          (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ X))
    (M : DerivedCategory (ℕᵒᵖ ⥤ A)) (n : ℕ) :
    κ.hom.app M ≫ (pB n).app
        (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor.obj M) ≫
      (β n).hom.app M = G.rightDerivedFunctor.map ((pA n).app M) := by
  let LA := standardPair (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  let LB := standardPair (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let γ₁ : LA.functor ⋙ (standardPair G).functor ⟶
      ((CategoryTheory.evaluation ℕᵒᵖ (A)).obj
        (op n)).mapDerivedCategory ⋙ (standardPair G).functor :=
    κ.hom ≫ Functor.whiskerLeft
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor (pB n) ≫
        (β n).hom
  let γ₂ := Functor.whiskerRight (pA n) (standardPair G).functor
  have hγ : γ₁ = γ₂ := by
    apply sectionsNatTransExt
    intro I hI
    have := hI
    have := LA.computes I hI
    have := (standardPair G).computes
      (((lim : (ℕᵒᵖ ⥤ A) ⥤
        A).mapHomologicalComplex (.up ℤ)).obj I) inferInstance
    have : IsIso ((sectionsCompositeUnit _ _ LA (standardPair G)).app I) := by
      change IsIso ((standardPair G).unit.app _ ≫ (standardPair G).functor.map (LA.unit.app I))
      infer_instance
    apply (cancel_epi ((sectionsCompositeUnit _ _ LA (standardPair G)).app I)).mp
    change ((standardPair G).unit.app _ ≫ (standardPair G).functor.map (LA.unit.app I)) ≫
      (κ.hom.app _ ≫ (pB n).app _ ≫ (β n).hom.app _) =
      ((standardPair G).unit.app _ ≫ (standardPair G).functor.map (LA.unit.app I)) ≫
        (standardPair G).functor.map ((pA n).app _)
    apply (cancel_mono ((standardPair G).functor.map
      (((CategoryTheory.evaluation ℕᵒᵖ (A)).obj
        (op n)).mapDerivedCategoryFactors.hom.app I))).mp
    have he := hβ n I hI
    have he' := congrArg (fun z ↦
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
            (.up ℤ)).obj I) ≫ z) he
    simp only [Iso.hom_inv_id_app_assoc] at he'
    have hn := (pB n).naturality
      (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ I)
    have hc : (NatIso.mapHomologicalComplex
        (preservesLimitNatIso (G) (J := ℕᵒᵖ))
          (.up ℤ)).hom.app I ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
            (.up ℤ)).obj I) =
      ((G).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
      apply HomologicalComplex.hom_ext
      intro i
      exact preservesLimitIso_hom_π (G) (I.X i) (op n)
    have hfπ := (standardPair G).unit.naturality
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)
    dsimp only [Functor.comp_map] at hfπ
    simp only [Category.assoc]
    have hk := congrArg (fun z ↦ z ≫
      (pB n).app
        (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I)) ≫
      (β n).hom.app (DerivedCategory.Q.obj I) ≫
      (standardPair G).functor.map
        (((CategoryTheory.evaluation ℕᵒᵖ (A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I)) (hκ I)
    simp only [Category.assoc] at hk
    rw [hk]
    erw [← Category.assoc (LB.functor.map
      (((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G).rightDerivedFunctorUnitQ I)), hn]
    simp only [Category.assoc]
    erw [he']
    have hs := congrArg (fun z ↦ z ≫ (standardPair G).unit.app
      ((((CategoryTheory.evaluation ℕᵒᵖ (A)).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj I))
      (hpB (((((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{w}).obj G)).mapHomologicalComplex
      (.up ℤ)).obj I) n)
    simp only [Category.assoc] at hs
    erw [hs]
    erw [← Category.assoc, ← DerivedCategory.Q.map_comp, hc, hfπ]
    simp only [← (standardPair G).functor.map_comp]
    rw [hpA I n]
  exact NatTrans.congr_app hγ M

end Tower
end WeilConjectures.CoefficientSectionsCoreComparison
