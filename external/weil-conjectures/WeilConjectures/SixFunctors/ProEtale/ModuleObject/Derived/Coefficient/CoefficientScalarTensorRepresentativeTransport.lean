/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeEquation
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
import WeilConjectures.CategoryTheory.Monoidal.UncurriedComparison
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.Algebra.Homology.Localization

/-! # Transport of scalar tensor representatives

The second strict substep transports the internal-image equation across the exact
section equivalence. It is independent of the bidegree generator calculation.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ModuleRingedComparison.tensor ModuleRingedComparison.qTensor
  coefficientScalarTensorRepresentativeEquation coefficientSectionScalarTotal
  SheafOfModules.scalarPairComplexComparison

universe uc vc w

private theorem resolving_of_iso
    {C : Type uc} [Category.{vc} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {A : Sheaf J CommRingCat.{w}}
    {P Q : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) ℤ}
    (e : P ≅ Q) (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := A) Q)
    (hfQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := A) (Q.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := A) P ∧
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := A) (P.X n)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  -- Supply the discrete colimits directly: unguided instance search times out here.
  have (I : Type w) : HasColimitsOfShape (Discrete I) (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) :=
    have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  constructor
  · intro V hV n
    exact (hQ V hV n).of_iso (((curriedTensor _).map₂CochainComplex.obj V).mapIso e.symm)
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (Q.X n) ≪≫
        (curriedTensor _).flip.mapIso ((HomologicalComplex.eval _ _ n).mapIso e.symm) ≪≫
        (SheafOfModules.siteSheafTensorRightIso A (P.X n)).symm) (hfQ n)

private theorem map_id_comp
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X : A} {Y : B} (f : F.obj X ⟶ Y) : F.map (𝟙 X) ≫ f = f := by
  rw [F.map_id, Category.id_comp]

private theorem app_eq_of_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (α β : F ⟶ G) {X Y : A} (e : X ≅ Y) (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  apply (cancel_epi (F.mapIso e).hom).mp
  change F.map e.hom ≫ α.app Y = F.map e.hom ≫ β.app Y
  rw [α.naturality, β.naturality, h]

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

-- Retain the original exactness hypothesis, although transport only uses the supplied data.
set_option linter.unusedSectionVars false in
-- Elaborate the whiskered naturality diagram without unfolding the derived tensor data.
/-- Transport an equation known on all internal complexes to arbitrary section
complexes satisfying the same flat-term and K-flat hypotheses. The proof uses the
counit isomorphisms of the termwise section equivalence and naturality of all maps.

Source: Stacks Project, Cohomology on Sites, Tag 07A4, transport along the section
equivalence. This is strictly the transport step and leaves the internal equation
as its hypothesis.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-transport). -/
theorem coefficientScalarTensorRepresentative_transport
    (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (hinternal :
      ∀ (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z)
          (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
            (.up ℤ)).obj P) →
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z)
          (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
            (.up ℤ)).obj Q) →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z)
          ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z)
          ((ModuleRingedComparison.equivalence R Z).functor.obj (Q.X n))) →
        coefficientScalarTensorRepresentativeEquation a Z d
          (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
            (.up ℤ)).obj P)
          (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
            (.up ℤ)).obj Q)) :
    ∀ (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) P →
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) Q →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
        (P.X n)) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
        (Q.X n)) →
      coefficientScalarTensorRepresentativeEquation a Z d P Q := by
  classical
  intro P Q hP hQ hfP hfQ
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (ModuleRingedComparison.ring R Z)
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (ModuleRingedComparison.ring S Z)
  let := SheafOfModules.monoidalCategory (ModuleRingedComparison.ring R Z)
  let := SheafOfModules.monoidalCategory (ModuleRingedComparison.ring S Z)
  let ec := (ModuleRingedComparison.equivalence R Z).mapHomologicalComplex (.up ℤ)
  let P₀ := ec.inverse.obj P
  let Q₀ := ec.inverse.obj Q
  let σ : ec.functor.obj P₀ ≅ P := ec.counitIso.app P
  let τ : ec.functor.obj Q₀ ≅ Q := ec.counitIso.app Q
  have hP₀ := resolving_of_iso.{u + 1, u, u + 1}
    (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
    (A := ModuleRingedComparison.ring R Z) σ hP hfP
  have hQ₀ := resolving_of_iso.{u + 1, u, u + 1}
    (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
    (A := ModuleRingedComparison.ring R Z) τ hQ hfQ
  have h := hinternal P₀ Q₀ hP₀.1 hQ₀.1 hP₀.2 hQ₀.2
  let := d.b.extension_additive
  let := d.m
  let : PreservesColimitsOfSize.{0, 0} d.b.extension :=
    d.b.ordinaryAdjunction.leftAdjoint_preservesColimits
  let E := d.b.extension.mapHomologicalComplex (.up ℤ)
  let F := d.b.derived
  let QR := DerivedCategory.Q (C := ModuleRingedComparison.modules R Z)
  let QS := DerivedCategory.Q (C := ModuleRingedComparison.modules S Z)
  let TR := ModuleRingedComparison.totalTensor R Z
  let TS := ModuleRingedComparison.totalTensor S Z
  let B := ModuleRingedComparison.tensor R Z
  let C := ModuleRingedComparison.tensor S Z
  let ε : QR ⋙ F ⟶ E ⋙ QS :=
    { app := fun K ↦ d.b.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
      naturality := fun _ _ f ↦ d.b.counit.naturality
        ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
  have hε (K : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
      SheafOfModules.scalarPairComplexComparison d.b.extension d.b.extension_additive
        F d.b.counit K = ε.app K := by
    unfold SheafOfModules.scalarPairComplexComparison
    have h₁ (K : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
        (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
    have h₂ (K : CochainComplex (ModuleRingedComparison.modules S Z) ℤ) :
        (DerivedCategory.quotientCompQhIso _).hom.app K = 𝟙 _ := rfl
    erw [h₁, h₂, F.map_id, Category.id_comp, Category.comp_id]
  -- Reuse the total-complex comparison's naturality before specializing to sheaves.
  let δ : TR ⋙ E ⟶ E.prod E ⋙ TS :=
    HomologicalComplex.mapBifunctorComparisonUncurried
      (Functor.OplaxMonoidal.δNatTrans d.b.extension) (.up ℤ)
  have hδ (K L : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
      coefficientSectionScalarTotal a Z d.b d.m K L = δ.app (K, L) := by
    unfold coefficientSectionScalarTotal
    simp only [eqToHom_refl, Category.comp_id]
    exact map_id_comp (d.b.extension.mapHomologicalComplex (.up ℤ))
      (HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans d.b.extension) (.up ℤ) K L)
  let L : QR.prod QR ⋙ B ⋙ F ⟶ E.prod E ⋙ TS ⋙ QS :=
    Functor.whiskerRight (ModuleRingedComparison.qTensor R Z) F ≫
      Functor.whiskerLeft TR ε ≫ Functor.whiskerRight δ QS
  let U : QR.prod QR ⋙ B ⋙ F ⟶ E.prod E ⋙ TS ⋙ QS :=
    Functor.whiskerLeft (QR.prod QR) d.t.hom ≫
      Functor.whiskerRight (NatTrans.prod ε ε) C ≫
      Functor.whiskerLeft (E.prod E) (ModuleRingedComparison.qTensor S Z)
  have hef : ec.functor =
      (ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex (.up ℤ) := rfl
  have h₀ : L.app (ec.functor.obj P₀, ec.functor.obj Q₀) =
      U.app (ec.functor.obj P₀, ec.functor.obj Q₀) := by
    rw [hef]
    simpa only [coefficientScalarTensorRepresentativeEquation, L, U,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.prod, ← hε, ← hδ, TR, TS, B, C, E, QR, QS, F,
      Functor.comp_obj, Functor.prod_obj] using h
  have hall : L.app (P, Q) = U.app (P, Q) :=
    app_eq_of_iso L U (Iso.prod σ τ) h₀
  simpa only [coefficientScalarTensorRepresentativeEquation, L, U,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.prod, ← hε, ← hδ, TR, TS, B, C, E, QR, QS, F,
    Functor.comp_obj, Functor.prod_obj] using hall

end AlgebraicGeometry.ProEtale.CondensedRing
