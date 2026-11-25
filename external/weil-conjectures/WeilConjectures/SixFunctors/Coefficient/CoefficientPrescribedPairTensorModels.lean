/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarHomTensor.PrescribedScalarTensorComparison
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
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

/-! # Scalar tensor comparison for independently prescribed tensor models

Source: Stacks 07A4 and 06YY.
(blueprint: lem-coef-prescribed-pair-tensor-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section PrescribedTensor
universe c v r w
open SheafOfModules CategoryTheory.MonoidalCategory CategoryTheory.Functor
open CategoryTheory.ScalarHomTensor
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.scalarPairComplexComparison CoefficientTensorModels.iso

/-- The scalar tensor descent proof works for two prescribed tensor models,
without requiring them to belong to the same simultaneous choice family.
Source: Stacks 07A4, using the existing scalar tensor descent argument.
Proof: form the ordinary normalized scalar tensor comparison and totalize it.
Scalar extension preserves K-flat complexes. Descend its natural chain comparison
through the fully faithful restriction to K-flat pairs and cancel the representative
isomorphisms. The two tensor models can be prescribed independently throughout.
(blueprint: lem-coef-prescribed-pair-tensor-models). -/
theorem coefficientPrescribedPairTensorComparison
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{max c v r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
    (s : ScalarDerivedPair a)
    (SR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (SS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (TR : CoefficientTensorModels.{r, c, v, w} J R SR)
    (TS : CoefficientTensorModels.{r, c, v, w} J S SS) :
    Nonempty (PairTensorComparison.{c, v, r, w} a s SR SS TR TS) := by
  classical
  let A := scalarModules J R
  let B := scalarModules J S
  let := monoidalCategory R
  let := monoidalCategory S
  let := symmetricCategory R
  let := symmetricCategory S
  let := s.extension_additive
  have (X : A) : (tensorLeft X).Additive := tensorLeft_additive_independent R X
  have (X : A) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  have (X : B) : (tensorLeft X).Additive := tensorLeft_additive_independent S X
  have (X : B) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  let : MonoidalPreadditive A :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let : MonoidalPreadditive B :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  obtain ⟨e, he, hgen⟩ :=
    SheafOfModules.ScalarHomOrdinary.scalarOrdinaryTensorComparison_exists.{c, v, max c v r, w} a s
  let F := scalarComplex s.extension s.extension_additive
  let tR := coefficientTotalTensor.{r, c, v} J R
  let tS := coefficientTotalTensor.{r, c, v} J S
  have hiso (P Q : CochainComplex A ℤ) :
      IsIso (tensorPullbackTotal s.extension e he P Q) :=
    tensorPullbackTotal_isIso s.extension e he (scalarRestriction a) s.ordinaryAdjunction P Q
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (tensorPullbackTotal s.extension e he X.1 X.2)
      (hiso X.1 X.2)) (by
        intro X Y f
        dsimp only [F, tR, tS, scalarComplex, Functor.comp_map, Functor.prod_map]
        simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
        exact tensorPullbackTotal_naturality s.extension e he f.1 f.2)
  let b := b0.symm
  have hg (P Q : CochainComplex A ℤ) (p q k : ℤ) (h : p + q = k)
      (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
      ((b.app (P, Q)).hom.f k).val.app V
          (pairUnit.{c, v, r, w} a s _ V
            (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
        coefficientTensorGenerator.{r, c, v} J S (F.obj P) (F.obj Q) p q k h V
          (pairUnit.{c, v, r, w} a s _ V x) (pairUnit.{c, v, r, w} a s _ V y) := by
    let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h
    let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q) (curriedTensor B) p q k h
    let z := (HomologicalComplex.eval B (.up ℤ) k).mapIso (b0.app (P, Q))
    have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ s.extension.map ι := by
      change ι' ≫ tensorPullbackTotalComponent s.extension e P Q k = _
      exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
    have hi : s.extension.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
      apply (cancel_mono z.hom).mp
      erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
        Iso.hom_inv_id_assoc]
    have hu := congrArg (fun f ↦ f.val.app V
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))
      (s.ordinaryAdjunction.unit.naturality ι)
    have hh := congrArg (fun f ↦ f.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) hi
    change z.inv.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) = _
    change ((s.ordinaryAdjunction.unit.app _).val.app V)
      (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) =
      (s.extension.map ι).val.app V (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) at hu
    erw [hu]
    exact hh.trans (congrArg (ι'.val.app V) (hgen _ _ V x y))
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
  have hF : ∀ P, PR P → PS (F.obj P) :=
    fun P hp ↦ scalarExtension_preservesKFlat a s P hp
  let eps : DerivedCategory.Q ⋙ s.derived ⟶ F ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv s.derived ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) s.counit ≫
      Functor.whiskerRight (s.extension.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso B).hom
  have heps (P : CochainComplex A ℤ) : eps.app P =
      scalarPairComplexComparison s.extension s.extension_additive s.derived s.counit P := by
    change s.derived.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
      s.counit.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ (DerivedCategory.quotientCompQhIso B).hom.app
        (F.obj P) = _
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    unfold scalarPairComplexComparison
    rfl
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  have hff := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  obtain ⟨ff⟩ := hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  obtain ⟨alpha, ha, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F s.derived eps PR PS hF ff' tR tS
    SR.tensor SS.tensor TR.comparison TS.comparison b
    (fun P hp ↦ by rw [heps]; exact s.computes P hp)
    (fun P Q hp hq ↦ by
      rw [heps]
      exact s.computes _ (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hp hq))
  refine ⟨{ preservesKFlat := hF
            complexIso := fun P Q ↦ b.app (P, Q)
            generators := hg
            iso := alpha
            normalization := ?_ }⟩
  unfold CategoryTheory.ScalarHomTensor.pairTensorNormalization
  intro P Q hp hq
  have hh := ha P Q hp hq
  rw [heps, heps, heps] at hh
  simpa only [CoefficientTensorModels.iso, Iso.app_hom] using hh

end PrescribedTensor

end WeilConjectures
