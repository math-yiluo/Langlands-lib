/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Residue cohomology of a finite integral reduction

Source: Weil blueprint, `lemma-bounds-finite-reductions--2`, proof step 2;
Stacks Project, Cohomology on Sites, Tags 06YY and 0D6D.
(blueprint: lem-coef-integral-residue-tor-residue-amplitude).

The proof compares universal derived scalar extensions, then computes the finite
residue extension on its given K-flat representative. Exact restriction detects
zero cohomology, so no identification of the two coefficient categories is needed.
-/

@[expose] public section
set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace IntegralResidueHelpers
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max a b} RingCat.{max a b})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a b}]
  [HasSheafify J AddCommGrpCat.{max a b}]
  {R S : Sheaf J CommRingCat.{max a b}}
set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" R:arg => SheafOfModules.{max a b}
  ((sheafCompose J (forget₂ CommRingCat.{max a b} RingCat.{max a b})).obj R)
set_option hygiene false in
set_option quotPrecheck false in
local notation "Res" φ:arg => SheafOfModules.restrictScalars.{max a b}
  ((sheafCompose J (forget₂ CommRingCat.{max a b} RingCat.{max a b})).map φ)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison (φ : R ⟶ S) :
    letI := SheafOfModules.monoidalCategory R
    let U := Res φ
    let B := U.obj (SheafOfModules.unit _)
    ∃ e : ∀ M : Mod R, U.obj (SheafOfModules.changeOfRings φ M) ≅ B ⊗ M,
      ∀ {M N : Mod R} (f : M ⟶ N),
        U.map (SheafOfModules.changeOfRingsHom φ M f) ≫ (e N).hom =
          (e M).hom ≫ B ◁ f := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let U := Res φ
  let B := U.obj (SheafOfModules.unit _)
  obtain ⟨c, hc⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation φ
  let e (M : Mod R) : U.obj (SheafOfModules.changeOfRings φ M) ≅ B ⊗ M :=
    U.mapIso (λ_ (SheafOfModules.changeOfRings φ M)).symm ≪≫
      c (SheafOfModules.unit _) M
  refine ⟨e, ?_⟩
  intro M N f
  have h := hc (𝟙 (SheafOfModules.unit _)) f
  simp only [id_tensorHom] at h
  change U.map (_ ◁ SheafOfModules.changeOfRingsHom φ M f) ≫ _ =
    _ ≫ (U.map (𝟙 _) ⊗ₘ f) at h
  rw [U.map_id, id_tensorHom] at h
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [leftUnitor_inv_naturality]
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ U.map (λ_ (SheafOfModules.changeOfRings φ M)).inv ≫ k) h).trans
      (Category.assoc _ _ _).symm)

noncomputable local instance derived (R : Sheaf J CommRingCat.{max a b}) :
    HasDerivedCategory (Mod R) := HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def ordinaryIso (φ : R ⟶ S)
    (E F : Mod R ⥤ Mod S)
    (hE : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hmE : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hE N).symm)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hF N).symm) : E ≅ F :=
  NatIso.ofComponents (fun M ↦ eqToIso (hE M) ≪≫ (eqToIso (hF M)).symm) (by
    intro M N f
    rw [hmE, hmF]
    simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedIso
    (E F : Mod R ⥤ Mod S) [E.Additive] [F.Additive]
    (G H : DerivedCategory (Mod R) ⥤ DerivedCategory (Mod S))
    (ε : DerivedCategory.Qh ⋙ G ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : DerivedCategory.Qh ⋙ H ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [G.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    [H.IsLeftDerivedFunctor δ (HomotopyCategory.quasiIso _ (.up ℤ))]
    (t : E ≅ F) : G ≅ H :=
  Functor.leftDerivedNatIso G H ε δ (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (show E.mapHomotopyCategory (.up ℤ) ≅
      F.mapHomotopyCategory (.up ℤ) from
      { hom := t.hom.mapHomotopyCategory (.up ℤ)
        inv := t.inv.mapHomotopyCategory (.up ℤ)
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, t.hom_inv_id]
          exact NatTrans.mapHomotopyCategory_id _ _
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, t.inv_hom_id]
          exact NatTrans.mapHomotopyCategory_id _ _ })
      DerivedCategory.Qh)

private theorem restriction_exact (φ : R ⟶ S) :
    PreservesFiniteLimits (Res φ) ∧ PreservesFiniteColimits (Res φ) := by
  let U := Res φ
  let A := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let B := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf B))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_homology_zero (φ : R ⟶ S)
    (K : DerivedCategory (Mod S)) (i : ℤ) :
    letI := (restriction_exact φ).1
    letI := (restriction_exact φ).2
    IsZero ((DerivedCategory.homologyFunctor (Mod R) i).obj
      ((Res φ).mapDerivedCategory.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor (Mod S) i).obj K) := by
  let := (restriction_exact φ).1
  let := (restriction_exact φ).2
  let U := Res φ
  have : U.Faithful := by
    constructor
    intro M N f g h
    apply (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).map_injective
    exact congrArg (fun k ↦ (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).map k) h
  have h := ((U.mapDerivedCategoryHomologyFunctorIso i).app K).isZero_iff
  apply h.symm.trans
  simp only [Functor.comp_obj, IsZero.iff_id_eq_zero, ← U.map_id, U.map_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presentationModelIso (φ : R ⟶ S)
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation φ)
    (P : CochainComplex (Mod R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
    Nonempty (p.derived.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)) := by
  classical
  obtain ⟨F, hobj, hmap, hadd, _, _, G, ε, huniv, _, hcomp⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
  let := hadd
  let := huniv
  let := p.universal
  let t := ordinaryIso φ p.ordinary F p.obj_eq hobj p.map_eq hmap
  let d := derivedIso p.ordinary F p.derived G p.counit ε t
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hcomp P hP
  refine ⟨d.app (DerivedCategory.Q.obj P) ≪≫
    G.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso (Mod S)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex t.symm (.up ℤ)).app P)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryRestrictionTensorIso (φ : R ⟶ S)
    (E : Mod R ⥤ Mod S)
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm) :
    letI := SheafOfModules.monoidalCategory R
    let U := Res φ
    Nonempty (E ⋙ U ≅ tensorLeft (U.obj (SheafOfModules.unit _))) := by
  let := SheafOfModules.monoidalCategory R
  let U := Res φ
  let B := U.obj (SheafOfModules.unit _)
  obtain ⟨c, hc⟩ := tensorComparison φ
  refine ⟨NatIso.ofComponents
    (fun M ↦ U.mapIso (eqToIso (hobj M)) ≪≫ c M) ?_⟩
  intro M N f
  change U.map (E.map f) ≫ (U.map (eqToHom (hobj N)) ≫ (c N).hom) =
    (U.map (eqToHom (hobj M)) ≫ (c M).hom) ≫ B ◁ f
  have h : E.map f ≫ eqToHom (hobj N) =
      eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f := by
    rw [hmap]
    simp
  rw [← U.map_comp_assoc, h, U.map_comp, Category.assoc, hc, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedPresentationTensorIso (φ : R ⟶ S)
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation φ)
    (P : CochainComplex (Mod R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
    letI := (restriction_exact φ).1
    letI := (restriction_exact φ).2
    letI := SheafOfModules.monoidalCategory R
    let U := Res φ
    let B := U.obj (SheafOfModules.unit _)
    Nonempty (U.mapDerivedCategory.obj (p.derived.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj (((tensorLeft B).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let := (restriction_exact φ).1
  let := (restriction_exact φ).2
  let := SheafOfModules.monoidalCategory R
  let U := Res φ
  obtain ⟨e⟩ := presentationModelIso φ p P hP
  obtain ⟨t⟩ := ordinaryRestrictionTensorIso φ p.ordinary p.obj_eq p.map_eq
  refine ⟨U.mapDerivedCategory.mapIso e ≪≫
    U.mapDerivedCategoryFactors.app _ ≪≫ (DerivedCategory.Q (C := Mod R)).mapIso ?_⟩
  exact (Functor.mapHomologicalComplexCompIso (Iso.refl (p.ordinary ⋙ U)) (.up ℤ)).app P ≪≫
    (NatIso.mapHomologicalComplex t (.up ℤ)).app P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presentationIso (φ : R ⟶ S)
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation φ)
    (E : Mod R ⥤ Mod S) [E.Additive]
    (G : DerivedCategory (Mod R) ⥤ DerivedCategory (Mod S))
    (ε : DerivedCategory.Qh ⋙ G ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [G.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm) :
    Nonempty (G ≅ p.derived) := by
  let := p.universal
  exact ⟨derivedIso E p.ordinary G p.derived ε p.counit
    (ordinaryIso φ E p.ordinary hobj p.obj_eq hmap p.map_eq)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presentationTensorComplexIso (φ : R ⟶ S)
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation φ)
    (L P : CochainComplex (Mod R) ℤ) (f : P ⟶ L) (hf : QuasiIso f)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
    letI := (restriction_exact φ).1
    letI := (restriction_exact φ).2
    letI := SheafOfModules.monoidalCategory R
    let U := Res φ
    let B := U.obj (SheafOfModules.unit _)
    Nonempty (U.mapDerivedCategory.obj (p.derived.obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj B) (curriedTensor _))) := by
  let := (restriction_exact φ).1
  let := (restriction_exact φ).2
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let U := Res φ
  let B := U.obj (SheafOfModules.unit _)
  have : IsIso (DerivedCategory.Q.map f) := by
    exact Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) f hf
  obtain ⟨e⟩ := restrictedPresentationTensorIso φ p P hP
  refine ⟨U.mapDerivedCategory.mapIso (p.derived.mapIso (asIso (DerivedCategory.Q.map f)).symm)
    ≪≫ e ≪≫ (DerivedCategory.Q (C := Mod R)).mapIso ?_⟩
  exact (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight B) (.up ℤ)).app P ≪≫
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) B P).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def regularMap {T : Sheaf J CommRingCat.{max a b}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (β : S ⟶ T) (h : φ ≫ β = ψ) :
    (Res φ).obj (SheafOfModules.unit _) ⟶ (Res ψ).obj (SheafOfModules.unit _) where
  val.app U := ModuleCat.ofHom
    (X := ((Res φ).obj (SheafOfModules.unit _)).val.obj U)
    (Y := ((Res ψ).obj (SheafOfModules.unit _)).val.obj U)
    (show ((Res φ).obj (SheafOfModules.unit _)).val.obj U →ₗ[R.obj.obj U]
      ((Res ψ).obj (SheafOfModules.unit _)).val.obj U from
    { toFun := fun x ↦ (β.hom.app U).hom x
      map_add' := (β.hom.app U).hom.map_add
      map_smul' := by
        intro r m
        change (β.hom.app U).hom ((φ.hom.app U).hom r * (show S.obj.obj U from m)) =
          (ψ.hom.app U).hom r * (β.hom.app U).hom m
        rw [map_mul]
        congr 1
        have h' := congrArg (fun f ↦ (f.hom.app U).hom r) h
        exact h' })
  val.naturality := by
    intro U V f
    ext x
    exact ConcreteCategory.congr_hom (β.hom.naturality f) x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def regularIso {T : Sheaf J CommRingCat.{max a b}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (β : S ≅ T) (h : φ ≫ β.hom = ψ) :
    (Res φ).obj (SheafOfModules.unit _) ≅ (Res ψ).obj (SheafOfModules.unit _) where
  hom := regularMap φ ψ β.hom h
  inv := regularMap ψ φ β.inv (by rw [← h, Category.assoc, β.hom_inv_id,
    Category.comp_id])
  hom_inv_id := by
    ext U x
    change (β.inv.hom.app U).hom ((β.hom.hom.app U).hom x) = x
    exact congrArg (fun f : S ⟶ S ↦ (f.hom.app U).hom x) β.hom_inv_id
  inv_hom_id := by
    ext U x
    change (β.hom.hom.app U).hom ((β.inv.hom.app U).hom x) = x
    exact congrArg (fun f : T ⟶ T ↦ (f.hom.app U).hom x) β.inv_hom_id

end IntegralResidueHelpers

universe u
namespace WeilConjectures

open AlgebraicGeometry.Scheme SheafOfModules.SuccessiveDerivedQuotient

private theorem residueIdeal_map
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    (Padic.coefficientExtensionIdeal l E 1).map
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) =
    Ideal.span {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E))} := by
  simp only [Padic.coefficientExtensionIdeal, pow_one, Ideal.map_span, Set.image_singleton]

private noncomputable def quotientResidueEquiv
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    (Padic.coefficientExtensionRing l E (n + 1) ⧸ Ideal.span
      {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (Padic.coefficientExtensionUniformizer l E))}) ≃+*
      Padic.coefficientExtensionRing l E 1 :=
  (Ideal.quotEquivOfEq (residueIdeal_map l E n).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (show
      Padic.coefficientExtensionIdeal l E (n + 1) ≤
        Padic.coefficientExtensionIdeal l E 1 by
      simp only [Padic.coefficientExtensionIdeal, pow_one]
      exact Ideal.pow_le_self (Nat.succ_ne_zero n)))

private noncomputable def finiteToFirst
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l E 1 :=
  Ideal.Quotient.factor (show Padic.coefficientExtensionIdeal l E (n + 1) ≤
    Padic.coefficientExtensionIdeal l E 1 by
    simp only [Padic.coefficientExtensionIdeal, pow_one]
    exact Ideal.pow_le_self (Nat.succ_ne_zero n))

private noncomputable def finiteToFirstSheaf
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    integralCoefficientCommRingSheaf l E X n ⟶ integralCoefficientCommRingSheaf l E X 0 :=
  (CategoryTheory.constantSheaf _ CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift (finiteToFirst l E n)))

private theorem finiteToFirstSheaf_zero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) :
    finiteToFirstSheaf l E X 0 = CategoryTheory.CategoryStruct.id _ := by
  have h : RingHom.ulift (finiteToFirst l E 0) = RingHom.id _ := by
    ext x
    obtain ⟨x⟩ := x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  dsimp [finiteToFirstSheaf]
  rw [h]
  exact CategoryTheory.Functor.map_id _ _

open CategoryTheory CategoryTheory.Limits Opposite

private noncomputable def finiteTransitionSheaf
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    integralCoefficientCommRingSheaf l E X (n + 1) ⟶
      integralCoefficientCommRingSheaf l E X n :=
  (constantSheaf _ CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1))))

private theorem finiteToFirstSheaf_succ
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    finiteToFirstSheaf l E X (n + 1) =
      finiteTransitionSheaf l E X n ≫ finiteToFirstSheaf l E X n := by
  have h : RingHom.ulift (finiteToFirst l E (n + 1)) =
      (RingHom.ulift (finiteToFirst l E n)).comp
        (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1))) := by
    ext x
    obtain ⟨x⟩ := x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  dsimp [finiteToFirstSheaf, finiteTransitionSheaf]
  rw [← Functor.map_comp]
  exact congrArg ((constantSheaf _ CommRingCat.{u + 1}).map) (congrArg CommRingCat.ofHom h)

private theorem integralProjection_succ
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E X (n + 1) ≫
      finiteTransitionSheaf l E X n =
        completedIntegralCommRingProjectionUnrestricted l E X n := by
  apply (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  change limit.π (integralCoefficientSheafSystem l E X) (op (n + 1)) ≫
    integralCoefficientSheafTransition l E X n =
      limit.π (integralCoefficientSheafSystem l E X) (op n)
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    using limit.w (integralCoefficientSheafSystem l E X)
      (homOfLE (Nat.le_succ n)).op

private theorem integralProjection_first
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E X n ≫
      finiteToFirstSheaf l E X n =
        completedIntegralCommRingProjectionUnrestricted l E X 0 := by
  induction n with
  | zero => rw [finiteToFirstSheaf_zero, Category.comp_id]
  | succ n ih =>
    rw [finiteToFirstSheaf_succ, ← Category.assoc, integralProjection_succ, ih]

attribute [-instance] integralCoefficientAbSheafify
  integralCoefficientAbLocallyBijective
local instance instHasSheafifyProEt_integralReductionResidueHomology
    (X : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
local instance instWEqualsLocallyBijective_integralReductionResidueHomology
    (X : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} X

@[instance_reducible]
private noncomputable def allDerived (X : AlgebraicGeometry.Scheme.{u}) :
    ∀ R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory (SheafOfModules.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  fun _ ↦ HasDerivedCategory.standard _

attribute [local instance] allDerived

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarPresentationIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingProjectionUnrestricted l E X n)) :
    Nonempty (scalarReductionDerivedExtension l E X n ≅ p.derived) := by
  let := scalarReductionExtensionAdditive.{u, u} l E X n
  let : (scalarReductionDerivedExtension l E X n).IsLeftDerivedFunctor
      (scalarReductionCounit l E X n) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (scalarReductionDerivedExistence.{u, u} l E X n).choose_spec.choose_spec.1
  exact IntegralResidueHelpers.presentationIso _ p (scalarReductionExtension l E X n)
    (scalarReductionDerivedExtension l E X n) (scalarReductionCounit l E X n)
    (scalarReductionExistence.{u, u} l E X n).choose_spec.choose
    (scalarReductionExistence.{u, u} l E X n).choose_spec.choose_spec.choose

private noncomputable def residueSheafEquiv
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1) ⧸
        Ideal.span {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          (Padic.coefficientExtensionUniformizer l E))}))) ≅
      integralCoefficientCommRingSheaf l E X 0 :=
  (constantSheaf _ CommRingCat.{u + 1}).mapIso
    ((ULift.ringEquiv.trans ((quotientResidueEquiv l E n).trans
      ULift.ringEquiv.symm)).toCommRingCatIso)

private theorem residueSheafEquiv_comp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk (Ideal.span
        {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          (Padic.coefficientExtensionUniformizer l E))})))) ≫
      (residueSheafEquiv l E X n).hom = finiteToFirstSheaf l E X n := by
  dsimp [residueSheafEquiv, finiteToFirstSheaf]
  rw [← Functor.map_comp]
  congr 1
  ext x
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Iterated reduction to the residue ring and direct level-one reduction have
vanishing cohomology in exactly the same degrees. No constructibility, completeness
or cohomological bound is assumed.

Source: blueprint `lemma-bounds-finite-reductions--2`, proof, first sentence;
Stacks Project, Cohomology on Sites, Tags 06YS and 06YY.
Proof:
1. Ordinary scalar extensions with the prescribed objects and maps are naturally
isomorphic. Uniqueness of universal left derived functors identifies the recorded
integral reductions with the presentations in successive derived quotient normalization.
That normalization and the inverse-limit cone equations identify extension of the
finite reduction to the first quotient with the direct first reduction.
2. The quotient of A_(n+1) by the image of the uniformizer is the first quotient:
apply the quotient-of-quotient equivalence to (uniformizer)^(n+1) ≤ (uniformizer).
The equivalence respects the quotient maps. Its constant-sheaf image identifies
the two residue regular modules after restricting them to A_(n+1).
3. On the given K-flat resolution P, the universal counit computes extension to
the first quotient. Tensor cancellation with the regular target module identifies
its restriction with tensor by the restricted regular module, naturally in P.
Symmetry and the tensor-with-single-complex isomorphism identify this with the
chosen `derivedTensorRing` model. The coefficient-module isomorphism of step 2
compares that model with the displayed residue quotient tensor.
4. Restriction of scalars is exact and faithful, since it leaves underlying
abelian sheaves unchanged. The homology comparison for exact functors therefore
preserves and reflects zero cohomology. Apply it to the isomorphism of step 1
and the model comparisons of step 3, in each degree i.
(blueprint: lem-coef-integral-residue-tor-residue-amplitude). -/
theorem integralReduction_residue_homology_zero_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ)
    (L P : CochainComplex (scalarReductionTarget.{u, u} l E X n) ℤ)
    (e : DerivedCategory.Q.obj L ≅ (scalarReductionDerivedExtension.{u, u} l E X n).obj K)
    (f : P ⟶ L) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P)
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
      (scalarReductionTarget.{u, u} l E X n) i).obj
        (derivedTensorRing.{u} X (Padic.coefficientExtensionRing l E (n + 1))
          (Padic.coefficientExtensionRing l E (n + 1) ⧸ Ideal.span
            {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
              (Padic.coefficientExtensionUniformizer l E))})
          (Ideal.Quotient.mk _) L P f hf hP)) ↔
    IsZero ((DerivedCategory.homologyFunctor
      (scalarReductionTarget.{u, u} l E X 0) i).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) := by
  classical
  let J := AlgebraicGeometry.Scheme.ProEt.topology X
  let := allDerived X
  obtain ⟨p, ⟨norm⟩⟩ :=
    successive_derived_quotient_normalization.{u + 1, u, u + 1, u + 2}
      (J := J)
  let a := completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n
  let b := finiteToFirstSheaf l E X n
  let c := completedIntegralCommRingProjectionUnrestricted.{u, u} l E X 0
  obtain ⟨en⟩ := scalarPresentationIso l E X n (p a)
  obtain ⟨e0⟩ := scalarPresentationIso l E X 0 (p c)
  -- Normalize the two universal derived coefficient extensions.
  let ee := (p b).derived.mapIso (e ≪≫ en.app K) ≪≫
    (norm.derived a b).app K ≪≫
    eqToIso (congrArg (fun f ↦ (p f).derived.obj K) (integralProjection_first l E X n)) ≪≫
    (e0.app K).symm
  let := (IntegralResidueHelpers.restriction_exact b).1
  let := (IntegralResidueHelpers.restriction_exact b).2
  obtain ⟨et⟩ := IntegralResidueHelpers.presentationTensorComplexIso b (p b) L P f hf hP
  let R := integralCoefficientCommRingSheaf.{u, u} l E X n
  let : MonoidalCategory (scalarReductionTarget.{u, u} l E X n) :=
    SheafOfModules.monoidalCategory R
  let : (curriedTensor (scalarReductionTarget.{u, u} l E X n)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor R
  let : ∀ M : scalarReductionTarget.{u, u} l E X n,
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj R M
  let q := (constantSheaf J CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk (Ideal.span
      {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (Padic.coefficientExtensionUniformizer l E))}))))
  -- The quotient-of-quotient equivalence respects the finite projection.
  let β := residueSheafEquiv l E X n
  let eb := IntegralResidueHelpers.regularIso q b β (residueSheafEquiv_comp l E X n)
  let Bq : scalarReductionTarget.{u, u} l E X n := (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q)).obj
      (SheafOfModules.unit _)
  let Bb : scalarReductionTarget.{u, u} l E X n := (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b)).obj
      (SheafOfModules.unit _)
  let bt : tensorRight Bq ≅ tensorRight Bb :=
    NatIso.ofComponents (fun M ↦ MonoidalCategory.whiskerLeftIso M eb) (by
      intro M N f
      simp only [MonoidalCategory.whiskerLeftIso_hom]
      exact (MonoidalCategory.whisker_exchange f eb.hom).symm)
  let ec := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Bq P) ≪≫
    (NatIso.mapHomologicalComplex bt (.up ℤ)).app P ≪≫
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Bb P).symm
  let eTensor := (DerivedCategory.Q (C := scalarReductionTarget.{u, u} l E X n)).mapIso ec
  -- Compare the given tensor model, then detect zero homology by restriction.
  let U := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b)
  let eTotal := eTensor ≪≫ et.symm ≪≫ U.mapDerivedCategory.mapIso ee
  exact ((DerivedCategory.homologyFunctor _ i).mapIso eTotal).isZero_iff.trans
    (IntegralResidueHelpers.restriction_homology_zero b
      ((scalarReductionDerivedExtension l E X 0).obj K) i)

end WeilConjectures
