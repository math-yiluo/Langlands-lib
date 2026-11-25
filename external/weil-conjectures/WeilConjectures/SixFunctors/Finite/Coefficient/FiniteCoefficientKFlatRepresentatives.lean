/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Resolving representatives for finite coefficient inverse image

Source: Stacks Project, Cohomology on Sites, Tags 06YN and 07A4.
(blueprint: lem-sf-finite-coefficient-kflat-representatives).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe v w u s
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

private theorem acyclic_map_iff
    {C D : Type*} [Category.{v} C] [Category.{w} D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic ↔ K.Acyclic := by
  constructor
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (h i)
    have hz' : IsZero (F.obj (K.homology i)) :=
      hz.of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K).symm
    apply (IsZero.iff_id_eq_zero _).2
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz'
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact (F.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1
      (h i))).of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K)

section
variable {C D : Type*} [Category.{v} C] [Category.{w} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
  [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Faithful]
  (S : D ⥤ D ⥤ D) [S.PreservesZeroMorphisms]
  [∀ M, (S.obj M).PreservesZeroMorphisms]
  [HasColimitsOfSize.{0, 0} D]
  (hcomp : ∀ V W : CochainComplex C ℤ,
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor V W (curriedTensor C)) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj V)
          ((F.mapHomologicalComplex (.up ℤ)).obj W) S))

include hcomp in
private theorem image_kflat [F.IsEquivalence] (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    ∀ V : CochainComplex D ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V ((F.mapHomologicalComplex (.up ℤ)).obj P) S).Acyclic := by
  intro V hV
  let E := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  let V' := E.inverse.obj V
  let eV : (F.mapHomologicalComplex (.up ℤ)).obj V' ≅ V := E.counitIso.app V
  have hV' : V'.Acyclic := by
    apply (acyclic_map_iff F _).1
    intro i
    exact (hV i).of_iso eV.symm
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
  have ht := (hP ((HomotopyCategory.quotient C (.up ℤ)).obj V')
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hV')).2
  have ht' : (CochainComplex.mapBifunctor V' P (curriedTensor C)).Acyclic := by
    apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    exact (HomotopyCategory.subcategoryAcyclic C).prop_of_iso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) V' P) ht
  obtain ⟨e⟩ := hcomp V' P
  let d := ((S.map₂CochainComplex).mapIso eV).app
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
  intro i
  exact (((acyclic_map_iff F _).2 ht') i).of_iso (e ≪≫ d)
end

open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification

namespace WeilConjectures
private theorem image_resolution
    {C B D : Type*} [Category.{u} C] [Category.{v} B] [Category.{w} D]
    [Abelian C] [Abelian B] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} B]
    [HasExactColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ B]
    (N : C ⥤ B) [N.Additive] [N.PreservesFlat] [N.IsLeftAdjoint]
    (F : B ⥤ D) [F.Additive] [F.IsEquivalence]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasColimitsOfSize.{0, 0} D]
    (S : D ⥤ D ⥤ D) [S.PreservesZeroMorphisms]
    [∀ M, (S.obj M).PreservesZeroMorphisms]
    (hcomp : ∀ V W : CochainComplex B ℤ,
      Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor V W (curriedTensor B)) ≅
          CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj V)
            ((F.mapHomologicalComplex (.up ℤ)).obj W) S))
    (G : CochainComplex C ℤ) :
    ∃ (P : CochainComplex C ℤ) (f : P ⟶ G), QuasiIso f ∧
      ∀ V : CochainComplex D ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V
          (((N ⋙ F).mapHomologicalComplex (.up ℤ)).obj P) S).Acyclic := by
  let Λ := (Classical.arbitrary
    (Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  let P := Λ.resolutionFunctor.obj G
  have hP := N.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
    ObjectProperty.flat.essImage_ι_le G
  have hF := image_kflat F S hcomp ((N.mapHomologicalComplex (.up ℤ)).obj P) hP
  refine ⟨P, Λ.resolutionNatTrans.app G, inferInstance, ?_⟩
  let e := (Functor.mapHomologicalComplexCompIso (Iso.refl (N ⋙ F)) (.up ℤ)).app P
  intro V hV i
  exact (hF V hV i).of_iso ((S.map₂CochainComplex.obj V).mapIso e)

private theorem comparison_has_kflat_resolutions
    (A : Type u) [CommRing A] [Finite A] (T : AlgebraicGeometry.Scheme.{u})
    (G : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    ∃ (P : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) (f : P ⟶ G), QuasiIso f ∧
      @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (AlgebraicGeometry.Scheme.ProEt.topology T)
        (AlgebraicGeometry.Scheme.proEtaleConstantRing T A)
        (((AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicComparison
          T A).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  let : EssentiallySmall.{u + 1, u, u + 1} T.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let C := Sheaf T.smallEtaleTopology B
  let N := AlgebraicGeometry.ProEtale.comparisonUpperStar B T
  let F := AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T A
  let : F.IsEquivalence :=
    (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  let R := AlgebraicGeometry.Scheme.proEtaleConstantRing T A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact image_resolution N F (curriedTensor _)
    (AlgebraicGeometry.ProEtale.intrinsic_realization_tensor_complex_iso A T) G

/-- Restriction to complexes with intrinsically K-flat inverse image is fully faithful
on functor categories, also for pairs of representatives.
Source: Stacks Project, Cohomology on Sites, Tags 06YN and 07A4
(blueprint: lem-sf-finite-coefficient-kflat-representatives).
Proof: choose the functorial flat resolution on the etale category. Ordinary inverse
image preserves flatness, and the intrinsic realization is an exact tensor equivalence.
Thus every complex admits a quasi-isomorphism from a complex in the specified class.
The same holds in the homotopy category. Resolve the vertices of roofs and common
refinements to obtain localization on this full subcategory. Localization is fully
faithful on functor categories, and taking products gives the assertion for pairs. -/
theorem finiteCoefficientKFlatRepresentativesFullyFaithful
    (A : Type u) [CommRing A] [Finite A] (T : AlgebraicGeometry.Scheme.{u})
    [hD : HasDerivedCategory.{s} (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))]
    (D : Type w) [Category.{v} D] :
    let C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    let P : ObjectProperty (CochainComplex C ℤ) := fun P ↦
      @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (AlgebraicGeometry.Scheme.ProEt.topology T)
        (AlgebraicGeometry.Scheme.proEtaleConstantRing T A)
        (((AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicComparison
          T A).mapHomologicalComplex
          (.up ℤ)).obj P)
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory C × DerivedCategory C) D).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  dsimp only
  let C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let P : ObjectProperty (CochainComplex C ℤ) := fun P ↦
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (AlgebraicGeometry.Scheme.ProEt.topology T)
      (AlgebraicGeometry.Scheme.proEtaleConstantRing T A)
      (((AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicComparison
          T A).mapHomologicalComplex
          (.up ℤ)).obj P)
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun X ↦ P X.as
  have hres : ∀ X : HomotopyCategory C (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X),
        HomotopyCategory.quasiIso C (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hq, hP⟩ := comparison_has_kflat_resolutions A T X.as
    exact ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj P, hP⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq⟩
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering D
    (HomotopyCategory.quotient C (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso C (.up ℤ)) DerivedCategory.Qh P H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ D).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C))))⟩

end WeilConjectures
