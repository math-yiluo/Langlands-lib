/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Computation of the native whole-system reduction counit on K-flat complexes

Source: Stacks 06YY, 0940--0941 and derived adjoint functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem ordinaryReduction_preserves (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (f : P ⟶ Q)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hf : QuasiIso f) :
    QuasiIso (((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ)).map f) := by
  let A := completedIntegralCommRingSheafUnrestricted l E W
  let B := coefficientSequenceCommRingSystem l E W
  let α : (Functor.const ℕᵒᵖ).obj A ⟶ B :=
    NatTrans.ofOpSequence
      (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n) (by
        intro n
        dsimp only [B, coefficientSequenceCommRingSystem]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        change completedIntegralCommRingProjectionUnrestricted l E W n =
          completedIntegralCommRingProjectionUnrestricted l E W (n + 1) ≫
            coefficientSequenceCommRingTransition l E W n
        apply (sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
        rw [Functor.map_comp]
        have hw := limit.w (integralCoefficientSheafSystem l E W)
          (homOfLE (Nat.le_succ n)).op
        simp only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] at hw
        exact hw.symm)
  let e := SheafOfModules.strictSystemSequenceEquivalence B
  let V := e.inverse ⋙ SheafOfModules.RestrictedTowerResolution.restrictionFunctor A B α
  have hEval (n : ℕ) : SheafOfModules.systemSequenceEvaluation B n =
      coefficientSequenceEvaluation l E W n := by
    have hφ : SheafOfModules.systemSequenceVerticalRingMap B n =
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      dsimp only [SheafOfModules.systemSequenceVerticalRingMap]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    exact congrArg (fun φ ↦ SheafOfModules.pushforward.{u + 1}
      (F := Prod.sectR n W.ProEt) φ) hφ
  have hV : V = coefficientSequenceRestriction l E W := by
    apply (coefficientSequenceRestriction_exists l E W).unique
    · refine ⟨?_, ?_, ?_⟩
      · intro M n
        change (SheafOfModules.RestrictedTowerResolution.restriction A B α n).obj
          ((SheafOfModules.systemSequenceEvaluation B n).obj M) = _
        rw [hEval]
        rfl
      · intro M m n h U
        exact HEq.rfl
      · intro M N f n U
        exact HEq.rfl
    · exact (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  let G := SheafOfModules.SequenceProjection.extension A B α ⋙ e.functor
  let F := e.inverse ⋙ SheafOfModules.SequenceProjection.directImage A B α
  have hF : F = ordinaryLimit l E W := by
    change V ⋙ lim = coefficientSequenceRestriction l E W ⋙ lim
    rw [hV]
  let a : G ⊣ ordinaryLimit l E W :=
    ((SheafOfModules.SequenceProjection.ordinaryAdjunction A B α).comp e.toAdjunction)
      |>.ofNatIsoRight (eqToIso hF)
  let d := a.leftAdjointUniq (ordinaryReductionAdj l E W)
  have hg := SheafOfModules.SequenceProjection.extension_preserves A B α f hP hQ hf
  have hG : QuasiIso (((G.mapHomologicalComplex (.up ℤ)).map f)) := by
    have : QuasiIso
        (((SheafOfModules.SequenceProjection.extension A B α).mapHomologicalComplex
          (.up ℤ)).map f) := hg
    exact inferInstanceAs (QuasiIso ((e.functor.mapHomologicalComplex (.up ℤ)).map
      (((SheafOfModules.SequenceProjection.extension A B α).mapHomologicalComplex
        (.up ℤ)).map f)))
  have hzero : (ordinaryReduction l E W).PreservesZeroMorphisms := by
    have hadd := ordinaryReduction_additive l E W
    infer_instance
  let dc := NatIso.mapHomologicalComplex d (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (dc.app P) (dc.app Q) (dc.hom.naturality f).symm)).1 hG

/-- The native reduction mate computes ordinary whole-system quotient extension on K-flats.
Source: Stacks, sites-cohomology.tex, Lemma derived-base-change (06YY),
section-derived-limits (0940), Lemma derived-limit-is-ok (0941), and derived.tex,
Lemma derived-adjoint-functors.
Proof: on the ringed sequence site ordinary quotient extension is the composite of
constant diagram formation and extension to the quotient ring sheaf. A K-flat complex
has a K-flat constant diagram: tensor and acyclicity are detected levelwise.
Extension of scalars computes its left derived functor on this diagram. Its right
adjoint is the ordinary inverse limit after coefficient restriction. Deriving this
adjunction identifies the derived left adjoint with S.reduction, since both are left
adjoint to the specified coefficientSequenceLimit. The isomorphism of right adjoints
is reductionRightComparison, normalized by its derived unit on every complex.
Under adjoint transposition the computing left comparison is therefore precisely
systemReductionCounit, defined as the mate of that same right-derived unit.
Its component on the given K-flat complex is consequently invertible. This argument
uses the full sequence site and all its transitions; it also applies to the zero
complex and to the empty site, without a derived-completeness hypothesis.
(blueprint: lem-pur-native-reduction-counit-kflat). -/
theorem nativeReductionCounit_kFlat (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    IsIso ((systemReductionCounit l E W S).app
      ((HomotopyCategory.quotient _ _).obj P)) := by
  let A := scalarReductionSource l E W
  let B := coefficientSequenceModules.{u, u} l E W
  let q := HomotopyCategory.quotient A (.up ℤ)
  let qB := HomotopyCategory.quotient B (.up ℤ)
  let QA := DerivedCategory.Qh (C := A)
  let QB := DerivedCategory.Qh (C := B)
  let G := ordinaryReduction l E W
  let F := ordinaryLimit l E W
  let a := (ordinaryReductionAdj l E W).mapHomotopyCategory (.up ℤ)
  let b := S.adjunction.ofNatIsoRight (reductionRightComparison l E W).symm
  let β := TwoSquare.mk _ _ _ _ F.rightDerivedFunctorUnit
  let c := ((mateEquiv a b).symm β)
  let K : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ P : CochainComplex A ℤ, P.IsKFlatIndependentCoefficients ∧ q.obj P = X
  have hres (X : HomotopyCategory A (.up ℤ)) :
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        K X' ∧ IsIso (QA.map s) := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E W) P
    refine ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩, ?_⟩
    exact Localization.inverts QA (HomotopyCategory.quasiIso A (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
  have hinv {X Y : HomotopyCategory A (.up ℤ)}
      (hX : K X) (hY : K Y) (s : X ⟶ Y) (hs : IsIso (QA.map s)) :
      IsIso (QB.map ((G.mapHomotopyCategory (.up ℤ)).map s)) := by
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨Q, hQ, rfl⟩ := hY
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1
      ((DerivedCategory.isIso_Qh_map_iff _).1 hs)
    have hg := ordinaryReduction_preserves l E W f hP hQ hf
    rw [G.mapHomotopyCategory_map]
    exact Localization.inverts QB (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  change IsIso (c.app (q.obj P))
  apply isIso_of_coyoneda_map_bijective
  intro T
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective T
  have : I.IsKInjective := hI
  let eT : T ≅ QB.obj (qB.obj I) :=
    e ≪≫ (DerivedCategory.quotientCompQhIso B).symm.app I
  have hloc := CategoryTheory.hom_localization_bijective a
    (HomotopyCategory.quasiIso A (.up ℤ)) QA QB K hres
    (fun hX hY s hs ↦ hinv hX hY s hs) (q.obj P) ⟨P, hP, rfl⟩ (qB.obj I)
    (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X I)
  have hη : IsIso (β.app (qB.obj I)) := inferInstance
  have hpost : Function.Bijective (fun f : QA.obj (q.obj P) ⟶
      QA.obj ((F.mapHomotopyCategory (.up ℤ)).obj (qB.obj I)) ↦
        f ≫ β.app (qB.obj I)) := by
    constructor
    · intro f g h
      exact (cancel_mono (β.app (qB.obj I))).mp h
    · intro f
      refine ⟨f ≫ inv (β.app (qB.obj I)), ?_⟩
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hm (f : (G.mapHomotopyCategory (.up ℤ)).obj (q.obj P) ⟶ qB.obj I) :
      b.homEquiv _ _ (c.app (q.obj P) ≫ QB.map f) =
        QA.map (a.homEquiv _ _ f) ≫ β.app (qB.obj I) := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    have hu : QA.map (a.unit.app (q.obj P)) ≫
        β.app ((G.mapHomotopyCategory (.up ℤ)).obj (q.obj P)) =
        b.unit.app (QA.obj (q.obj P)) ≫ F.rightDerivedFunctor.map (c.app (q.obj P)) := by
      simpa only [Functor.id_obj] using unit_mateEquiv_symm a b β (q.obj P)
    rw [← Category.assoc, ← hu, Category.assoc]
    have hn : QA.map ((F.mapHomotopyCategory (.up ℤ)).map f) ≫
        β.app (qB.obj I) =
        β.app ((G.mapHomotopyCategory (.up ℤ)).obj (q.obj P)) ≫
          F.rightDerivedFunctor.map (QB.map f) := β.naturality f
    rw [hn]
  have hcomp : Function.Bijective
      (fun f : (G.mapHomotopyCategory (.up ℤ)).obj (q.obj P) ⟶ qB.obj I ↦
        b.homEquiv _ _ (c.app (q.obj P) ≫ QB.map f)) := by
    simp only [hm]
    exact hpost.comp (hloc.comp (a.homEquiv _ _).bijective)
  have hpre : Function.Bijective
      (fun f : QB.obj ((G.mapHomotopyCategory (.up ℤ)).obj (q.obj P)) ⟶
        QB.obj (qB.obj I) ↦ c.app (q.obj P) ≫ f) := by
    apply (Function.Bijective.of_comp_iff _
      (CochainComplex.IsKInjective.Qh_map_bijective _ I)).1
    exact Function.Bijective.of_comp_left hcomp (b.homEquiv _ _).injective
  constructor
  · intro f g h
    apply (cancel_mono eT.hom).1
    apply hpre.injective
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ eT.hom) h
  · intro f
    obtain ⟨g, hg⟩ := hpre.surjective (f ≫ eT.hom)
    refine ⟨g ≫ eT.inv, ?_⟩
    change c.app (q.obj P) ≫ (g ≫ eT.inv) = f
    change c.app (q.obj P) ≫ g = f ≫ eT.hom at hg
    rw [← Category.assoc, hg, Category.assoc, eT.hom_inv_id, Category.comp_id]

end WeilConjectures.PurStrictScalar
