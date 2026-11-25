/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.TraceFormula.Sequence.SequenceScalarGeneratorInterchange
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # A component of strict quotient-system coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

private theorem sequenceDerived_flat_ext
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{t}) {D : Type a} [Category.{v} D]
    {F G : coefficientSequenceDerived l E Y ⥤ D} (α β : F ⟶ G)
    (h : ∀ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E Y) P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := coefficientSequenceTopology (ProEt.topology Y))
        (R := coefficientSequenceCommRingSheaf l E Y) (P.X n)) →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, r, hP, hf, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) K
  let := hr
  have : IsIso (DerivedCategory.Q.map r) := inferInstance
  have hflat (n : ℤ) : SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) (P.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E Y) (P.X n)).symm (hf n)
  apply (cancel_epi (F.map (DerivedCategory.Q.map r))).mp
  rw [α.naturality, β.naturality, h P hP hflat]

private theorem sequencePrimeStalkUnit (l : ℕ) (X : Scheme.{t})
    [∀ x : X, Invertible (l : X.residueField x)] (x : X) :
    IsUnit (l : X.presheaf.stalk x) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (X.residue x).hom (l : X.presheaf.stalk x) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x)).ne_zero

/-- Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
(blueprint: lem-trf-sequence-derived-scalar-unit).
Proof: Resolve the input whole quotient system by a flat-term K-flat complex. Geometric pullback
preserves these complexes. The normalization of the scalar identity comparison is ordinary scalar
multiplication, and the normalization of the scalar-pullback comparison is the ordinary generator
interchange. Compose these equations and use the ordinary scalar-unit interchange equation,
including the canonical functor unitors. Cancel the invertible geometric counit. Naturality and
the localized resolution isomorphism extend the resulting equality to every input. -/
theorem sequenceDerivedScalarUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y) :
    (integralComparisonSystemScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
      Functor.whiskerRight (integralComparisonSystemScalarUnit l E Y).hom
        (integralComparisonDerivedSequencePullback l E f) =
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemScalarUnit l E X).hom := by
  let F := integralComparisonSequencePullback l E f
  let U := integralComparisonDerivedSequencePullback l E f
  let MX := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X
  let MY := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) Y
  let eX := integralComparisonSystemScalarUnit l E X
  let eY := integralComparisonSystemScalarUnit l E Y
  let uX := NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E X) (.up ℤ)
  let uY := NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E Y) (.up ℤ)
  let k := NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarPullback l E E (AlgHom.id ℚ_[l] E) f) (.up ℤ)
  let c := integralComparisonSystemScalarPullback l E E (AlgHom.id ℚ_[l] E) f
  apply sequenceDerived_flat_ext l E Y
  intro P hP hf
  have hFP := sequencePullback_kflatgood l E f P hP hf
  have huX : eX.hom.app (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
      MX.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (uX.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    (integralComparisonSystemScalarUnit_existsUnique l E X).exists.choose_spec _ hFP
  have huY : eY.hom.app (DerivedCategory.Q.obj P) =
      MY.ε.app P ≫ DerivedCategory.Q.map (uY.hom.app P) :=
    (integralComparisonSystemScalarUnit_existsUnique l E Y).exists.choose_spec P hP
  have hc :=
    (integralComparisonSystemScalarPullback_existsUnique l E E (AlgHom.id ℚ_[l] E) f
      ).exists.choose_spec P hP
  change MX.T.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      MX.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (k.hom.app P) =
    c.hom.app (DerivedCategory.Q.obj P) ≫ U.map (MY.ε.app P) ≫
      F.mapDerivedCategoryFactors.hom.app
        ((MY.E.mapHomologicalComplex (.up ℤ)).obj P) at hc
  have hcomplex : k.hom.app P ≫
      (F.mapHomologicalComplex (.up ℤ)).map (uY.hom.app P) =
        uX.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply HomologicalComplex.Hom.ext
    funext n
    have h := congrArg (fun z ↦ z.app (P.X n))
      (sequenceScalarUnit_interchange l E f
        (sequencePrimeStalkUnit l X) (sequencePrimeStalkUnit l Y))
    simpa [F, k, uX, uY, NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
      sequenceScalarUnitLeft, sequenceScalarUnitRight] using h
  have hn : U.map (DerivedCategory.Q.map (uY.hom.app P)) ≫
      F.mapDerivedCategoryFactors.hom.app P =
    F.mapDerivedCategoryFactors.hom.app
        ((MY.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (uY.hom.app P)) :=
    F.mapDerivedCategoryFactors_hom_naturality (uY.hom.app P)
  have hc' := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map (uY.hom.app P))) hc
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp, hcomplex, ← huX] at hc'
  change c.hom.app (DerivedCategory.Q.obj P) ≫ U.map (eY.hom.app _) =
    eX.hom.app (U.obj (DerivedCategory.Q.obj P))
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
  rw [huY, U.map_comp]
  simp only [Category.assoc]
  rw [hn, ← hc']
  exact eX.hom.naturality (F.mapDerivedCategoryFactors.hom.app P)

end WeilConjectures
