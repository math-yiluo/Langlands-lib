/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteChainTensor
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
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # K-flatness reflected by finite coefficient inverse image

Source: blueprint site comparison paragraph; Stacks 06YN and 07A4.
(blueprint: lem-sf-finite-coefficient-kflat-reflection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe v w u
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
private theorem kflat_of_image (P : CochainComplex C ℤ)
    (hP : ∀ V : CochainComplex D ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V ((F.mapHomologicalComplex (.up ℤ)).obj P) S).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro V hV
  obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
  have hp' : (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic := by
    apply (acyclic_map_iff F _).1
    obtain ⟨e⟩ := hcomp V P
    intro i
    exact (hP _ ((acyclic_map_iff F V).2 hV) i).of_iso e.symm
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor V P (curriedTensor C))).2 hp'
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

end

open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification

private theorem finiteIntrinsic_kflat_of_image
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (P : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (Scheme.ProEt.topology X) (Scheme.proEtaleConstantRing X A)
      (((ProEtale.finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex
        (.up ℤ)).obj P)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let R := Scheme.proEtaleConstantRing X A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let F := ProEtale.finiteCoefficientIntrinsicRealization X A
  let : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact X A).1
  let : (ProEtale.finiteCoefficientIntrinsicComparison X A).Faithful :=
    inferInstanceAs ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X) ⋙ F).Faithful
  exact kflat_of_image (ProEtale.finiteCoefficientIntrinsicComparison X A) (curriedTensor _)
    (fun V W ↦ ⟨ProEtale.finiteCoefficientIntrinsicChainTensor X A V W⟩) P hP

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The finite-level site inverse image reflects K-flatness of etale complexes.
Source: blueprint site comparison paragraph; Stacks 06YN and 07A4
(blueprint: lem-sf-finite-coefficient-kflat-reflection).

Proof: ordinary etale-to-pro-etale inverse image is exact and faithful, and intrinsic
realization is an exact equivalence. Their composite therefore reflects acyclicity
by reflecting zero homology. For each acyclic etale test complex V, apply intrinsic
K-flatness to its acyclic inverse image. The already specified chain tensor
comparison identifies this with the image of the etale tensor. Reflect acyclicity
and use symmetry to obtain both tensor tests in categorical K-flatness. -/
theorem finiteHomNuKFlatReflection (n : ℕ)
    (P : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
      ((finiteHomNuComplex l E X n).obj P)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exact finiteIntrinsic_kflat_of_image X (Padic.coefficientExtensionRing l E (n + 1)) P hP

end WeilConjectures
