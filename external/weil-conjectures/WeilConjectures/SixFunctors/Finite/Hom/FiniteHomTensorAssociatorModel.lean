/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorChainSquare
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorChainSquare

/-! # The prescribed intrinsic scalar associator on chain representatives

Source: blueprint lemma-change-coefficients-internal-hom--1, successive quotient paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a₁ b₁ v₁ v₂ w₁ w₂
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

open CategoryTheory.Functor CategoryTheory.Limits Opposite

attribute [local irreducible] constantSheaf
attribute [local irreducible] CoefficientClosedStructure.tensor
  SheafOfModules.monoidalCategory coefficientTotalTensor coefficientTensorGenerator
  coefficientFiniteQuotientExistence coefficientFiniteQuotientDerivedExistence
  coefficientFiniteQuotientExtension coefficientFiniteQuotientDerived
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.standard SheafOfModules.instPreadditive

attribute [local irreducible] finiteHomTensorRepresentativeComparison
  coefficientLocalizedCounitModel
  finiteHomTensorComplexAssociator scalarUnitSection

/-- The native smallness witness at the coefficient-site universe. -/
theorem finiteHomTensorSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

attribute [local instance 2000] finiteHomTensorSiteSmall

section Representatives
attribute [local instance 2000] HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private abbrev calculus := (coefficientDerivedSystemEvaluationCalculus.{u, u} l E X).choose

/-- Actual termwise application of the prescribed quotient extension. -/
abbrev finiteHomTensorExtensionComplex {n m : ℕ} (h : m ≤ n) :=
  (coefficientFiniteQuotientExtension.{u, u} l E X h).mapHomologicalComplex (.up ℤ)

/-- The localization comparison for the exact counit fixed by the quotient calculus.
Source: blueprint lemma-change-coefficients-internal-hom--1, representative normalization. -/
def finiteHomTensorComparison {n m : ℕ} (h : m ≤ n) :=
  finiteHomTensorRepresentativeComparison (coefficientFiniteQuotientExtension.{u, u} l E X h)
    (coefficientFiniteQuotientDerived.{u, u} l E X h)
    (coefficientFiniteQuotientCounit.{u, u} l E X h)

private theorem comparison_model {n m : ℕ} (h : m ≤ n)
    (P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P) :
    (finiteHomTensorComparison l E X h).app P =
      (coefficientFiniteQuotientModel.{u, u} l E X h P hp).hom := by
  exact representativeComparison_model
    (coefficientFiniteQuotientExtension.{u, u} l E X h)
    (coefficientFiniteQuotientDerived.{u, u} l E X h)
    (coefficientFiniteQuotientCounit.{u, u} l E X h) P
    (coefficientFiniteQuotientCounit_isIso.{u, u} l E X h P hp)

private theorem comparison_unit {n m : ℕ} (h : m ≤ n)
    (P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ) :
    ((calculus l E X).quotientCalculus.adjunction h).unit.app (DerivedCategory.Q.obj P) ≫
        (normalizedDVRRes.{u, u} l E X h).map ((finiteHomTensorComparison l E X h).app P) ≫
        (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.hom.app
          ((finiteHomTensorExtensionComplex l E X h).obj P) =
      DerivedCategory.Q.map
        ((((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  apply normalized_unit_extension DerivedCategory.Q DerivedCategory.Q
    (finiteHomTensorExtensionComplex l E X h)
    ((normalizedDVRModuleRes.{u, u} l E X h).mapHomologicalComplex (.up ℤ))
    (coefficientFiniteQuotientDerived.{u, u} l E X h) (normalizedDVRRes.{u, u} l E X h)
    (((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex (.up ℤ))
    ((calculus l E X).quotientCalculus.adjunction h) (finiteHomTensorComparison l E X h)
    (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n))
  · intro Y
    obtain ⟨Y', f, hy, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Y
    exact ⟨Y', f, hy, q_iso_of_quasi f hq⟩
  · intro Y hy
    rw [comparison_model l E X h Y hy]
    exact (calculus l E X).quotientCalculus.unit_model h Y hy

private theorem comparison_transpose {n m : ℕ} (h : m ≤ n)
    (P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (H : CochainComplex (normalizedDVRModules.{u, u} l E X m) ℤ)
    (t : (finiteHomTensorExtensionComplex l E X h).obj P ⟶ H) :
    ((calculus l E X).quotientCalculus.adjunction h).homEquiv _ _
        ((finiteHomTensorComparison l E X h).app P ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map
        (((((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex
          (.up ℤ)).homEquiv _ _ t)) ≫
        (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.inv.app H := by
  let d := (calculus l E X).quotientCalculus.adjunction h
  let a := ((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex
    (.up ℤ)
  have hu : d.homEquiv _ _ ((finiteHomTensorComparison l E X h).app P) =
      DerivedCategory.Q.map (a.unit.app P) ≫
        (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.inv.app
          ((finiteHomTensorExtensionComplex l E X h).obj P) := by
    rw [d.homEquiv_unit]
    apply (Iso.eq_comp_inv ((normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.app
      ((finiteHomTensorExtensionComplex l E X h).obj P))).2
    simpa only [d, a, Iso.app_hom, Category.assoc] using comparison_unit l E X h P
  rw [d.homEquiv_naturality_right, hu]
  have hn := (NatTrans.naturality
    (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.inv t).symm
  change (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.inv.app _ ≫
      (normalizedDVRRes.{u, u} l E X h).map (DerivedCategory.Q.map t) =
    DerivedCategory.Q.map (((normalizedDVRModuleRes.{u, u} l E X h).mapHomologicalComplex
      (.up ℤ)).map t) ≫ (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.inv.app H
      at hn
  rw [Category.assoc, hn, ← Category.assoc, ← DerivedCategory.Q.map_comp]
  rfl

/-- Ordinary restriction composition, using the fixed quotient-map equality. -/
def finiteHomTensorRestrictionComp {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :
    normalizedDVRModuleRes.{u, u} l E X k ⋙ normalizedDVRModuleRes.{u, u} l E X h ≅
      normalizedDVRModuleRes.{u, u} l E X (k.trans h) :=
  normalizedDVRRestrictionCompIso (normalizedDVRQuotient.{u, u} l E X h)
      (normalizedDVRQuotient.{u, u} l E X k) ≪≫
    eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f)
      ((integralCoefficientSheafSystem.{u, u} l E X).map_comp
        (homOfLE h).op (homOfLE k).op).symm)

/-- The ordinary chain associator, formed from the prescribed ordinary adjunctions.
Source: blueprint lemma-change-coefficients-internal-hom--1, successive quotients. -/
def finiteHomTensorChainAssoc {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :
    finiteHomTensorExtensionComplex l E X h ⋙ finiteHomTensorExtensionComplex l E X k ≅
      finiteHomTensorExtensionComplex l E X (k.trans h) :=
  let S := (coefficientDerivedSystemEvaluationCalculus.{u, u} l E X).choose
  finiteHomTensorComplexAssociator (S.quotientCalculus.ordinaryAdjunction h)
    (S.quotientCalculus.ordinaryAdjunction k)
    (S.quotientCalculus.ordinaryAdjunction (k.trans h))
    (finiteHomTensorRestrictionComp l E X h k)

private theorem chainAssoc_transpose {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ) :
    (((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex
      (.up ℤ) |>.comp
        (((calculus l E X).quotientCalculus.ordinaryAdjunction k).mapHomologicalComplex
          (.up ℤ))).homEquiv _ _ ((finiteHomTensorChainAssoc l E X h k).hom.app P) =
      ((((calculus l E X).quotientCalculus.ordinaryAdjunction (k.trans h)).mapHomologicalComplex
        (.up ℤ)).unit.app P ≫
        (NatIso.mapHomologicalComplex (finiteHomTensorRestrictionComp l E X h k) (.up ℤ)).inv.app
          ((finiteHomTensorExtensionComplex l E X (k.trans h)).obj P)) := by
  exact complexAssoc_transpose _ _ _ _ P

/-- The prescribed derived associator is computed by its ordinary adjunction mate.
Source: blueprint lemma-change-coefficients-internal-hom--1, successive-quotient normalization
(blueprint: lem-coef-finite-hom-associator-model).
Proof: extend the calculus unit equation from K-flat representatives to all complexes
by naturality along K-flat resolutions. Transpose each normalized comparison.
The horizontal composition law for these transposes and exact restriction coherence
identify the derived left-adjoint mate with the localization of the ordinary mate. -/
theorem finiteHomTensor_associatorModel {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ) :
    (finiteHomIntrinsicAssoc l E X h k).hom.app (DerivedCategory.Q.obj P) ≫
        (finiteHomTensorComparison l E X (k.trans h)).app P =
      (coefficientFiniteQuotientDerived.{u, u} l E X k).map
          ((finiteHomTensorComparison l E X h).app P) ≫
        (finiteHomTensorComparison l E X k).app ((finiteHomTensorExtensionComplex l E X h).obj P) ≫
          DerivedCategory.Q.map ((finiteHomTensorChainAssoc l E X h k).hom.app P) := by
  let a := ((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex
    (.up ℤ)
  let b := ((calculus l E X).quotientCalculus.ordinaryAdjunction k).mapHomologicalComplex
    (.up ℤ)
  let c := ((calculus l E X).quotientCalculus.ordinaryAdjunction (k.trans h)).mapHomologicalComplex
    (.up ℤ)
  let ad := (calculus l E X).quotientCalculus.adjunction h
  let bd := (calculus l E X).quotientCalculus.adjunction k
  let cd := (calculus l E X).quotientCalculus.adjunction (k.trans h)
  let H := (finiteHomTensorExtensionComplex l E X (k.trans h)).obj P
  have hu : cd.homEquiv _ _ ((finiteHomTensorComparison l E X (k.trans h)).app P) =
      DerivedCategory.Q.map (c.unit.app P) ≫
        (normalizedDVRModuleRes.{u, u} l E X (k.trans h)).mapDerivedCategoryFactors.inv.app H := by
    rw [cd.homEquiv_unit]
    apply (Iso.eq_comp_inv
      ((normalizedDVRModuleRes.{u, u} l E X (k.trans h)).mapDerivedCategoryFactors.app H)).2
    simpa only [cd, c, H, Iso.app_hom, Category.assoc] using
      comparison_unit l E X (k.trans h) P
  have hf := Functor.exactDerivedRestrictionComposition_inv_factors
    (normalizedDVRModuleRes.{u, u} l E X k) (normalizedDVRModuleRes.{u, u} l E X h)
    (normalizedDVRModuleRes.{u, u} l E X (k.trans h)) (finiteHomTensorRestrictionComp l E X h k) H
  have hre : Functor.exactDerivedRestrictionComposition
      (normalizedDVRModuleRes.{u, u} l E X k) (normalizedDVRModuleRes.{u, u} l E X h)
      (normalizedDVRModuleRes.{u, u} l E X (k.trans h)) (finiteHomTensorRestrictionComp l E X h k) =
        normalizedDVRResComp.{u, u} l E X h k := by
    rfl
  rw [hre] at hf
  exact normalized_tensor_comparison_assoc a b c ad bd cd
    (finiteHomTensorComparison l E X h) (finiteHomTensorComparison l E X k)
    (finiteHomTensorComparison l E X (k.trans h))
    (normalizedDVRModuleRes.{u, u} l E X h).mapDerivedCategoryFactors.inv
    (normalizedDVRModuleRes.{u, u} l E X k).mapDerivedCategoryFactors.inv
    (normalizedDVRModuleRes.{u, u} l E X (k.trans h)).mapDerivedCategoryFactors.inv
    (comparison_transpose l E X h) (comparison_transpose l E X k)
    (NatIso.mapHomologicalComplex (finiteHomTensorRestrictionComp l E X h k) (.up ℤ))
    (normalizedDVRResComp.{u, u} l E X h k) (finiteHomTensorChainAssoc l E X h k).hom P hu
    (chainAssoc_transpose l E X h k P) hf

end Representatives

end WeilConjectures
