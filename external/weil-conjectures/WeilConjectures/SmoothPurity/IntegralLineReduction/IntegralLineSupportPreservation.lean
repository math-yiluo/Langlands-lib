/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # Support preservation for finite ordinary line tensor

(blueprint: lem-pur-integral-line-support-preservation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem flat_tensor_homology_zero
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    (S : RingedSiteDualityModel.{u + 1, u, u, u + 2} (ProEt.topology X) R)
    (M : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R) M)
    (K : DerivedCategory (SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (i : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (S.closed.tensor.obj (K, (DerivedCategory.singleFunctor _ 0).obj M))) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let A := SheafOfModules.{u + 1, u, u + 1, u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := R) G
  have := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨hSingle, _, hLim, hCol, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
      R M hM
  have := hLim
  have := hCol
  let T := CategoryTheory.MonoidalCategory.tensorRight M
  let collapse := SheafOfModules.FlatSingleDerivedNormalization.collapse.{u + 1, u, u + 1} R M
  let tensorIso : DerivedCategory.Q.obj
      ((T.mapHomologicalComplex (.up ℤ)).obj P) ≅
      S.closed.tensor.obj (K, (DerivedCategory.singleFunctor _ 0).obj M) :=
    (DerivedCategory.Q.mapIso (collapse.app P)).symm ≪≫
      S.models.iso.{u, u + 1, u, u + 2} (ProEt.topology X) R S.closed P
        ((CochainComplex.singleFunctor _ 0).obj M) hP hSingle ≪≫
      S.closed.tensor.mapIso (Iso.prod e (Iso.refl _))
  have hP0 : IsZero (P.homology i) :=
    (h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)).of_iso
      ((DerivedCategory.homologyFunctorFactors A i).app P).symm
  have hT0 : IsZero (((T.mapHomologicalComplex (.up ℤ)).obj P).homology i) :=
    (T.map_isZero hP0).of_iso ((P.sc i).mapHomologyIso T)
  have hQ0 : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj P))) :=
    hT0.of_iso ((DerivedCategory.homologyFunctorFactors A i).app
      ((T.mapHomologicalComplex (.up ℤ)).obj P))
  exact hQ0.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso tensorIso).symm

private theorem finite_power_rank
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (n : ℕ) (m : ℤ) : (finitePower l E X L n m).IsFiniteLocallyFreeOfRank 1 := by
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  let S := integralCoefficientCommRingSheaf.{u, u} l E X n
  let α := completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n
  have : L.IsInvertible :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).2 inferInstance
  let c : (scalarReductionExtension.{u, u} l E X n).obj L ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L :=
    eqToIso ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose L) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} α L
  have : (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L).IsInvertible :=
    (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1} R S α L).1
  have : (line l E X L n).IsInvertible :=
    SheafOfModules.IsInvertible.of_iso.{u + 1, u, u + 1} c.symm
  have : (line l E X L n).IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
      _).1 inferInstance
  rw [finitePower_eq_coefficient]
  exact (signedLineTensor_equivalence X S (line l E X L n) m).1

/-- Tensoring by a finite signed line does not enlarge cohomological support.

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 010N; blueprint proof
of `lem-pur-integral-line-derived-comparisons`, final support sentence.
Proof: the finite signed line is finite locally free of rank one, hence flat. On a
K-flat representative, tensoring by its degree-zero single complex is exact and the
canonical homology comparison identifies each cohomology object with the original
cohomology tensored by the line. Exact tensoring sends a zero cohomology object to
zero, which is precisely the asserted inclusion of supports.
(blueprint: lem-pur-integral-line-support-preservation).
-/
theorem finite_ordinary_support_subset
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (n : ℕ) (m : ℤ) (K : DerivedCategory (scalarReductionTarget.{u, u} l E X n)) :
    proEtaleCohomologicalSupport ((finiteOrdinary l E X L n m).obj K) ⊆
      proEtaleCohomologicalSupport K := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := integralCoefficientCommRingSheaf.{u, u} l E X n
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  have := finite_power_rank l E X L n m
  have hM := (SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u, u + 2}
    X R (finitePower l E X L n m)).1
  intro i hi hK
  exact hi (flat_tensor_homology_zero X R (finiteModel l E X n)
    (finitePower l E X L n m) hM K i hK)

end WeilConjectures.IntegralLineReduction
