/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
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
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Derived quotient reduction of a flat line

Source: Stacks 06YY and 07A4; definition-tate-twists--10, integral finite-level step.
(blueprint: lem-weil-flat-line-derived-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.sheafCompose
  SheafOfModules.unit PresheafOfModules.unit
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

private local instance (priority := 10000) siteSmall (S : Scheme.{u}) :
    EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private local instance allRingDerived (S : Scheme.{u}) :
    ∀ R : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1, u, u + 1, u + 1}
        ((sheafCompose (Scheme.ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  fun _ ↦ HasDerivedCategory.standard _

private theorem derived_tensor_identification
    (S : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (d : @SheafOfModules.OrdinaryLineScalar.LineData.{u, u + 1, u + 2}
      S (essentiallySmallSelf.{0, u, u + 1} S.ProEt) (allRingDerived S) R L)
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L)]
    [PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L)] :
    Nonempty (SheafOfModules.OrdinaryLineScalar.twist.{u, u + 1, u + 2} (X := S) (R := R) L 1 ≅
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := R) L).mapDerivedCategory) := by
  let A := SheafOfModules.OrdinaryLineScalar.Modules.{u, u + 1} S R
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  have : (SheafOfModules.OrdinaryLineScalar.tensor.{u, u + 1}
      (X := S) (R := R) L 1).Additive :=
    SheafOfModules.LineUnbounded.tensorAdditive.{u, u + 1} S R L
  let T := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L
  let e : SheafOfModules.OrdinaryLineScalar.tensor.{u, u + 1} (X := S) (R := R) L 1 ≅ T :=
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} (R := R) L).symm
  let c := SheafOfModules.OrdinaryLineScalar.LineData.factors.{u, u + 1, u + 2} d 1 ≪≫
    Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q ≪≫
      T.mapDerivedCategoryFactors.symm
  exact ⟨Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ _ _ c⟩

/-- Derived quotient extension computes a line in degree zero and commutes with
exact tensor by that line, after any specified ordinary reduction identification.
Source: Stacks 06YY and 07A4; definition-tate-twists--10, integral finite-level step.
(blueprint: lem-weil-flat-line-derived-reduction).

Proof: a locally free rank-one sheaf is flat, so its degree-zero single complex is
K-flat. The universal scalar-extension counit on this complex is invertible; compose
it with the single-complex comparison and the specified ordinary isomorphism b.
For the functor comparison, resolve an arbitrary complex by a flat-term K-flat
complex P. Tensor by L preserves K-flatness: tensor an acyclic complex with P first,
then apply exact tensor by L, using associativity of total tensor and the fact that
L is in degree zero. Base extension preserves K-flat flat-term complexes. The
termwise balanced isomorphism sends a tensor (x tensor y) to
(a tensor x) tensor b(1 tensor y); its inverse uses b inverse and multiplies the
quotient coefficients. The two maps respect balanced relations, restrictions, and
differentials. They are mutually inverse and natural in P. The K-flat scalar counits
and exact tensor factorization maps descend this natural isomorphism through
localization at quasi-isomorphisms. Every object has a K-flat resolution, so this
gives the natural isomorphism on the full unbounded derived categories. -/
theorem flatLineDerivedReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (n : ℕ)
    (L : scalarReductionSource.{u, u} l E S) (N : scalarReductionTarget.{u, u} l E S n)
    [L.IsFiniteLocallyFreeOfRank 1] [N.IsFiniteLocallyFreeOfRank 1]
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L).Additive]
    [PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L)]
    [PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L)]
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf.{u, u} l E S n) N).Additive]
    [PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf.{u, u} l E S n) N)]
    [PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf.{u, u} l E S n) N)]
    (b : (scalarReductionExtension.{u, u} l E S n).obj L ≅ N) :
    Nonempty ((scalarReductionDerivedExtension.{u, u} l E S n).obj
      ((DerivedCategory.singleFunctor _ 0).obj L) ≅
        (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E S n) 0).obj N) ∧
    Nonempty ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) L).mapDerivedCategory ⋙
      scalarReductionDerivedExtension.{u, u} l E S n ≅
      scalarReductionDerivedExtension.{u, u} l E S n ⋙
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := integralCoefficientCommRingSheaf.{u, u} l E S n) N).mapDerivedCategory) := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S
  let Q := integralCoefficientCommRingSheaf.{u, u} l E S n
  let α := completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n
  let F := scalarReductionExtension.{u, u} l E S n
  let LF := scalarReductionDerivedExtension.{u, u} l E S n
  have := scalarReductionExtensionAdditive.{u, u} l E S n
  let p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology S) α := {
    ordinary := F
    obj_eq := (scalarReductionExistence.{u, u} l E S n).choose_spec.choose
    map_eq := (scalarReductionExistence.{u, u} l E S n).choose_spec.choose_spec.choose
    additive := inferInstance
    derived := LF
    counit := scalarReductionCounit.{u, u} l E S n
    universal := (scalarReductionDerivedExistence.{u, u} l E S n).choose_spec.choose_spec.1 }
  obtain ⟨dL⟩ := @SheafOfModules.OrdinaryLineScalar.exists_lineData.{u, u + 1, u + 2}
    S (essentiallySmallSelf.{0, u, u + 1} S.ProEt) (allRingDerived S) R L inferInstance
  obtain ⟨dN⟩ := @SheafOfModules.OrdinaryLineScalar.exists_lineData.{u, u + 1, u + 2}
    S (essentiallySmallSelf.{0, u, u + 1} S.ProEt) (allRingDerived S) Q N inferInstance
  let A := eqToIso ((scalarReductionExistence.{u, u} l E S n).choose_spec.choose L) ≪≫
    SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} α L
  let b' := A.symm ≪≫ b
  have cover (O : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1})
      (P : SheafOfModules.{u + 1, u, u + 1, u + 1}
        ((sheafCompose (Scheme.ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
      [P.IsFiniteLocallyFreeOfRank 1] :
      ∃ (I : Type (u + 1)) (V : I → S.ProEt), (Scheme.ProEt.topology S).CoversTop V ∧
        ∀ i, Nonempty (P.over (V i) ≅ SheafOfModules.unit
          (((sheafCompose (Scheme.ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over (V i))) := by
    obtain ⟨I, V, hV, e⟩ :=
      (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
        (M := P) (r := 1)).mp inferInstance
    exact ⟨I, V, hV, fun i ↦ ⟨(e i).some ≪≫
      SheafOfModules.freeUniqueIso.{u + 1, u, u + 1} _⟩⟩
  obtain ⟨B, hB, _, _⟩ := SheafOfModules.exists_signedLineComparison.{u + 1, u, u + 1}
    α L N (cover R L) (cover Q N) b'
  obtain ⟨cmp⟩ :=
    @SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison.{u, u + 1, u + 2}
      S (essentiallySmallSelf.{0, u, u + 1} S.ProEt) (allRingDerived S)
      R Q α p L N inferInstance inferInstance dL dN b' B hB
  constructor
  · let P := SheafOfModules.LineUnbounded.single.{u, u + 1} S R L
    have hK := (SheafOfModules.OrdinaryLineScalar.LineData.single_flat.{u, u + 1, u + 2} dL 1).1
    have hc : IsIso ((scalarReductionCounit.{u, u} l E S n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
      (scalarReductionDerivedExistence.{u, u} l E S n).choose_spec.choose_spec.2.2 P hK
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    have : IsIso ((scalarReductionCounit.{u, u} l E S n).app H) := hc
    exact ⟨LF.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso ((scalarReductionCounit.{u, u} l E S n).app H) ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      ((DerivedCategory.quotientCompQhIso _).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F
        (.up ℤ) 0).app L) ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso b⟩
  · obtain ⟨eL⟩ := derived_tensor_identification S R L dL
    obtain ⟨eN⟩ := derived_tensor_identification S Q N dN
    exact ⟨Functor.isoWhiskerRight eL.symm LF ≪≫
      SheafOfModules.OrdinaryLineScalar.Comparison.derived.{u, u + 1, u + 2} cmp 1 ≪≫
      Functor.isoWhiskerLeft LF eN⟩

end WeilConjectures
