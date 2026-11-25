/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorComparisonConstruction
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # K-injectivity after tensoring with a two-term unit complex
Source: Stacks Tags 08J7 and 08J9; the blueprint finite-free coefficient argument.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open CategoryTheory.MonoidalCategory
open scoped ZeroObject
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

open CategoryTheory.RingedDerivedNative
attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose
attribute [local instance] signedModuleMonoidal signedModuleSymmetric
  signedModulePreadditive signedModuleClosed signedModuleLimits signedModuleColimits
  signedGradedTensor signedGradedTensorFour signedGradedTensorLeft signedGradedTensorRight
attribute [local instance 5000] signedComplexMonoidal signedComplexBraided
attribute [local instance 10000] signedComplexStruct

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Tensoring a K-injective complex with a two-term complex of units preserves K-injectivity.
Source: the finite-free argument in paragraph 1 of
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 08J7 and 08J9.
(blueprint: lem-sf-two-term-unit-tensor-kinjective).

Proof: the coefficient terms are dualizable, including the zero terms. Its bounded
termwise right dual D has flat terms and is K-flat by the bounded-above flat criterion.
The bounded duality descends through the strong monoidal homotopy quotient. The
adjunction (-) tensor D left adjoint to (-) tensor Q identifies maps from an acyclic
A to I tensor Q with maps from A tensor D to I. The source is acyclic by K-flatness
of D, and the latter maps vanish by K-injectivity of I. Thus every original chain
map is nullhomotopic. This includes zero coefficients and the empty site. -/
theorem twoTermUnit_tensor_isKInjective
    (I Q : CochainComplex (Modules.{t, u} Y R) ℤ) (hI : I.IsKInjective)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from
      SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from
      SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R))) :
    (((totalTensor.{t, u} Y R).obj I).obj Q).IsKInjective := by
  classical
  let M := Modules.{t, u} Y R
  have (X : M) : PreservesColimitsOfSize.{0, 0}
      (CategoryTheory.MonoidalCategory.tensorLeft X) :=
    preservesColimitsOfSize_shrink _
  have (X : M) : PreservesColimitsOfSize.{0, 0}
      (CategoryTheory.MonoidalCategory.tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  have : HasExactColimitsOfShape ℤ M :=
    HasExactColimitsOfShape.domain_of_functor ℤ (SheafOfModules.toSheaf _)
  have hunit : (𝟙_ M) = (show M from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) := by
    with_unfolding_all rfl
  have hdual (n : ℤ) : IsDualizable (Q.X n) := by
    by_cases hn : n = -1
    · subst n
      exact (show IsDualizable (𝟙_ M) from isDualizable_unit).of_iso
        (eNeg ≪≫ eqToIso hunit.symm).symm
    by_cases hn' : n = 0
    · subst n
      exact (show IsDualizable (𝟙_ M) from isDualizable_unit).of_iso
        (eZero ≪≫ eqToIso hunit.symm).symm
    exact CategoryTheory.IsZero.isDualizable (hzero n hn hn')
  let : ∀ n, HasRightDual (Q.X n) := fun n ↦ (hdual n).some
  have : Q.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff _ _).2 (by
    intro n hn
    exact hzero n (by omega) (by omega))
  have : Q.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff _ _).2 (by
    intro n hn
    exact hzero n (by omega) (by omega))
  let D := Q.rightDual
  have hd (n : ℤ) : ObjectProperty.flat (D.X n) := by
    have hh : IsDualizable (D.X n) :=
      ⟨{ rightDual := Q.X (-n)
         exact := BraidedCategory.exactPairing_swap (Q.X (-n)) (Q.X (-n))ᘁ }⟩
    exact hh.flat
  have : D.IsStrictlyLE 1 := by
    simpa using (inferInstance : Q.rightDual.IsStrictlyLE (-(-1 : ℤ)))
  have hk := CochainComplex.kFlat_of_isStrictlyLE_of_flat D 1 hd
  let π := HomotopyCategory.quotient M (.up ℤ)
  let := CochainComplex.exactPairingRightDual Q (-1) 0
  let := BraidedCategory.exactPairing_swap Q D
  let : ExactPairing (π.obj D) (π.obj Q) := ExactPairing.map π D Q
  let adj := tensorRightAdjunction (π.obj D) (π.obj Q)
  have := adj.isLeftAdjoint
  have : I.IsKInjective := hI
  refine ⟨fun {A} f hA ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  change π.map f = π.map 0
  rw [Functor.map_zero]
  apply (adj.homEquiv (π.obj A) (π.obj I)).symm.injective
  have hAD : (A ⊗ D).Acyclic := by
    have hz : QuasiIso (0 : (0 : CochainComplex M ℤ) ⟶ A) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hA i)
    let T := CategoryTheory.MonoidalCategory.tensorRight D
    have hf : QuasiIso (T.map (0 : (0 : CochainComplex M ℤ) ⟶ A)) := hk.2 _ hz
    have ht : (T.obj (0 : CochainComplex M ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (T.map (0 : (0 : CochainComplex M ℤ) ⟶ A)) i).1 (ht i)
  have hg : (adj.homEquiv (π.obj A) (π.obj I)).symm (π.map f) = 0 := by
    apply CochainComplex.IsKInjective.rightOrthogonal I
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hAD
  erw [hg]
  symm
  erw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

end WeilConjectures.IntegralHom
