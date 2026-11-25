/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import WeilConjectures.SixFunctors.Open.OpenDvrRoosCompletionComparison
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
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
import Mathlib.Data.Nat.Prime.Infinite

/-! # The intrinsic DVR completion criterion under canonical coefficient transport

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-intrinsic-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
  IntegralOnSlice.hasDerived integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory in
/-- Quotient Roos completeness is invertibility of the specified intrinsic Koszul unit.
Source: Stacks Tags 093M, 099B and 0A0E
(blueprint: lem-sf-open-dvr-intrinsic-criterion).

Proof: the completed constant-sheaf reduction theorem transports the two-term free
resolution of the positive DVR quotients to the completed coefficient sheaf. Thus the
uniformizer section is regular and its positive power quotients are precisely the
finite coefficients, with their prescribed quotient maps. On a single flat-term K-flat
representative the principal quotient tensor tower is therefore the recorded integral
reduction tower, including its augmentation. Apply regular_roos_koszul_unit. Its
existential Roos-triangle condition is the definition of quotient completeness; its
Koszul unit is the localized signed singleton Koszul fiber unit. The finite-constant
and completed-projection normalizations of C transport multiplication by t and every
power of t to those in completedAdicIntrinsicUnit. Exact scalar equivalence preserves
cones, products and the signed fiber inclusion, hence identifies these units by an
isomorphism. Transport the theorem's TFAE between its first and third conditions.
The auxiliary finite-field datum in IsDerivedCompleteUnrestricted affects none of
these constructions; one of F_2 and F_3 always has characteristic different from ell.
The empty scheme, zero complex and arbitrary unbounded complexes are included. -/
theorem openDvrIntrinsicCriterion
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal)
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (P : DerivedCategory (scalarReductionSource.{u, u} l E T)) :
    IsDerivedCompleteUnrestricted.{u, u} l E T P ↔
      IsIso (completedAdicIntrinsicUnit T d 1
        (fun _ ↦ Padic.coefficientExtensionUniformizer l E) (C.derived.functor.obj P)) := by
  classical
  obtain ⟨Q, f, hQ, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (DerivedCategory.Q.objPreimage P)
  let := hf
  let e : DerivedCategory.Q.obj Q ≅ P :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso P
  have hsite : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i)).symm (hflat i)
  let Qgood : (IntegralOnSlice.Good.{u, u} l E T none).FullSubcategory :=
    ⟨Q, hQ, hsite⟩
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hgen : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
    rw [← hd, Set.range_const]
  have hcomplete := (roosIntrinsicCompletenessEquivalence.{u, u} p l (by omega)
    E T d hgen P Qgood e).out 1 5
  change IsDerivedCompleteUnrestricted.{u, u} l E T P ↔
    IsIso ((IntegralOnSlice.completionUnit.{u, u} l E T none).app P) at hcomplete
  rw [hcomplete]
  obtain ⟨j, hj⟩ := openDvrRoosCompletionComparison l E d T C P
  obtain ⟨k, hk, _⟩ := koszulReconstruction T d 1
    (fun _ ↦ Padic.coefficientExtensionUniformizer l E) hd
  obtain ⟨i, hi⟩ := reconstructionKoszulIntrinsicComparison T d 1
    (fun _ ↦ Padic.coefficientExtensionUniformizer l E) (C.derived.functor.obj P)
  have hquot : IsIso ((reconstructionCompletionUnit T d).app
      (C.derived.functor.obj P)) ↔
      IsIso ((IntegralOnSlice.completionUnit.{u, u} l E T none).app P) := by
    constructor
    · intro h
      let := h
      have : IsIso (C.derived.functor.map
          ((IntegralOnSlice.completionUnit.{u, u} l E T none).app P)) := by
        rw [← hj]
        infer_instance
      exact isIso_of_reflects_iso _ C.derived.functor
    · intro h
      let := h
      have : IsIso ((reconstructionCompletionUnit T d).app
          (C.derived.functor.obj P) ≫ j.hom) := by
        rw [hj]
        infer_instance
      exact IsIso.of_isIso_comp_right _ j.hom
  rw [← hquot, ← hk (C.derived.functor.obj P), ← hi]
  simp only [isIso_comp_right_iff]

end WeilConjectures
