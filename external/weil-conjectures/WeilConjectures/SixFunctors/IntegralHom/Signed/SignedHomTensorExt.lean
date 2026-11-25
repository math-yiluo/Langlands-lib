/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorCoordinateMap
import WeilConjectures.SixFunctors.IntegralHom.Tensor.TensorHomEvaluationExt

/-! # Uniqueness of signed tensor--Hom comparison on arbitrary coefficients
Source: Stacks Tag 0A8X and the blueprint finite-free coefficient calculation.
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

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
  totalPair pair projection evaluate

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The local signed formula determines the chain tensor--Hom comparison uniquely.
Source: paragraph 1 of `lem-coef-integral-hom-reduction.proof.md`, and Stacks
Tag 0A8X for the product Hom complex.
(blueprint: lem-sf-signed-hom-tensor-ext).

Proof: total tensor coproduct inclusions reduce equality to each homogeneous tensor
summand. The chosen Hom product cone is limiting, so its projections detect equality.
Apply tensorHomEvaluation_ext to each projected pair of maps. Their evaluations on
all local pure tensors and all source sections agree by the two signed formulas.
No boundedness, flatness, injectivity or coefficient support is needed. -/
theorem signedHomTensor_ext
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (f g : ((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R) P (((totalTensor.{t, u} Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (hg : IsSignedHomTensor Y R P I Q g) : f = g := by
  let := countableColimits.{t, u} Y R
  let := ordinaryTensorZero.{t, u} Y R
  let : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = j at hab
  subst j
  apply ((Classical.choose_spec
    (homComplex_projections_exists.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R))).1 P (((totalTensor Y R).obj I).obj Q) (a + b)).some.hom_ext
  intro ⟨p⟩
  apply tensorHomEvaluation_ext.{t + 1, t, u} R
  intro U v z x
  have h := (hf a b p U v z x).trans (hg a b p U v z x).symm
  unfold evaluate projection totalPair pair at h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact h

end WeilConjectures.IntegralHom
