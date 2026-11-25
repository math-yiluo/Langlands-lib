/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Tensor.TensorHomEvaluationExt
import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! Extensionality for a total tensor mapped into a Hom-complex term.
Source: Stacks 03EK, 03EO and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
attribute [local instance 2000] abSheafify abLocallyBijective
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Hom projections and total tensor inclusions jointly detect maps by local evaluation.
Source: Stacks 03EK, 03EO and 0A8X
(blueprint: lem-sf-total-tensor-hom-evaluation-ext).
Proof: use the coproduct universal property for the total tensor term. Then use
the product projections of the Hom term. Tensor-to-Hom evaluation extensionality
reduces each component to pure tensors and evaluation on a section of P^p.
There are no support, boundedness or freeness hypotheses. -/
theorem totalTensorHomEvaluation_ext
    (A Q P N : CochainComplex (Modules.{t, u} Y R) ℤ) (j : ℤ)
    (f g : (((totalTensor Y R).obj A).obj Q).X j ⟶ (homComplex (R := R) P N).X j)
    (h : ∀ (a b : ℤ) (hab : a + b = j) (p : ℤ)
      (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (v : (A.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
      let w := (eqToHom (congrArg
        (fun k ↦ (((totalTensor Y R).obj A).obj Q).X k) hab)).val.app U
          (totalPair Y R A Q a b U v z)
      evaluate Y R P N j p U (f.val.app U w) x =
        evaluate Y R P N j p U (g.val.app U w) x) : f = g := by
  let := countableColimits.{t, u} Y R
  let := ordinaryTensorZero.{t, u} Y R
  let : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = j at hab
  subst j
  apply homComplex_hom_ext
  intro p q hpq
  subst q
  apply tensorHomEvaluation_ext.{t + 1, t, u} R
  intro U v z x
  exact h a b rfl p U v z x
end WeilConjectures.IntegralHom
