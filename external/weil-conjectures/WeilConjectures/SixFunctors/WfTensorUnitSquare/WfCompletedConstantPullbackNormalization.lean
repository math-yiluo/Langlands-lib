/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfTensorUnitSquareData
import all WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeConstructibleScalarTransport
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

/-! # Normalized pullback of completed constant modules

Source: the coefficient-normalization step of the Frobenius tensor-unit argument.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.WfTensorUnitSquare
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A) (e : Aut X)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory

attribute [local irreducible] pbcCompletedComparison completedCoefficientMap
attribute [local irreducible] HasDerivedCategory.standard

attribute [local instance 40000] AlgebraicGeometry.Scheme.adicDatumModulesAbelian
attribute [local instance 30000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev direct := proEtaleRingModuleDirectImage e.asIso.hom (ring X d) (ring X d)
  (coefficientIso X d e)

private theorem generator_natural (M : ModuleCat.{u + 1} A)
    {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (x : M) :
    ((constants X d).obj M).val.map f (generator X d M U x) =
      generator X d M V x := by
  let η := (adicDatumOrdinaryAdjunction X
    (adicDatumScalar X (intrinsicPresentationDatum d))).unit.app
    ((adicLisseConstantModules X A).obj M)
  have hη (W : X.ProEtᵒᵖ) :
      η.val.app W (completedConstantGenerator X A M W x) = generator X d M W x := by
    dsimp only [η]
    erw [(adicDatumOrdinaryAdjunction_exists X
    (adicDatumScalar X (intrinsicPresentationDatum d))).choose_spec]
    exact (adicDatumOrdinaryUnit_exists X (adicDatumScalar X (intrinsicPresentationDatum d))
      ((adicLisseConstantModules X A).obj M)).exists.choose_spec W _
  rw [← hη U, ← hη V]
  refine (PresheafOfModules.naturality_apply η.val f _).symm.trans ?_
  congr 1
  exact (NatTrans.naturality_apply (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of M))) f x).symm

end WeilConjectures.WfTensorUnitSquare
