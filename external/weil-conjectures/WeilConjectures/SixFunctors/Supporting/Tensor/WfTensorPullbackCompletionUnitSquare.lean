/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfTensorUnitSquareData
import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfCompletedConstantPullbackNormalization
import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfNormalizedKoszulFiberUnitTransport
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

/-! # Frobenius tensor comparison and the actual completion unit

The derived unit square follows from the specified completion comparison.
The strict square combines normalized constants and augmented Koszul transport;
applying localization gives the equality on the recorded models.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.WfTensorUnitSquare
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A) (e : Aut X)

variable (p : A)

private theorem derivedSquare (hp : Ideal.span (Set.range (fun _ : Fin 1 ↦ p)) = d.ideal)
    (M N : PbcBoundedConstructibleComplete X d) :
    DerivedSquare X d e p hp M N := by
  unfold DerivedSquare completed
  rw [Iso.trans_hom, ← Category.assoc]
  have h := (wfPullbackCompletion_exists X d 1 (fun _ ↦ p) hp e
    ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj))).exists.choose_spec
  change _ ≫ (wfPullbackCompletion X d 1 (fun _ ↦ p) hp e _).hom = _ at h
  rw [h]
  exact (wfCompletion_unit_map X d 1 (fun _ ↦ p) hp (ordinary X d e M N).hom)

end WeilConjectures.WfTensorUnitSquare

namespace WeilConjectures

end WeilConjectures
