/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorNaturality
import Mathlib.Algebra.CharP.CharAndCard

/-! # A natural tensor comparison for finite-stage inclusion

Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

/-- The coefficient prime is invertible on every space over the fixed base field.
Source: the coefficient convention, l different from the characteristic
(blueprint: def-sf-common-projection-tensor-comparison).
Proof: compute the characteristic from the finite base field and its algebraic
closure, then map the resulting unit to each residue field. -/
theorem sixFunctorSpace_coefficient_invertible
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum) (X : SixFunctorSpace D) :
    ∀ x : X.obj.left, Nonempty (Invertible (C.l : X.obj.left.residueField x)) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  intro x
  let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.obj.hom.appTop ≫
    X.obj.left.Γevaluation x).hom
  exact ⟨(Eq.mp (congrArg IsUnit (map_natCast φ C.l))
    ((isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
        C.different.symm)).map φ)).invertible⟩

/-- One canonical tensor comparison for all morphisms and compactifications.
Source: thm-sf-pf-field.proof.md, common finite coefficient field paragraph
(blueprint: def-sf-common-projection-tensor-comparison). -/
@[irreducible] def commonProjectionTensorComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D) :
    Functor.uncurry.obj ((H.coefficientStages E).rationalTensor X) ⋙
        inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E ≅
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E).prod
          (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E) ⋙
        Functor.uncurry.obj (H.commonStageTensor X) := by
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (sixFunctorSpace_coefficient_invertible C X x).some
  rw [(H.coefficientStages E).rationalTensorNormalization X,
    H.commonStageTensorNormalization X]
  simpa only [Functor.currying, Functor.uncurry_obj_curry_obj] using
    commonInclusionTensorComparison C.l C.Qbar X.obj.left E

end WeilConjectures
