/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # The integral representative of a scalar-stage object -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
variable (l : ℕ) [Fact l.Prime]

/-- The scalar-stage object is the raw localization of its integral transition.
Source: the canonical stage-system and rational scalar-extension object equations.
Proof: evaluate the specified transition-functor equality at raw localization of K,
then apply sfRationalScalarExtension_obj to identify its value with raw localization
of the prescribed integral transition. The initial value is the toStage object.
(blueprint: lem-sf-native-integral-stage-object). -/
theorem integralStageObject
    (T : Scheme.{u}) (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) i) T) :
    ((⟨i, (sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) i) T).obj K⟩ :
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T).toStage h) =
      (sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) T).obj
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) T
            i E h).obj K) := by
  have ht := (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l (PadicAlgCl l) T).exists.choose_spec.1 i E h
  exact (congrArg (fun F :
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T i ⥤
        GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ↦
      F.obj ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) i) T).obj K)) ht).trans
    (sfRationalScalarExtension_obj l (Coefficient.{u} l (PadicAlgCl l) i) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l (PadicAlgCl l) E)
      (coefficientInclusion l (PadicAlgCl l) i E h) _)

end WeilConjectures.LocallyFiniteAdicCompactSupport
