/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import all WeilConjectures.SmoothPurity.Supporting.ConnectedAdicIntegralBasis

/-! # Actual completed coefficient changes determine their field embeddings -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- A completed coefficient change at all schemes determines its coefficient embedding.
Source: Bhatt--Scholze, Section 6.8; Serre, Local Fields, Chapter II, Section 2.

Proof: evaluate the maps on the connected scheme Spec E. Constant completed sections
identify with the valuation rings. The maps on those constants are exactly the
restrictions of the two field embeddings. The target constant-section identification
is injective, so their restrictions to the valuation ring agree. Since E is the fraction
field of that valuation ring, the two field homomorphisms agree.
(blueprint: lem-sf-completed-change-injective). -/
theorem completedChange_injective (l : ℕ) [Fact l.Prime]
    (E L : FieldStage.{u} l) :
    Function.Injective (PurCompactSupport.completedChange l E.carrier L.carrier) := by
  intro i j hij
  let W : Scheme.{u} := Spec (.of E.carrier)
  have hmap : completedCoefficientMap l E.carrier L.carrier i W =
      completedCoefficientMap l E.carrier L.carrier j W :=
    congrArg (fun a ↦ a.map W) hij
  have hi (x : Padic.coefficientExtensionIntegers l E.carrier) :
      integralScalarIntegerInclusion l E.carrier L.carrier i x =
        integralScalarIntegerInclusion l E.carrier L.carrier j x := by
    apply (scalarValue_bijective l L.carrier W).injective
    rw [← scalarValue_map l E.carrier W L.carrier i,
      ← scalarValue_map l E.carrier W L.carrier j, hmap]
  let O := Padic.coefficientExtensionIntegers l E.carrier
  have hO := (Padic.coefficientExtensionIntegers_dvr l E.carrier).choose_spec
  have : IsFractionRing O E.carrier := hO.2.2.2.2.2.2.1
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors O)
  ext x
  exact congrArg Subtype.val (hi x)

end WeilConjectures.ExceptionalIntegralScalar
