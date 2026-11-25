/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistDerivedScalarCanonical
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence

/-! # Normalization of a common ordinary twist/scalar model

Source: blueprint `definition-tate-twists--10`, final integral/common-stage sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (S : Scheme.{u}) [∀ x : S, Invertible (l : S.residueField x)]
  (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
  (ι : E →ₐ[Padic l] F) (κ : F →ₐ[Padic l] G)

end WeilConjectures
