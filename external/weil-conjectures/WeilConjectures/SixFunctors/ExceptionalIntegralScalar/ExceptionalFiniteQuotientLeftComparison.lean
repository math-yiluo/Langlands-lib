/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalFiniteScalarLeftComparison
import all WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
/-! # The canonical finite quotient left comparison

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-finite-quotient-left-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients CategoryTheory.Limits
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- The chosen derived presentations require an extended conversion budget.
/-- The finite quotient proper/open comparison is invertible on its finite-Tor domain.
Source: Zheng, Lemma 5.22; finite scalar mates, Construction 2.26 and Proposition 2.29.

Proof: specialize the finite coefficient comparison theorem to the quotient factor
map. The literal finiteQuotientChange sheaf maps are its constant sheaf maps, by
finiteQuotient_eq_map. The comparison theorem supplies precisely the actual proper/open
mate, so no flatness of the quotient map is asserted. This includes exponent one,
equal exponents, and empty schemes, with no absolute separatedness assumption.
(blueprint: lem-sf-finite-quotient-left-comparison). -/
theorem finiteQuotientLeftComparison_isIso
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (E : FieldStage.{u} l) (m n : ℕ+) (h : (n : ℕ) ≤ m)
    (K : C.{u} l Ω X (.finite E m)) :
    IsIso ((PurCompactSupport.comparison
      (PurCompactSupport.finiteQuotientChange l E.carrier m n m.pos n.pos h) c).app K.obj)
    := by
  apply finiteScalarLeftComparison_isIso l Ω D hl c E E m n
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) _ _ K
  intro T
  exact PurCompactSupport.finiteQuotient_eq_map l E.carrier m n m.pos n.pos h T

end WeilConjectures.ExceptionalIntegralScalar
