/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- Scalar extension preserves every specified Tor interval of a finite-Tor object.
Source: Stacks 06YY and 09AL; finite scalar construction, step 1
(blueprint: lem-sf-exceptional-finite-scalar-tor-interval).

Proof in words.  Choose the bounded flat constructible model in the source Tor interval.
Termwise tensoring with the target coefficient ring remains flat after restriction of scalars
and is supported in the same degrees.  The K-flat derived change-of-rings comparison identifies
its derived tensor with scalar extension, and the Tor-amplitude predicate therefore has exactly
the original interval, including for a nonflat coefficient map.
-/
theorem finiteScalar_torInterval
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] :
    ∀ (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) (r s : ℤ),
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) K.obj r s →
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l L (m + 1))
          ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj) r s := by
  intro K r s hK
  exact ProEtale.scalarExtension_tor a T K.obj r s hK

end WeilConjectures.ExceptionalFiniteScalar
