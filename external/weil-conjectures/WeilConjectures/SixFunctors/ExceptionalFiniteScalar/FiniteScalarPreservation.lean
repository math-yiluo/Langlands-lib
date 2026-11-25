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

/-- Scalar extension preserves finite-Tor constructibility at a finite coefficient stage.
Source: Stacks 06YY and 09AL; finite scalar construction, step 1
(blueprint: lem-sf-exceptional-finite-scalar-preserves).

Proof in words.  A finite-Tor constructible object has a bounded constructible etale-origin
model with a bounded flat constructible representative.  Tensor this representative termwise
with the target finite coefficient ring.  Flatness is preserved by restriction of scalars,
and finite coefficient changes preserve constructibility of each term and of its cohomology.
The derived change-of-rings comparison identifies this tensor complex with the pro-etale scalar
extension, so the resulting object satisfies the target finite-Tor constructibility predicate.
-/
theorem finiteScalar_preserves
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] :
    ∀ K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T,
      finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj) := by
  intro K
  obtain ⟨r, s, hTor⟩ := K.property.2
  have ht := ProEtale.scalarExtension_tor a T K.obj r s hTor
  exact ⟨⟨ProEtale.scalarExtension_bounded_of_tor T _ _ r s ht,
    ProEtale.scalarExtension_constructible a T K.obj K.property.1.1 K.property.1.2⟩,
    r, s, ht⟩

end WeilConjectures.ExceptionalFiniteScalar
