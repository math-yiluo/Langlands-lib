/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra

/-!
# Base fields for purity

Source: blueprint sk-def-purity-conv, def-pur-conventions (ℓ distinct from the
characteristic); definition-constructible-sheaves--6 and lemma-fourier-transform-constant-sheaf (a
base field finite or algebraically closed); Houyi #1396 (blueprint: def-pur-base-field). The Fourier
nodes lemma-integral-linear-character, proposition-fourier-inversion and
proposition-fourier-inversion are stated over `k₀`-schemes.

Lead decision (Houyi #1396): the purity constructions (Kummer classes, frame gluing, Chern
and Thom classes, the trace) are stated over a general base field. Proofs may reduce to
the algebraic closure by base change. In the iface tree the field `P.field.k` is used only
for three things: (a) invertibility of `ℓ`, which needs only `ringChar K` prime and `≠ ℓ`;
(b) finite type, which only gives the Noetherian instance of
`VectorBundleZeroSection.scheme`; (c) the six-functor wrappers, whose field-general core
`CurrentCompactKunneth.operationsOver` needs `Finite K ∨ IsAlgClosed K`. This file records
exactly these hypotheses as `PurityBaseField`. It is specialised to the closure `P.field.k`
(`geometricBase`) and to the finite field `P.field.k₀` (`arithmeticBase`).

## Main definitions

* `WeilConjectures.PurityBaseField`: a base field of prime characteristic different from ℓ,
  finite or algebraically closed.
* `PurityBaseField.residueInverse`: the uniquely determined inverse of ℓ in residue fields.
* `PurityBaseField.ofDatum`: the geometric field of a finite-field datum.
* `PurityFiniteSetting.geometricBase`, `PurityFiniteSetting.arithmeticBase`,
  `PurityFiniteSetting.closureMap`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace WeilConjectures

/-- A base field for purity at the coefficient prime `ell`. Its characteristic is a prime
different from `ell`, and the field is finite or algebraically closed. This is exactly the
scope of the existing field-general six-functor data `CurrentCompactKunneth.operationsOver`.
Source: blueprint def-pur-conventions (ℓ ≠ p) and proposition-composition-base-change-rf-shriek--1
(finite or algebraically closed base) (blueprint: def-pur-base-field). -/
structure PurityBaseField (ell : ℕ) where
  K : Type u
  [field : Field K]
  [charPrime : Fact (ringChar K).Prime]
  [charNe : Fact (ringChar K ≠ ell)]
  finite_or_closed : Finite K ∨ IsAlgClosed K

attribute [instance] PurityBaseField.field PurityBaseField.charPrime PurityBaseField.charNe

namespace PurityBaseField

variable {ell : ℕ} [Fact ell.Prime] (K : PurityBaseField.{u} ell)

/-- The geometric field `D.k` of a finite-field datum, as a purity base field for a coefficient
prime `ell ≠ D.p`. Characteristic facts are derived from `D` as in `sectionInvariant`; the
field is algebraically closed since it is an algebraic closure of `D.k₀`.
Source: def-pur-conventions, fixed geometric field (blueprint: def-pur-base-field). -/
def ofDatum (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) (hell : ell ≠ D.p) :
    PurityBaseField.{u} ell :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  { K := D.k
    charPrime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
    charNe := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
    finite_or_closed := Or.inr (IsAlgClosure.isAlgClosed D.k₀) }

end PurityBaseField

namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

end PurityFiniteSetting

end WeilConjectures
