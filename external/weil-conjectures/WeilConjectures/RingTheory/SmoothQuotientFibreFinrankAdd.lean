/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

import WeilConjectures.RingTheory.SmoothQuotientFibreFinrankAddLe
import WeilConjectures.RingTheory.SmoothQuotientFibreFinrankEqSub

@[expose] public section


universe u

open scoped TensorProduct

namespace Algebra

/-- Intermediate rank-additivity for fibres of a smooth polynomial quotient.

Source: Stacks Project, Smoothing Ring Maps, Lemmas 07CG and 07CH.
(blueprint: lem-weil-pbc-smooth-quotient-fibre-finrank-add)

Proof. Tensor the split conormal sequence with the residue field at the chosen
prime. The conormal basis and polynomial coordinate basis give ranks `c` and
`n`; differential base change and tensor associativity identify the remaining
summand with the displayed differential fibre. The direct-sum dimension formula
therefore gives the additive equality `c + d = n`.
-/
theorem smooth_quotient_fibre_finrank_add
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (p : Ideal R) [p.IsPrime]
    (q : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    c + Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.Fiber
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
          KaehlerDifferential p.ResidueField
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) = n := by
  have hsub : c ≤ n := by
    exact smooth_quotient_fibre_finrank_add_le f b p q
  have hdim : Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.Fiber
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
          KaehlerDifferential p.ResidueField
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) = n - c := by
    exact smooth_quotient_fibre_finrank_eq_sub f b p q
  omega


end Algebra
