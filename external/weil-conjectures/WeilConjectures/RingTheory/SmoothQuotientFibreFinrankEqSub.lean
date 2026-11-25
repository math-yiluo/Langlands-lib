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

import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Prod

@[expose] public section

universe u
open scoped TensorProduct
namespace Algebra

/--
Source: Stacks Project, Smoothing Ring Maps, Lemmas 07CG and 07CH.
(blueprint: new-smooth-quotient-fibre-finrank-eq-sub)
Tensoring the split conormal sequence with the residue field and applying
base change identifies the differential summand; rank additivity gives its
dimension as n - c.
-/
theorem smooth_quotient_fibre_finrank_eq_sub
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (p : Ideal R) [p.IsPrime]
    (q : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.Fiber
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
          KaehlerDifferential p.ResidueField
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) = n - c := by
  classical
  let P := MvPolynomial (Fin n) R
  let J : Ideal P := Ideal.span (Set.range f)
  let C := P ⧸ J
  let F := p.Fiber C
  let K := q.asIdeal.ResidueField
  let : Algebra C F := Algebra.TensorProduct.rightAlgebra
  let : Algebra C K := ((algebraMap F K).comp (algebraMap C F)).toAlgebra
  let : Module C K := Algebra.toModule
  have : IsScalarTower C F K := IsScalarTower.of_algebraMap_eq' rfl
  -- Split the conormal sequence over the polynomial quotient.
  have hq : Function.Surjective (algebraMap P C) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap P C) = J := Ideal.mk_ker
  obtain ⟨l, hl⟩ := (FormallySmooth.iff_split_injection (R := R) hq).mp
    (inferInstance : FormallySmooth R C)
  obtain ⟨e, _, _⟩ :=
    ((KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R P C hq).split_tfae'
      (g := (KaehlerDifferential.mapBaseChange R P C).restrictScalars P)).out
        2 3 rfl rfl |>.mp
          ⟨KaehlerDifferential.mapBaseChange_surjective R P C hq, l, hl⟩
  let e' : (C ⊗[P] KaehlerDifferential R P) ≃ₗ[P]
      J.Cotangent × KaehlerDifferential R C :=
    e.trans ((Ideal.Cotangent.equivOfEq _ J hker).prodCongr (LinearEquiv.refl P _))
  let ec := e'.extendScalarsOfSurjective hq
  let ep := ((KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange C).equivFun
  let eC : (Fin n → C) ≃ₗ[C] J.Cotangent × KaehlerDifferential R C :=
    ep.symm.trans ec
  -- Extend the split sequence to the residue field and compute its two free ranks.
  let eK : (K ⊗[C] (Fin n → C)) ≃ₗ[K]
      (K ⊗[C] J.Cotangent) × (K ⊗[C] KaehlerDifferential R C) :=
    (eC.baseChange C K _ _).trans
      (TensorProduct.prodRight C K K J.Cotangent (KaehlerDifferential R C))
  let bc := b.baseChange K
  have hleft : Module.finrank K (K ⊗[C] J.Cotangent) = c := by
    simpa using Module.finrank_eq_card_basis bc
  let bn := (Pi.basisFun C (Fin n)).baseChange K
  have hn : Module.finrank K (K ⊗[C] (Fin n → C)) = n := by
    simpa using Module.finrank_eq_card_basis bn
  have : Module.Finite K (K ⊗[C] J.Cotangent) := Module.Finite.of_basis bc
  have : Module.Finite K (K ⊗[C] KaehlerDifferential R C) := inferInstance
  have hadd : c + Module.finrank K (K ⊗[C] KaehlerDifferential R C) = n := by
    have hr := eK.finrank_eq
    rw [Module.finrank_prod, hleft, hn] at hr
    exact hr.symm
  -- Identify the remaining summand with the differential module of the fibre.
  let ed := KaehlerDifferential.tensorKaehlerEquiv R p.ResidueField C F
  let ef : (K ⊗[C] KaehlerDifferential R C) ≃ₗ[K]
      K ⊗[F] KaehlerDifferential p.ResidueField F :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C F K K _).symm.trans
      (ed.baseChange F K _ _)
  change Module.finrank K (K ⊗[F] KaehlerDifferential p.ResidueField F) = n - c
  rw [← ef.finrank_eq]
  omega

end Algebra
