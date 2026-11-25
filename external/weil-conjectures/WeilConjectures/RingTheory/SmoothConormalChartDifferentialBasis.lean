/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.KaehlerDifferentialsPolynomialExtension
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Free

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace KaehlerDifferential

/-- The differentials of a smooth quotient with free conormal module become free
of rank `n` after adjoining `c` variables and localizing.

Source: Stacks Project, proof of Lemma 07CH, its split conormal sequence;
Tags 031J, 00RS, 00RX, and 00RV.
(blueprint: lem-weil-pbc-smooth-conormal-chart-differential-basis).

Proof. Write P = R[x_1,...,x_n], J = (f), C = P/J, and D = C[y_1,...,y_c].
Smoothness splits the conormal sequence 0 -> J/J^2 -> C tensor_P Omega(P/R)
-> Omega(C/R) -> 0. The polynomial differential basis and the given conormal
basis therefore give C^n isomorphic to Omega(C/R) plus C^c. Tensor this split
isomorphism with D over C. The polynomial-extension decomposition identifies
D tensor_C Omega(C/R) plus D^c with Omega(D/R), hence gives a Fin n basis of
Omega(D/R). Localization is formally etale, so its differential base-change
isomorphism carries the localized basis to Omega(D_g/R). No condition on g is
needed; localization at zero and zero coefficient rings give zero modules
with the same basis equations. No map from P to D_g is used. -/
theorem nonempty_basis_smooth_conormal_chart
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Algebra.Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    Nonempty (Module.Basis (Fin n) (Localization.Away g)
      (KaehlerDifferential R (Localization.Away g))) := by
  classical
  let P := MvPolynomial (Fin n) R
  let J : Ideal P := Ideal.span (Set.range f)
  let C := P ⧸ J
  let D := MvPolynomial (Fin c) C
  let B := Localization.Away g
  have hq : Function.Surjective (algebraMap P C) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap P C) = J := Ideal.mk_ker
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) hq).mp
    (inferInstance : Algebra.FormallySmooth R C)
  obtain ⟨e, _, _⟩ := ((exact_kerCotangentToTensor_mapBaseChange R P C hq).split_tfae'
    (g := (mapBaseChange R P C).restrictScalars P)).out 2 3 rfl rfl |>.mp
      ⟨mapBaseChange_surjective R P C hq, l, hl⟩
  let e' : (C ⊗[P] KaehlerDifferential R P) ≃ₗ[P]
      J.Cotangent × KaehlerDifferential R C :=
    e.trans ((Ideal.Cotangent.equivOfEq _ J hker).prodCongr (LinearEquiv.refl P _))
  let ec := e'.extendScalarsOfSurjective hq
  let ep := ((mvPolynomialBasis R (Fin n)).baseChange C).equivFun
  let eC : (Fin n → C) ≃ₗ[C] KaehlerDifferential R C × (Fin c → C) :=
    ep.symm.trans ec |>.trans (LinearEquiv.prodComm C _ _) |>.trans
      ((LinearEquiv.refl C _).prodCongr b.equivFun)
  obtain ⟨eD, _⟩ := (exists_polynomial_extension_equiv R C c).1
  let ed : (D ⊗[C] (KaehlerDifferential R C × (Fin c → C))) ≃ₗ[D]
      KaehlerDifferential R D :=
    (TensorProduct.prodRight C D D _ _).trans
      (((LinearEquiv.refl D _).prodCongr
        (Algebra.TensorProduct.equivPiOfFiniteBasis D (Pi.basisFun C (Fin c)))).trans eD)
  let bD : Module.Basis (Fin n) D (KaehlerDifferential R D) :=
    ((Pi.basisFun C (Fin n)).baseChange D).map
      ((eC.baseChange C D _ _).trans ed)
  exact ⟨(bD.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R D B)⟩

end KaehlerDifferential
