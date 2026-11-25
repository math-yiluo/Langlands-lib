/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.ClosedFiberEquationRemoval
import WeilConjectures.RingTheory.FlatClosedFiberKernelRigidity

/-! # Removing the equations of a regular closed fibre

Source: Stacks Project, Tag 07NQ, proof of (2) implies (3), through the isomorphism
S tensor_R A -> B. (blueprint: lem-weil-pbc-flat-closed-fibre-power-series-model)
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace RingHom

/-- Given a compatible power-series presentation of a flat local map with smooth closed
fibre, remove the equations of the fibre while retaining the base presentation.
The kernel identity says precisely
that the target is the base change along the surjective base presentation. This statement
asserts no relative formal smoothness of the power-series map or of the original map.

Source: Stacks Project, Tag 07NQ, proof of (2) implies (3), from the diagram of Tag 07NN
through the displayed isomorphism S tensor_R A -> B.
(blueprint: lem-weil-pbc-flat-closed-fibre-power-series-model)

Proof:
1. Use the given compatible Cohen presentation R -> S, R -> A, S -> B of Tag 07NN.
The coefficient hypotheses make these complete power-series rings over fields or Cohen rings.
The parameters t of R extend to parameters of S. The surjection R -> A identifies
residue fields. No completeness assumption on A or B is needed after this presentation.
2. The closed fibre of B is regular by Tag 07EL, since it is adically formally smooth
 over the residue field. The closed fibre of S is regular by the parameter quotient
 theorem. Tag 00NR gives generators of the kernel between these fibres which extend
 to parameters. Lift them to ker(S -> B): subtract an element of m_R S from each lift,
 using surjectivity onto m_A B. Their cotangent classes together with those of t are
 independent; extend to a basis, and apply Nakayama to obtain parameters of S.
3. Quotient S by these lifted equations. Tag 07NM identifies the quotient with a
 power-series ring T over the same coefficients, retaining the images of t as parameters
 (and retaining p in the Cohen case). The map T -> B is surjective. The parameter
 regular-sequence criterion and Tag 07DY give flatness of R -> T. The induced map of
 closed fibres is an isomorphism, so the fibre of T has the given formal smoothness.
4. Set D = T/(ker(R -> A))T = T tensor_R A. The induced map D -> B is surjective.
Both sides are A-flat, by base change and the hypothesis. Tensor its kernel sequence
with the residue field: flatness of B gives left exactness, and the fibre isomorphism
shows that the kernel modulo m_A is zero. D is Noetherian local, being a proper
quotient of T. Its kernel is finitely generated and m_A D lies in its maximal ideal;
Nakayama gives zero kernel. Thus ker(T -> B) = (ker(R -> A))T, as asserted.
The zero-dimensional and empty-equation cases use empty parameter lists and zero ideals.
-/
theorem exists_flat_closedFiber_powerSeries_model
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat)
    (ΛR ΛS : Type w) [CommRing ΛR] [CommRing ΛS] (n m : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) ΛR)]
    [IsRegularLocalRing (MvPowerSeries (Fin m) ΛS)]
    (q : MvPowerSeries (Fin n) ΛR →+* A) [IsLocalHom q]
    (b : MvPowerSeries (Fin m) ΛS →+* B) [IsLocalHom b]
    (i : MvPowerSeries (Fin n) ΛR →+* MvPowerSeries (Fin m) ΛS) [IsLocalHom i]
    (hq : Function.Surjective q) (hb : Function.Surjective b)
    (hcomm : b.comp i = f.comp q)
    (t : List (MvPowerSeries (Fin n) ΛR))
    (z : List (MvPowerSeries (Fin m) ΛS))
    (ht : IsRegularSystemOfParameters t)
    (hz : IsRegularSystemOfParameters (t.map i ++ z))
    (hcoeff : (IsField ΛR ∧ IsField ΛS ∧ CharZero ΛR ∧ CharZero ΛS) ∨
      ∃ p : ℕ, p.Prime ∧ IsCohenRing p ΛR ∧ IsCohenRing p ΛS ∧
        t.head? = some (p : MvPowerSeries (Fin n) ΛR)) :
    letI : Algebra A B := f.toAlgebra
    let I : Ideal B := Ideal.map f (maximalIdeal A)
    letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal A ≤ I.comap (algebraMap A B))
    Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)) →
    ∃ m' : ℕ, let T := MvPowerSeries (Fin m') ΛS
      ∃ (_ : IsRegularLocalRing T)
        (v : T →+* B) (j : MvPowerSeries (Fin n) ΛR →+* T),
        Function.Surjective v ∧ IsLocalHom j ∧
        v.comp j = f.comp q ∧ RingHom.ker v = (RingHom.ker q).map j ∧
        ∃ y : List T, IsRegularSystemOfParameters (t.map j ++ y) ∧
          (let R := MvPowerSeries (Fin n) ΛR
           letI : Algebra R T := j.toAlgebra
           let L : Ideal T := (maximalIdeal R).map j
           letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
             Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
               maximalIdeal R ≤ L.comap (algebraMap R T))
           Algebra.FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
             ((maximalIdeal T).map (Ideal.Quotient.mk L))) := by
  dsimp only
  intro hsmooth
  obtain ⟨m', hT, v, j, hv, hj, hcomm', hker, y, hparams, hsmooth'⟩ :=
    exists_closedFiber_equation_removal A B f ΛR ΛS n m q b i
      hq hb hcomm t z ht hz hcoeff hsmooth
  let := hT
  let := hj
  have hker' : RingHom.ker v = (RingHom.ker q).map j :=
    ker_eq_map_of_flat_of_ker_le_maximal q f hflat j v hq hv hcomm' hker
  exact ⟨m', hT, v, j, hv, hj, hcomm', hker', y, hparams, hsmooth'⟩

end RingHom
