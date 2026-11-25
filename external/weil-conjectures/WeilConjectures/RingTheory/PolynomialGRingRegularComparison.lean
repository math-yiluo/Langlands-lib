/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.PolynomialAlgebra
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularBaseChange
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularThroughLocalization

/-!
# The regular comparison localization for a polynomial ring over a G-ring

Source: Stacks Project, More on Algebra, Proposition 07PV, second paragraph.
(blueprint: lem-weil-pbc-polynomial-g-ring-regular-comparison).
-/

@[expose] public section

universe u

private theorem regular_of_algEquiv
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)
    (h : (algebraMap A B).IsRegular) : (algebraMap A C).IsRegular := by
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at h ⊢
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp h.1
  refine ⟨RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_linearEquiv e.symm.toLinearEquiv), ?_⟩
  intro p hp
  let ef : p.Fiber B ≃ₐ[p.ResidueField] p.Fiber C :=
    Algebra.TensorProduct.congr (.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField) e
  have hB := h.2 p
  have : IsNoetherianRing (p.Fiber B) := hB.1
  have : IsNoetherianRing (p.Fiber C) :=
    isNoetherianRing_of_ringEquiv (p.Fiber B) ef.toRingEquiv
  refine ⟨inferInstance, ?_⟩
  intro k _ _ _ _
  have : IsRegularRing (TensorProduct p.ResidueField k (p.Fiber B)) := hB.2 k
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (.refl : k ≃ₐ[p.ResidueField] k) ef).toRingEquiv

private theorem regular_polynomial_map
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (h : (algebraMap A B).IsRegular) :
    (Polynomial.mapRingHom (algebraMap A B)).IsRegular := by
  let : Algebra (Polynomial A) (Polynomial B) := Polynomial.algebra A B
  let : Algebra (Polynomial A) (TensorProduct A B (Polynomial A)) :=
    Algebra.TensorProduct.rightAlgebra
  let e : (TensorProduct A B (Polynomial A)) ≃ₐ[Polynomial A] Polynomial B :=
    { (polyEquivTensor A B).symm with
      commutes' := by
        intro p
        change (polyEquivTensor A B).symm (TensorProduct.tmul A (1 : B) p) = p.map (algebraMap A B)
        simp }
  change (algebraMap (Polynomial A) (Polynomial B)).IsRegular
  apply regular_of_algEquiv e
  exact RingHom.regular_base_change h

private theorem regular_localRingHom
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (f : A →+* B) (h : f.IsRegular) (p : Ideal A) [p.IsPrime]
    (q : Ideal B) [q.IsPrime] (hpq : p = q.comap f) :
    (Localization.localRingHom p q f hpq).IsRegular := by
  let : Algebra A B := f.toAlgebra
  let C := Localization.AtPrime q
  have : IsNoetherianRing C := IsLocalization.isNoetherianRing q.primeCompl C inferInstance
  have hAC : (algebraMap A C).IsRegular :=
    RingHom.IsRegular.comp_of_fiber_noetherian h
      (IsLocalization.isRegular_and_fiber q.primeCompl).1
      (fun _ _ ↦ Ideal.isNoetherianRing_fiber _)
  let g := Localization.localRingHom p q f hpq
  let : Algebra (Localization.AtPrime p) C := g.toAlgebra
  have : IsScalarTower A (Localization.AtPrime p) C :=
    IsScalarTower.of_algebraMap_eq (fun x ↦
      (Localization.localRingHom_to_map p q f hpq x).symm)
  exact RingHom.isRegular_of_comp_algebraMap_localization p.primeCompl hAC

/-- A polynomial localization over a G-ring maps regularly and locally to a polynomial
localization over a complete Noetherian local ring, at a maximal ideal over its closed point.

Source: Stacks Project, More on Algebra, Proposition 07PV, second paragraph, the bottom
map of the completion square.
(blueprint: lem-weil-pbc-polynomial-g-ring-regular-comparison).

Proof: Contract Q to p in R and let A = R_p. Extend Q to A[x], obtaining a maximal
ideal q whose contraction is the maximal ideal of A: coefficient localization
misses Q, and its quotient remains the field R[x]/Q. Localization at q identifies
A[x]_q with R[x]_Q by the universal properties of successive localization and
polynomial extension. Set S = Ahat, the completion at the maximal ideal m of A.
It is Noetherian and local, with maximal ideal mS. It is complete for mS because
m is finitely generated; thus it is complete at its own maximal ideal. Its
residue field agrees with that of A. Thus q modulo the maximal ideal of A determines
a maximal ideal q' in S[x] modulo the maximal ideal of S, and its inverse image Q'
is maximal and contracts to the maximal ideal of S. The G-ring assumption says
A → S is regular. Base change along the finite type map A → A[x] gives a regular
map A[x] → S[x], using the canonical tensor-product identification. Compose with
the regular localization S[x] → S[x]_(Q'); the composite has Noetherian fibres,
since its target is Noetherian. Its denominators outside q become units, so it
factors through A[x]_q. Regularity through localization makes this factored map
regular. Transport along A[x]_q ≃ R[x]_Q to obtain φ. The contraction of Q' to
A[x] is q (the residue-field identification), so the induced map on localizations
sends the maximal ideal into the maximal ideal, proving the asserted locality.
This constructs only the bottom map; regularity after completion is a separate step. -/
theorem exists_polynomial_regular_local_comparison
    (R : Type u) [CommRing R] (hR : IsGRing R)
    (Q : Ideal (Polynomial R)) [Q.IsMaximal] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : IsLocalRing S)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal S) S),
      ∃ (Q' : Ideal (Polynomial S)) (_ : Q'.IsMaximal),
        Q'.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S ∧
        ∃ φ : Localization.AtPrime Q →+* Localization.AtPrime Q',
          φ.IsRegular ∧
          (∀ x : Localization.AtPrime Q,
            x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) →
              φ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q')) := by
  classical
  have : IsNoetherianRing R := hR.1
  let p := Q.comap (Polynomial.C : R →+* Polynomial R)
  have : p.IsPrime := Ideal.comap_isPrime _ Q
  let A := Localization.AtPrime p
  let S := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : IsNoetherianRing A := inferInstance
  have : IsNoetherianRing S := AdicCompletion.isNoetherianRing _
  let K := Q.ResidueField
  let tA : A →+* K :=
    (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (Localization.localRingHom p Q Polynomial.C rfl)
  have : IsLocalHom tA := inferInstance
  let e : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField S :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap A S))
      (AdicCompletion.residueField_map_bijective A)
  let tS : S →+* K := (IsLocalRing.ResidueField.lift tA).comp
    (e.symm.toRingHom.comp (IsLocalRing.residue S))
  have htS (a : A) : tS (algebraMap A S a) = tA a := by
    change IsLocalRing.ResidueField.lift tA
      (e.symm (IsLocalRing.residue S (algebraMap A S a))) = tA a
    rw [← IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.ResidueField.lift tA (e.symm (e (IsLocalRing.residue A a))) = _
    simp
  have hker : RingHom.ker tS = IsLocalRing.maximalIdeal S := by
    ext x
    change IsLocalRing.ResidueField.lift tA (e.symm (IsLocalRing.residue S x)) = 0 ↔ _
    rw [map_eq_zero_iff _ (RingHom.injective _), e.symm.map_eq_zero_iff]
    exact IsLocalRing.residue_eq_zero_iff x
  let f := algebraMap R S
  let g : Polynomial S →+* K := Polynomial.eval₂RingHom tS
    (algebraMap (Polynomial R) K Polynomial.X)
  have hcomm : g.comp (Polynomial.mapRingHom f) = algebraMap (Polynomial R) K := by
    apply Polynomial.ringHom_ext
    · intro r
      change g (Polynomial.mapRingHom f (Polynomial.C r)) = _
      rw [show Polynomial.mapRingHom f (Polynomial.C r) = Polynomial.C (f r) from
        DFunLike.congr_fun (Polynomial.mapRingHom_comp_C f) r]
      rw [show g (Polynomial.C (f r)) = tS (f r) from
        DFunLike.congr_fun (Polynomial.eval₂RingHom_comp_C tS
          (algebraMap (Polynomial R) K Polynomial.X)) (f r)]
      change tS (algebraMap R S r) = algebraMap (Polynomial R) K (Polynomial.C r)
      rw [IsScalarTower.algebraMap_apply R A S, htS]
      exact congrArg (IsLocalRing.residue (Localization.AtPrime Q))
        (Localization.localRingHom_to_map p Q Polynomial.C rfl r)
    · simp [g]
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := Q.algebraMap_residueField_surjective y
    exact ⟨Polynomial.mapRingHom f x, (congrArg (fun h ↦ h x) hcomm).trans hx⟩
  let Q' := RingHom.ker g
  have : Q'.IsMaximal := RingHom.ker_isMaximal_of_surjective g hg
  have hQc : Q'.comap (Polynomial.C : S →+* Polynomial S) =
      IsLocalRing.maximalIdeal S := by
    rw [show Q'.comap Polynomial.C = RingHom.ker tS by
      ext x
      simp [Q', g, RingHom.mem_ker], hker]
  have hQ : Q = Q'.comap (Polynomial.mapRingHom f) := by
    ext x
    change x ∈ Q ↔ g (Polynomial.mapRingHom f x) = 0
    rw [show g (Polynomial.mapRingHom f x) = algebraMap (Polynomial R) K x from
      congrArg (fun h ↦ h x) hcomm]
    exact Ideal.algebraMap_residueField_eq_zero.symm
  have hf : f.IsRegular := RingHom.IsRegular.comp_of_fiber_noetherian
    (IsLocalization.isRegular_and_fiber p.primeCompl).1 (hR.2 p)
    (fun q _ ↦ Ideal.isNoetherianRing_fiber q)
  let φ := Localization.localRingHom Q Q' (Polynomial.mapRingHom f) hQ
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    Q', inferInstance, hQc, φ, ?_, ?_⟩
  · exact regular_localRingHom _ (regular_polynomial_map hf) Q Q' hQ
  · intro x hx
    exact map_nonunit φ x hx
