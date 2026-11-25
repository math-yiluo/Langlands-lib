/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.PopescuRescalingData
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.RingTheory.EssentiallySmoothBaseChange

/-!
# Simultaneous rescaling of an existing Artinian coefficient chart

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15, 23 and 25.
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

private theorem essentiallySmooth_equiv_target
    {B : Type u} {D E : Type (max u v)} [CommRing B] [CommRing D] [CommRing E]
    [Algebra B D] [Algebra B E] (e : D ≃ₐ[B] E)
    (h : EssentiallySmooth B D) : EssentiallySmooth B E := by
  rcases h with ⟨P, hP, hBP, hPsmooth, T, ⟨eD⟩⟩
  exact ⟨P, hP, hBP, hPsmooth, T, ⟨e.symm.trans eD⟩⟩

private theorem essentiallySmooth_equiv_source
    {R B : Type u} {D : Type v} [CommRing R] [CommRing B] [CommRing D]
    [Algebra B D] (e : R ≃+* B) (h : EssentiallySmooth B D) :
    letI : Algebra R D := ((algebraMap B D).comp e.toRingHom).toAlgebra
    EssentiallySmooth R D := by
  let : Algebra R B := e.toRingHom.toAlgebra
  let : Algebra R D := ((algebraMap B D).comp e.toRingHom).toAlgebra
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  rcases h with ⟨P, hP, hBP, hPsmooth, T, ⟨eD⟩⟩
  let : CommRing P := hP
  let : Algebra B P := hBP
  let : Algebra R P := ((algebraMap B P).comp e.toRingHom).toAlgebra
  have : IsScalarTower R B P := IsScalarTower.of_algebraMap_eq' rfl
  have : Smooth R R := by constructor <;> infer_instance
  let eR : R ≃ₐ[R] B := { e with commutes' := fun _ ↦ rfl }
  have : Smooth R B := Smooth.of_equiv eR
  have : Smooth B P := hPsmooth
  have hRP : Smooth R P := Smooth.comp R B P
  exact ⟨P, hP, inferInstance, hRP, T, ⟨eD.restrictScalars R⟩⟩

private theorem essentiallySmooth_polynomial
    {B : Type u} {D : Type (max u v)} [CommRing B] [CommRing D] [Algebra B D]
    (d : ℕ) (h : EssentiallySmooth B D) :
    letI : Algebra (MvPolynomial (Fin d) B) (MvPolynomial (Fin d) D) :=
      (MvPolynomial.map (algebraMap B D)).toAlgebra
    EssentiallySmooth (MvPolynomial (Fin d) B) (MvPolynomial (Fin d) D) := by
  let : Algebra (MvPolynomial (Fin d) B) (MvPolynomial (Fin d) D) :=
    (MvPolynomial.map (algebraMap B D)).toAlgebra
  let Q := MvPolynomial (Fin d) B
  let T := _root_.TensorProduct B Q D
  let e : T ≃+* MvPolynomial (Fin d) D :=
    (Algebra.TensorProduct.comm B Q D).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv B D).toRingEquiv
  let eQ : T ≃ₐ[Q] MvPolynomial (Fin d) D :=
    { e with
      commutes' := by
        intro q
        change MvPolynomial.algebraTensorAlgEquiv B D (_root_.TensorProduct.tmul B (1 : D) q) =
          MvPolynomial.map (algebraMap B D) q
        simp }
  exact essentiallySmooth_equiv_target eQ (essentiallySmooth_baseChange h)

/-- Construct the rescaled coefficient algebra before padding the parameter list and
comparing powers of its parameter ideals. Source: Stacks Project, Smoothing Ring Maps,
Lemma 07FJ, steps 10--13, 15 and 25.
(blueprint: lem-weil-pbc-popescu-unpadded-coefficient-chart).

Proof: The rescaling-data theorem gives the parameters, kernel equalities, ideal H,
coefficient ring D', its flat local map and coefficient lifts. It also retains a
coefficient quotient B, essential smoothness of D' over B, and the k-algebra
identification e : R/H^n ≃ B[t_i], with n = N+d(8c). It supplies polynomial
coefficient-map and evaluation identities, without algebra structures on D'[t_i].

Set E=D'[t_i]. The coefficient homomorphism B[t_i]→E composed with e defines
θ:R/H^n→E as a k-algebra homomorphism. Its composite χ with the quotient map gives
the R-algebra structure. Composition with S→R gives the S-algebra structure.
These explicit maps prove the R→R/H^n→E and S→R→E scalar towers; k-linearity
proves the k→S→E tower. The canonical polynomial structure supplies k→D'→E.

Base change of the essentially smooth B-algebra D' gives an essentially smooth
B[t_i]-algebra B[t_i]⊗_B D'. Tensor commutativity followed by the polynomial tensor
identification is a B[t_i]-algebra equivalence from this tensor product to E, with
structure map given by coefficient mapping. Transport the smooth localization
presentation to E. Restrict it along e: the equivalence R/H^n→B[t_i] is smooth,
and smooth composition gives a smooth R/H^n-algebra presentation of the same
localization. This proves essential smoothness of E over R/H^n.

The supplied polynomial identities are now exactly the required S-generator and
R-evaluation identities by the definitions of θ, χ and the S-map. Retain the
A-map, coefficient lifts, localness and flatness unchanged. No positive-d assumption
is used: the zero-variable polynomial tensor equivalence also applies when d=0. -/
theorem exists_popescu_unpadded_coefficient_chart
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (s : ℕ) (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (c : ℕ) (hc : 0 < c)
    (r : ℕ) (f : MvPolynomial (Fin r) k →ₐ[k] A) (hf : Function.Surjective f)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (hflat₀ : ψ₀.Flat)
    (D₀ : Type (max u w)) [CommRing D₀] [IsLocalRing D₀] [IsArtinianRing D₀]
    [Algebra (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^ (N + d * (8 * c))) D₀]
    (g₀ : D₀ →+* Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
    [IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
          (N + d * (8 * c))) D₀)]
    [IsLocalHom g₀]
    (hsmooth₀ : EssentiallySmooth
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)
    (hgflat₀ : g₀.Flat)
    (hfactor₀ : (g₀.comp (algebraMap
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)).comp
      (Ideal.Quotient.mk (((q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c)))) =
      (Ideal.Quotient.mk ((q.asIdeal.map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
          (N + d * (8 * c)))).comp ψ₀)
    (hinc₀ : ∀ i : Fin r, Ideal.Quotient.mk
      ((q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i)))) ∈
        Set.range g₀) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ) (ell : Fin d × Fin s → Λ)
      (rho : Fin d → MvPolynomial (Fin m) k),
    (rho = fun i ↦ algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X i)) ∧
    (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
      ∑ j : Fin s, ell (i, j) * α (a j)) ∧
    (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (rho i) ∈ q.asIdeal) ∧
    (∀ (i : Fin d)
      (x : MvPolynomial (Fin m) k ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧ y = rho j ^ (c * 8)}),
      rho i • x = 0 ↔ rho i ^ 2 • x = 0) ∧
    (∀ (i : Fin d)
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (rho j) ^ (c * 8)}),
      rho i • x = 0 ↔ rho i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ (N + d * (8 * c))
    ∃ (H : Ideal R),
      H.map (algebraMap R Q) =
        Ideal.span (Set.range (fun i : Fin d ↦ algebraMap R Q (rho i))) ∧
      H.map ((algebraMap Λ L).comp (algebraMap R Λ)) = IsLocalRing.maximalIdeal L ∧
      ∃ (D' : Type (max u v)) (_ : CommRing D')
        (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D'),
        let I₀ := H ^ (N + d * (8 * c))
        let E := MvPolynomial (Fin d) D'
        ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
          (_ : IsScalarTower R (R ⧸ I₀) E)
          (algSE : Algebra S E) (_ : IsScalarTower S R E)
          (_ : Algebra k E) (_ : IsScalarTower k S E),
          EssentiallySmooth (R ⧸ I₀) E ∧
          ∃ (_ : IsScalarTower k D' E)
            (f₀ : A →ₐ[k] D') (g : D' →+* L ⧸ K)
            (u₀ : Fin d → D') (δ : Fin d → D'ˣ) (coeff : Fin d × Fin s → D'),
            IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
            (∀ i : Fin d, @algebraMap S E _ _ algSE (MvPolynomial.X (R := k) i) =
              MvPolynomial.C (σ := Fin d) (u₀ i) * MvPolynomial.X (R := D') i) ∧
            (∀ z : R, MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D'))
              (algebraMap R E z) =
              Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z))) ∧
            (∀ x, g (f₀ x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
            (∀ ij, g (coeff ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  obtain ⟨m, algRΛ, towerkRΛ, algSR, towerkSR, algSΛ, towerSRΛ, towerkSΛ,
    ell, rho, hrho, heq, hmem, hkerR, hkerΛ, H, hHQ, hHL, B, ringB, algkB,
    D', ringD, localD, artD, algkD, algBD, towerkBD, e, hsmoothB,
    f₀, g, u₀, δ, coeff, localLK, localg, hgflat, hX, hev, hf₀, hcoeff⟩ :=
    exists_popescu_rescaling_data p hp α q hreg N hN hpower d hd s a ha c hc
      r f hf m₀ φ₀ ψ₀ hψ₀ hideal₀ hflat₀ D₀ g₀ hsmooth₀ hgflat₀ hfactor₀ hinc₀
  let S := MvPolynomial (Fin d) k
  let R := MvPolynomial (Fin m) k
  let : Algebra R Λ := algRΛ
  have : IsScalarTower k R Λ := towerkRΛ
  let : Algebra S R := algSR
  have : IsScalarTower k S R := towerkSR
  let : Algebra S Λ := algSΛ
  have : IsScalarTower S R Λ := towerSRΛ
  have : IsScalarTower k S Λ := towerkSΛ
  let : CommRing B := ringB
  let : Algebra k B := algkB
  let : CommRing D' := ringD
  have : IsLocalRing D' := localD
  have : IsArtinianRing D' := artD
  let : Algebra k D' := algkD
  let : Algebra B D' := algBD
  have : IsScalarTower k B D' := towerkBD
  let I₀ := H ^ (N + d * (8 * c))
  let E := MvPolynomial (Fin d) D'
  let θ : (R ⧸ I₀) →ₐ[k] E :=
    (MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom k B D')).comp e.toAlgHom
  let χ : R →ₐ[k] E := θ.comp (Ideal.Quotient.mkₐ k I₀)
  let : Algebra R E := χ.toRingHom.toAlgebra
  let : Algebra (R ⧸ I₀) E := θ.toRingHom.toAlgebra
  have : IsScalarTower R (R ⧸ I₀) E := IsScalarTower.of_algebraMap_eq' rfl
  let η : S →ₐ[k] E := χ.comp (IsScalarTower.toAlgHom k S R)
  let algSE : Algebra S E := η.toRingHom.toAlgebra
  have : IsScalarTower S R E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k S E := IsScalarTower.of_algebraMap_eq fun x ↦
    (η.commutes x).symm
  let : Algebra (MvPolynomial (Fin d) B) E :=
    (MvPolynomial.map (algebraMap B D')).toAlgebra
  have hsmooth : EssentiallySmooth (R ⧸ I₀) E :=
    essentiallySmooth_equiv_source e.toRingEquiv (essentiallySmooth_polynomial d hsmoothB)
  refine ⟨m, algRΛ, towerkRΛ, algSR, towerkSR, algSΛ, towerSRΛ, towerkSΛ,
    ell, rho, hrho, heq, hmem, hkerR, hkerΛ, H, hHQ, hHL, D', ringD,
    localD, artD, algkD, inferInstance, inferInstance, inferInstance,
    algSE, inferInstance, inferInstance, inferInstance, hsmooth,
    inferInstance, f₀, g, u₀, δ, coeff, localLK, localg, hgflat, ?_, ?_, hf₀, hcoeff⟩
  · intro i
    exact hX i
  · intro z
    exact hev z


end Algebra
