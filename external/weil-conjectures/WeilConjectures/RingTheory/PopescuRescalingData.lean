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
import WeilConjectures.RingTheory.PopescuCoefficientRescaling
import WeilConjectures.RingTheory.PolynomialParameterQuotientChart

/-!
# Rescaling data before polynomial coefficient base change

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15
and the coefficient quotient of step 25.
(blueprint: lem-weil-pbc-popescu-rescaling-data).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Simultaneous rescaling, retaining the coefficient quotient and its polynomial
identification, before giving the polynomial ring over D' its algebra structures.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13 and 15;
the coefficient quotient used in step 25.
(blueprint: lem-weil-pbc-popescu-rescaling-data).

Proof: Write P = k[y] for the given polynomial source and p₀ for the contracted prime.
Smooth ascent from the field makes P regular. Geometric regularity makes Λ and its
localization L regular, so the embedding dimension d of L equals its Krull dimension.
The flat local height formula and the extended-prime equality show that P localized
at p₀ also has dimension d: its closed fibre in L is the residue field of L.
Choose d polynomial representatives u_i of a regular
system of parameters. Their images generate the maximal ideal of L. Every permutation
is regular. Adjoin variables t_i and put rho_i = u_i t_i. After localization away from
p₀ this is a regular sequence. On each quotient by preceding (8c)-th powers, use
regular-sequence powers and Ogoma to multiply the next u_i by an element outside p₀
so that multiplication by rho_i and its square have the same kernel before localization.
The preceding ideals and their kernel equalities remain unchanged.

The given flat local g₀ is faithfully flat and injective. Lift the images of the finite
polynomial generators of A to D₀. The relations vanish by injectivity, so the lift factors
through A. Regard D₀ as a k-algebra through the old coefficient quotient and retain this
A-map during all subsequent enlargements. Induct on the parameters to construct the
units δ_i and the coefficients ell(i,j). Faithfully flat ideal contraction writes u_i^N
as a sum of the images of a_j times coefficients d_j in the current coefficient ring.
Lift g(d_j) to c_j in L. The error lies in m_L^n with n = N + d(8c); since m_L^N is
contained in the singular ideal, it is a sum a_j c'_j with c'_j in m_L^(n-N).
Multiplication by u_i^N gives u_i^(2N) = sum a_j w_j, where
w_j = u_i^N(c_j+c'_j), and the correction u_i^N c'_j vanishes modulo m_L^n.
Thus all w_j have residue in the coefficient ring.

Choose a common denominator s₀ outside q and v_j in Λ with w_j = v_j/s₀, then s₁
outside q annihilating s₀ u_i^(2N) - sum v_j α(a_j). Put s=s₀s₁ and
μ_j=s^(2N-1)s₁v_j. Direct multiplication gives (s u_i)^(2N)=sum μ_j α(a_j) in Λ
and μ_j/s^(2N)=w_j in L. Lemma 07FI includes s^r, for some r>0, in an enlarged
coefficient ring; replace s by s^r and μ_j by s^(2N(r-1))μ_j. The displayed equation
and the fractions μ_j/s^(2N)=w_j are preserved, and the new μ_j have residue
(s^r)^(2N)u_i^N d_j in that ring.
Apply Ogoma on Λ modulo preceding rescaled parameter powers and use 07FI once more
to include a positive power of its clearing factor. Their product is δ_i outside q.
The correspondingly rescaled μ_j are ell(i,j). This supplies the equations, the second
kernel equalities, and all required coefficient residues, while preserving earlier steps.

Let R=P[t_i] and map it to Λ by the original map on P and t_i to δ_i. Map S to R by
X_i to u_i t_i, and set H=p₀R. Since t_i maps outside q it is a unit in Q, and the
u_i generate p₀P_(p₀), giving HQ=(rho_i)Q and HL=m_L. Put B=P/p₀^n. Polynomial
quotients and Ideal.map_pow identify R/H^n with B[t_i] as k-algebras. The coefficient
ring after the finite induction is essentially smooth over P_(p₀)/p₀^nP_(p₀), hence
over B by composition with the localization B→P_(p₀)/p₀^nP_(p₀).

The coefficient ring is essentially of finite type over the small ring B. Shrink its
smooth finite-presentation model and localization to Type(max u v): present the model
as a quotient of a finite polynomial ring over B, whose universe is u, and present
its localization by fractions in that quotient. Both are small in max u v. Transport
all maps and properties along the resulting algebra equivalence. Reindex the finite old
and added polynomial variables as Fin m. This gives the stated e. Polynomial coefficient
mapping sends each rho_i to C(u₀(i))X_i. Evaluation at the included units δ_i agrees
with R→Λ→L→L/K on coefficients and on every old and added variable; polynomial
extensionality proves the displayed equality for all z. Locality of g turns the included
δ_i into units. The retained A-map and chosen coefficients give the final two identities.
If d=0, the induction is empty, the parameter ideals are zero, and the polynomial
identification is the zero-variable equivalence. This result supplies no algebra structure
on D'[t_i] over R/H^n and asserts no essential smoothness for that polynomial ring. -/
theorem exists_popescu_rescaling_data
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
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B)
        (D' : Type (max u v)) (_ : CommRing D')
        (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D')
        (_ : Algebra B D') (_ : IsScalarTower k B D'),
        let I₀ := H ^ (N + d * (8 * c))
        ∃ (e : (R ⧸ I₀) ≃ₐ[k] MvPolynomial (Fin d) B),
          EssentiallySmooth B D' ∧
          ∃ (f₀ : A →ₐ[k] D') (g : D' →+* L ⧸ K)
            (u₀ : Fin d → D') (δ : Fin d → D'ˣ) (coeff : Fin d × Fin s → D'),
            IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
            (∀ i : Fin d,
              MvPolynomial.map (algebraMap B D')
                (e (Ideal.Quotient.mk I₀ (algebraMap S R (MvPolynomial.X i)))) =
              MvPolynomial.C (σ := Fin d) (u₀ i) * MvPolynomial.X (R := D') i) ∧
            (∀ z : R, MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D'))
              (MvPolynomial.map (algebraMap B D') (e (Ideal.Quotient.mk I₀ z))) =
              Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z))) ∧
            (∀ x, g (f₀ x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
            (∀ ij, g (coeff ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  classical
  obtain ⟨m, hRΛ, hkRΛ, hSR, hkSR, hSΛ, hSRΛ, hkSΛ, ell, rho,
    hrho, hrel, hmem, hkerR, hkerΛ, E, uP, tΛ, huP, hparameters, ht,
    hErho, hC, hX, D, hD, hlocalD, hartD, hkD, hBD, hkBD, hsmooth,
    f₀, g, δ, coeff, hlocal, hlocalg, hflatg, hgC, hgX, hgf, hgcoeff⟩ :=
    exists_popescu_coefficient_rescaling p hp α q hreg N hN hpower d hd s a ha c hc
      r f hf m₀ φ₀ ψ₀ hψ₀ hideal₀ hflat₀ D₀ g₀ hsmooth₀ hgflat₀ hfactor₀ hinc₀
  let R := MvPolynomial (Fin m) k
  let P := MvPolynomial (Fin m₀) k
  let p₀ := q.asIdeal.comap φ₀.toRingHom
  let n := N + d * (8 * c)
  let B := P ⧸ p₀ ^ n
  let S := MvPolynomial (Fin d) k
  let L := Localization.AtPrime q.asIdeal
  let K := IsLocalRing.maximalIdeal L ^ n
  let : Algebra R Λ := hRΛ
  have : IsScalarTower k R Λ := hkRΛ
  let : Algebra S R := hSR
  have : IsScalarTower k S R := hkSR
  let : Algebra S Λ := hSΛ
  have : IsScalarTower S R Λ := hSRΛ
  have : IsScalarTower k S Λ := hkSΛ
  let : CommRing D := hD
  have : IsLocalRing D := hlocalD
  have : IsArtinianRing D := hartD
  let : Algebra k D := hkD
  let : Algebra B D := hBD
  have : IsScalarTower k B D := hkBD
  obtain ⟨H, e, hHQ, hHL, heC, heX⟩ :=
    exists_polynomial_parameter_quotient_chart m₀ m d n φ₀ q E uP tΛ
      hparameters hideal₀ ht hC hX
  have hrhoE (i : Fin d) : rho i = E.symm (MvPolynomial.C (uP i) * MvPolynomial.X i) :=
    E.injective (by simpa only [AlgEquiv.apply_symm_apply] using hErho i)
  have hHQ' : H.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) =
      Ideal.span (Set.range (fun i ↦
        algebraMap R (Localization.AtPrime (q.asIdeal.under R)) (rho i))) := by
    simpa only [hrhoE] using hHQ
  let u₀ : Fin d → D := fun i ↦ algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) (uP i))
  have hpoly (i : Fin d) :
      MvPolynomial.map (algebraMap B D)
        (e (Ideal.Quotient.mk (H ^ n) (algebraMap S R (MvPolynomial.X i)))) =
      MvPolynomial.C (u₀ i) * MvPolynomial.X i := by
    have hi : algebraMap S R (MvPolynomial.X i) = rho i := congrFun hrho i |>.symm
    rw [hi, hrhoE i, map_mul, map_mul, map_mul, heC, heX, map_mul]
    change MvPolynomial.map (algebraMap B D)
      (MvPolynomial.C (Ideal.Quotient.mk (p₀ ^ n) (uP i))) *
        MvPolynomial.map (algebraMap B D) (MvPolynomial.X i) = _
    rw [MvPolynomial.map_C, MvPolynomial.map_X]
  let ev : MvPolynomial (Fin d) D →+* L ⧸ K :=
    MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D))
  let red : R →+* MvPolynomial (Fin d) D :=
    (MvPolynomial.map (algebraMap B D)).comp
      (e.toRingHom.comp (Ideal.Quotient.mk (H ^ n)))
  let target : R →+* L ⧸ K :=
    (Ideal.Quotient.mk K).comp ((algebraMap Λ L).comp (algebraMap R Λ))
  have heval : ev.comp (red.comp E.symm.toRingHom) = target.comp E.symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      change ev (MvPolynomial.map (algebraMap B D)
        (e (Ideal.Quotient.mk (H ^ n) (E.symm (MvPolynomial.C z))))) =
        Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ (E.symm (MvPolynomial.C z))))
      rw [heC, MvPolynomial.map_C, hC]
      simp only [ev, MvPolynomial.eval₂Hom_C]
      exact hgC z
    · intro i
      change ev (MvPolynomial.map (algebraMap B D)
        (e (Ideal.Quotient.mk (H ^ n) (E.symm (MvPolynomial.X i))))) =
        Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ (E.symm (MvPolynomial.X i))))
      rw [heX, MvPolynomial.map_X, hX]
      simp only [ev, MvPolynomial.eval₂Hom_X']
      exact hgX i
  have heval' (z : R) :
      MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D))
        (MvPolynomial.map (algebraMap B D) (e (Ideal.Quotient.mk (H ^ n) z))) =
      Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z)) := by
    have hz := RingHom.congr_fun heval (E z)
    change ev (red (E.symm (E z))) = target (E.symm (E z)) at hz
    rw [AlgEquiv.symm_apply_apply] at hz
    dsimp only [ev, red, target] at hz
    simp only [RingHom.comp_apply] at hz
    exact hz
  exact ⟨m, hRΛ, hkRΛ, hSR, hkSR, hSΛ, hSRΛ, hkSΛ, ell, rho,
    hrho, hrel, hmem, hkerR, hkerΛ, H, hHQ', hHL, B, inferInstance, inferInstance,
    D, hD, hlocalD, hartD, hkD, hBD, hkBD, e, hsmooth,
    f₀, g, u₀, δ, coeff, hlocal, hlocalg, hflatg, hpoly, heval', hgf, hgcoeff⟩


end Algebra
