/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs

import WeilConjectures.RingTheory.PopescuUniversalStandardizer
import WeilConjectures.RingTheory.PopescuParameterSolution

/-!
# Global auxiliary factorization in characteristic p

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ.
-/

@[expose] public section
universe u v w
open scoped TensorProduct
namespace Algebra

/-- The standardizer admits a factorization before localizing the polynomial base at q.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, items item-power
through item-eighth-resolve; the earlier thickening is retained.
(blueprint: lem-weil-pbc-popescu-char-p-preparation-global).

Proof:
1. Let H be the singular ideal of A over k. Use the supplied N>0 and containment
m^N⊆HΛ_q. Since A is a finite-type algebra over a field, it is Noetherian; choose
generators a_j of H and set d=dim Λ_q. No minimal-prime argument is part of this lemma.
2. Form B=A[x_i,z_ij]/(x_i^(2N)-sum_j z_ij a_j). Eliminating z_ij on the a_j-open
shows that B localized there is smooth over k[x]. The a_j generate the unit ideal
on each x_i-open, which is consequently smooth too. Improve the presentation to a
finite-type B-algebra C_old with retraction to B and free differentials on these
opens. Over the Noetherian polynomial base it is finitely presented. Choose c>0
such that every x_i^c is strictly standard, set e=8c and n=N+de.
3. Apply 07FH to the images of generators of A modulo m^n. Obtain a polynomial map
k[y]→Λ with pΛ_q=m and flat local map P₀=k[y]_p→Λ_q, and an essentially smooth
Artinian solution D₀ over P₀/p^n with flat local map to Λ_q/m^n containing these
images. The latter map is faithfully flat and injective, so A maps to D₀.
4. The flat height formula shows dim P₀=d. The polynomial base is regular, so
choose π_i in p whose images generate the maximal ideal of P₀. They also generate
m in Λ_q and give regular systems of parameters in both local rings.
5. Put R=k[y,t] and γ_i=π_i t_i. Every permutation of the parameters is regular in
P₀; hence γ_i form a regular sequence after inverting k[y]\p. Apply Ogoma successively
on R/(γ_j^e:j<i), multiplying π_i by elements outside p, to arrange equality of the
first and second annihilators on these modules. Earlier conditions are unchanged.
6. Inductively choose δ_i outside q and enlarge D₀ by 07FI. Faithful flatness puts
π_i^N in (a_j)D₀ modulo m^n. Lift the coefficients to Λ_q and correct them in
m^(n-N) so π_i^(2N)=sum_j a_j w_j, with w_j modulo m^n equal to π_i^N times the
chosen coefficients. Clear the finitely many denominators and the equality itself:
if s₀π_i^(2N)-sum_j u_j a_j vanishes locally, multiply by s₁ outside q killing it;
put s=s₀s₁ and μ_j=s^(2N-1)s₁u_j. Then (sπ_i)^(2N)=sum_j a_j μ_j.
Enlarge D₀ to contain a positive power of s, and rescale the μ_j accordingly.
Ogoma on Λ/(previous (δ_jπ_j)^e) supplies s' outside q such that every positive
power of s' gives equal first/square annihilators. Enlarge again to contain (s')^q,
and set δ_i=(s')^q s and λ_ij=(s')^(2Nq)μ_j. These satisfy the relation in Λ,
the annihilator condition, and membership of δ_i and λ_ij in the enlarged D'.
7. Map B to Λ using x_i↦δ_iπ_i and z_ij↦λ_ij, and compose with the retraction.
Base change C_old along x_i↦π_it_i to get C over R, and let R→Λ send t_i↦δ_i.
The composite A→C→Λ is α. Smoothness on the a_j-opens implies the required inclusion
of extended singular ideals. Strict standardness survives base change. Equal kernels
for x and x² imply equal kernels for all positive powers, by induction; apply this
with exponent c, and use (γ_j^c)^8=γ_j^e, for the two annihilator conditions.
8. Let I₀=p^nR and K=m^n in L=Λ_q. In Q=R_(q∩R) all t_i are units since their
images δ_i are outside q. The pigeonhole bound m^(d(e-1)+1)⊆(π_i^e)L and the same
bound in P₀ show that I₀Q⊆JQ and K⊆JL since n=N+de. Also I₀L⊆K.
9. Set E=D'[t], with the induced R/I₀-algebra structure. The map R/I₀→
(P₀/p^n)[t] is localization, hence essentially smooth; E is essentially smooth over
(P₀/p^n)[t] by base change, and composition proves essential smoothness over R/I₀.
Send C_old through its retraction to B, then send a∈A to its image in D', x_i to π_it_i,
and z_ij to bar(λ_ij)t_i^(2N)bar(δ_i)^(-2N). The δ_i are units in D' because D'→L/K
is local. Faithful-flat injectivity verifies all B-relations in D'[t]. Tensor lifting
then defines a:C→E. Evaluate t_i at δ_i and use D'→L/K to define b:E→L/K.
The two maps agree with C→Λ→L/K on A,x_i,z_ij and the polynomial base, so ba is
that map by the tensor universal property. This step does not yet localize E at q∩R.
10. Pad the parameter list by a zero to make it nonempty. Zero satisfies both kernel
conditions and is strictly standard (choose zero coefficients of the minors). J is
unchanged. For d=0, m=0 and every positive power bound still holds. Finite polynomial
presentations give small representatives of C_old and of the smooth models for D';
transport the multiplicative subsets and localize these representatives. Thus C and
E have carriers in Type(max u v), independently of the universe of Λ. -/
theorem exists_popescu_char_p_preparation_global
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) :
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin m) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin m) k) C)
      (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ),
      (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ ∧
      ∃ (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k),
        1 ≤ r ∧
        (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
        (∀ (i : Fin r)
          (x : MvPolynomial (Fin m) k ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ (i : Fin r)
          (x : Λ ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧
              y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ i, IsStrictlyStandardElement
          (R := MvPolynomial (Fin m) k) (algebraMap (MvPolynomial (Fin m) k) C (π i))) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I₀ : Ideal R) (K : Ideal L),
        I₀.map (algebraMap R Q) ≤ JQ ∧ K ≤ JL ∧
        (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K ∧
        ∃ (t : ℕ) (D' : Type (max u v)) (_ : CommRing D')
          (_ : IsLocalRing D') (_ : IsArtinianRing D'),
          let E := MvPolynomial (Fin t) D'
          ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
            (_ : IsScalarTower R (R ⧸ I₀) E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (a : C →ₐ[R] E) (b : E →ₐ[R] L ⧸ K),
              b.comp a = (Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ) := by
  let L := Localization.AtPrime q.asIdeal
  let d := (IsLocalRing.maximalIdeal L).spanFinrank
  obtain ⟨s, gens, hgens, B, hB, hkB, hAB, hkAB, hSB, hkSB, P, hval, hrel,
    C₀, hC₀, hkC₀, hSC₀, hkSC₀, hfpC₀, β₀, ρ, c, hc, hρβ, hgeometry⟩ :=
    exists_popescu_universal_standardizer (k := k) (A := A) (Λ := Λ) d N hN
  let S := MvPolynomial (Fin d) k
  let : CommRing B := hB
  let : Algebra k B := hkB
  let : Algebra A B := hAB
  have : IsScalarTower k A B := hkAB
  let : Algebra S B := hSB
  have : IsScalarTower k S B := hkSB
  let : CommRing C₀ := hC₀
  let : Algebra k C₀ := hkC₀
  let : Algebra S C₀ := hSC₀
  have : IsScalarTower k S C₀ := hkSC₀
  have : FinitePresentation S C₀ := hfpC₀
  obtain ⟨m, hRΛ, hkRΛ, hSR, hkSR, hSΛ, hSRΛ, hkSΛ, η, π,
    hη, hπ, hmem, hkerR, hkerΛ, hsolution⟩ :=
    exists_popescu_parameter_solution p hp α q hreg N hN hpower d rfl
      s gens hgens B P hval hrel c hc
  let R := MvPolynomial (Fin m) k
  let : Algebra R Λ := hRΛ
  have : IsScalarTower k R Λ := hkRΛ
  let : Algebra S R := hSR
  have : IsScalarTower k S R := hkSR
  let : Algebra S Λ := hSΛ
  have : IsScalarTower S R Λ := hSRΛ
  have : IsScalarTower k S Λ := hkSΛ
  let C := R ⊗[S] C₀
  let β : A →ₐ[k] C :=
    (TensorProduct.includeRight.restrictScalars k).comp β₀
  let γ : C →ₐ[R] Λ := AlgHom.liftEquiv S R C₀ Λ (η.comp ρ)
  have hfactor : (γ.restrictScalars k).comp β = α := by
    ext x
    change γ (β x) = α x
    have hβ : β x = 1 ⊗ₜ[S] β₀ x := rfl
    rw [hβ]
    change (AlgHom.liftEquiv S R C₀ Λ (η.comp ρ)) (1 ⊗ₜ[S] β₀ x) = α x
    rw [AlgHom.liftEquiv_tmul]
    simp only [one_smul, AlgHom.comp_apply]
    have hρβx : ρ (β₀ x) = algebraMap A B x := AlgHom.congr_fun hρβ x
    exact (congrArg η hρβx).trans (AlgHom.congr_fun hη x)
  obtain ⟨hideal, hstandard⟩ := hgeometry R η
  refine ⟨m, hRΛ, hkRΛ, C, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, β, γ, hfactor, ?_, d + 1, π,
    Nat.le_add_left 1 d, hmem, hkerR, hkerΛ, ?_, ?_⟩
  · simpa only [hη] using hideal
  · intro i
    exact hstandard (π i) (hπ i)
  · dsimp only at hsolution ⊢
    obtain ⟨n, hn, hnil, I₀, K, hI₀, hK, hIK, t, D', hD', hlocal, hart,
      hRE, hquotE, htowerE, hSE, hSRE, hsmooth, θ, b, hθ⟩ := hsolution
    let : CommRing D' := hD'
    have : IsLocalRing D' := hlocal
    have : IsArtinianRing D' := hart
    let E := MvPolynomial (Fin t) D'
    let : Algebra R E := hRE
    let : Algebra (R ⧸ I₀) E := hquotE
    have : IsScalarTower R (R ⧸ I₀) E := htowerE
    let : Algebra S E := hSE
    have : IsScalarTower S R E := hSRE
    let a : C →ₐ[R] E := AlgHom.liftEquiv S R C₀ E (θ.comp ρ)
    refine ⟨n, hn, hnil, I₀, K, hI₀, hK, hIK, t, D', hD', hlocal, hart,
      hRE, hquotE, htowerE, hsmooth, a, b, ?_⟩
    apply TensorProduct.ext_ring
    ext x
    simp only [a, γ, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
      Function.comp_apply, TensorProduct.includeRight_apply]
    rw [AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul]
    simp only [one_smul, AlgHom.comp_apply]
    change b (θ (ρ x)) = _
    exact AlgHom.congr_fun hθ (ρ x)


end Algebra
