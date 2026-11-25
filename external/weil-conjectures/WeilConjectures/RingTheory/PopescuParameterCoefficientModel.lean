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
import WeilConjectures.RingTheory.PopescuSolutionModulo
import WeilConjectures.RingTheory.PopescuRescaledCoefficientChart
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Rescaled parameters and their Artinian coefficient model

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, items item-NP through
item-choose-deltai, item-set-map-R, item-sixth-resolve and item-eighth-resolve.
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

private theorem kernel_pow_eq_kernel
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (t : R) (h : ∀ x : M, t • x = 0 ↔ t ^ 2 • x = 0)
    (n : ℕ) (hn : 0 < n) (x : M) : t ^ n • x = 0 ↔ t • x = 0 := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      calc
        t ^ (n + 1 + 1) • x = 0 ↔ t ^ (n + 1) • (t • x) = 0 := by
          rw [pow_succ, mul_smul]
        _ ↔ t • (t • x) = 0 := ih (by omega) (t • x)
        _ ↔ t • x = 0 := by simpa [pow_two, mul_smul] using (h x).symm

/-- Construct rescaled parameters and the coefficient model before solving the polynomial
coefficient equations. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ,
items item-NP through item-choose-deltai and item-eighth-resolve.
(blueprint: lem-weil-pbc-popescu-parameter-coefficient-model).

Proof: Put e = 8c and n = N + de. Apply 07FH to the images of finite algebra generators
of A modulo the n-th maximal-ideal power in L. The flat local polynomial model has
maximal ideal extending to that of L. The flat height formula and regularity give d
parameters u_i generating both maximal ideals. Adjoin t_i and send X_i to u_i t_i.
Regular-sequence powers and successive applications of Ogoma rescale the polynomial
parameters outside their prime until the first and square kernels agree modulo preceding
e-th powers. Such rescalings preserve generation of both localized maximal ideals.

Contract u_i^N into the singular ideal along the faithfully flat Artinian coefficient
map. Lift the coefficients to L, correct the error modulo m_L^n using
m_L^n <= m_L^(n-N) times the singular ideal, and multiply by u_i^N. Clear coefficient
and equality denominators in Lambda. This gives (delta_i u_i)^(2N) = sum lambda_ij a_j.
Use 07FI to adjoin suitable positive powers of the clearing units to the Artinian model.
Ogoma on Lambda modulo preceding e-th powers gives its kernel equalities; use 07FI again
to include the new rescaling units and coefficients. All earlier conditions persist.

Map t_i to delta_i in Lambda and set ell = lambda. Append zero to the list (u_i t_i)^c.
Induction from equality of first and square kernels gives equality for all positive
powers, hence the displayed c-th-power kernels. Set I0 = p^n R and K = m_L^n.
The t_i are units in Q. The pigeonhole bound for d generators,
m_L^(d(e-1)+1) <= (u_i^e)L, and its polynomial analogue give the ideal containments.
The extension of p to L is m_L, so I0 extends into K. When d = 0 the maximal ideal
is zero and n = N > 0, so the same assertions hold.

Let D' be the enlarged local Artinian coefficient ring. Its faithfully flat local map
to L/K is injective. The images of A and all lambda_ij and delta_i lie in D'; this
gives f0 and lambda. Each delta_i is a unit in D' because the coefficient map is local
and its image is outside the maximal ideal. Put E = D'[t_i]. Its R/I0-algebra is
essentially smooth: R/I0 maps by localization to the polynomial ring over the localized
prime-power quotient, and D' is essentially smooth over that quotient. Apply polynomial
base change and composition. Evaluation at the delta_i defines b; its restriction to
constants is the injective coefficient map. The defining R and S maps give image(X_i)
= C(u_i)t_i, and evaluation gives b(t_i) = b(C(delta_i)). The inclusions of A and the
lambda_ij give the final two image formulas. Present the finite smooth algebras and
transport their localizations to Type(max u v), then reindex the finite polynomial
variables to Fin m. No polynomial coefficient equation in E is asserted here: these
are proved separately by contraction and division by delta_i^(2N). -/
theorem exists_popescu_parameter_coefficient_model
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
    (c : ℕ) (hc : 0 < c) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ)
      (ell : Fin d × Fin s → Λ) (π : Fin (d + 1) → MvPolynomial (Fin m) k),
      (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
        ∑ j : Fin s, ell (i, j) * α (a j)) ∧
      (∀ i, π i = 0 ∨ ∃ j : Fin d,
        π i = algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X j ^ c)) ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin (d + 1))
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin (d + 1))
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin (d + 1) ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I₀ : Ideal R) (K : Ideal L),
        I₀.map (algebraMap R Q) ≤ JQ ∧ K ≤ JL ∧
        (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K ∧
        ∃ (D' : Type (max u v)) (_ : CommRing D')
          (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D'),
          let E := MvPolynomial (Fin d) D'
          ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
            (_ : IsScalarTower R (R ⧸ I₀) E)
            (algSE : Algebra S E) (_ : IsScalarTower S R E)
            (_ : Algebra k E) (_ : IsScalarTower k S E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (_ : IsScalarTower k D' E)
              (f₀ : A →ₐ[k] D') (b : E →ₐ[R] L ⧸ K)
              (u₀ : Fin d → D') (δ : Fin d → D'ˣ) (coeff : Fin d × Fin s → D'),
              Function.Injective (fun z : D' ↦ b (MvPolynomial.C z)) ∧
              (∀ i : Fin d, @algebraMap S E _ _ algSE (MvPolynomial.X (R := k) i) =
                MvPolynomial.C (σ := Fin d) (u₀ i) * MvPolynomial.X (R := D') i) ∧
              (∀ i : Fin d, b (MvPolynomial.X i) = b (MvPolynomial.C (δ i : D'))) ∧
              (∀ x, b (MvPolynomial.C (f₀ x)) =
                Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
              (∀ ij, b (MvPolynomial.C (coeff ij)) =
                Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  classical
  obtain ⟨r, f, hf, _⟩ := FinitePresentation.out (R := k) (A := A)
  let n₀ := N + d * (8 * c)
  have hn₀ : 1 ≤ n₀ := by dsimp [n₀]; omega
  let ρ : Fin r → Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^ n₀ :=
    fun i ↦ Ideal.Quotient.mk _
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i))))
  obtain ⟨m₀, φ₀, ψ₀, hψ₀, hideal₀, hflat₀, localP₀, artP₀, localB₀, artB₀,
    D₀, ringD₀, algD₀, g₀, localD₀, artD₀, localAlgD₀, localg₀,
    hsmooth₀, hgflat₀, hfactor₀, hinc₀⟩ :=
    exists_essentiallySmooth_artinian_factorization_mod_prime_pow
      k Λ p hp hreg q.asIdeal n₀ hn₀ (Finset.univ.image ρ)
  let : CommRing D₀ := ringD₀
  let : IsLocalRing D₀ := localD₀
  let : IsArtinianRing D₀ := artD₀
  let : Algebra _ D₀ := algD₀
  let : IsLocalHom (algebraMap _ D₀) := localAlgD₀
  let : IsLocalHom g₀ := localg₀
  have hgenerators : ∀ i : Fin r, ρ i ∈ Set.range g₀ := by
    intro i
    exact hinc₀ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  obtain ⟨m, algR, towerkR, algSR, towerkSR, algSL, towerSRL, towerkSL,
    ell, τ, heq, hτ, hq, hkerR, hkerΛ, n, hn, hbound, I₀, K,
    hI₀, hK, hIK, D', ringD, localD, artD, algkD, algRE, algQE,
    towerRQE, algSE, towerSRE, algkE, towerkSE, hsmooth,
    towerkDE, f₀, g, u₀, δ, coeff, localB, localg, hgflat, hX, hcompat, hf₀, hcoeff⟩ :=
    exists_popescu_rescaled_coefficient_chart p hp α q hreg N hN hpower d hd s a ha c hc
      r f hf m₀ φ₀ ψ₀ hψ₀ hideal₀ hflat₀ D₀ g₀ hsmooth₀ hgflat₀ hfactor₀ hgenerators
  let R := MvPolynomial (Fin m) k
  let S := MvPolynomial (Fin d) k
  let L := Localization.AtPrime q.asIdeal
  let E := MvPolynomial (Fin d) D'
  let : CommRing D' := ringD
  let : IsLocalRing D' := localD
  let : IsArtinianRing D' := artD
  let : Algebra R Λ := algR
  let : IsScalarTower k R Λ := towerkR
  let : Algebra S R := algSR
  let : IsScalarTower k S R := towerkSR
  let : Algebra S Λ := algSL
  let : IsScalarTower S R Λ := towerSRL
  let : IsScalarTower k S Λ := towerkSL
  let : Algebra k D' := algkD
  let : Algebra R E := algRE
  let : Algebra (R ⧸ I₀) E := algQE
  let : IsScalarTower R (R ⧸ I₀) E := towerRQE
  let : Algebra S E := algSE
  let : IsScalarTower S R E := towerSRE
  let : Algebra k E := algkE
  let : IsScalarTower k S E := towerkSE
  let : IsScalarTower k D' E := towerkDE
  let : IsLocalRing (L ⧸ K) := localB
  let : IsLocalHom g := localg
  let π : Fin (d + 1) → R := fun i ↦ τ i ^ c
  have hπ (i : Fin (d + 1)) : π i = 0 ∨
      ∃ j : Fin d, π i = algebraMap S R (MvPolynomial.X j ^ c) := by
    rcases hτ i with hzero | ⟨j, hj⟩
    · left
      simp [π, hzero, Nat.ne_of_gt hc]
    · right
      refine ⟨j, ?_⟩
      exact (congrArg (fun z : R ↦ z ^ c) hj).trans
        (map_pow (algebraMap S R) (MvPolynomial.X j) c).symm
  have hπq (i : Fin (d + 1)) : algebraMap R Λ (π i) ∈ q.asIdeal := by
    simpa only [π, map_pow] using q.asIdeal.pow_mem_of_mem (hq i) c hc
  have hJR (i : Fin (d + 1)) :
      Ideal.span {y : R | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ 8} =
      Ideal.span {y : R | ∃ j : Fin (d + 1), j.val < i.val ∧ y = τ j ^ (c * 8)} := by
    congr 1
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, (pow_mul (τ j) c 8).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, pow_mul (τ j) c 8⟩
  have hJΛ (i : Fin (d + 1)) :
      Ideal.span {y : Λ | ∃ j : Fin (d + 1), j.val < i.val ∧
        y = algebraMap R Λ (π j) ^ 8} =
      Ideal.span {y : Λ | ∃ j : Fin (d + 1), j.val < i.val ∧
        y = algebraMap R Λ (τ j) ^ (c * 8)} := by
    congr 1
    ext y
    have hp (j : Fin (d + 1)) :
        algebraMap R Λ (π j) ^ 8 = algebraMap R Λ (τ j) ^ (c * 8) := by
      rw [show π j = τ j ^ c from rfl, map_pow, ← pow_mul]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, hp j⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, (hp j).symm⟩
  have hπkerR (i : Fin (d + 1))
      (x : R ⧸ Ideal.span {y | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ 8}) :
      π i • x = 0 ↔ π i ^ 2 • x = 0 := by
    revert x
    rw [hJR i]
    intro x
    change τ i ^ c • x = 0 ↔ (τ i ^ c) ^ 2 • x = 0
    rw [← pow_mul]
    exact (kernel_pow_eq_kernel (τ i) (hkerR i) c hc x).trans
      (kernel_pow_eq_kernel (τ i) (hkerR i) (c * 2) (by omega) x).symm
  have hπkerΛ (i : Fin (d + 1))
      (x : Λ ⧸ Ideal.span {y | ∃ j : Fin (d + 1), j.val < i.val ∧
        y = algebraMap R Λ (π j) ^ 8}) :
      π i • x = 0 ↔ π i ^ 2 • x = 0 := by
    revert x
    rw [hJΛ i]
    intro x
    change τ i ^ c • x = 0 ↔ (τ i ^ c) ^ 2 • x = 0
    rw [← pow_mul]
    exact (kernel_pow_eq_kernel (τ i) (hkerΛ i) c hc x).trans
      (kernel_pow_eq_kernel (τ i) (hkerΛ i) (c * 2) (by omega) x).symm
  let ev : E →+* L ⧸ K := MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D'))
  let b : E →ₐ[R] L ⧸ K := { ev with commutes' := hcompat }
  have hinjg : Function.Injective g := by
    let : Algebra D' (L ⧸ K) := g.toAlgebra
    let : IsLocalHom (algebraMap D' (L ⧸ K)) := localg
    have : Module.Flat D' (L ⧸ K) := hgflat
    have : Module.FaithfullyFlat D' (L ⧸ K) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective D' (L ⧸ K)
  have hbC (z : D') : b (MvPolynomial.C z) = g z := by
    exact MvPolynomial.eval₂Hom_C g _ z
  refine ⟨m, algR, towerkR, algSR, towerkSR, algSL, towerSRL, towerkSL,
    ell, π, heq, hπ, hπq, hπkerR, hπkerΛ, n, hn, ?_, I₀, K,
    ?_, ?_, hIK, D', ringD, localD, artD, algkD, algRE, algQE,
    towerRQE, algSE, towerSRE, algkE, towerkSE, hsmooth,
    towerkDE, f₀, b, u₀, δ, coeff, ?_, hX, ?_, ?_, ?_⟩
  · simpa only [π, ← pow_mul] using hbound
  · simpa only [π, ← pow_mul] using hI₀
  · simpa only [π, ← pow_mul] using hK
  · intro x y hxy
    apply hinjg
    exact (hbC x).symm.trans (hxy.trans (hbC y))
  · intro i
    exact (MvPolynomial.eval₂Hom_X' g _ i).trans (hbC (δ i : D')).symm
  · intro x
    exact (hbC (f₀ x)).trans (hf₀ x)
  · intro ij
    exact (hbC (coeff ij)).trans (hcoeff ij)

end Algebra
