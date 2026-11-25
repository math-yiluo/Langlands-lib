/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The Nullstellensatz for finitely generated algebras

Let `A` be a finitely generated algebra over an algebraically closed field `k`. Every maximal ideal
of `A` is the kernel of a `k`-algebra map `A →ₐ[k] k`, i.e. closed points of `Spec A` have residue
field `k`; and an element of `A` vanishing at every `k`-point is nilpotent.

## Main results

- `exists_algHom_ker_eq_of_isMaximal`: maximal ideals are kernels of `k`-points.
- `iInf_ker_algHom_eq_nilradical`: the vanishing principle.
- `eq_zero_of_forall_algHom_apply_eq_zero`: the vanishing principle on a reduced algebra.
- `existsUnique_comp_mkₐ_eq_of_forall_algHom`: a regular map sending `k`-points into a closed
  subvariety factors through it.
- `Algebra.TensorProduct.eq_zero_of_forall_lift_algHom_eq_zero`: the vanishing principle on a
  product of affine varieties.

## Blueprint

- `det-i-geometry`: the Nullstellensatz and the vanishing principle.
- `lem-wf-affine-nullstellensatz-vanishing`: residue fields of closed points and the vanishing
  principle.
- `lem-wf-affine-product-reduced`: the vanishing principle on a product of reduced affine
  varieties. Its reducedness clause holds over any perfect field, see
  `isReduced_tensorProduct_of_perfectField`.
-/

@[expose] public section

variable (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Over an algebraically closed field `k`, every maximal ideal of a finitely generated
`k`-algebra is the kernel of a `k`-algebra map to `k`: closed points have residue field `k`.
(blueprint: `det-i-geometry`) -/
theorem exists_algHom_ker_eq_of_isMaximal (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ φ : A →ₐ[k] k, RingHom.ker φ = 𝔪 := by
  let : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite k (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k _
  refine ⟨(IsAlgClosed.lift : (A ⧸ 𝔪) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k 𝔪), ?_⟩
  ext a
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The vanishing principle: over an algebraically closed field `k`, an element of a finitely
generated `k`-algebra vanishing at every `k`-point is nilpotent.
(blueprint: `det-i-geometry`) -/
theorem iInf_ker_algHom_eq_nilradical :
    (⨅ φ : A →ₐ[k] k, RingHom.ker φ) = nilradical A := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  refine le_antisymm ?_ ?_
  · rw [nilradical, Ideal.radical_eq_jacobson, Ideal.jacobson]
    refine le_sInf ?_
    rintro 𝔪 ⟨-, h𝔪⟩
    obtain ⟨φ, rfl⟩ := exists_algHom_ker_eq_of_isMaximal k A 𝔪
    exact iInf_le _ φ
  · exact le_iInf fun φ ↦ @nilradical_le_prime _ _ _ (RingHom.ker_isPrime φ)

/-- Blueprint `lem-wf-affine-nullstellensatz-vanishing`, clause (2) (the vanishing principle): over
an algebraically closed field `k`, an element of a reduced finitely generated `k`-algebra vanishing
at every `k`-point is zero.

By `iInf_ker_algHom_eq_nilradical` such an element is nilpotent, hence zero. Clause (1), that the
closed points are the `k`-points, is `exists_algHom_ker_eq_of_isMaximal`. -/
theorem eq_zero_of_forall_algHom_apply_eq_zero [IsReduced A] {a : A}
    (h : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 := by
  have : a ∈ nilradical A := by
    rw [← iInf_ker_algHom_eq_nilradical k A, Ideal.mem_iInf]
    exact fun φ ↦ h φ
  rwa [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.mem_bot] at this

/-- Blueprint `lem-wf-affine-nullstellensatz-vanishing`, clause (3): let `f : B →ₐ[k] A` be the
coordinate map of a regular map `X → Y` of affine varieties over an algebraically closed field `k`,
with `A` reduced and finitely generated, and let `J` be an ideal of `B` (cutting out `Z ⊆ Y`). If
every `k`-point of `X` maps into `Z`, i.e. `φ (f b) = 0` for every `k`-point `φ` of `X` and
`b ∈ J`, then `f` factors uniquely through `B ⧸ J`.

Each `f b` with `b ∈ J` vanishes at every `k`-point, so it is zero by the vanishing principle
`eq_zero_of_forall_algHom_apply_eq_zero`; uniqueness holds as `B → B ⧸ J` is surjective. -/
theorem existsUnique_comp_mkₐ_eq_of_forall_algHom {B : Type*} [CommRing B] [Algebra k B]
    [IsReduced A] (f : B →ₐ[k] A) (J : Ideal B) (h : ∀ φ : A →ₐ[k] k, ∀ b ∈ J, φ (f b) = 0) :
    ∃! g : B ⧸ J →ₐ[k] A, g.comp (Ideal.Quotient.mkₐ k J) = f := by
  have hJ (b : B) (hb : b ∈ J) : f b = 0 :=
    eq_zero_of_forall_algHom_apply_eq_zero k A fun φ ↦ h φ b hb
  refine ⟨Ideal.Quotient.liftₐ J f hJ, by ext; simp, fun g hg ↦ ?_⟩
  exact Ideal.Quotient.algHom_ext k (by rw [hg]; ext; simp)


open TensorProduct in
/-- Blueprint `lem-wf-affine-product-reduced`: let `A` and `B` be reduced finitely generated
algebras over an algebraically closed field `k`, the coordinate algebras of affine varieties `X`
and `Y`. The `k`-points of `X × Y = Spec (A ⊗[k] B)` are the pairs `(φ, ψ)` of `k`-points, and a
function on `X × Y` vanishing at all of them is zero.

Evaluating the first factor at a `k`-point `φ` of `X` sends `t` to a function on `Y`, which
vanishes at every `k`-point of `Y` and hence is zero by the vanishing principle for `B`. As the
evaluations at `k`-points of `X` are jointly injective on `A` (the vanishing principle for `A`),
`t = 0` by `TensorProduct.eq_zero_of_forall_rTensor_eq_zero`. In particular `A ⊗[k] B` is reduced,
which holds more generally over a perfect field (`isReduced_tensorProduct_of_perfectField`). -/
theorem Algebra.TensorProduct.eq_zero_of_forall_lift_algHom_eq_zero (B : Type*) [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [IsReduced A] [IsReduced B] {t : A ⊗[k] B}
    (h : ∀ (φ : A →ₐ[k] k) (ψ : B →ₐ[k] k), lift φ ψ (fun _ _ ↦ .all _ _) t = 0) : t = 0 := by
  refine TensorProduct.eq_zero_of_forall_rTensor_eq_zero (fun φ : A →ₐ[k] k ↦ φ.toLinearMap)
    (fun a ha ↦ eq_zero_of_forall_algHom_apply_eq_zero k A ha) fun φ ↦ ?_
  have key (ψ : B →ₐ[k] k) (t : A ⊗[k] B) :
      ψ (TensorProduct.lid k B (φ.toLinearMap.rTensor B t)) = lift φ ψ (fun _ _ ↦ .all _ _) t := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  simpa using eq_zero_of_forall_algHom_apply_eq_zero k B fun ψ ↦ (key ψ t).trans (h φ ψ)

namespace MvPolynomial

/-- The translation automorphism `X i ↦ X i + C (c i)` of `MvPolynomial σ R`. -/
noncomputable def translateAlgEquiv {R σ : Type*} [CommRing R] (c : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun i ↦ X i + C (c i)) (aeval fun i ↦ X i - C (c i))
    (algHom_ext fun i ↦ by simp) (algHom_ext fun i ↦ by simp)

/-- Evaluating a translated polynomial at `x` is evaluating the polynomial at `x + c`. -/
@[simp]
lemma eval_translateAlgEquiv {R σ : Type*} [CommRing R] (c x : σ → R) (p : MvPolynomial σ R) :
    eval x (translateAlgEquiv c p) = eval (x + c) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [translateAlgEquiv]
  | add p q hp hq => simp_all
  | mul_X p i hp => simp_all [translateAlgEquiv]

/-- The ideals of any two points of affine space have the same height: they are exchanged by a
translation automorphism. -/
lemma height_vanishingIdeal_singleton {k σ : Type*} [Field k] (a b : σ → k) :
    (vanishingIdeal k {a}).height = (vanishingIdeal k {b}).height := by
  rw [← RingEquiv.height_comap (translateAlgEquiv (b - a)).toRingEquiv]
  congr 1
  ext p
  simp

end MvPolynomial

/-- **Affine dimension theorem, homogeneous form.** Over an algebraically closed field, finitely
many polynomials without constant term in more variables than there are polynomials have a
common nontrivial zero. This follows from Krull's height theorem: otherwise the ideal they
generate would have the ideal of the origin, of height `Nat.card σ`, as its radical. -/
theorem MvPolynomial.exists_ne_zero_forall_eval_eq_zero {k σ ι : Type*} [Field k] [IsAlgClosed k]
    [Finite σ] [Finite ι] (f : ι → MvPolynomial σ k) (hf : ∀ i, constantCoeff (f i) = 0)
    (hcard : Nat.card ι < Nat.card σ) : ∃ x : σ → k, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  by_contra! H
  set I := Ideal.span (Set.range f)
  have hI : I ≤ vanishingIdeal k {(0 : σ → k)} := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simp [hf]
  have hzero : zeroLocus k I = {0} := by
    ext x
    refine ⟨fun hx ↦ ?_, ?_⟩
    · by_contra hx0
      obtain ⟨i, hi⟩ := H x hx0
      exact hi (hx _ (Ideal.subset_span ⟨i, rfl⟩))
    · rintro rfl p hp
      simpa using hI hp
  have hrad : I.radical = vanishingIdeal k {(0 : σ → k)} := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k), hzero]
  -- the ideal of the origin is minimal over `I`, so has height at most `Nat.card ι`
  have hmin : vanishingIdeal k {(0 : σ → k)} ∈ I.minimalPrimes := by
    refine ⟨⟨(isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨0, rfl⟩).isPrime, hI⟩,
      fun q ⟨hq, hIq⟩ _ ↦ ?_⟩
    rw [← hrad]
    exact (Ideal.IsPrime.radical_le_iff hq).mpr hIq
  have hheight := Ideal.height_le_ncard_of_mem_minimalPrimes_span (Set.finite_range f) hmin
  -- hence so does every maximal ideal, contradicting `dim k[σ] = Nat.card σ`
  have hdim : ringKrullDim (MvPolynomial σ k) ≤ (Nat.card ι : ℕ∞) := by
    refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun m hm ↦ ?_
    obtain ⟨a, rfl⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.mp hm
    rw [height_vanishingIdeal_singleton a 0]
    exact WithBot.coe_le_coe.mpr (hheight.trans (by exact_mod_cast Finite.card_range_le f))
  rw [ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add] at hdim
  exact absurd hdim (by exact_mod_cast hcard.not_ge)
