/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Nilpotent.Defs
public import WeilConjectures.Mathlib.Algebra.MvPolynomial.PDeriv
public import WeilConjectures.Mathlib.RingTheory.Derivation.Basic
public import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.RingTheory.KrullDimension.FiniteType
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-!
# Cartier's theorem: Hopf algebras in characteristic zero are reduced

A finitely generated commutative Hopf algebra `A` over a field `k` of characteristic zero is
reduced (Cartier). Geometrically: an affine group scheme of finite type over `k` is reduced.

We follow the invariant derivation argument (Waterhouse, *Introduction to affine group schemes*,
§11.4). Let `ε : A → k` be the counit with augmentation ideal `I`, and choose `x₁, …, xₙ ∈ I`
lifting a basis of `I / I²`. Every tangent vector `d` at the identity extends to the invariant
derivation `a ↦ ∑ a₁ d(a₂)` of `A`; derivations `Dⱼ` with `ε (Dⱼ xᵢ) = δᵢⱼ` lower the `I`-adic
order by one, so by Euler's identity a homogeneous polynomial `f` of degree `r` with
`f(x) ∈ I ^ (r + 1)` vanishes in characteristic zero. Hence the associated graded ring of `I` is a
polynomial ring, `⋂ₙ Iⁿ` is a prime ideal, and by Krull's intersection theorem every nilpotent of
`A` vanishes in the local ring at the identity. Translating by `k`-points (the convolution group
of `k`-points acts on `A` by algebra automorphisms) moves this to every `k`-point, so over an
algebraically closed field `A` is reduced; the general case follows by base change.

This proves the blueprint's *Cartier step* `𝔫 ⊆ 𝔪²` in a stronger form, and replaces the passage
through the smoothness of the reduced group by the invariant derivations.

## Main results

- `AlgHom.isPrime_iInf_pow_ker_of_forall_exists_derivation`: Cartier's lemma for a `k`-point of a
  Noetherian `k`-algebra whose tangent vectors extend to derivations.
- `Bialgebra.exists_derivation_of_cotangent`: invariant derivations of a commutative bialgebra.
- `HopfAlgebra.isPrime_iInf_pow_ker`: the functions vanishing near a `k`-point of a Noetherian
  commutative Hopf algebra in characteristic zero form a prime ideal.
- `HopfAlgebra.isReduced_of_charZero`: Cartier's theorem.
- `Ideal.IsHopfIdeal.isRadical`: Hopf ideals are radical in characteristic zero.
- `AlgHom.finrank_cotangent_le_ringKrullDim`, `AlgHom.height_ker_liftEquiv_le`: the cotangent
  space at a rational point bounds the dimension, and the height of the point after base change.
- `HopfAlgebra.finrank_cotangent_eq_ringKrullDim`: the cotangent space at the identity has the
  dimension of the group.

## Blueprint

- `proposition-cartier-s-theorem`: Cartier's theorem.
- `lemma-connected-components-images-homomorphisms--3`: the dimension clause (2).
-/

@[expose] public section

open MvPolynomial

/-! ### Cartier's argument

Let `ε : A → k` be a `k`-point of a `k`-algebra `A` with augmentation ideal `I = ker ε`. Suppose
that `x₁, …, xₙ ∈ I` span `I / I²` and that there are derivations `D₁, …, Dₙ` of `A` with
`ε (Dⱼ xᵢ) = δᵢⱼ` (invariant vector fields, for a Hopf algebra). In characteristic zero, a
homogeneous polynomial `f` of degree `r` with `f(x) ∈ I ^ (r + 1)` vanishes: differentiating
lowers the degree, and Euler's identity recovers `f` from its partial derivatives. So the
associated graded ring of `A` for `I` is a polynomial ring, and `⋂ₙ Iⁿ` is a prime ideal. -/

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {ε : A →ₐ[k] k}
  {ι : Type*} {x : ι → A} (hx : ∀ i, x i ∈ RingHom.ker ε)

include hx in
/-- If the homogeneous components of `f` of degree `< r` vanish, then `f(x) ∈ I ^ r`. -/
theorem aeval_mem_pow_of_homogeneousComponent_eq_zero {r : ℕ} {f : MvPolynomial ι k}
    (hf : ∀ m < r, homogeneousComponent m f = 0) : aeval x f ∈ RingHom.ker ε ^ r := by
  rw [← sum_homogeneousComponent f, map_sum]
  refine Ideal.sum_mem _ fun m _ ↦ ?_
  by_cases hm : m < r
  · rw [hf m hm, map_zero]
    exact zero_mem _
  · exact Ideal.pow_le_pow_right (not_lt.1 hm)
      ((homogeneousComponent_isHomogeneous m f).aeval_mem_pow hx)

section Spanning

variable [Fintype ι] (hspan : ∀ a ∈ RingHom.ker ε, ∃ c : ι → k,
    a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2)

include hx hspan in
/-- Modulo `I ^ (r + 1)`, every element of `I ^ r` is a homogeneous polynomial of degree `r` in
the `xᵢ`. -/
theorem exists_isHomogeneous_sub_aeval_mem_pow_succ {r : ℕ} {a : A}
    (ha : a ∈ RingHom.ker ε ^ r) :
    ∃ f : MvPolynomial ι k, f.IsHomogeneous r ∧ a - aeval x f ∈ RingHom.ker ε ^ (r + 1) := by
  induction r generalizing a with
  | zero => exact ⟨C (ε a), isHomogeneous_C _ _, by simp [ε.sub_algebraMap_mem_ker a]⟩
  | succ r ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun a ha b hb ↦ ?_) ?_
    · obtain ⟨f, hf, ha'⟩ := ih ha
      obtain ⟨c, hb'⟩ := hspan b hb
      refine ⟨f * ∑ i, C (c i) * X i,
        hf.mul (IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_C_mul_X _ _), ?_⟩
      set s := ∑ i, algebraMap k A (c i) * x i
      have hs : aeval x (∑ i, C (c i) * X i) = s := by simp [s]
      have hsI : s ∈ RingHom.ker ε := Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hx i)
      have hF := hf.aeval_mem_pow hx
      rw [map_mul, hs, show a * b - aeval x f * s = (a - aeval x f) * s + aeval x f * (b - s) +
        (a - aeval x f) * (b - s) by ring]
      refine add_mem (add_mem ?_ ?_) ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ha' hsI
      · rw [show r + 1 + 1 = r + 2 by ring, pow_add]
        exact Ideal.mul_mem_mul hF hb'
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ha' (Ideal.pow_le_self two_ne_zero hb')
    · rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
      refine ⟨f + g, hf.add hg, ?_⟩
      rw [map_add, add_sub_add_comm]
      exact add_mem ha hb

end Spanning

section Graded

variable [CharZero k] [DecidableEq ι] {D : ι → Derivation k A A}
  (hD : ∀ i j, ε (D j (x i)) = if i = j then 1 else 0)

include hx hD in
/-- **Cartier's lemma**: in characteristic zero, a homogeneous polynomial `f` of degree `r` with
`f(x) ∈ I ^ (r + 1)` is zero. -/
theorem eq_zero_of_isHomogeneous_of_aeval_mem_pow_succ [_root_.Finite ι] {r : ℕ}
    {f : MvPolynomial ι k} (hf : f.IsHomogeneous r)
    (hfx : aeval x f ∈ RingHom.ker ε ^ (r + 1)) : f = 0 := by
  have := Fintype.ofFinite ι
  induction r generalizing f with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c, f = C c :=
      ⟨_, totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hf)⟩
    simp [RingHom.mem_ker] at hfx
    simp [hfx]
  | succ r ih =>
    have hpd (j : ι) : pderiv j f = 0 := by
      have hf' (i : ι) : (pderiv i f).IsHomogeneous r := by simpa using hf.pderiv (i := i)
      refine ih (hf' j) ?_
      have h1 := (D j).map_mem_pow_of_mem_pow_succ hfx
      rw [(D j).map_aeval_eq_sum] at h1
      have h2 : ∑ i, aeval x (pderiv i f) * (D j (x i) - algebraMap k A (ε (D j (x i)))) ∈
          RingHom.ker ε ^ (r + 1) :=
        Ideal.sum_mem _ fun i _ ↦ by
          rw [pow_succ]
          exact Ideal.mul_mem_mul ((hf' i).aeval_mem_pow hx) (ε.sub_algebraMap_mem_ker _)
      have h3 : aeval x (pderiv j f) = ∑ i, aeval x (pderiv i f) * D j (x i) -
          ∑ i, aeval x (pderiv i f) * (D j (x i) - algebraMap k A (ε (D j (x i)))) := by
        rw [← Finset.sum_sub_distrib]
        simp_rw [mul_sub, sub_sub_cancel, hD, apply_ite (algebraMap k A), map_one, map_zero,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [h3]
      exact sub_mem h1 h2
    have h := hf.sum_X_mul_pderiv
    simp only [hpd, mul_zero, Finset.sum_const_zero] at h
    rw [eq_comm, nsmul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero r))

include hx hD in
/-- In characteristic zero, the `xᵢ` are algebraically independent modulo `⋂ₙ Iⁿ`: if `f(x)`
lies in every power of `I`, then by Cartier's lemma every homogeneous component of `f`
vanishes, by induction on the degree. -/
theorem algebraicIndependent_mk_iInf_pow_ker [_root_.Finite ι] :
    AlgebraicIndependent k
      (fun i ↦ Ideal.Quotient.mkₐ k (⨅ r : ℕ, RingHom.ker ε ^ r) (x i)) := by
  rw [_root_.algebraicIndependent_iff]
  intro p hp
  rw [← MvPolynomial.comp_aeval_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hp
  have hcomp (n : ℕ) : homogeneousComponent n p = 0 := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      refine eq_zero_of_isHomogeneous_of_aeval_mem_pow_succ hx hD
        (homogeneousComponent_isHomogeneous n p) ?_
      have h1 : aeval x (p - homogeneousComponent n p) ∈ RingHom.ker ε ^ (n + 1) := by
        refine aeval_mem_pow_of_homogeneousComponent_eq_zero hx fun m hm ↦ ?_
        rw [map_sub, homogeneousComponent_of_mem (homogeneousComponent_mem n p)]
        rcases (Nat.lt_succ_iff.1 hm).lt_or_eq with hm | rfl
        · rw [ih m hm, ite_eq_right hm.ne, sub_zero]
        · rw [ite_eq_left rfl, sub_self]
      have h2 := sub_mem (Submodule.mem_iInf _ |>.1 hp (n + 1)) h1
      rwa [map_sub, sub_sub_cancel] at h2
  rw [← sum_homogeneousComponent p]
  exact Finset.sum_eq_zero fun n _ ↦ hcomp n

end Graded

variable [Fintype ι] (hspan : ∀ a ∈ RingHom.ker ε, ∃ c : ι → k,
    a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2)
  [CharZero k] [DecidableEq ι] {D : ι → Derivation k A A}
  (hD : ∀ i j, ε (D j (x i)) = if i = j then 1 else 0)

include hx hspan hD in
/-- The `I`-adic order is additive: the associated graded ring of `I` is a domain. -/
theorem mul_notMem_pow_add_add_one {a b : A} {r s : ℕ} (ha : a ∈ RingHom.ker ε ^ r)
    (ha' : a ∉ RingHom.ker ε ^ (r + 1)) (hb : b ∈ RingHom.ker ε ^ s)
    (hb' : b ∉ RingHom.ker ε ^ (s + 1)) : a * b ∉ RingHom.ker ε ^ (r + s + 1) := by
  obtain ⟨f, hf, hfa⟩ := exists_isHomogeneous_sub_aeval_mem_pow_succ hx hspan ha
  obtain ⟨g, hg, hgb⟩ := exists_isHomogeneous_sub_aeval_mem_pow_succ hx hspan hb
  intro hab
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact ha' (by simpa using hfa)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hb' (by simpa using hgb)
  refine mul_ne_zero hf0 hg0 (eq_zero_of_isHomogeneous_of_aeval_mem_pow_succ hx hD (hf.mul hg) ?_)
  rw [show aeval x (f * g) = a * b - ((a - aeval x f) * b + aeval x f * (b - aeval x g)) by
    rw [map_mul]; ring]
  refine sub_mem hab (add_mem ?_ ?_)
  · rw [show r + s + 1 = r + 1 + s by ring, pow_add]
    exact Ideal.mul_mem_mul hfa hb
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul (hf.aeval_mem_pow hx) hgb

include hx hspan hD in
/-- The intersection of the powers of the augmentation ideal is a prime ideal. -/
theorem isPrime_iInf_pow_ker : (⨅ r : ℕ, RingHom.ker ε ^ r).IsPrime := by
  refine ⟨ne_top_of_le_ne_top ?_ (iInf_le _ 1), fun {a b} hab ↦ ?_⟩
  · rw [pow_one, Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact one_ne_zero
  by_contra! h
  obtain ⟨r, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ_of_notMem_iInf h.1
  obtain ⟨s, hb, hb'⟩ := Ideal.exists_mem_pow_notMem_pow_succ_of_notMem_iInf h.2
  exact mul_notMem_pow_add_add_one hx hspan hD ha ha' hb hb' (Submodule.mem_iInf _ |>.1 hab _)

end AlgHom

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k)

/-- On the cotangent space at a `k`-point `ε`, the ring `A` acts through `ε`. -/
theorem smul_cotangent_eq (a : A) (v : (RingHom.ker ε).Cotangent) :
    a • v = ε a • v := by
  rw [← algebraMap_smul A (ε a) v, ← sub_eq_zero, ← sub_smul]
  exact Ideal.Cotangent.smul_eq_zero_of_mem (ε.sub_algebraMap_mem_ker a) v

/-- The cotangent space at a `k`-point of a Noetherian `k`-algebra is finite-dimensional. -/
theorem finiteDimensional_cotangent [IsNoetherianRing A] :
    FiniteDimensional k (RingHom.ker ε).Cotangent := by
  have : Module.Finite A (RingHom.ker ε).Cotangent :=
    .of_surjective _ (RingHom.ker ε).toCotangent_surjective
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := (RingHom.ker ε).Cotangent)
  refine ⟨⟨S, eq_top_iff.2 fun v _ ↦ ?_⟩⟩
  let N : Submodule A (RingHom.ker ε).Cotangent :=
    { carrier := Submodule.span k (S : Set (RingHom.ker ε).Cotangent)
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun a v hv ↦ by
        rw [ε.smul_cotangent_eq]
        exact Submodule.smul_mem _ _ hv }
  have : Submodule.span A (S : Set (RingHom.ker ε).Cotangent) ≤ N :=
    Submodule.span_le.2 fun s hs ↦ Submodule.subset_span hs
  exact this (hS ▸ Submodule.mem_top)

/-- Lifts `xᵢ ∈ I` of a basis of the cotangent space `I / I²` at a `k`-point `ε` span `I` modulo
`I²`; if every tangent vector at `ε` extends to a derivation, there are moreover derivations
`Dⱼ` with `ε (Dⱼ xᵢ) = δᵢⱼ`. -/
theorem exists_spanning_and_derivation [IsNoetherianRing A]
    (hD : ∀ φ : (RingHom.ker ε).Cotangent →ₗ[k] k, ∃ D : Derivation k A A,
      ∀ a (ha : a ∈ RingHom.ker ε), ε (D a) = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩)) :
    ∃ (x : Fin (Module.finrank k (RingHom.ker ε).Cotangent) → A)
      (D : Fin (Module.finrank k (RingHom.ker ε).Cotangent) → Derivation k A A),
      (∀ i, x i ∈ RingHom.ker ε) ∧
      (∀ a ∈ RingHom.ker ε, ∃ c : Fin (Module.finrank k (RingHom.ker ε).Cotangent) → k,
        a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2) ∧
      ∀ i j, ε (D j (x i)) = if i = j then 1 else 0 := by
  classical
  have := ε.finiteDimensional_cotangent
  set I := RingHom.ker ε
  let B := Module.finBasis k I.Cotangent
  choose y hy using fun i ↦ I.toCotangent_surjective (B i)
  choose D hD' using fun j ↦ hD (B.coord j)
  refine ⟨fun i ↦ (y i : A), D, fun i ↦ (y i).2,
    fun a ha ↦ ⟨fun i ↦ B.repr (I.toCotangent ⟨a, ha⟩) i, ?_⟩, fun i j ↦ ?_⟩
  · have h : I.toCotangent (⟨a, ha⟩ - ∑ i, B.repr (I.toCotangent ⟨a, ha⟩) i • y i) = 0 := by
      rw [map_sub, map_sum]
      simp_rw [LinearMap.map_smul_of_tower, hy]
      rw [B.sum_repr, sub_self]
    rw [I.toCotangent_eq_zero] at h
    simpa [Algebra.smul_def] using h
  · rw [hD' j (y i) (y i).2, hy, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]

variable {ε} [CharZero k]

/-- **Cartier's lemma**, invariant derivation form: let `ε` be a `k`-point of a Noetherian
`k`-algebra `A` over a field of characteristic zero, such that every tangent vector at `ε`
extends to a derivation of `A`. Then the intersection of the powers of the ideal of `ε` is a
prime ideal. -/
theorem isPrime_iInf_pow_ker_of_forall_exists_derivation [IsNoetherianRing A]
    (hD : ∀ φ : (RingHom.ker ε).Cotangent →ₗ[k] k, ∃ D : Derivation k A A,
      ∀ a (ha : a ∈ RingHom.ker ε), ε (D a) = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩)) :
    (⨅ r : ℕ, RingHom.ker ε ^ r).IsPrime := by
  classical
  have := ε.finiteDimensional_cotangent
  set I := RingHom.ker ε
  let B := Module.finBasis k I.Cotangent
  choose y hy using fun i ↦ I.toCotangent_surjective (B i)
  choose D hD' using fun j ↦ hD (B.coord j)
  refine isPrime_iInf_pow_ker (x := fun i ↦ (y i : A)) (fun i ↦ (y i).2)
    (fun a ha ↦ ⟨fun i ↦ B.repr (I.toCotangent ⟨a, ha⟩) i, ?_⟩) (D := D) (fun i j ↦ ?_)
  · have h : I.toCotangent (⟨a, ha⟩ - ∑ i, B.repr (I.toCotangent ⟨a, ha⟩) i • y i) = 0 := by
      rw [map_sub, map_sum]
      simp_rw [LinearMap.map_smul_of_tower, hy]
      rw [B.sum_repr, sub_self]
    rw [I.toCotangent_eq_zero] at h
    simpa [Algebra.smul_def] using h
  · rw [hD' j (y i) (y i).2, hy, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]

omit [CharZero k] in
/-- In a Noetherian ring, an element lies in every power of the ideal of a `k`-point `ε` if and
only if it vanishes in the local ring at `ε` (Krull's intersection theorem). -/
theorem mem_iInf_pow_ker_iff [IsNoetherianRing A] {b : A} :
    b ∈ ⨅ r : ℕ, RingHom.ker ε ^ r ↔ ∃ s, ε s = 1 ∧ s * b = 0 := by
  constructor
  · intro hb
    obtain ⟨⟨r, hr⟩, hrb⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (RingHom.ker ε) b).1 (by
      simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hb)
    refine ⟨1 - r, by simp [RingHom.mem_ker.1 hr], ?_⟩
    rw [sub_mul, one_mul, ← smul_eq_mul, hrb, sub_self]
  · rintro ⟨s, hs, hsb⟩
    refine Submodule.mem_iInf _ |>.2 fun r ↦ ?_
    have h1 : 1 - s ∈ RingHom.ker ε := by simp [RingHom.mem_ker, hs]
    have : b = (1 - s) ^ r * b := by
      induction r with
      | zero => simp
      | succ r ih => rw [pow_succ, mul_assoc, sub_mul, hsb, one_mul, sub_zero, ← ih]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h1 r)

/-- **Cartier's lemma**, invariant derivation form: under the assumptions of
`isPrime_iInf_pow_ker_of_forall_exists_derivation`, every nilpotent element of `A` is killed by an
element `s` with `ε s = 1`, that is, it vanishes in the local ring at `ε`. -/
theorem exists_apply_eq_one_mul_eq_zero_of_forall_exists_derivation [IsNoetherianRing A]
    (hD : ∀ φ : (RingHom.ker ε).Cotangent →ₗ[k] k, ∃ D : Derivation k A A,
      ∀ a (ha : a ∈ RingHom.ker ε), ε (D a) = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩))
    {b : A} (hb : IsNilpotent b) : ∃ s, ε s = 1 ∧ s * b = 0 := by
  obtain ⟨n, hn⟩ := hb
  exact mem_iInf_pow_ker_iff.1 ((isPrime_iInf_pow_ker_of_forall_exists_derivation hD).mem_of_pow_mem
    n (hn ▸ zero_mem _))


/-- **Cartier's lemma**, stable-subset form: let `ε` be a `k`-point of a Noetherian `k`-algebra
`A` over a field of characteristic zero, and `W` a set of functions vanishing at `ε`. If every
tangent vector at `ε` extends to a derivation of `A` preserving `W`, then the elements of `W`
lie in every power of the ideal of `ε`: a derivation of an element of `I ^ r ∖ I ^ (r + 1)` in a
suitable direction lies outside `I ^ r`, by Euler's identity. -/
theorem mem_iInf_pow_ker_of_forall_exists_derivation [IsNoetherianRing A] {W : Set A}
    (hW : ∀ a ∈ W, a ∈ RingHom.ker ε)
    (hD : ∀ φ : (RingHom.ker ε).Cotangent →ₗ[k] k, ∃ D : Derivation k A A,
      (∀ a ∈ W, D a ∈ W) ∧
        ∀ a (ha : a ∈ RingHom.ker ε), ε (D a) = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩))
    {a : A} (ha : a ∈ W) : a ∈ ⨅ r : ℕ, RingHom.ker ε ^ r := by
  classical
  have := ε.finiteDimensional_cotangent
  set I := RingHom.ker ε
  let B := Module.finBasis k I.Cotangent
  choose y hy using fun i ↦ I.toCotangent_surjective (B i)
  choose D hDW hD' using fun j ↦ hD (B.coord j)
  set x : Fin (Module.finrank k I.Cotangent) → A := fun i ↦ (y i : A)
  have hx (i) : x i ∈ I := (y i).2
  have hspan : ∀ a ∈ I, ∃ c : Fin (Module.finrank k I.Cotangent) → k,
      a - ∑ i, algebraMap k A (c i) * x i ∈ I ^ 2 := fun a ha ↦ by
    refine ⟨fun i ↦ B.repr (I.toCotangent ⟨a, ha⟩) i, ?_⟩
    have h : I.toCotangent (⟨a, ha⟩ - ∑ i, B.repr (I.toCotangent ⟨a, ha⟩) i • y i) = 0 := by
      rw [map_sub, map_sum]
      simp_rw [LinearMap.map_smul_of_tower, hy]
      rw [B.sum_repr, sub_self]
    rw [I.toCotangent_eq_zero] at h
    simpa [Algebra.smul_def] using h
  have hDx (i j) : ε (D j (x i)) = if i = j then 1 else 0 := by
    rw [hD' j (y i) (y i).2, hy, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  have key (r : ℕ) : ∀ a ∈ W, a ∈ I ^ (r + 1) := by
    induction r with
    | zero => exact fun a ha ↦ by simpa using hW a ha
    | succ r ih =>
      intro a ha
      obtain ⟨f, hf, hfa⟩ := exists_isHomogeneous_sub_aeval_mem_pow_succ hx hspan (ih a ha)
      have hpd (j) : pderiv j f = 0 := by
        have hf' (i) : (pderiv i f).IsHomogeneous r := by simpa using hf.pderiv (i := i)
        refine eq_zero_of_isHomogeneous_of_aeval_mem_pow_succ hx hDx (hf' j) ?_
        have h1 : D j (aeval x f) ∈ I ^ (r + 1) := by
          have h := (D j).map_mem_pow_of_mem_pow_succ hfa
          rw [map_sub] at h
          simpa using sub_mem (ih _ (hDW j a ha)) h
        rw [(D j).map_aeval_eq_sum] at h1
        have h2 : ∑ i, aeval x (pderiv i f) * (D j (x i) - algebraMap k A (ε (D j (x i)))) ∈
            I ^ (r + 1) :=
          Ideal.sum_mem _ fun i _ ↦ by
            rw [pow_succ]
            exact Ideal.mul_mem_mul ((hf' i).aeval_mem_pow hx) (ε.sub_algebraMap_mem_ker _)
        have h3 : aeval x (pderiv j f) = ∑ i, aeval x (pderiv i f) * D j (x i) -
            ∑ i, aeval x (pderiv i f) * (D j (x i) - algebraMap k A (ε (D j (x i)))) := by
          rw [← Finset.sum_sub_distrib]
          simp_rw [mul_sub, sub_sub_cancel, hDx, apply_ite (algebraMap k A), map_one, map_zero,
            mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [h3]
        exact sub_mem h1 h2
      have h := hf.sum_X_mul_pderiv
      simp only [hpd, mul_zero, Finset.sum_const_zero] at h
      rw [eq_comm, nsmul_eq_mul, mul_eq_zero] at h
      have hf0 : f = 0 := h.resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero r))
      simpa [hf0] using hfa
  exact Submodule.mem_iInf _ |>.2 fun r ↦ Ideal.pow_le_pow_right (Nat.le_succ r) (key r a ha)
end AlgHom

/-! ### Invariant derivations of a bialgebra -/

section Bialgebra

open Coalgebra TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A]

private theorem mul'_map_id_algebraMap_mul (d e : A →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = e a * d b + e b * d a) (u v : A ⊗[k] A) :
    LinearMap.mul' k A (map LinearMap.id (Algebra.linearMap k A ∘ₗ d) (u * v)) =
      LinearMap.mul' k A (map LinearMap.id (Algebra.linearMap k A ∘ₗ e) u) *
          LinearMap.mul' k A (map LinearMap.id (Algebra.linearMap k A ∘ₗ d) v) +
        LinearMap.mul' k A (map LinearMap.id (Algebra.linearMap k A ∘ₗ e) v) *
          LinearMap.mul' k A (map LinearMap.id (Algebra.linearMap k A ∘ₗ d) u) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; ring
  | tmul a b =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; ring
    | tmul c f =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
        hd, map_add, map_mul]
      ring

/-- A `k`-linear map `d : A → k` which is a derivation at the counit extends to the invariant
derivation `a ↦ ∑ a₁ d(a₂)` of `A`. -/
theorem Bialgebra.exists_derivation_counitAlgHom_comp (d : A →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = counit a * d b + counit b * d a) :
    ∃ D : Derivation k A A, ∀ a, counit (D a) = d a := by
  let L : A →ₗ[k] A :=
    LinearMap.mul' k A ∘ₗ map LinearMap.id (Algebra.linearMap k A ∘ₗ d) ∘ₗ comul
  have hM (a : A) : LinearMap.mul' k A
      (map LinearMap.id (Algebra.linearMap k A ∘ₗ (counit : A →ₗ[k] k)) (comul a)) = a := by
    have h : LinearMap.mul' k A ∘ₗ map LinearMap.id (Algebra.linearMap k A ∘ₗ counit) =
        (_root_.TensorProduct.rid k A).toLinearMap ∘ₗ (counit : A →ₗ[k] k).lTensor A := by
      ext a b
      simp [Algebra.smul_def, mul_comm]
    rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, lTensor_counit_comul]
    simp
  refine ⟨Derivation.mk' L fun a b ↦ ?_, fun a ↦ ?_⟩
  · simp only [L, LinearMap.coe_comp, Function.comp_apply, Bialgebra.comul_mul]
    rw [mul'_map_id_algebraMap_mul d counit hd, hM, hM, smul_eq_mul, smul_eq_mul]
  · have h : (counit : A →ₗ[k] k) ∘ₗ LinearMap.mul' k A ∘ₗ
        map LinearMap.id (Algebra.linearMap k A ∘ₗ d) =
        d ∘ₗ (_root_.TensorProduct.lid k A).toLinearMap ∘ₗ (counit : A →ₗ[k] k).rTensor A := by
      ext a b
      simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, _root_.TensorProduct.map_tmul,
        LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, _root_.TensorProduct.lid_tmul]
      rw [← Algebra.commutes, Bialgebra.counit_mul, Bialgebra.counit_algebraMap, map_smul,
        smul_eq_mul, mul_comm]
    have h' := LinearMap.congr_fun h (comul a)
    simp only [LinearMap.comp_apply, rTensor_counit_comul] at h'
    exact h'.trans (by simp)

local notation "𝔪" => RingHom.ker (Bialgebra.counitAlgHom k A)

variable (k A) in
/-- Every tangent vector at the identity of a commutative bialgebra extends to an invariant
derivation. -/
theorem Bialgebra.exists_derivation_of_cotangent (φ : (𝔪).Cotangent →ₗ[k] k) :
    ∃ D : Derivation k A A, ∀ a (ha : a ∈ 𝔪),
      counitAlgHom k A (D a) = φ ((𝔪).toCotangent ⟨a, ha⟩) := by
  obtain ⟨D, hD⟩ := Bialgebra.exists_derivation_counitAlgHom_comp
    ((counitAlgHom k A).cotangentDerivation φ) fun a b ↦ by
      simpa using (counitAlgHom k A).cotangentDerivation_mul φ a b
  exact ⟨D, fun a ha ↦ by rw [counitAlgHom_apply, hD, AlgHom.cotangentDerivation_of_mem φ ha]⟩

variable [CharZero k]

variable (k A) in
/-- **Cartier's lemma** for bialgebras: in characteristic zero, the intersection of the powers of
the augmentation ideal of a Noetherian commutative bialgebra is a prime ideal. Geometrically, a
single irreducible component passes through the identity. -/
theorem Bialgebra.isPrime_iInf_pow_ker_counitAlgHom [IsNoetherianRing A] :
    (⨅ r : ℕ, RingHom.ker (Bialgebra.counitAlgHom k A) ^ r).IsPrime :=
  AlgHom.isPrime_iInf_pow_ker_of_forall_exists_derivation
    (Bialgebra.exists_derivation_of_cotangent k A)

end Bialgebra

/-! ### Heights of ideals -/

/-- **Nakayama's lemma**: if a finitely generated prime ideal `p` satisfies `p ≤ J ⊔ p ^ 2` for
an ideal `J ≤ p`, then `p` is a minimal prime of `J`. -/
theorem Ideal.mem_minimalPrimes_of_le_sup_sq {R : Type*} [CommRing R] {p J : Ideal R}
    [hp : p.IsPrime] (hfg : p.FG) (hJp : J ≤ p) (hle : p ≤ J ⊔ p ^ 2) :
    p ∈ J.minimalPrimes := by
  obtain ⟨r, hr, hrp⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := p)
    (N := J) (N' := p) (P := p) hfg le_rfl (by rwa [Ideal.smul_eq_mul, ← sq])
  have hr' : r ∉ p := fun h ↦ hp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h hr))
  refine ⟨⟨hp, hJp⟩, fun q ⟨hq, hJq⟩ hqp a ha ↦ ?_⟩
  have h := hJq (hrp (Submodule.smul_mem_pointwise_smul a r p ha))
  rw [smul_eq_mul] at h
  exact (hq.mem_or_mem h).resolve_left fun h ↦ hr' (hqp h)

/-- A prime ideal `p` of a Noetherian ring with `p ≤ span s ⊔ p ^ 2` for a finite set `s ⊆ p`
has height at most `#s` (Nakayama's lemma and Krull's height theorem). -/
theorem Ideal.height_le_card_of_le_span_sup_sq {R : Type*} [CommRing R] [IsNoetherianRing R]
    {p : Ideal R} [p.IsPrime] {s : Finset R} (hs : (s : Set R) ⊆ p)
    (hle : p ≤ Ideal.span s ⊔ p ^ 2) : p.height ≤ s.card :=
  Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (Ideal.mem_minimalPrimes_of_le_sup_sq (IsNoetherian.noetherian p) (Ideal.span_le.2 hs) hle)

/-! ### Dimension of the cotangent space at a rational point -/

namespace AlgHom

open scoped TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {ε : A →ₐ[k] k}

/-- In characteristic zero, the cotangent space at a `k`-point `ε` of a finitely generated
`k`-algebra `A` has dimension at most `dim A`, provided every tangent vector at `ε` extends to a
derivation of `A`: lifts `xᵢ` of a basis of `I / I²` are algebraically independent modulo the
prime ideal `⋂ₙ Iⁿ` (Cartier's lemma). -/
theorem finrank_cotangent_le_ringKrullDim [CharZero k] [Algebra.FiniteType k A]
    (hD : ∀ φ : (RingHom.ker ε).Cotangent →ₗ[k] k, ∃ D : Derivation k A A,
      ∀ a (ha : a ∈ RingHom.ker ε), ε (D a) = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩)) :
    (Module.finrank k (RingHom.ker ε).Cotangent : WithBot ℕ∞) ≤ ringKrullDim A := by
  classical
  have := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨x, D, hx, -, hD'⟩ := ε.exists_spanning_and_derivation hD
  set P := ⨅ r : ℕ, RingHom.ker ε ^ r
  have : P.IsPrime := isPrime_iInf_pow_ker_of_forall_exists_derivation hD
  have : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast_of_finiteType k (A ⧸ P)
  have hle := (algebraicIndependent_mk_iInf_pow_ker hx hD').lift_cardinalMk_le_trdeg
  rw [Algebra.trdeg_eq_of_ringKrullDim_eq k (A ⧸ P) hn] at hle
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast, Nat.cast_le] at hle
  calc (Module.finrank k (RingHom.ker ε).Cotangent : WithBot ℕ∞) ≤ n := by
        exact_mod_cast hle
    _ = ringKrullDim (A ⧸ P) := hn.symm
    _ ≤ ringKrullDim A := ringKrullDim_quotient_le P

variable (K : Type*) [Field K] [Algebra k K]

/-- The ideal of the base change `K ⊗[k] A → K` of a `k`-point `ε` of `A` is generated by the
ideal of `ε`. -/
theorem ker_liftEquiv_le_map :
    RingHom.ker (liftEquiv k K A K ((Algebra.ofId k K).comp ε)) ≤
      (RingHom.ker ε).map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) := by
  set ε' := liftEquiv k K A K ((Algebra.ofId k K).comp ε)
  have key (b : K ⊗[k] A) : b - algebraMap K (K ⊗[k] A) (ε' b) ∈
      (RingHom.ker ε).map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) := by
    induction b using TensorProduct.inductionOn with
    | add b c hb hc =>
      rw [map_add, map_add, add_sub_add_comm]
      exact add_mem hb hc
    | tmul a y =>
      have h : a ⊗ₜ[k] y - algebraMap K (K ⊗[k] A) (ε' (a ⊗ₜ y)) =
          (a ⊗ₜ 1) * Algebra.TensorProduct.includeRight (y - algebraMap k A (ε y)) := by
        simp [ε', mul_sub, Algebra.TensorProduct.one_def, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_sub, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      rw [h]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ε.sub_algebraMap_mem_ker y))
  intro b hb
  simpa [RingHom.mem_ker.1 hb] using key b

/-- If `xᵢ ∈ I` span the ideal `I` of a `k`-point `ε` of a finitely generated `k`-algebra `A`
modulo `I²`, then the ideal of the base change `K ⊗[k] A → K` of `ε` has height at most the number
of the `xᵢ` (Nakayama's lemma and Krull's height theorem). -/
theorem height_ker_liftEquiv_le_card [Algebra.FiniteType k A] {ι : Type*} [Fintype ι]
    {x : ι → A} (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ a ∈ RingHom.ker ε, ∃ c : ι → k,
      a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2) :
    (RingHom.ker (liftEquiv k K A K ((Algebra.ofId k K).comp ε))).height ≤ Fintype.card ι := by
  classical
  have := Algebra.FiniteType.isNoetherianRing K (K ⊗[k] A)
  set ε' := liftEquiv k K A K ((Algebra.ofId k K).comp ε)
  have := RingHom.ker_isPrime ε'
  set f : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  have hf (a : A) (ha : a ∈ RingHom.ker ε) : f a ∈ RingHom.ker ε' := by
    simp_all [f, ε']
  have hmap : (RingHom.ker ε).map f ≤ RingHom.ker ε' := Ideal.map_le_iff_le_comap.2 hf
  refine (Ideal.height_le_card_of_le_span_sup_sq (s := Finset.univ.image fun i ↦ f (x i))
    ?_ ?_).trans (by exact_mod_cast Finset.card_image_le)
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    exact hf _ (hx i)
  · refine (ker_liftEquiv_le_map K).trans (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
    obtain ⟨c, hc⟩ := hspan a ha
    rw [Ideal.mem_comap, ← sub_add_cancel a (∑ i, algebraMap k A (c i) * x i), map_add,
      add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [map_sum]
      refine Ideal.sum_mem _ fun i _ ↦ ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _
        (Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
    · refine Ideal.pow_right_mono hmap 2 ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc

/-- The ideal of the base change `K ⊗[k] A → K` of a `k`-point `ε` of a finitely generated
`k`-algebra `A` has height at most the dimension of the cotangent space of `A` at `ε`. -/
theorem height_ker_liftEquiv_le [Algebra.FiniteType k A] :
    (RingHom.ker (liftEquiv k K A K ((Algebra.ofId k K).comp ε))).height ≤
      Module.finrank k (RingHom.ker ε).Cotangent := by
  classical
  have := Algebra.FiniteType.isNoetherianRing k A
  have := ε.finiteDimensional_cotangent
  set I := RingHom.ker ε
  let B := Module.finBasis k I.Cotangent
  choose y hy using fun i ↦ I.toCotangent_surjective (B i)
  have h := height_ker_liftEquiv_le_card K (x := fun i ↦ (y i : A)) (fun i ↦ (y i).2)
    fun a ha ↦ ⟨fun i ↦ B.repr (I.toCotangent ⟨a, ha⟩) i, by
      have h : I.toCotangent (⟨a, ha⟩ - ∑ i, B.repr (I.toCotangent ⟨a, ha⟩) i • y i) = 0 := by
        rw [map_sub, map_sum]
        simp_rw [LinearMap.map_smul_of_tower, hy]
        rw [B.sum_repr, sub_self]
      rw [I.toCotangent_eq_zero] at h
      simpa [Algebra.smul_def] using h⟩
  rwa [Fintype.card_fin] at h

end AlgHom

/-! ### Cartier's theorem -/

section HopfAlgebra

open Bialgebra Coalgebra WithConv
open scoped TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]

/-- The translation `a ↦ ∑ h(a₁) a₂` of a commutative Hopf algebra by a `k`-point `h`. -/
private noncomputable def translation (h : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (toConv ((Algebra.ofId k A).comp h.ofConv) * toConv (AlgHom.id k A)).ofConv

private theorem comp_ofId_comp (f : A →ₐ[k] A) (h : A →ₐ[k] k) :
    f.comp ((Algebra.ofId k A).comp h) = (Algebra.ofId k A).comp h := by
  rw [← AlgHom.comp_assoc, Subsingleton.elim (f.comp (Algebra.ofId k A)) (Algebra.ofId k A)]

private theorem translation_comp_translation (h₁ h₂ : WithConv (A →ₐ[k] k)) :
    (translation h₁).comp (translation h₂) = translation (h₂ * h₁) := by
  rw [translation, translation, AlgHom.comp_convMul_distrib, comp_ofId_comp, AlgHom.comp_id,
    translation, AlgHom.comp_convMul_distrib (Algebra.ofId k A)]
  simp only [toConv_ofConv, mul_assoc]

private theorem translation_one : translation (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  rw [translation, AlgHom.convOne_def, ofConv_toConv, ← AlgHom.comp_assoc,
    Subsingleton.elim ((Algebra.ofId k A).comp (Algebra.ofId k k)) (Algebra.ofId k A),
    ← AlgHom.convOne_def, toConv_ofConv, one_mul, ofConv_toConv]

private theorem comp_translation_inv (g : WithConv (A →ₐ[k] k)) :
    g.ofConv.comp (translation g⁻¹) = counitAlgHom k A := by
  rw [translation, AlgHom.comp_convMul_distrib, ← AlgHom.comp_assoc,
    Subsingleton.elim (g.ofConv.comp (Algebra.ofId k A)) (AlgHom.id k k), AlgHom.id_comp,
    AlgHom.comp_id, toConv_ofConv, toConv_ofConv, inv_mul_cancel, AlgHom.convOne_def,
    ofConv_toConv, Subsingleton.elim (Algebra.ofId k k) (AlgHom.id k k), AlgHom.id_comp]

private theorem counitAlgHom_comp_translation (g : WithConv (A →ₐ[k] k)) :
    (counitAlgHom k A).comp (translation g) = g.ofConv := by
  rw [translation, AlgHom.comp_convMul_distrib, ← AlgHom.comp_assoc,
    Subsingleton.elim ((counitAlgHom k A).comp (Algebra.ofId k A)) (AlgHom.id k k),
    AlgHom.id_comp, AlgHom.comp_id, toConv_ofConv,
    show toConv (counitAlgHom k A) = 1 by
      rw [AlgHom.convOne_def, Subsingleton.elim (Algebra.ofId k k) (AlgHom.id k k),
        AlgHom.id_comp],
    mul_one, ofConv_toConv]

/-- Translations act transitively on the `k`-points of a commutative Hopf algebra: for every
`k`-point `g` there is an algebra automorphism `τ` of `A` with `g ∘ τ = ε`. -/
theorem HopfAlgebra.exists_algEquiv_comp_eq_counitAlgHom (g : A →ₐ[k] k) :
    ∃ τ : A ≃ₐ[k] A, g.comp τ.toAlgHom = counitAlgHom k A := by
  have h₁ : (translation (toConv g)⁻¹).comp (translation (toConv g)) = AlgHom.id k A := by
    rw [translation_comp_translation, mul_inv_cancel, translation_one]
  have h₂ : (translation (toConv g)).comp (translation (toConv g)⁻¹) = AlgHom.id k A := by
    rw [translation_comp_translation, inv_mul_cancel, translation_one]
  refine ⟨AlgEquiv.ofAlgHom _ _ h₁ h₂, ?_⟩
  have h := comp_translation_inv (toConv g)
  rwa [ofConv_toConv] at h

/-- Over an algebraically closed field, the Krull dimension of a finitely generated commutative
Hopf algebra is at most the height of its augmentation ideal: by the Nullstellensatz every
maximal ideal is the ideal of a `k`-point, which a translation moves to the identity. -/
theorem HopfAlgebra.ringKrullDim_le_height_ker_counitAlgHom [IsAlgClosed k]
    [Algebra.FiniteType k A] : ringKrullDim A ≤ (RingHom.ker (counitAlgHom k A)).height := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro M hM
  obtain ⟨g, rfl⟩ := exists_algHom_ker_eq_of_isMaximal k A M
  obtain ⟨τ, hτ⟩ := HopfAlgebra.exists_algEquiv_comp_eq_counitAlgHom g
  have h : RingHom.ker (counitAlgHom k A) = (RingHom.ker g).comap (τ : A ≃+* A) := by
    ext a
    simp [← hτ]
  rw [h, RingEquiv.height_comap]

/-- The counit of the base change `K ⊗[k] A` of a commutative bialgebra is the base change of the
counit of `A`. -/
theorem Bialgebra.counitAlgHom_baseChange_eq_liftEquiv (K : Type*) [Field K] [Algebra k K] :
    counitAlgHom K (K ⊗[k] A) =
      AlgHom.liftEquiv k K A K ((Algebra.ofId k K).comp (counitAlgHom k A)) :=
  Algebra.TensorProduct.ext_ring (AlgHom.ext fun a ↦ by simp)

/-- The augmentation ideal of the base change `K ⊗[k] A` of a commutative Hopf algebra is
generated by the augmentation ideal of `A`. -/
theorem HopfAlgebra.ker_counitAlgHom_baseChange_le_map (K : Type*) [Field K] [Algebra k K] :
    RingHom.ker (counitAlgHom K (K ⊗[k] A)) ≤ (RingHom.ker (counitAlgHom k A)).map
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) := by
  rw [Bialgebra.counitAlgHom_baseChange_eq_liftEquiv]
  exact AlgHom.ker_liftEquiv_le_map K


/-- If `xᵢ ∈ 𝔪` span the augmentation ideal `𝔪` of a commutative Hopf algebra `A` modulo `𝔪²`,
then the augmentation ideal of a base change `K ⊗[k] A` has height at most the number of
the `xᵢ`. -/
theorem HopfAlgebra.height_ker_counitAlgHom_baseChange_le (K : Type*) [Field K] [Algebra k K]
    [Algebra.FiniteType k A] {ι : Type*} [Fintype ι] {x : ι → A}
    (hx : ∀ i, x i ∈ RingHom.ker (counitAlgHom k A))
    (hspan : ∀ a ∈ RingHom.ker (counitAlgHom k A), ∃ c : ι → k,
      a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker (counitAlgHom k A) ^ 2) :
    (RingHom.ker (counitAlgHom K (K ⊗[k] A))).height ≤ Fintype.card ι := by
  rw [Bialgebra.counitAlgHom_baseChange_eq_liftEquiv]
  exact AlgHom.height_ker_liftEquiv_le_card K hx hspan

variable (k A) in
/-- The Krull dimension of a finitely generated commutative Hopf algebra is at most the
dimension of its cotangent space at the identity: this holds after base change to an algebraic
closure, where translations move every closed point to the identity. -/
theorem HopfAlgebra.ringKrullDim_le_finrank_cotangent [Algebra.FiniteType k A] :
    ringKrullDim A ≤
      (Module.finrank k (RingHom.ker (counitAlgHom k A)).Cotangent : WithBot ℕ∞) := by
  have := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨x, -, hx, hspan, -⟩ := (counitAlgHom k A).exists_spanning_and_derivation
    (Bialgebra.exists_derivation_of_cotangent k A)
  let K := AlgebraicClosure k
  have : FaithfulSMul A (A ⊗[k] K) := (faithfulSMul_iff_algebraMap_injective _ _).2
    (Algebra.TensorProduct.includeLeft_injective (S := A) (algebraMap k K).injective)
  calc ringKrullDim A = ringKrullDim (A ⊗[k] K) := (ringKrullDim_eq_of_isIntegral A _).symm
    _ = ringKrullDim (K ⊗[k] A) :=
      ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv
    _ ≤ (RingHom.ker (counitAlgHom K (K ⊗[k] A))).height :=
      HopfAlgebra.ringKrullDim_le_height_ker_counitAlgHom
    _ ≤ _ := by
      have h := HopfAlgebra.height_ker_counitAlgHom_baseChange_le K hx hspan
      rw [Fintype.card_fin] at h
      exact_mod_cast h

variable [CharZero k]

/-- **Cartier's lemma** for Hopf algebras: in characteristic zero, a nilpotent element of a
Noetherian commutative Hopf algebra vanishes in the local ring at every `k`-point `g`. -/
theorem HopfAlgebra.exists_apply_eq_one_mul_eq_zero_of_isNilpotent [IsNoetherianRing A]
    (g : A →ₐ[k] k) {b : A} (hb : IsNilpotent b) : ∃ t, g t = 1 ∧ t * b = 0 := by
  have hφψ : (translation (toConv g)⁻¹).comp (translation (toConv g)) = AlgHom.id k A := by
    rw [translation_comp_translation, mul_inv_cancel, translation_one]
  obtain ⟨s, hs, hsb⟩ := AlgHom.exists_apply_eq_one_mul_eq_zero_of_forall_exists_derivation
    (Bialgebra.exists_derivation_of_cotangent k A) (IsNilpotent.map hb (translation (toConv g)))
  refine ⟨translation (toConv g)⁻¹ s, ?_, ?_⟩
  · have h := comp_translation_inv (toConv g)
    rw [ofConv_toConv] at h
    rw [← AlgHom.comp_apply, h, hs]
  · have h := congrArg (translation (toConv g)⁻¹) hsb
    rwa [map_mul, map_zero, ← AlgHom.comp_apply _ (translation (toConv g)), hφψ,
      AlgHom.id_apply] at h

/-- **Cartier's lemma** at an arbitrary `k`-point `g` of a Noetherian commutative Hopf algebra in
characteristic zero: the functions vanishing near `g` form a prime ideal, so a single
irreducible component passes through `g`. It is the translate by `g` of
`Bialgebra.isPrime_iInf_pow_ker_counitAlgHom`. -/
theorem HopfAlgebra.isPrime_iInf_pow_ker [IsNoetherianRing A] (g : A →ₐ[k] k) :
    (⨅ r : ℕ, RingHom.ker g ^ r).IsPrime := by
  have hP := Bialgebra.isPrime_iInf_pow_ker_counitAlgHom k A
  have hφψ : (translation (toConv g)⁻¹).comp (translation (toConv g)) = AlgHom.id k A := by
    rw [translation_comp_translation, mul_inv_cancel, translation_one]
  have hε := counitAlgHom_comp_translation (toConv g)
  have hg := comp_translation_inv (toConv g)
  rw [ofConv_toConv] at hε hg
  convert Ideal.IsPrime.comap (translation (toConv g)) (hK := hP) using 1
  ext b
  rw [Ideal.mem_comap, AlgHom.mem_iInf_pow_ker_iff, AlgHom.mem_iInf_pow_ker_iff]
  constructor
  · rintro ⟨t, ht, htb⟩
    refine ⟨translation (toConv g) t, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hε, ht]
    · rw [← map_mul, htb, map_zero]
  · rintro ⟨s, hs, hsb⟩
    refine ⟨translation (toConv g)⁻¹ s, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hg, hs]
    · have h := congrArg (translation (toConv g)⁻¹) hsb
      rwa [map_mul, map_zero, ← AlgHom.comp_apply _ (translation (toConv g)), hφψ,
        AlgHom.id_apply] at h

/-- Over an algebraically closed field of characteristic zero, a finitely generated commutative
Hopf algebra is reduced. -/
theorem HopfAlgebra.isReduced_of_isAlgClosed [IsAlgClosed k] [Algebra.FiniteType k A] :
    IsReduced A := by
  refine ⟨fun b hb ↦ ?_⟩
  have := Algebra.FiniteType.isNoetherianRing k A
  let J : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A A b)
  by_cases hJ : J = ⊤
  · have h : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
    simpa [J] using h
  obtain ⟨M, hM, hJM⟩ := J.exists_le_maximal hJ
  obtain ⟨g, rfl⟩ := exists_algHom_ker_eq_of_isMaximal k A M
  obtain ⟨t, ht, htb⟩ := exists_apply_eq_one_mul_eq_zero_of_isNilpotent g hb
  have h := RingHom.mem_ker.1 (hJM (show t ∈ J by simpa [J] using htb))
  rw [ht] at h
  exact absurd h one_ne_zero

/-- **Cartier's theorem**: over a field of characteristic zero, a finitely generated commutative
Hopf algebra is reduced. Equivalently, an affine group scheme of finite type over a field of
characteristic zero is reduced. (blueprint: `proposition-cartier-s-theorem`) -/
theorem HopfAlgebra.isReduced_of_charZero [Algebra.FiniteType k A] : IsReduced A := by
  have : CharZero (AlgebraicClosure k) :=
    charZero_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective
  have : IsReduced (AlgebraicClosure k ⊗[k] A) :=
    HopfAlgebra.isReduced_of_isAlgClosed (k := AlgebraicClosure k)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] AlgebraicClosure k ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k (AlgebraicClosure k)).injective)

/-- In characteristic zero, every Hopf ideal of a finitely generated commutative Hopf algebra is
radical: closed subgroup schemes are reduced. (blueprint: `proposition-cartier-s-theorem`) -/
theorem Ideal.IsHopfIdeal.isRadical [Algebra.FiniteType k A] (I : Ideal A) [I.IsHopfIdeal k] :
    I.IsRadical := by
  have := HopfAlgebra.isReduced_of_charZero (k := k) (A := A ⧸ I)
  exact (Ideal.isRadical_iff_quotient_reduced I).2 this

variable (k A) in
/-- In characteristic zero, the cotangent space at the identity of a finitely generated
commutative Hopf algebra `A` has dimension at most `dim A`: lifts `xᵢ` of a basis of `𝔪 / 𝔪²`
are algebraically independent modulo the prime ideal `⋂ₙ 𝔪ⁿ` (Cartier's lemma). -/
theorem HopfAlgebra.finrank_cotangent_le_ringKrullDim [Algebra.FiniteType k A] :
    (Module.finrank k (RingHom.ker (counitAlgHom k A)).Cotangent : WithBot ℕ∞) ≤
      ringKrullDim A :=
  AlgHom.finrank_cotangent_le_ringKrullDim (Bialgebra.exists_derivation_of_cotangent k A)

variable (k A) in
/-- **Dimension of a group scheme in characteristic zero.** For a finitely generated commutative
Hopf algebra `A` over a field `k` of characteristic zero, the cotangent space `𝔪 / 𝔪²` at the
identity has dimension `dim A`: the group scheme `Spec A` is smooth, so its tangent space at the
identity has the dimension of the local ring there, and translations make all its local
dimensions equal. (blueprint: `lemma-connected-components-images-homomorphisms--3`, clause (2)) -/
theorem HopfAlgebra.finrank_cotangent_eq_ringKrullDim [Algebra.FiniteType k A] :
    (Module.finrank k (RingHom.ker (counitAlgHom k A)).Cotangent : WithBot ℕ∞) =
      ringKrullDim A :=
  le_antisymm (HopfAlgebra.finrank_cotangent_le_ringKrullDim k A)
    (HopfAlgebra.ringKrullDim_le_finrank_cotangent k A)

end HopfAlgebra
