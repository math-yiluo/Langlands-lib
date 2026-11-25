/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of quotient algebras

## Main results

- `Algebra.TensorProduct.liftQuotient`: the homomorphism `(A ⧸ I) ⊗[R] (B ⧸ J) → C` induced by
  two homomorphisms killing `I` and `J`.
- `Algebra.TensorProduct.map_mkQ_restrictScalars_eq_zero_iff`: the module and algebra quotient
  maps by two ideals kill the same elements of `A ⊗[R] B`.
- `Algebra.TensorProduct.eq_zero_of_forall_lift_eq_zero`,
  `Algebra.TensorProduct.eq_zero_of_forall_liftQuotient_eq_zero`: over a field, an element of a
  tensor product of algebras is detected on pairs of characters from jointly injective families.
  For quotients by the ideals of common zeros of two families of `K`-points this says that the
  product of the two families is schematically dense in the product of their Zariski closures.
- `Algebra.TensorProduct.isNilpotent_of_productMap_eq_zero`: if two `K`-points have nilpotent
  kernels, then so has their tensor product.
- `Algebra.TensorProduct.eq_zero_or_eq_one_of_isIdempotentElem`: if `A` has an `R`-point whose
  kernel is nil and `B` has no idempotents other than `0` and `1`, then neither has `A ⊗[R] B`.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

section CommRing

variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] (I : Ideal A) (J : Ideal B)

/-- The algebra homomorphism `(A ⧸ I) ⊗[R] (B ⧸ J) → C` induced by two algebra homomorphisms
`f : A → C` and `g : B → C` killing `I` and `J`. -/
noncomputable def liftQuotient (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ b ∈ J, g b = 0) : (A ⧸ I) ⊗[R] (B ⧸ J) →ₐ[R] C :=
  lift (Ideal.Quotient.liftₐ I f hf) (Ideal.Quotient.liftₐ J g hg) fun _ _ ↦ .all _ _

variable {I J}

@[simp]
theorem liftQuotient_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ b ∈ J, g b = 0) (a : A) (b : B) :
    liftQuotient I J f g hf hg (Ideal.Quotient.mk I a ⊗ₜ Ideal.Quotient.mk J b) = f a * g b :=
  rfl

theorem liftQuotient_map_mkₐ (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ b ∈ J, g b = 0) (t : A ⊗[R] B) :
    liftQuotient I J f g hf hg (map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) t) =
      lift f g (fun _ _ ↦ .all _ _) t := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul a b => simp [liftQuotient]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (I J) in
/-- The tensor product of the module quotient maps by the ideals `I` and `J`, viewed as
`R`-submodules, kills an element if and only if the tensor product of the algebra quotient maps
does. -/
theorem map_mkQ_restrictScalars_eq_zero_iff (t : A ⊗[R] B) :
    _root_.TensorProduct.map (I.restrictScalars R).mkQ (J.restrictScalars R).mkQ t = 0 ↔
      map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) t = 0 := by
  let e := _root_.TensorProduct.congr (Submodule.Quotient.restrictScalarsEquiv R I)
    (Submodule.Quotient.restrictScalarsEquiv R J)
  have key (t : A ⊗[R] B) : e (_root_.TensorProduct.map (I.restrictScalars R).mkQ
      (J.restrictScalars R).mkQ t) = map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) t := by
    induction t using _root_.TensorProduct.inductionOn with
    | tmul a b => simp [e]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, LinearEquiv.map_eq_zero_iff]

end CommRing

section Field

variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- Over a field `K`, an element of `A ⊗[K] B` vanishes as soon as it is killed by every
`lift (f i) (g j)`, for jointly injective families of characters `f i : A → K` and `g j : B → K`.

The images of `x` in `K ⊗[K] B = B` under the `f i ⊗ B` are killed by every `g j`, so they vanish,
and `TensorProduct.eq_zero_of_forall_rTensor_eq_zero` applies. -/
theorem eq_zero_of_forall_lift_eq_zero {ι κ : Type*} (f : ι → A →ₐ[K] K) (g : κ → B →ₐ[K] K)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (hg : ∀ b, (∀ j, g j b = 0) → b = 0)
    {x : A ⊗[K] B} (hx : ∀ i j, lift (f i) (g j) (fun _ _ ↦ .all _ _) x = 0) : x = 0 := by
  refine _root_.TensorProduct.eq_zero_of_forall_rTensor_eq_zero (fun i ↦ (f i).toLinearMap) hf
    fun i ↦ ?_
  have key (j : κ) (y : A ⊗[K] B) :
      g j (_root_.TensorProduct.lid K B ((f i).toLinearMap.rTensor B y)) =
        lift (f i) (g j) (fun _ _ ↦ .all _ _) y := by
    induction y using _root_.TensorProduct.inductionOn with
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  refine (_root_.TensorProduct.lid K B).injective ?_
  rw [map_zero]
  exact hg _ fun j ↦ (key j x).trans (hx i j)

/-- Let `I ⊆ A` and `J ⊆ B` be the ideals of common zeros of two families of `K`-points `χ s` and
`χ' t`. An element of `(A ⧸ I) ⊗[K] (B ⧸ J)` vanishing at every pair of points `(χ s, χ' t)` is
zero: the product of the two families is schematically dense in the product of their Zariski
closures. -/
theorem eq_zero_of_forall_liftQuotient_eq_zero {I : Ideal A} {J : Ideal B} {S T : Type*}
    (χ : S → A →ₐ[K] K) (χ' : T → B →ₐ[K] K) (hI : ∀ a, a ∈ I ↔ ∀ s, χ s a = 0)
    (hJ : ∀ b, b ∈ J ↔ ∀ t, χ' t b = 0) {c : (A ⧸ I) ⊗[K] (B ⧸ J)}
    (hc : ∀ s t, liftQuotient I J (χ s) (χ' t) (fun a ha ↦ (hI a).1 ha s)
      (fun b hb ↦ (hJ b).1 hb t) c = 0) : c = 0 := by
  refine eq_zero_of_forall_lift_eq_zero
    (fun s ↦ Ideal.Quotient.liftₐ I (χ s) fun a ha ↦ (hI a).1 ha s)
    (fun t ↦ Ideal.Quotient.liftₐ J (χ' t) fun b hb ↦ (hJ b).1 hb t) (fun v hv ↦ ?_)
    (fun v hv ↦ ?_) hc
  · induction v using Quotient.inductionOn' with | h a => ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI a).2 hv)
  · induction v using Quotient.inductionOn' with | h b => ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hJ b).2 hv)

end Field

section Idempotent

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Let `φ : A → R` be an `R`-algebra homomorphism whose kernel consists of nilpotent elements,
and let `B` be an `R`-algebra with no idempotents other than `0` and `1`. Then `A ⊗[R] B` has no
idempotents other than `0` and `1`: the kernel of `φ ⊗ id : A ⊗[R] B → B` is spanned by the
nilpotent elements `(a - φ a) ⊗ b`, so an idempotent is congruent to `0` or `1` modulo nilpotents.

Geometrically: if `Spec A` is a single point with an `R`-rational structure, then the base change
of a connected `Spec B` along it stays connected. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem (φ : A →ₐ[R] R)
    (hφ : ∀ a, φ a = 0 → IsNilpotent a) (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    {e : A ⊗[R] B} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  let ψ : A ⊗[R] B →ₐ[R] B := lift ((Algebra.ofId R B).comp φ) (AlgHom.id R B) fun _ _ ↦ .all _ _
  have key (x : A ⊗[R] B) : IsNilpotent (x - includeRight (ψ x)) := by
    induction x using _root_.TensorProduct.inductionOn with
    | tmul a b =>
      have hn : IsNilpotent (a - algebraMap R A (φ a)) := hφ _ (by simp)
      have : a ⊗ₜ[R] b - includeRight (ψ (a ⊗ₜ[R] b)) =
          includeLeft (S := R) (a - algebraMap R A (φ a)) * includeRight b := by
        simp [ψ, Algebra.algebraMap_eq_smul_one, _root_.TensorProduct.sub_tmul,
          _root_.TensorProduct.smul_tmul', sub_mul]
      rw [this]
      exact Commute.isNilpotent_mul_right (.all _ _) (hn.map (includeLeft (S := R)))
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact (Commute.all _ _).isNilpotent_add hx hy
  rcases hB (ψ e) (he.map ψ) with h | h
  · have := key e
    rw [h, map_zero, sub_zero] at this
    exact .inl (he.eq_zero_of_isNilpotent this)
  · have := key e
    rw [h, map_one, ← neg_sub, isNilpotent_neg_iff] at this
    exact .inr (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent this)).symm

end Idempotent

section Nilpotent

open _root_.TensorProduct

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

/-- If `f : R → K` and `g : S → K` are `K`-points with nilpotent ideals, then every element of
`R ⊗[K] S` killed by the tensor product point `f ⊗ g` is nilpotent. -/
theorem isNilpotent_of_productMap_eq_zero {f : R →ₐ[K] K} {g : S →ₐ[K] K}
    (hf : IsNilpotent (RingHom.ker f)) (hg : IsNilpotent (RingHom.ker g)) {t : R ⊗[K] S}
    (ht : productMap f g t = 0) : IsNilpotent t := by
  set I₁ := (RingHom.ker f).map (includeLeft : R →ₐ[K] R ⊗[K] S)
  set I₂ := (RingHom.ker g).map (includeRight : S →ₐ[K] R ⊗[K] S)
  have key (t : R ⊗[K] S) : t - algebraMap K _ (productMap f g t) ∈ I₁ ⊔ I₂ := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
    | tmul a b =>
      have h₁ : includeLeft (S := K) (a - algebraMap K R (f a)) ∈ I₁ :=
        Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
      have h₂ : includeRight (b - algebraMap K S (g b)) ∈ I₂ :=
        Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
      have heq : a ⊗ₜ[K] b - algebraMap K _ (productMap f g (a ⊗ₜ b)) =
          includeLeft (S := K) (a - algebraMap K R (f a)) * (1 ⊗ₜ b) +
            algebraMap K _ (f a) * includeRight (b - algebraMap K S (g b)) := by
        simp only [productMap_apply_tmul, includeLeft_apply, includeRight_apply, sub_tmul,
          tmul_sub, sub_mul, mul_sub, tmul_mul_tmul, mul_one, one_mul, algebraMap_apply,
          map_mul]
        simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul,
          tmul_smul, ← smul_tmul', mul_comm (g b)]
        abel
      rw [heq]
      exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ h₁))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ h₂))
  have h := key t
  rw [ht, map_zero, sub_zero] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hg
  have hy' : IsNilpotent y := ⟨n, by
    have : y ^ n ∈ I₁ ^ n := Ideal.pow_mem_pow hy n
    rwa [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot] at this⟩
  have hz' : IsNilpotent z := ⟨m, by
    have : z ^ m ∈ I₂ ^ m := Ideal.pow_mem_pow hz m
    rwa [← Ideal.map_pow, hm, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot] at this⟩
  exact (Commute.all y z).isNilpotent_add hy' hz'

end Nilpotent

end Algebra.TensorProduct
