/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Frobenius modules and their weights

A *Frobenius module* over a field `K` is a finite-dimensional `K`-vector space together with a
distinguished automorphism, the geometric Frobenius. It is the linear-algebra shadow of every
cohomological construction of the Weil conjectures: the stalk of an `ℓ`-adic sheaf at a closed
point with its local Frobenius, or a compactly supported cohomology group with the global
geometric Frobenius.

Fix a prime power `q` and an embedding `ι : K →+* ℂ`. A Frobenius module is *`ι`-pure of weight
`w` relative to `q`* if every eigenvalue `α` of its Frobenius satisfies `|ι α| = q ^ (w / 2)`,
and *has weights at most `w`* if `|ι α| ≤ q ^ (w / 2)`. The two cardinalities that occur in
practice are the residue cardinality `q_x` at a closed point and the cardinality `q` of the base
field; `FrobeniusModule.IsPureOfWeightOver` names the second one so that the convention is
visible at the use site.

This is the eigenvalue form of `Polynomial.IsPureOfWeight` of
`WeilConjectures.ZetaLinearAlgebra.Weights`, which says the same thing about the roots of the
reversed characteristic polynomial, for an integral weight and with the normalization
`‖z‖ = q ^ (-w / 2)` on the roots rather than on their reciprocals.

## Main declarations

- `FrobeniusModule`: the structure, with `FrobeniusModule.frobeniusEnd` the Frobenius as an
  endomorphism and `FrobeniusModule.Equiv` the isomorphisms.
- `FrobeniusModule.IsPureOfWeight`, `FrobeniusModule.HasWeightsAtMost` and their
  `…Over k` variants, the weight conditions relative to `q` and to `#k`.
- `FrobeniusModule.localPolynomial`: the polynomial `det (1 - T F)`, and
  `FrobeniusModule.IsReal`, the condition that its image under `ι : K →+* ℂ` has real
  coefficients.
- `FrobeniusModule.tateTwist`: the Tate twist `M(n)`, rescaling the Frobenius by `q ^ (-n)`.
- `FrobeniusModule.dual`: the dual `M^∨` with the inverse transpose of the Frobenius, and
  `FrobeniusModule.Equiv.dual` the dual of an isomorphism.
- `FrobeniusModule.IsPureOfWeight.tateTwist`: the twist by `n` lowers the weight by `2 n`.
- `FrobeniusModule.prod`: the direct sum `M ⊕ N`.
- `FrobeniusModule.IsPureOfWeight.isReal_prod_rescale_dual`: for `M` pure of weight `w` and
  `ι c = q ^ w`, the sum `M ⊕ M^∨(c)` is `ι`-real.
-/

@[expose] public section

universe u v t

/-- A *Frobenius module* over a field `K`: a finite-dimensional `K`-vector space together with
an automorphism, the geometric Frobenius. -/
structure FrobeniusModule.{w, x} (K : Type x) [Field K] : Type (max x (w + 1)) where
  /-- The underlying `K`-vector space. -/
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  /-- The geometric Frobenius automorphism. -/
  frobenius : carrier ≃ₗ[K] carrier

namespace FrobeniusModule

attribute [instance] addCommGroup module finiteDimensional

variable {K : Type v} [Field K]

/-- The geometric Frobenius of a Frobenius module, as an endomorphism. -/
noncomputable def frobeniusEnd (M : FrobeniusModule.{u, v} K) :
    Module.End K M.carrier :=
  M.frobenius.toLinearMap

/-- The Frobenius of a Frobenius module is an automorphism, so its eigenvalues are nonzero. -/
theorem ne_zero_of_hasEigenvalue {M : FrobeniusModule.{u, v} K} {β : K}
    (hβ : M.frobeniusEnd.HasEigenvalue β) : β ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hx
  exact hx.2 (M.frobenius.injective (hx.1.trans (map_zero _).symm))

/-- An isomorphism of Frobenius modules: a `K`-linear isomorphism intertwining the two
Frobenius automorphisms. -/
structure Equiv (M N : FrobeniusModule.{u, v} K) where
  /-- The underlying `K`-linear isomorphism. -/
  toLinearEquiv : M.carrier ≃ₗ[K] N.carrier
  /-- The isomorphism intertwines the two Frobenius automorphisms. -/
  map_frobenius (x : M.carrier) :
    toLinearEquiv (M.frobenius x) = N.frobenius (toLinearEquiv x)

/-- The identity isomorphism of a Frobenius module. -/
@[simps toLinearEquiv]
def Equiv.refl (M : FrobeniusModule.{u, v} K) : M.Equiv M where
  toLinearEquiv := LinearEquiv.refl K M.carrier
  map_frobenius _ := rfl

/-- The inverse of an isomorphism of Frobenius modules. -/
@[simps toLinearEquiv]
def Equiv.symm {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) : N.Equiv M where
  toLinearEquiv := e.toLinearEquiv.symm
  map_frobenius y := e.toLinearEquiv.injective (by
    rw [e.map_frobenius, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])

/-- The composite of two isomorphisms of Frobenius modules. -/
@[simps toLinearEquiv]
def Equiv.trans {M N P : FrobeniusModule.{u, v} K} (e : M.Equiv N) (e' : N.Equiv P) :
    M.Equiv P where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  map_frobenius x := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e.map_frobenius, e'.map_frobenius]

/-- `M` is *`ι`-pure of weight `w` relative to `q`* if every eigenvalue `α` of its geometric
Frobenius satisfies `|ι α| = q ^ (w / 2)`. -/
def IsPureOfWeight (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K) (w : ℝ) : Prop :=
  ∀ α : K, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ = (q : ℝ) ^ (w / 2)

/-- `M` *has weights at most `w` relative to `q`* if every eigenvalue `α` of its geometric
Frobenius satisfies `|ι α| ≤ q ^ (w / 2)`. -/
def HasWeightsAtMost (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K) (w : ℝ) : Prop :=
  ∀ α : K, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ ≤ (q : ℝ) ^ (w / 2)

/-- A module pure of weight `w` has weights at most `w`. -/
theorem IsPureOfWeight.hasWeightsAtMost {ι : K →+* ℂ} {q : ℕ} {M : FrobeniusModule.{u, v} K}
    {w : ℝ} (h : M.IsPureOfWeight ι q w) : M.HasWeightsAtMost ι q w :=
  fun α hα ↦ (h α hα).le

/-- For `q ≥ 1`, weights at most `w` are weights at most any `w' ≥ w`. -/
theorem HasWeightsAtMost.mono {ι : K →+* ℂ} {q : ℕ} (hq : 1 ≤ q)
    {M : FrobeniusModule.{u, v} K} {w w' : ℝ} (h : M.HasWeightsAtMost ι q w) (hww' : w ≤ w') :
    M.HasWeightsAtMost ι q w' :=
  fun α hα ↦ (h α hα).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) (by linarith))

/-- An isomorphism of Frobenius modules preserves the eigenvalues of the Frobenius. -/
theorem Equiv.hasEigenvalue {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) : N.frobeniusEnd.HasEigenvalue α := by
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.toLinearEquiv x) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · change N.frobenius (e.toLinearEquiv x) = α • e.toLinearEquiv x
    rw [← e.map_frobenius, ← map_smul]
    exact congrArg e.toLinearEquiv hx.1
  · exact (map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.2

/-- The isomorphism of Frobenius modules given by a linear isomorphism `e` with
`e ∘ F_M = F_N ∘ e`. -/
def Equiv.ofComp {M N : FrobeniusModule.{u, v} K} (e : M.carrier ≃ₗ[K] N.carrier)
    (h : e.toLinearMap ∘ₗ M.frobeniusEnd = N.frobeniusEnd ∘ₗ e.toLinearMap) : M.Equiv N :=
  ⟨e, fun x ↦ LinearMap.congr_fun h x⟩

/-- An isomorphism of Frobenius modules conjugates the two Frobenius endomorphisms. -/
theorem Equiv.frobeniusEnd_eq_conj {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    N.frobeniusEnd = e.toLinearEquiv.conj M.frobeniusEnd := by
  ext x
  change N.frobenius x = e.toLinearEquiv (M.frobenius (e.toLinearEquiv.symm x))
  rw [e.map_frobenius, LinearEquiv.apply_symm_apply]

/-- Isomorphic Frobenius modules have the same characteristic polynomial of the Frobenius. -/
theorem Equiv.charpoly_frobeniusEnd {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    N.frobeniusEnd.charpoly = M.frobeniusEnd.charpoly := by
  rw [e.frobeniusEnd_eq_conj, LinearEquiv.charpoly_conj]

/-- Isomorphic Frobenius modules have the same traces of the powers of the Frobenius. -/
theorem Equiv.trace_frobeniusEnd_pow {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) (m : ℕ) :
    LinearMap.trace K _ (N.frobeniusEnd ^ m) = LinearMap.trace K _ (M.frobeniusEnd ^ m) := by
  have hpow : ∀ k : ℕ, e.toLinearEquiv.conj M.frobeniusEnd ^ k =
      e.toLinearEquiv.conj (M.frobeniusEnd ^ k) := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearEquiv.conj_comp]
  rw [e.frobeniusEnd_eq_conj, hpow, LinearMap.trace_conj']

/-- A Frobenius module isomorphic to one with weights at most `w` has weights at most `w`. -/
theorem HasWeightsAtMost.of_equiv {ι : K →+* ℂ} {q : ℕ} {M N : FrobeniusModule.{u, v} K}
    (e : M.Equiv N) {w : ℝ} (h : N.HasWeightsAtMost ι q w) : M.HasWeightsAtMost ι q w :=
  fun α hα ↦ h α (e.hasEigenvalue hα)

/-- The local polynomial `det (1 - T F)` of a Frobenius module, the reverse characteristic
polynomial of its Frobenius `F`. -/
noncomputable def localPolynomial (M : FrobeniusModule.{u, v} K) : Polynomial K :=
  M.frobeniusEnd.charpolyRev

/-- `M` is `ι`-*real* if the image under `ι` of its local polynomial `det (1 - T F)` has real
coefficients; equivalently, if the multiset of complex eigenvalues of `F` is stable under
complex conjugation. -/
def IsReal (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K) : Prop :=
  ∀ n : ℕ, (starRingEnd ℂ) (ι (M.localPolynomial.coeff n)) = ι (M.localPolynomial.coeff n)

/-- `M` is `ι`-pure of weight `w` *over the field `k`*: purity relative to `q = #k`. This is
the convention for the geometric Frobenius acting on the cohomology of a `k`-scheme, as opposed
to the Frobenius acting on a stalk, whose weights are taken relative to the residue cardinality
`q_x` at the point. -/
def IsPureOfWeightOver (k : Type*) [Field k] (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K)
    (w : ℝ) : Prop :=
  M.IsPureOfWeight ι (Nat.card k) w

/-- `M` has weights at most `w` *over the field `k`*: the bound relative to `q = #k`. See
`FrobeniusModule.IsPureOfWeightOver` for the two cardinality conventions. -/
def HasWeightsAtMostOver (k : Type*) [Field k] (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K)
    (w : ℝ) : Prop :=
  M.HasWeightsAtMost ι (Nat.card k) w

/-- A module pure of weight `w` over `k` has weights at most `w` over `k`. -/
theorem IsPureOfWeightOver.hasWeightsAtMostOver {k : Type*} [Field k] {ι : K →+* ℂ}
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeightOver k ι w) :
    M.HasWeightsAtMostOver k ι w :=
  IsPureOfWeight.hasWeightsAtMost h

/-- The Frobenius module with the same underlying space as `M` and the Frobenius of `M`
rescaled by a scalar `c`, with junk value `M` itself when `c = 0`. -/
noncomputable def rescale (M : FrobeniusModule.{u, v} K) (c : K) : FrobeniusModule.{u, v} K :=
  letI : Decidable (c = 0) := Classical.dec _
  { carrier := M.carrier
    frobenius := M.frobenius ≪≫ₗ LinearEquiv.smulOfNeZero K M.carrier (if c = 0 then 1 else c)
      (by split <;> simp_all) }

/-- The Tate twist `M(n)` relative to `q`: the same space with the geometric Frobenius
rescaled by `q ^ (-n)`. The twist `(-1)` multiplies the Frobenius by `q`, and hence raises
weights by two (`FrobeniusModule.IsPureOfWeight.tateTwist`). -/
noncomputable def tateTwist (M : FrobeniusModule.{u, v} K) (q : ℕ) (n : ℤ) :
    FrobeniusModule.{u, v} K :=
  M.rescale ((q : K) ^ (-n))

/-- The Frobenius of `M.rescale c`, for `c ≠ 0`, is `c` times the Frobenius of `M`. -/
theorem frobeniusEnd_rescale_apply {M : FrobeniusModule.{u, v} K} {c : K} (hc : c ≠ 0)
    (x : M.carrier) : (M.rescale c).frobeniusEnd x = c • M.frobeniusEnd x := by
  classical
  change (LinearEquiv.smulOfNeZero K M.carrier (if c = 0 then 1 else c) _) (M.frobenius x) = _
  simp [frobeniusEnd, ite_eq_right hc]

/-- The eigenvalues of a rescaled Frobenius are those of the Frobenius, scaled. -/
theorem hasEigenvalue_frobeniusEnd_rescale_iff {M : FrobeniusModule.{u, v} K} {c : K}
    (hc : c ≠ 0) (α : K) :
    (M.rescale c).frobeniusEnd.HasEigenvalue (c * α) ↔ M.frobeniusEnd.HasEigenvalue α := by
  have key : ∀ x : M.carrier, (M.rescale c).frobeniusEnd x = (c * α) • x ↔
      M.frobeniusEnd x = α • x := by
    intro x
    rw [frobeniusEnd_rescale_apply hc, mul_smul]
    exact ⟨fun h ↦ smul_right_injective _ hc h, fun h ↦ by rw [h]⟩
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ((key x).1 hx.1), hx.2⟩)
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ((key x).2 hx.1), hx.2⟩)

/-- A Frobenius module isomorphic to one pure of weight `w` is pure of weight `w`. -/
theorem IsPureOfWeight.of_equiv {ι : K →+* ℂ} {q : ℕ} {M N : FrobeniusModule.{u, v} K}
    (e : M.Equiv N) {w : ℝ} (h : N.IsPureOfWeight ι q w) : M.IsPureOfWeight ι q w :=
  fun α hα ↦ h α (e.hasEigenvalue hα)

/-- Rescaling the Frobenius by `c` with `|ι c| = q ^ (w' / 2)` raises the weight by `w'`. -/
theorem IsPureOfWeight.rescale {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeight ι q w) {c : K} (hc : c ≠ 0)
    {w' : ℝ} (hcw : ‖ι c‖ = (q : ℝ) ^ (w' / 2)) :
    (M.rescale c).IsPureOfWeight ι q (w + w') := by
  intro β hβ
  obtain ⟨α, rfl⟩ : ∃ α, β = c * α := ⟨c⁻¹ * β, by field_simp⟩
  rw [map_mul, norm_mul, h α ((hasEigenvalue_frobeniusEnd_rescale_iff hc α).1 hβ), hcw,
    ← Real.rpow_add (by exact_mod_cast hq)]
  congr 1
  ring

/-- The Tate twist by `n` lowers the weight by `2 n`: the twist `(-1)` raises it by two. -/
theorem IsPureOfWeight.tateTwist {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeight ι q w) (n : ℤ) :
    (M.tateTwist q n).IsPureOfWeight ι q (w - 2 * n) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqK : (q : K) ≠ 0 := by
    intro hK
    have hnorm : ‖ι (q : K)‖ = 0 := by rw [hK, map_zero, norm_zero]
    rw [map_natCast] at hnorm
    simp only [norm_natCast] at hnorm
    exact hq0.ne' (by exact_mod_cast hnorm)
  have hc : ((q : K) ^ (-n)) ≠ 0 := zpow_ne_zero _ hqK
  intro β hβ
  obtain ⟨α, rfl⟩ : ∃ α, β = (q : K) ^ (-n) * α := ⟨((q : K) ^ (-n))⁻¹ * β, by field_simp⟩
  have hα := h α ((hasEigenvalue_frobeniusEnd_rescale_iff hc α).1 hβ)
  have hcnorm : ‖ι ((q : K) ^ (-n))‖ = (q : ℝ) ^ (-n) := by
    rw [map_zpow₀, map_natCast]
    simp
  rw [map_mul, norm_mul, hα, hcnorm, ← Real.rpow_intCast (q : ℝ) (-n), ← Real.rpow_add hq0]
  congr 1
  push_cast
  ring

/-- The dual `M^∨ = Hom_K(M, K)` of a Frobenius module, with the inverse transpose
`f ↦ f ∘ F⁻¹` of the Frobenius `F`, so that the evaluation pairing `M^∨ ⊗ M → K` is
Frobenius-invariant (`FrobeniusModule.dual_frobenius_comp_frobenius`).

The carrier `Module.Dual K M.carrier` lives in universe `max u v`, since the linear maps
`M → K` involve both the carrier of `M` and the field `K`. -/
noncomputable def dual (M : FrobeniusModule.{u, v} K) : FrobeniusModule.{max u v, v} K where
  carrier := Module.Dual K M.carrier
  frobenius := M.frobenius.symm.dualMap

/-- The Frobenius of the dual `M^∨` sends a linear form `f` to `f ∘ F⁻¹`. -/
@[simp]
lemma dual_frobenius_apply (M : FrobeniusModule.{u, v} K) (f : Module.Dual K M.carrier) :
    (M.dual.frobenius f : Module.Dual K M.carrier) = f ∘ₗ M.frobenius.symm.toLinearMap :=
  rfl

/-- The dual `e^∨ : M^∨ ≅ N^∨`, `f ↦ f ∘ e⁻¹`, of an isomorphism of Frobenius modules
`e : M ≅ N`. -/
@[simps toLinearEquiv]
noncomputable def Equiv.dual {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    M.dual.Equiv N.dual where
  toLinearEquiv := e.toLinearEquiv.symm.dualMap
  map_frobenius f := by
    refine LinearMap.ext fun y ↦ ?_
    have h := e.symm.map_frobenius (N.frobenius.symm y)
    rw [LinearEquiv.apply_symm_apply, Equiv.symm_toLinearEquiv] at h
    erw [LinearEquiv.dualMap_apply]
    rw [dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
      LinearEquiv.symm_apply_apply]
    rfl

/-- The dual of a module pure of weight `w` is pure of weight `-w`: the eigenvalues of the
inverse transpose `(F⁻¹)^∨` are the inverses of those of `F`. -/
theorem IsPureOfWeight.dual {ι : K →+* ℂ} {q : ℕ} {M : FrobeniusModule.{u, v} K} {w : ℝ}
    (h : M.IsPureOfWeight ι q w) : M.dual.IsPureOfWeight ι q (-w) := by
  intro α hα
  have hF : M.dual.frobeniusEnd.charpoly = M.frobenius.symm.toLinearMap.charpoly :=
    LinearMap.charpoly_dualMap _
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hF,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have hx' : x = α • M.frobenius x := by
    simpa using congrArg M.frobenius hx.1
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hx.2 (by simpa using hx')
  have hev : M.frobeniusEnd.HasEigenvalue α⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x)
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, hx.2⟩)
    change M.frobenius x = α⁻¹ • x
    conv_rhs => rw [hx', inv_smul_smul₀ hα0]
  have hn := h _ hev
  rw [map_inv₀, norm_inv] at hn
  rw [neg_div, Real.rpow_neg (Nat.cast_nonneg q), ← hn, inv_inv]

/-- The evaluation pairing `M^∨ ⊗ M → K` is invariant under the Frobenius:
`(F^∨ f) (F x) = f x`. -/
lemma dual_frobenius_comp_frobenius (M : FrobeniusModule.{u, v} K)
    (f : Module.Dual K M.carrier) :
    (M.dual.frobenius f : Module.Dual K M.carrier) ∘ₗ M.frobenius.toLinearMap = f := by
  ext
  simp

section Realization

open Polynomial

/-- The direct sum `M ⊕ N` of two Frobenius modules, with the Frobenius acting diagonally. -/
noncomputable def prod (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    FrobeniusModule.{max u t, v} K where
  carrier := M.carrier × N.carrier
  frobenius := M.frobenius.prodCongr N.frobenius

/-- The local polynomial of a direct sum is the product of the local polynomials. -/
theorem localPolynomial_prod (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    (M.prod N).localPolynomial = M.localPolynomial * N.localPolynomial := by
  rw [localPolynomial, localPolynomial, localPolynomial, LinearMap.charpolyRev_def,
    LinearMap.charpolyRev_def, LinearMap.charpolyRev_def, ← Polynomial.reverse_mul_of_domain,
    ← LinearMap.charpoly_prodMap]
  rfl

/-- A direct sum of two modules pure of weight `w` is pure of weight `w`: the characteristic
polynomial of the diagonal Frobenius is the product of those of the summands. -/
theorem IsPureOfWeight.prod {ι : K →+* ℂ} {q : ℕ} {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{t, v} K} {w : ℝ} (hM : M.IsPureOfWeight ι q w)
    (hN : N.IsPureOfWeight ι q w) : (M.prod N).IsPureOfWeight ι q w := by
  intro α hα
  have hF : (M.prod N).frobeniusEnd.charpoly =
      M.frobeniusEnd.charpoly * N.frobeniusEnd.charpoly := by
    rw [← LinearMap.charpoly_prodMap]
    rfl
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hF, Polynomial.IsRoot, Polynomial.eval_mul,
    mul_eq_zero] at hα
  rcases hα with hα | hα
  · exact hM α ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hα)
  · exact hN α ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hα)

/-- Isomorphic Frobenius modules have the same local polynomial. -/
theorem Equiv.localPolynomial_eq {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    M.localPolynomial = N.localPolynomial := by
  have h : N.frobeniusEnd = e.toLinearEquiv.conj M.frobeniusEnd := by
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    simp [LinearEquiv.conj_apply, frobeniusEnd, e.map_frobenius]
  rw [localPolynomial, localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def, h,
    LinearEquiv.charpoly_conj]

/-- An isomorphism of Frobenius modules is also one between their rescalings by `c`. -/
noncomputable def Equiv.rescale {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) (c : K) :
    (M.rescale c).Equiv (N.rescale c) where
  toLinearEquiv := e.toLinearEquiv
  map_frobenius x := by
    change e.toLinearEquiv ((_ : K) • M.frobenius x) = (_ : K) • N.frobenius (e.toLinearEquiv x)
    rw [map_smul]
    exact congrArg _ (e.map_frobenius x)

/-- `ι`-reality only depends on the local polynomial. -/
theorem IsReal.of_localPolynomial_eq {ι : K →+* ℂ} {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{t, v} K} (h : N.IsReal ι) (e : M.localPolynomial = N.localPolynomial) :
    M.IsReal ι := by
  rw [IsReal, e]
  exact h

/-- **A pure Frobenius module is realizable.** If `M` is `ι`-pure of weight `w` relative to `q`
and `ι c = q ^ w`, then `M ⊕ M^∨(c)`, the sum of `M` and of its dual with the Frobenius rescaled
by `c`, is `ι`-real. Over the algebraically closed field `K` the Frobenius `F` has eigenvalues
`α₁, …, αₙ`; those of the second summand are the `c αᵢ⁻¹`, and
`ι (c αᵢ⁻¹) = |ι αᵢ|² / ι αᵢ = conj (ι αᵢ)`. Hence the local polynomial of the sum is
`Q · conj Q` for `Q = ∏ (1 - ι αᵢ T)`, which has real coefficients.
(blueprint: `proposition-twisting-weight-zero-adding-dual`) -/
theorem IsPureOfWeight.isReal_prod_rescale_dual [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ}
    (hq : 0 < q) {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeight ι q w) {c : K}
    (hc : ι c = (((q : ℝ) ^ w : ℝ) : ℂ)) :
    (M.prod (M.dual.rescale c)).IsReal ι := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Complex.ofReal_eq_zero] at hc
    exact (Real.rpow_pos_of_pos hq0 w).ne' hc
  set F := M.frobeniusEnd with hF
  set n := Module.finrank K M.carrier
  -- the second summand has the reverse characteristic polynomial of `c F⁻¹`
  set G : Module.End K M.carrier := c • M.frobenius.symm.toLinearMap
  have hFG : F * G = c • 1 := by
    ext x
    simp [F, G, frobeniusEnd]
  have hGdual : (M.dual.rescale c).localPolynomial = G.charpolyRev := by
    rw [localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def,
      ← LinearMap.charpoly_dualMap G]
    congr 2
    refine LinearMap.ext fun (f : Module.Dual K M.carrier) ↦
      (frobeniusEnd_rescale_apply (M := M.dual) hc0 f).trans ?_
    refine LinearMap.ext fun x ↦ ?_
    change c * f (M.frobenius.symm x) = f (c • M.frobenius.symm x)
    rw [map_smul, smul_eq_mul]
  have key := LinearMap.C_det_mul_charpolyRev hFG
  -- the roots of the realized characteristic polynomial
  set R : ℂ[X] := F.charpoly.map ι
  set s := R.roots
  have hsplit : F.charpoly.Splits := IsAlgClosed.splits _
  have hRm : R.Monic := (LinearMap.charpoly_monic F).map ι
  have hRs : R.Splits := IsAlgClosed.splits _
  have hR : R = (s.map fun z ↦ X - C z).prod := by
    simpa [hRm.leadingCoeff] using hRs.eq_prod_roots
  have hroots : s = F.charpoly.roots.map ι := hsplit.roots_map ι
  have hs : ∀ z ∈ s, z * (starRingEnd ℂ) z = ι c := by
    intro z hz
    rw [hroots, Multiset.mem_map] at hz
    obtain ⟨α, hα, rfl⟩ := hz
    have hev : F.HasEigenvalue α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly F α).2
        (Polynomial.isRoot_of_mem_roots hα)
    have hn := h α hev
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, hc, ← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le]
    norm_num
  have hcard : s.card = n := by
    rw [← hRs.natDegree_eq_card_roots, Polynomial.natDegree_map, LinearMap.charpoly_natDegree]
  have hdet : ι F.det = s.prod := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, map_mul, map_pow, map_neg, map_one,
      ← Polynomial.coeff_map, hRs.coeff_zero_eq_prod_roots_of_monic hRm,
      hRs.natDegree_eq_card_roots, hcard, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hrev (t : Multiset ℂ) :
      ((t.map fun z ↦ X - C z).prod).reverse = (t.map fun z ↦ 1 - C z * X).prod := by
    induction t using Multiset.induction_on with
    | empty => simpa using reverse_C (1 : ℂ)
    | cons a t ih =>
      have hX : (X : ℂ[X]).reverse = 1 := by rw [← one_mul X, reverse_mul_X, ← C_1, reverse_C]
      rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons,
        Multiset.prod_cons, sub_eq_add_neg, ← C_neg, reverse_add_C, hX]
      simp [sub_eq_add_neg]
  have hQ : M.localPolynomial.map ι = (s.map fun z ↦ 1 - C z * X).prod := by
    rw [localPolynomial, LinearMap.charpolyRev_def, ← hrev, ← hR]
    simp only [R, F, reverse, reflect_map, natDegree_map]
  have hdet0 : s.prod ≠ 0 := by
    rw [← hdet]
    exact (map_ne_zero ι).2 (LinearEquiv.isUnit_det' M.frobenius).ne_zero
  have hcomp : R.comp (C (ι c) * X) = C ((-1) ^ n * s.prod) *
      (s.map fun z ↦ 1 - C ((starRingEnd ℂ) z) * X).prod := by
    have hfac : ∀ z ∈ s, (X - C z).comp (C (ι c) * X) =
        C (-z) * (1 - C ((starRingEnd ℂ) z) * X) := by
      intro z hz
      rw [← hs z hz]
      simp only [sub_comp, X_comp, C_comp, C_neg, C_mul]
      ring
    rw [hR, multiset_prod_comp, Multiset.map_map, Function.comp_def, Multiset.map_congr rfl hfac,
      Multiset.prod_map_mul, ← hcard, ← Multiset.prod_map_neg, map_multiset_prod, Multiset.map_map]
    rfl
  have hQ' : (M.dual.rescale c).localPolynomial.map ι =
      (s.map fun z ↦ 1 - C ((starRingEnd ℂ) z) * X).prod := by
    have hkey := congrArg (Polynomial.map ι) key
    rw [Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, Polynomial.map_comp,
      Polynomial.map_mul, map_C, map_X, hcomp, hdet, ← mul_assoc, ← C_mul, map_pow, map_neg,
      map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at hkey
    rw [hGdual]
    exact mul_left_cancel₀ (C_ne_zero.2 hdet0) hkey
  intro k
  rw [localPolynomial_prod, ← Polynomial.coeff_map, Polynomial.map_mul, hQ, hQ']
  set A := (s.map fun z ↦ 1 - C z * X).prod
  have hB : (s.map fun z ↦ 1 - C ((starRingEnd ℂ) z) * X).prod = A.map (starRingEnd ℂ) := by
    simp [A, Polynomial.map_multiset_prod, Multiset.map_map]
  rw [hB, ← Polynomial.coeff_map (starRingEnd ℂ), Polynomial.map_mul, Polynomial.map_map]
  have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ :=
    RingHom.ext Complex.conj_conj
  rw [hcc, Polynomial.map_id, mul_comm]

/-- Rescaling the Frobenius by `1` does not change it. -/
noncomputable def rescaleOneEquiv (M : FrobeniusModule.{u, v} K) : (M.rescale 1).Equiv M where
  toLinearEquiv := LinearEquiv.refl K M.carrier
  map_frobenius x := (frobeniusEnd_rescale_apply (M := M) one_ne_zero x).trans (one_smul K _)

/-- If `M` is `ι`-pure of weight `0` relative to `q > 0`, then `M ⊕ M^∨` is `ι`-real: this is
`FrobeniusModule.IsPureOfWeight.isReal_prod_rescale_dual` with `c = 1`. -/
theorem IsPureOfWeight.isReal_prod_dual [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} (h : M.IsPureOfWeight ι q 0) : (M.prod M.dual).IsReal ι := by
  refine (h.isReal_prod_rescale_dual hq (c := 1) (by simp)).of_localPolynomial_eq ?_
  rw [localPolynomial_prod, localPolynomial_prod, (rescaleOneEquiv _).localPolynomial_eq]

end Realization

end FrobeniusModule
