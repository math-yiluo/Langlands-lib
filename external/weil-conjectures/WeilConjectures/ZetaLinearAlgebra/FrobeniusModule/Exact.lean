/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Upper weight bounds along exact sequences of Frobenius modules

An upper weight bound `|ι α| ≤ q ^ (w / 2)` on the eigenvalues of the Frobenius passes to
subobjects and quotients, and from the two outer terms of an exact sequence `A → B → C` of
Frobenius modules to the middle one: an eigenvalue of `B` is an eigenvalue of `A` or of `C`. It
also descends along finite constant extensions, where the Frobenius `F` becomes `Fᵐ` and the
field cardinality `q` becomes `qᵐ`.

## Main statements

- `FrobeniusModule.hasEigenvalue_of_exact`: an eigenvalue of the middle term of an exact
  sequence is one of an outer term.
- `FrobeniusModule.HasWeightsAtMost.of_functionExact`
(`proposition-weights-under-usual-operations--2`): the middle
  term of an exact sequence inherits a common upper weight bound.
- `FrobeniusModule.hasWeightsAtMost_of_forall_hasEigenvalue`
  (`lemma-bounding-weights-mixed-sheaf--1`): a bound on all eigenvalues is an upper weight bound.
- `FrobeniusModule.HasWeightsAtMost.of_powFrobenius` (`lemma-weight-bound-constant-extension`):
  a weight bound over a finite constant extension descends.
- `FrobeniusModule.roots_charpoly_frobeniusEnd_map_eq_add` (`lemma-filtrations-spectra--2`): the
  spectrum of the middle term of a short exact sequence is the sum of those of the outer terms.
- `FrobeniusModule.HasWeightsAtMost.of_subquotient` (`lemma-subobjects-quotients-weil-sheaves--3`):
  weights of subquotients.
-/

@[expose] public section

universe u v t s

namespace FrobeniusModule

variable {K : Type v} [Field K]

section Range

variable {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{t, v} K}
  (g : M.carrier →ₗ[K] N.carrier) (hg : ∀ x, g (M.frobenius x) = N.frobenius (g x))
include hg

/-- If an eigenvector of the Frobenius of `N` lies in the range of a Frobenius-equivariant map
`g : M → N`, its eigenvalue is an eigenvalue of the Frobenius of `M`: otherwise `F - α` is
injective on `M`, hence bijective on the Frobenius-stable subspace `ker g`, and the eigenvector
would be `0`. -/
theorem hasEigenvalue_of_hasEigenvector_mem_range {α : K} {y : N.carrier}
    (hy : N.frobeniusEnd.HasEigenvector α y) (hyg : y ∈ LinearMap.range g) :
    M.frobeniusEnd.HasEigenvalue α := by
  by_contra hM
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  let T : Module.End K M.carrier := M.frobeniusEnd - α • LinearMap.id
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    by_contra h0
    refine hM (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, h0⟩
    have : M.frobeniusEnd v - α • v = 0 := hv
    exact sub_eq_zero.1 this
  have hgT : ∀ v, g (T v) = N.frobeniusEnd (g v) - α • g v := fun v ↦ by
    simp [T, frobeniusEnd, hg]
  have hmaps : ∀ v ∈ LinearMap.ker g, T v ∈ LinearMap.ker g := fun v hv ↦ by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hgT, hv, map_zero, smul_zero, sub_zero]
  have hT'inj : Function.Injective (T.restrict hmaps) := fun a b hab ↦
    Subtype.ext (hTinj (congrArg Subtype.val hab))
  have hT'surj := LinearMap.injective_iff_surjective.mp hT'inj
  obtain ⟨x, rfl⟩ := hyg
  have hTx : T x ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker, hgT, hy.1, sub_self]
  obtain ⟨z, hz⟩ := hT'surj ⟨T x, hTx⟩
  have hzx : (z : M.carrier) = x := hTinj (congrArg Subtype.val hz)
  apply hy.2
  rw [← hzx]
  exact z.2

end Range

section Exact

variable {A : FrobeniusModule.{u, v} K} {B : FrobeniusModule.{t, v} K}
  {C : FrobeniusModule.{s, v} K} (f : A.carrier →ₗ[K] B.carrier) (g : B.carrier →ₗ[K] C.carrier)
  (hf : ∀ x, f (A.frobenius x) = B.frobenius (f x))
  (hg : ∀ x, g (B.frobenius x) = C.frobenius (g x))
include hf hg

/-- An eigenvalue of the Frobenius of the middle term of an exact sequence `A → B → C` of
Frobenius modules is an eigenvalue of the Frobenius of `A` or of `C`: an eigenvector `y` of `B`
either has a nonzero image in `C`, an eigenvector there, or lies in the image of `A`. -/
theorem hasEigenvalue_of_exact (hfg : Function.Exact f g) {α : K}
    (hα : B.frobeniusEnd.HasEigenvalue α) :
    A.frobeniusEnd.HasEigenvalue α ∨ C.frobeniusEnd.HasEigenvalue α := by
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  by_cases hgy : g y = 0
  · exact Or.inl (hasEigenvalue_of_hasEigenvector_mem_range f hf hy ((hfg y).1 hgy))
  · refine Or.inr (Module.End.hasEigenvalue_of_hasEigenvector (x := g y) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy ⊢
    refine ⟨?_, hgy⟩
    change C.frobenius (g y) = α • g y
    rw [← hg, ← map_smul]
    exact congrArg g hy.1

/-- **Extension bounds.** If the outer terms of an exact sequence `A → B → C` of Frobenius
modules have weights at most `w`, so has the middle term. In particular this holds for a short
exact sequence `0 → A → B → C → 0`. (blueprint: `proposition-weights-under-usual-operations--2`) -/
theorem HasWeightsAtMost.of_functionExact (hfg : Function.Exact f g) {ι : K →+* ℂ} {q : ℕ}
    {w : ℝ} (hA : A.HasWeightsAtMost ι q w) (hC : C.HasWeightsAtMost ι q w) :
    B.HasWeightsAtMost ι q w := fun α hα ↦
  (hasEigenvalue_of_exact f g hf hg hfg hα).elim (hA α) (hC α)

end Exact

/-- **A punctual bound is a module bound.** If every eigenvalue `α` of the Frobenius of `M`
satisfies `|ι α| ≤ q ^ (w / 2)`, then `M` has weights at most `w`: upper weight bounds of
Frobenius modules are phrased on the eigenvalues, every simple Frobenius module over an
algebraically closed field being a line with a single eigenvalue.
(blueprint: `lemma-bounding-weights-mixed-sheaf--1`) -/
theorem hasWeightsAtMost_of_forall_hasEigenvalue {M : FrobeniusModule.{u, v} K} {ι : K →+* ℂ}
    {q : ℕ} {w : ℝ} (h : ∀ α, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ ≤ (q : ℝ) ^ (w / 2)) :
    M.HasWeightsAtMost ι q w :=
  h

/-- The Frobenius module `(M, Fᵐ)`: the same space, with the `m`-th power of the Frobenius. It
is the Frobenius module of `M` over the constant extension of degree `m` of the base field. -/
noncomputable def powFrobenius (M : FrobeniusModule.{u, v} K) (m : ℕ) :
    FrobeniusModule.{u, v} K where
  carrier := M.carrier
  frobenius := M.frobenius ^ m

lemma powFrobenius_frobeniusEnd (M : FrobeniusModule.{u, v} K) (m : ℕ) :
    (M.powFrobenius m).frobeniusEnd = M.frobeniusEnd ^ m := by
  ext x
  change (M.frobenius ^ m) x = (M.frobeniusEnd ^ m) x
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, pow_succ, LinearEquiv.mul_apply, Module.End.mul_apply, ih]; rfl

/-- If `α` is an eigenvalue of the Frobenius `F`, then `αᵐ` is an eigenvalue of `Fᵐ`. -/
theorem hasEigenvalue_powFrobenius {M : FrobeniusModule.{u, v} K} {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) (m : ℕ) :
    (M.powFrobenius m).frobeniusEnd.HasEigenvalue (α ^ m) := by
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_
  have key : ∀ n : ℕ, (M.frobeniusEnd ^ n) x = α ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx.1, smul_smul, pow_succ]
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, powFrobenius_frobeniusEnd]
  exact ⟨key m, hx.2⟩

/-- **Weight bounds over a finite constant extension.** If, over the constant extension of
degree `m ≠ 0`, where the Frobenius becomes `Fᵐ` and the field cardinality becomes `qᵐ`, the
module `M` has weights at most `b`, then it has weights at most `b` over the original field:
`|ι α|ᵐ = |ι αᵐ| ≤ (qᵐ) ^ (b / 2)` gives `|ι α| ≤ q ^ (b / 2)`.
(blueprint: `lemma-weight-bound-constant-extension`) -/
theorem HasWeightsAtMost.of_powFrobenius {M : FrobeniusModule.{u, v} K} {ι : K →+* ℂ} {q m : ℕ}
    (hm : m ≠ 0) {b : ℝ} (h : (M.powFrobenius m).HasWeightsAtMost ι (q ^ m) b) :
    M.HasWeightsAtMost ι q b := by
  intro α hα
  have hb := h _ (hasEigenvalue_powFrobenius hα m)
  have e : ((q : ℝ) ^ m) ^ (b / 2) = ((q : ℝ) ^ (b / 2)) ^ m := by
    rw [← Real.rpow_natCast ((q : ℝ) ^ (b / 2)) m, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast (q : ℝ) m, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  rw [map_pow, norm_pow, Nat.cast_pow, e] at hb
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hm).1 hb

/-- A Frobenius module with weights at most `w` whose dual has weights at most `-w` (through an
isomorphism `N ≃ M^∨`) is pure of weight `w`: the eigenvalues of the Frobenius of `M^∨` are the
inverses of those of `M`. -/
theorem IsPureOfWeight.of_hasWeightsAtMost_of_equiv_dual {ι : K →+* ℂ} {q : ℕ}
    {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{max u v, v} K} (e : N.Equiv M.dual) {w : ℝ}
    (h : M.HasWeightsAtMost ι q w) (h' : N.HasWeightsAtMost ι q (-w)) :
    M.IsPureOfWeight ι q w := by
  intro α hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hx.2 (M.frobenius.injective
      ((by simpa using hx.1 : M.frobeniusEnd x = 0).trans (map_zero _).symm))
  have hx' : M.frobenius.symm x = α⁻¹ • x := by
    apply M.frobenius.injective
    rw [LinearEquiv.apply_symm_apply, map_smul]
    change x = α⁻¹ • M.frobeniusEnd x
    rw [hx.1, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hinv : Module.End.HasEigenvalue (M.frobenius.symm.toLinearMap : Module.End K M.carrier)
      α⁻¹ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hx', hx.2⟩)
  have hN : N.frobeniusEnd.HasEigenvalue α⁻¹ := by
    have hF : M.dual.frobeniusEnd.charpoly = M.frobenius.symm.toLinearMap.charpoly :=
      LinearMap.charpoly_dualMap _
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← e.charpoly_frobeniusEnd, hF,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hinv
  have hn := h' _ hN
  rw [map_inv₀, norm_inv, neg_div, Real.rpow_neg (Nat.cast_nonneg q)] at hn
  have hpos : 0 < ‖ι α‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hα0)
  have hq : 0 < (q : ℝ) ^ (w / 2) := by
    rcases (Nat.cast_nonneg q : (0 : ℝ) ≤ q).lt_or_eq with hq | hq
    · exact Real.rpow_pos_of_pos hq _
    · have := h α hα
      rw [← hq] at this ⊢
      by_contra hle
      have h0 : (0 : ℝ) ^ (w / 2) = 0 := le_antisymm (not_lt.1 hle) (Real.rpow_nonneg le_rfl _)
      rw [h0] at this
      exact absurd this (not_le.2 hpos)
  exact le_antisymm (h α hα) ((inv_le_inv₀ hpos hq).1 hn)

section CharpolyExact

open Polynomial

variable {M' M M'' : FrobeniusModule.{u, v} K}
  (f : M'.carrier →ₗ[K] M.carrier) (g : M.carrier →ₗ[K] M''.carrier)
  (hf : ∀ x, f (M'.frobenius x) = M.frobenius (f x))
  (hg : ∀ x, g (M.frobenius x) = M''.frobenius (g x))

include hf hg in
/-- *Spectrum of an exact Frobenius sequence*, characteristic polynomials: for a short exact
sequence `0 → V' → V → V'' → 0` of Frobenius modules with Frobenius-equivariant maps,
`χ_V = χ_{V'} χ_{V''}`. The image of `V'` is a Frobenius-stable subspace of `V`, isomorphic to
`V'`, with quotient isomorphic to `V''`, so this is
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`.
(blueprint: `lemma-filtrations-spectra--2`) -/
theorem charpoly_frobeniusEnd_eq_mul (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    M.frobeniusEnd.charpoly = M'.frobeniusEnd.charpoly * M''.frobeniusEnd.charpoly := by
  set W : Submodule K M.carrier := LinearMap.range f
  have hW : W ≤ W.comap M.frobeniusEnd := by
    rintro _ ⟨x, rfl⟩
    exact ⟨M'.frobenius x, hf x⟩
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ _ W hW]
  congr 1
  · -- the restriction to `W = f(V')` is conjugate to the Frobenius of `V'`
    refine (LinearMap.charpoly_eq_of_comp_eq (LinearEquiv.ofInjective f hinj) ?_).symm
    ext x
    exact hf x
  · -- the quotient `V ⧸ W` is identified with `V''` by `g`
    have hker : LinearMap.ker g = W := by
      ext x
      exact (hexact x).trans (by rfl)
    let e : (M.carrier ⧸ W) ≃ₗ[K] M''.carrier :=
      (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)
    refine LinearMap.charpoly_eq_of_comp_eq e ?_
    ext x
    exact hg x

include hf hg in
/-- *Spectrum of an exact Frobenius sequence*: for a short exact sequence `0 → V' → V → V'' → 0`
of Frobenius modules with Frobenius-equivariant maps, the spectrum of `V` — the multiset of the
images under `ι : K →+* ℂ` of the eigenvalues of its Frobenius, counted with algebraic
multiplicity — is the sum of the spectra of `V'` and `V''`.
(blueprint: `lemma-filtrations-spectra--2`) -/
theorem roots_charpoly_frobeniusEnd_map_eq_add (ι : K →+* ℂ) (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    (M.frobeniusEnd.charpoly.map ι).roots =
      (M'.frobeniusEnd.charpoly.map ι).roots + (M''.frobeniusEnd.charpoly.map ι).roots := by
  rw [charpoly_frobeniusEnd_eq_mul f g hf hg hinj hsurj hexact, Polynomial.map_mul,
    Polynomial.roots_mul]
  exact mul_ne_zero ((M'.frobeniusEnd.charpoly_monic.map ι).ne_zero)
    ((M''.frobeniusEnd.charpoly_monic.map ι).ne_zero)

end CharpolyExact



/-- *Subquotient bounds for Frobenius modules*: if `(V, F)` has weights at most `w`, then so
has every Frobenius-stable subquotient of `V`, presented as a Frobenius-equivariant quotient
`A ↠ S` of a Frobenius-equivariant subspace `A ↪ V`.
(blueprint: `lemma-subobjects-quotients-weil-sheaves--3`) -/
theorem HasWeightsAtMost.of_subquotient {V A S : FrobeniusModule.{u, v} K}
    (i : A.carrier →ₗ[K] V.carrier) (hi : ∀ x, i (A.frobenius x) = V.frobenius (i x))
    (hinj : Function.Injective i) (p : A.carrier →ₗ[K] S.carrier)
    (hp : ∀ x, p (A.frobenius x) = S.frobenius (p x)) (hsurj : Function.Surjective p)
    {ι : K →+* ℂ} {q : ℕ} {w : ℝ} (h : V.HasWeightsAtMost ι q w) :
    S.HasWeightsAtMost ι q w :=
  (h.of_injective i hi hinj).of_surjective p hp hsurj

end FrobeniusModule
