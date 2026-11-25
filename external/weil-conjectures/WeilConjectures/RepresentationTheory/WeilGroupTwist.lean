/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.RepresentationTheory.CompositionSeries

/-!
# Twisting irreducible representations of a Weil group to bounded ones

Let `W` be a group with a surjection `deg : W →* Multiplicative ℤ` (the Weil group of a scheme
over a finite field, `deg` the degree, `I = ker deg` the geometric fundamental group), and let
`ρ` be a finite-dimensional irreducible representation of `W` over an algebraically closed
field `k`. Following Deligne, *La conjecture de Weil II*, 1.3.13–1.3.14, we show that if the
image of `I` is small then a twist of `ρ` by a character `b ^ (-deg)` has small image:

* `Representation.exists_isBoundedOn_twist` (Weil II, 1.3.14): if `k` is a normed field
  and `ρ(I)` is bounded, then for some `b ∈ kˣ` the twist `ρ ⊗ b ^ (-deg)` has bounded image.
  For `k = ℚ̄_ℓ` (e.g. `PadicAlgCl ℓ`) this is the statement that an irreducible Weil sheaf
  is the twist of an étale `ℚ̄_ℓ`-sheaf.
* `Representation.exists_finite_range_twist`: if `ρ(I)` is finite (finite geometric
  monodromy), then for some `b ∈ kˣ` the twist `ρ ⊗ b ^ (-deg)` has finite image.
* `Representation.finrank_eq_one_and_exists_twist_eq_one`: if `I` acts trivially, then
  `V` is one-dimensional and `ρ = b ^ deg` for some `b ∈ kˣ`; without irreducibility, every
  composition factor is such a character
  (`Representation.CompositionSeries.finrank_factor_eq_one_and_exists_twist_eq_one`).
* `Representation.exists_isBoundedOn_twist_padicAlgCl`: the case `k = PadicAlgCl ℓ = ℚ̄_ℓ`.

Boundedness of a set of vectors is expressed basis-free by `Module.IsWeaklyBounded`: every
linear form is bounded on it. For a finite-dimensional space this is boundedness of the
coordinates in one (equivalently any) basis, and for a set of endomorphisms (via
`Representation.IsBoundedOn`) boundedness of the matrix entries; for `ℚ̄_ℓ` and a subgroup
`ρ(H)` this is the property of being contained in `GL(L)` for a lattice `L` over the ring of
integers of a finite extension of `ℚ_ℓ` over which `ρ(H)` is defined.

The proof of 1.3.14 is elementary: choose `F` of degree one and an eigenvalue `λ` of `ρ(F)`,
and let `Ψ = λ⁻¹ ρ(F)`. Since `F` normalises `I`, the vectors whose forward `Ψ`-orbit is bounded
form a subrepresentation, which contains a `λ`-eigenvector of `ρ(F)`; by irreducibility every
vector has bounded forward orbit. The same holds for backward orbits, and since every element
of `W` is a product of an element of `I` with a power of `F`, the twist by `λ⁻¹ ^ deg` is
bounded.
-/

@[expose] public section

open Module

namespace Module

section WeaklyBounded

variable (k : Type*) {V : Type*} [NormedField k] [AddCommGroup V] [Module k V]

/-- A set of vectors in a vector space over a normed field is *weakly bounded* if every linear
form is bounded on it. In finite dimension this means that the coordinates in a (any) basis are
bounded. -/
def IsWeaklyBounded (s : Set V) : Prop :=
  ∀ φ : Module.Dual k V, ∃ C, ∀ x ∈ s, ‖φ x‖ ≤ C

variable {k}

theorem IsWeaklyBounded.mono {s t : Set V} (h : IsWeaklyBounded k t) (hst : s ⊆ t) :
    IsWeaklyBounded k s :=
  fun φ ↦ (h φ).imp fun _ hC x hx ↦ hC x (hst hx)

theorem IsWeaklyBounded.union {s t : Set V} (hs : IsWeaklyBounded k s)
    (ht : IsWeaklyBounded k t) : IsWeaklyBounded k (s ∪ t) := by
  intro φ
  obtain ⟨C, hC⟩ := hs φ
  obtain ⟨D, hD⟩ := ht φ
  refine ⟨max C D, fun x hx ↦ ?_⟩
  rcases hx with hx | hx
  · exact (hC x hx).trans (le_max_left _ _)
  · exact (hD x hx).trans (le_max_right _ _)

theorem isWeaklyBounded_singleton (x : V) : IsWeaklyBounded k {x} :=
  fun φ ↦ ⟨‖φ x‖, by simp⟩

/-- In finite dimension, applying a pointwise weakly bounded set of endomorphisms to a weakly
bounded set of vectors gives a weakly bounded set. -/
theorem IsWeaklyBounded.image2_apply [FiniteDimensional k V] {S : Set (Module.End k V)}
    {s : Set V} (hS : ∀ v, IsWeaklyBounded k ((fun f : Module.End k V ↦ f v) '' S))
    (hs : IsWeaklyBounded k s) : IsWeaklyBounded k (Set.image2 (fun f x ↦ f x) S s) := by
  intro φ
  let b := Module.finBasis k V
  choose C hC using fun j ↦ hs (b.coord j)
  choose D hD using fun j ↦ hS (b j) φ
  refine ⟨∑ j, C j * D j, ?_⟩
  rintro _ ⟨f, hf, x, hx, rfl⟩
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul (hC j x hx) (hD j _ ⟨f, hf, rfl⟩) (norm_nonneg _)
    ((norm_nonneg _).trans (hC j x hx))

end WeaklyBounded

namespace End

variable {k V : Type*} [NormedField k] [AddCommGroup V] [Module k V]

/-- The subspace of vectors whose forward orbit under an endomorphism `Ψ` is weakly bounded. -/
def boundedOrbitSubmodule (Ψ : Module.End k V) : Submodule k V where
  carrier := {v | IsWeaklyBounded k (Set.range fun n : ℕ ↦ (Ψ ^ n) v)}
  zero_mem' φ := ⟨0, by simp⟩
  add_mem' {u v} hu hv φ := by
    obtain ⟨C, hC⟩ := hu φ
    obtain ⟨D, hD⟩ := hv φ
    refine ⟨C + D, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [map_add, map_add]
    exact (norm_add_le _ _).trans (add_le_add (hC _ ⟨n, rfl⟩) (hD _ ⟨n, rfl⟩))
  smul_mem' c v hv φ := by
    obtain ⟨C, hC⟩ := hv φ
    refine ⟨‖c‖ * C, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [map_smul, map_smul, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨n, rfl⟩) (norm_nonneg c)

theorem mem_boundedOrbitSubmodule {Ψ : Module.End k V} {v : V} :
    v ∈ boundedOrbitSubmodule Ψ ↔ IsWeaklyBounded k (Set.range fun n : ℕ ↦ (Ψ ^ n) v) :=
  Iff.rfl

/-- **Bounded forward orbits** (the key step of Deligne, Weil II, 1.3.14). Let `K` be a pointwise
weakly bounded set of endomorphisms of a finite-dimensional space, normalised by an invertible
endomorphism `Ψ` (with inverse `Ψ'`), such that `V` is irreducible under `K`, `Ψ` and `Ψ'`.
If `Ψ` fixes a nonzero vector, then every vector has a weakly bounded forward `Ψ`-orbit. -/
theorem isWeaklyBounded_range_pow_apply [FiniteDimensional k V] {K : Set (Module.End k V)}
    (hK : ∀ v, IsWeaklyBounded k ((fun f : Module.End k V ↦ f v) '' K))
    {Ψ Ψ' : Module.End k V} (hΨΨ' : Ψ * Ψ' = 1)
    (hΨK : ∀ g ∈ K, ∃ g' ∈ K, Ψ * g = g' * Ψ)
    (hirr : ∀ U : Submodule k V, (∀ g ∈ K, U ≤ U.comap g) → U ≤ U.comap Ψ →
      U ≤ U.comap Ψ' → U = ⊥ ∨ U = ⊤)
    {v₀ : V} (hv₀ : v₀ ≠ 0) (hΨv₀ : Ψ v₀ = v₀) (v : V) :
    IsWeaklyBounded k (Set.range fun n : ℕ ↦ (Ψ ^ n) v) := by
  have hpow (n : ℕ) (g : Module.End k V) (hg : g ∈ K) : ∃ g' ∈ K, Ψ ^ n * g = g' * Ψ ^ n := by
    induction n generalizing g with
    | zero => exact ⟨g, hg, by simp⟩
    | succ n ih =>
      obtain ⟨g₁, hg₁, h₁⟩ := ih g hg
      obtain ⟨g₂, hg₂, h₂⟩ := hΨK g₁ hg₁
      refine ⟨g₂, hg₂, ?_⟩
      rw [pow_succ', mul_assoc, h₁, ← mul_assoc, h₂, mul_assoc]
  have hK' (g : Module.End k V) (hg : g ∈ K) :
      boundedOrbitSubmodule Ψ ≤ (boundedOrbitSubmodule Ψ).comap g := by
    intro x hx
    refine (IsWeaklyBounded.image2_apply hK hx).mono ?_
    rintro _ ⟨n, rfl⟩
    obtain ⟨g', hg', h⟩ := hpow n g hg
    exact ⟨g', hg', _, ⟨n, rfl⟩, by
      beta_reduce
      rw [← Module.End.mul_apply, ← h, Module.End.mul_apply]⟩
  have hΨU : boundedOrbitSubmodule Ψ ≤ (boundedOrbitSubmodule Ψ).comap Ψ := by
    intro x hx
    refine (hx : IsWeaklyBounded k _).mono ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 1, by
      beta_reduce
      rw [pow_succ, Module.End.mul_apply]⟩
  have hΨ'U : boundedOrbitSubmodule Ψ ≤ (boundedOrbitSubmodule Ψ).comap Ψ' := by
    intro x hx
    refine ((isWeaklyBounded_singleton (Ψ' x)).union hx).mono ?_
    rintro _ ⟨n, rfl⟩
    rcases n with _ | n
    · left
      simp
    · right
      refine ⟨n, ?_⟩
      beta_reduce
      rw [pow_succ, Module.End.mul_apply, ← Module.End.mul_apply Ψ, hΨΨ', Module.End.one_apply]
  obtain h | h := hirr (boundedOrbitSubmodule Ψ) hK' hΨU hΨ'U
  · refine absurd ?_ hv₀
    rw [← Submodule.mem_bot k, ← h, mem_boundedOrbitSubmodule]
    have hfix (n : ℕ) : (Ψ ^ n) v₀ = v₀ := by
      rw [Module.End.pow_apply]
      exact Function.iterate_fixed hΨv₀ n
    simp_rw [hfix]
    exact (isWeaklyBounded_singleton v₀).mono (by simp)
  · rw [← mem_boundedOrbitSubmodule, h]
    exact Submodule.mem_top

end End

end Module

namespace Representation

section Twist

variable {k W V : Type*} [Field k] [Group W] [AddCommGroup V] [Module k V]

/-- The twist `ρ ⊗ χ` of a representation by a character `χ : W →* kˣ`, acting on the same
space by `w ↦ χ(w) • ρ(w)`. -/
def twist (ρ : Representation k W V) (χ : W →* kˣ) : Representation k W V where
  toFun w := (χ w : k) • ρ w
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

@[simp]
theorem twist_apply (ρ : Representation k W V) (χ : W →* kˣ) (w : W) :
    ρ.twist χ w = (χ w : k) • ρ w :=
  rfl

/-- The character `w ↦ b ^ deg w` of a group with a degree map `deg : W →* Multiplicative ℤ`. -/
def degreeCharacter (deg : W →* Multiplicative ℤ) (b : kˣ) : W →* kˣ :=
  (zpowersHom kˣ b).comp deg

@[simp]
theorem degreeCharacter_apply (deg : W →* Multiplicative ℤ) (b : kˣ) (w : W) :
    degreeCharacter deg b w = b ^ Multiplicative.toAdd (deg w) :=
  rfl

/-- An element of degree one together with the kernel of `deg` generates `W`: every `w` is
`(w * F ^ (-deg w)) * F ^ deg w` with the first factor in the kernel. -/
theorem mul_zpow_neg_mem_ker {deg : W →* Multiplicative ℤ} {F : W}
    (hF : deg F = Multiplicative.ofAdd 1) (w : W) :
    w * F ^ (-Multiplicative.toAdd (deg w)) ∈ deg.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_zpow, hF]
  apply Multiplicative.toAdd.injective
  simp

end Twist

section Bounded

variable {k W V : Type*} [NormedField k] [Group W] [AddCommGroup V] [Module k V]

/-- A representation `ρ` is *bounded* on a subset `H` if for every vector `v` the set
`{ρ(w) v | w ∈ H}` is weakly bounded. For a finite-dimensional representation this means that
the matrix entries of `ρ(w)`, `w ∈ H`, in one (equivalently any) basis are bounded. -/
def IsBoundedOn (ρ : Representation k W V) (H : Set W) : Prop :=
  ∀ v, Module.IsWeaklyBounded k ((fun w ↦ ρ w v) '' H)

/-- **Deligne, Weil II, 1.3.14.** Let `deg : W →* ℤ` be surjective with kernel `I` and let `ρ` be
a finite-dimensional irreducible representation of `W` over an algebraically closed normed
field `k` such that `ρ(I)` is bounded. Then there is `b ∈ kˣ` such that the twist
`ρ ⊗ b ^ (-deg)` is bounded on all of `W`. -/
theorem exists_isBoundedOn_twist [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k W V) [ρ.IsIrreducible] {deg : W →* Multiplicative ℤ}
    (hdeg : Function.Surjective deg) (hI : ρ.IsBoundedOn deg.ker) :
    ∃ b : kˣ, (ρ.twist (degreeCharacter deg b⁻¹)).IsBoundedOn Set.univ := by
  have := ‹ρ.IsIrreducible›.nontrivial
  obtain ⟨F, hF⟩ := hdeg (Multiplicative.ofAdd 1)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ F)
  obtain ⟨v₀, hv₀⟩ := hμ.exists_hasEigenvector
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hv₀.2
    rw [← ρ.inv_self_apply F v₀, hv₀.apply_eq_smul, zero_smul, map_zero]
  set b := Units.mk0 μ hμ0
  set σ := ρ.twist (degreeCharacter deg b⁻¹)
  have hσ (w w' : W) : σ w * σ w' = σ (w * w') := (map_mul σ w w').symm
  have hσI (i : W) (hi : i ∈ deg.ker) : σ i = ρ i := by
    rw [MonoidHom.mem_ker] at hi
    simp [σ, hi]
  have hΨv₀ : σ F v₀ = v₀ := by
    simp [σ, hF, hv₀.apply_eq_smul, b, smul_smul, hμ0]
  set K := σ '' deg.ker
  have hK (v : V) : Module.IsWeaklyBounded k ((fun f : Module.End k V ↦ f v) '' K) := by
    refine (hI v).mono ?_
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, by rw [hσI i hi]⟩
  have hconj (g : Module.End k V) (hg : g ∈ K) (x : W) : ∃ g' ∈ K, σ x * g = g' * σ x := by
    obtain ⟨i, hi, rfl⟩ := hg
    refine ⟨σ (x * i * x⁻¹), ⟨_, deg.normal_ker.conj_mem i hi x, rfl⟩, ?_⟩
    rw [hσ, hσ]
    group
  have hirr (U : Submodule k V) (hKU : ∀ g ∈ K, U ≤ U.comap g) (h₁ : U ≤ U.comap (σ F))
      (h₂ : U ≤ U.comap (σ F⁻¹)) : U = ⊥ ∨ U = ⊤ := by
    let M : Submonoid W :=
      { carrier := {w | U ≤ U.comap (σ w)}
        mul_mem' {w w'} hw hw' x hx := by
          rw [Submodule.mem_comap, ← hσ, Module.End.mul_apply]
          exact hw (hw' hx)
        one_mem' x hx := by simpa using hx }
    have hM (w : W) : w ∈ M := by
      have hFd (d : ℤ) : F ^ d ∈ M := by
        obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
        · rw [zpow_natCast]
          exact M.pow_mem h₁ n
        · rw [zpow_neg, zpow_natCast, ← inv_pow]
          exact M.pow_mem h₂ n
      simpa using M.mul_mem (hKU _ ⟨_, mul_zpow_neg_mem_ker hF w, rfl⟩)
        (hFd (Multiplicative.toAdd (deg w)))
    refine (isIrreducible_iff.1 ‹ρ.IsIrreducible›).2 U fun w x hx ↦ ?_
    have : ρ w x = ((degreeCharacter deg b⁻¹ w : kˣ) : k)⁻¹ • σ w x := by
      rw [twist_apply, LinearMap.smul_apply, inv_smul_smul₀ (Units.ne_zero _)]
    rw [this]
    exact U.smul_mem _ (hM w hx)
  have hfwd (v : V) := Module.End.isWeaklyBounded_range_pow_apply hK (Ψ := σ F)
    (Ψ' := σ F⁻¹) (by rw [hσ, mul_inv_cancel, map_one]) (fun g hg ↦ hconj g hg F) hirr hv₀.2
    hΨv₀ v
  have hΨ'v₀ : σ F⁻¹ v₀ = v₀ := by
    conv_lhs => rw [← hΨv₀]
    rw [← Module.End.mul_apply, hσ, inv_mul_cancel, map_one, Module.End.one_apply]
  have hbwd (v : V) := Module.End.isWeaklyBounded_range_pow_apply hK (Ψ := σ F⁻¹)
    (Ψ' := σ F) (by rw [hσ, inv_mul_cancel, map_one]) (fun g hg ↦ hconj g hg F⁻¹)
    (fun U h₀ h₁ h₂ ↦ hirr U h₀ h₂ h₁) hv₀.2 hΨ'v₀ v
  refine ⟨b, fun v ↦ ?_⟩
  refine (Module.IsWeaklyBounded.image2_apply hK ((hfwd v).union (hbwd v))).mono ?_
  rintro _ ⟨w, -, rfl⟩
  refine ⟨σ (w * F ^ (-Multiplicative.toAdd (deg w))), ⟨_, mul_zpow_neg_mem_ker hF w, rfl⟩,
    σ (F ^ Multiplicative.toAdd (deg w)) v, ?_, ?_⟩
  · obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (Multiplicative.toAdd (deg w))
    · left
      exact ⟨n, by rw [hn, zpow_natCast, map_pow]⟩
    · right
      exact ⟨n, by rw [hn, zpow_neg, zpow_natCast, ← inv_pow, map_pow]⟩
  · beta_reduce
    rw [← Module.End.mul_apply, hσ, zpow_neg, inv_mul_cancel_right]

end Bounded
section Finite

variable {k W V : Type*} [Field k] [Group W] [AddCommGroup V] [Module k V]

/-- If a normal subgroup `H` has finite image under `ρ`, then for every `F` some positive power
`ρ(F ^ n)` commutes with `ρ(H)`: conjugation by `ρ(F)` permutes the finite set `ρ(H)`. -/
theorem exists_pow_commute_of_finite (ρ : Representation k W V) (H : Subgroup W) [H.Normal]
    (hH : (ρ '' H).Finite) (F : W) : ∃ n : ℕ, 0 < n ∧ ∀ i ∈ H, Commute (ρ (F ^ n)) (ρ i) := by
  have := hH.to_subtype
  let f : ℕ → ρ '' H → ρ '' H := fun n x ↦ ⟨ρ (F ^ n) * x * ρ ((F ^ n)⁻¹), by
    obtain ⟨i, hi, hx⟩ := x.2
    exact ⟨F ^ n * i * (F ^ n)⁻¹, Subgroup.Normal.conj_mem ‹_› i hi _, by
      rw [map_mul, map_mul, hx]⟩⟩
  obtain ⟨a, c, hne, hac⟩ := Finite.exists_ne_map_eq_of_infinite f
  wlog hlt : a < c generalizing a c
  · exact this c a hne.symm hac.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  refine ⟨d, by omega, fun i hi ↦ ?_⟩
  have h := congrArg Subtype.val (congrFun hac ⟨ρ ((F ^ a)⁻¹ * i * F ^ a),
    ⟨_, Subgroup.Normal.conj_mem' ‹_› i hi _, rfl⟩⟩)
  simp only [f, ← map_mul] at h
  have e₁ : F ^ a * ((F ^ a)⁻¹ * i * F ^ a) * (F ^ a)⁻¹ = i := by group
  have e₂ : F ^ (a + d) * ((F ^ a)⁻¹ * i * F ^ a) * (F ^ (a + d))⁻¹ = F ^ d * i * (F ^ d)⁻¹ := by
    rw [add_comm, pow_add]
    group
  rw [e₁, e₂] at h
  rw [Commute, SemiconjBy]
  conv_rhs => rw [h]
  rw [← map_mul, ← map_mul, inv_mul_cancel_right]

/-- Over an algebraically closed field, if the image under an irreducible `ρ` of the kernel `I`
of `deg` commutes with `ρ(F ^ n)` for some `F` of degree one, then `ρ(F ^ n)` is a scalar. -/
theorem exists_pow_eq_smul_one [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k W V) [ρ.IsIrreducible] {deg : W →* Multiplicative ℤ} {F : W}
    (hF : deg F = Multiplicative.ofAdd 1) {n : ℕ}
    (hcomm : ∀ i ∈ deg.ker, Commute (ρ (F ^ n)) (ρ i)) :
    ∃ c : k, c ≠ 0 ∧ ρ (F ^ n) = c • 1 := by
  have := ‹ρ.IsIrreducible›.nontrivial
  have hz (w : W) : Commute (ρ (F ^ n)) (ρ w) := by
    have h := (hcomm _ (mul_zpow_neg_mem_ker hF w)).mul_right
      ((((Commute.refl F).pow_left n).zpow_right (Multiplicative.toAdd (deg w))).map ρ)
    rwa [← map_mul, zpow_neg, inv_mul_cancel_right] at h
  obtain ⟨c, hc, -⟩ := ‹ρ.IsIrreducible›.existsUnique_eq_smul_id _ fun w ↦ (hz w).eq
  rw [← Module.End.one_eq_id] at hc
  refine ⟨c, fun hc0 ↦ one_ne_zero (α := Module.End k V) ?_, hc⟩
  rw [← map_one ρ, ← mul_inv_cancel (F ^ n), map_mul, hc, hc0, zero_smul, zero_mul]

/-- **Finite geometric monodromy** (cf. Deligne, Weil II, 1.3.14). Let `deg : W →* ℤ` be
surjective with kernel `I`, and let `ρ` be a finite-dimensional irreducible representation of `W`
over an algebraically closed field with `ρ(I)` finite. Then there is `b ∈ kˣ` such that the twist
`ρ ⊗ b ^ (-deg)` has finite image. -/
theorem exists_finite_range_twist [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k W V) [ρ.IsIrreducible] {deg : W →* Multiplicative ℤ}
    (hdeg : Function.Surjective deg) (hI : (ρ '' deg.ker).Finite) :
    ∃ b : kˣ, (Set.range (ρ.twist (degreeCharacter deg b⁻¹))).Finite := by
  obtain ⟨F, hF⟩ := hdeg (Multiplicative.ofAdd 1)
  obtain ⟨n, hn, hcomm⟩ := exists_pow_commute_of_finite ρ deg.ker hI F
  obtain ⟨c, hc0, hc⟩ := exists_pow_eq_smul_one ρ hF hcomm
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hβ, zero_pow hn.ne'])
  set b := Units.mk0 β hβ0
  set σ := ρ.twist (degreeCharacter deg b⁻¹)
  have hσ (w w' : W) : σ w * σ w' = σ (w * w') := (map_mul σ w w').symm
  have hσI (i : W) (hi : i ∈ deg.ker) : σ i = ρ i := by
    rw [MonoidHom.mem_ker] at hi
    simp [σ, hi]
  have hσn : σ (F ^ n) = 1 := by
    simp [σ, hF, hc, b, ← hβ, smul_smul, hβ0]
  have hσF (d : ℤ) : σ (F ^ d) ∈ Set.range fun r : Fin n ↦ σ (F ^ (r : ℕ)) := by
    have hd₀ : 0 ≤ d % n := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have hd₁ : d % n < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    have hk : (F ^ n) ^ (d / n) ∈ σ.ker := Subgroup.zpow_mem _ hσn _
    rw [MonoidHom.mem_ker] at hk
    refine ⟨⟨(d % n).toNat, by omega⟩, ?_⟩
    beta_reduce
    rw [← zpow_natCast, Int.toNat_of_nonneg hd₀]
    conv_rhs =>
      rw [← Int.emod_add_mul_ediv d n, zpow_add, zpow_mul, zpow_natCast, ← hσ, hk, mul_one]
  refine ⟨b, (hI.image2 (· * ·) (Set.finite_range fun r : Fin n ↦ σ (F ^ (r : ℕ)))).subset ?_⟩
  rintro _ ⟨w, rfl⟩
  refine ⟨σ (w * F ^ (-Multiplicative.toAdd (deg w))),
    ⟨_, mul_zpow_neg_mem_ker hF w, (hσI _ (mul_zpow_neg_mem_ker hF w)).symm⟩,
    σ (F ^ Multiplicative.toAdd (deg w)), hσF _, ?_⟩
  beta_reduce
  rw [hσ, zpow_neg, inv_mul_cancel_right]

/-- **Trivial geometric monodromy.** If the kernel of `deg` acts trivially in a
finite-dimensional irreducible representation `ρ` over an algebraically closed field, then `ρ`
is one-dimensional and `ρ = b ^ deg` for some `b ∈ kˣ`, i.e. the twist `ρ ⊗ b ^ (-deg)` is
trivial. -/
theorem finrank_eq_one_and_exists_twist_eq_one [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k W V) [ρ.IsIrreducible] {deg : W →* Multiplicative ℤ}
    (hdeg : Function.Surjective deg) (hI : ∀ i ∈ deg.ker, ρ i = 1) :
    Module.finrank k V = 1 ∧ ∃ b : kˣ, ∀ w, ρ.twist (degreeCharacter deg b⁻¹) w = 1 := by
  have := ‹ρ.IsIrreducible›.nontrivial
  obtain ⟨F, hF⟩ := hdeg (Multiplicative.ofAdd 1)
  obtain ⟨c, hc0, hc⟩ := exists_pow_eq_smul_one ρ hF (n := 1) fun i hi ↦ by
    rw [hI i hi]
    exact Commute.one_right _
  set b := Units.mk0 c hc0
  set σ := ρ.twist (degreeCharacter deg b⁻¹)
  have hσF : F ∈ σ.ker := by
    rw [pow_one] at hc
    rw [MonoidHom.mem_ker]
    simp [σ, hF, hc, b, smul_smul, hc0]
  have hσ (w : W) : σ w = 1 := by
    have hk := Subgroup.zpow_mem _ hσF (Multiplicative.toAdd (deg w))
    rw [MonoidHom.mem_ker] at hk
    have hi := mul_zpow_neg_mem_ker hF w
    have hσi : σ (w * F ^ (-Multiplicative.toAdd (deg w))) = 1 := by
      rw [twist_apply, hI _ hi, degreeCharacter_apply, MonoidHom.mem_ker.1 hi]
      simp
    calc σ w = σ (w * F ^ (-Multiplicative.toAdd (deg w))) *
          σ (F ^ Multiplicative.toAdd (deg w)) := by
          rw [← map_mul, zpow_neg, inv_mul_cancel_right]
      _ = 1 := by rw [hσi, hk, one_mul]
  refine ⟨?_, b, hσ⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain h | h := (isIrreducible_iff.1 ‹ρ.IsIrreducible›).2 (k ∙ v) fun w x hx ↦ by
    have : ρ w x = ((degreeCharacter deg b⁻¹ w : kˣ) : k)⁻¹ • σ w x := by
      rw [twist_apply, LinearMap.smul_apply, inv_smul_smul₀ (Units.ne_zero _)]
    rw [this, hσ, Module.End.one_apply]
    exact Submodule.smul_mem _ _ hx
  · exact absurd (h ▸ Submodule.mem_span_singleton_self v) (by simpa using hv)
  · rw [← finrank_top k V, ← h, finrank_span_singleton hv]

/-- **Trivial geometric monodromy, semisimplification.** If the kernel of `deg` acts trivially
in a finite-dimensional representation `ρ` over an algebraically closed field, then every
composition factor of `ρ` is one-dimensional, given by a character `b ^ deg`. -/
theorem CompositionSeries.finrank_factor_eq_one_and_exists_twist_eq_one [IsAlgClosed k]
    [FiniteDimensional k V] {ρ : Representation k W V} {deg : W →* Multiplicative ℤ}
    (hdeg : Function.Surjective deg) (hI : ∀ i ∈ deg.ker, ρ i = 1) (s : ρ.CompositionSeries)
    (j : Fin s.length) :
    Module.finrank k ((s.series j.succ).toSubmodule ⧸
      (s.series j.castSucc).toSubmodule.comap (s.series j.succ).toSubmodule.subtype) = 1 ∧
    ∃ b : kˣ, ∀ w, (s.factor j).twist (degreeCharacter deg b⁻¹) w = 1 := by
  have := s.isIrreducible_factor j
  refine finrank_eq_one_and_exists_twist_eq_one (s.factor j) hdeg fun i hi ↦ ?_
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
  simp [Subrepresentation.subquotient, hI i hi]
  rfl


end Finite

section PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {W V : Type*} [Group W] [AddCommGroup V]
  [Module (PadicAlgCl ℓ) V] [FiniteDimensional (PadicAlgCl ℓ) V]

/-- **Deligne, Weil II, 1.3.14**, for `ℚ̄_ℓ`-coefficients: an irreducible finite-dimensional
`ℚ̄_ℓ`-representation of a Weil group `W` whose restriction to the geometric fundamental group
`ker deg` is bounded becomes bounded on all of `W` after a twist by `b ^ (-deg)`. -/
theorem exists_isBoundedOn_twist_padicAlgCl (ρ : Representation (PadicAlgCl ℓ) W V)
    [ρ.IsIrreducible] {deg : W →* Multiplicative ℤ} (hdeg : Function.Surjective deg)
    (hI : ρ.IsBoundedOn deg.ker) :
    ∃ b : (PadicAlgCl ℓ)ˣ, (ρ.twist (degreeCharacter deg b⁻¹)).IsBoundedOn Set.univ :=
  ρ.exists_isBoundedOn_twist hdeg hI


end PadicAlgCl

end Representation
