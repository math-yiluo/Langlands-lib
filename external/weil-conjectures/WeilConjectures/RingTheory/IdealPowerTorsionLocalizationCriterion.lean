/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Detecting torsion kernels and cokernels on finite localization charts

Source: Stacks Project, More on Algebra, proof of Lemma 0ALK and Proposition 05ER
(blueprint: lem-weil-pbc-ideal-power-torsion-localization-criterion).
-/

@[expose] public section

universe u v w

namespace FormalGlueing

private theorem torsion_iff_localizations_subsingleton
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (t : ℕ) (f : Fin t → R) :
    (∀ x : M, ∃ n : ℕ, ∀ r ∈ (Ideal.span (Set.range f)) ^ n, r • x = 0) ↔
      ∀ i : Fin t, Subsingleton (LocalizedModule.Away (f i) M) := by
  constructor
  · intro h i
    apply LocalizedModule.subsingleton_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := h x
    have hfi : f i ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨i, rfl⟩
    exact ⟨f i ^ n, ⟨n, rfl⟩, hn _ (Ideal.pow_mem_pow hfi n)⟩
  · intro h x
    let J : Ideal R := (LinearMap.toSpanSingleton R M x).ker
    have hJ : Ideal.span (Set.range f) ≤ J.radical := by
      apply Ideal.span_le.mpr
      rintro r ⟨i, rfl⟩
      obtain ⟨r, hr, hx⟩ := (LocalizedModule.subsingleton_iff.mp (h i)) x
      obtain ⟨n, rfl⟩ := hr
      exact ⟨n, hx⟩
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ
      (Submodule.fg_span (Set.finite_range f))
    exact ⟨n, fun r hr => hn hr⟩

private theorem localMap_injective_iff_kernel_subsingleton
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submonoid R) (g : M →ₗ[R] N) :
    Function.Injective (IsLocalizedModule.map p
      (LocalizedModule.mkLinearMap p M) (LocalizedModule.mkLinearMap p N) g) ↔
      Subsingleton (LocalizedModule p g.ker) := by
  let k := LinearMap.toKerIsLocalized p (LocalizedModule.mkLinearMap p M)
    (LocalizedModule.mkLinearMap p N) g
  have : IsLocalizedModule p k :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization p) p
      (LocalizedModule.mkLinearMap p M) (LocalizedModule.mkLinearMap p N) g
  let e := IsLocalizedModule.linearEquiv p (LocalizedModule.mkLinearMap p g.ker) k
  rw [e.toEquiv.subsingleton_congr, Submodule.subsingleton_iff_eq_bot,
    LinearMap.ker_eq_bot]

/-- A map is bijective on the charts of a finitely generated ideal exactly when its
kernel and cokernel are ideal-power torsion.
Source: Stacks Project, More on Algebra, proof of Lemma 0ALK, first sentence of part (1),
and Proposition 05ER, the torsion argument for the kernel and cokernel.
(blueprint: lem-weil-pbc-ideal-power-torsion-localization-criterion).

Proof: Localization commutes with kernels and cokernels. An ideal-power torsion
module localizes to zero at each generator: a power of the generator belongs to
that ideal power and kills every given numerator. Conversely, a numerator that
vanishes in each localization is killed by a power of each generator. Its
annihilator therefore contains every generator in its radical, hence contains a
power of their finitely generated ideal. This also handles the empty generating
family: the ideal is zero, so its first power annihilates every element. Apply this
module criterion to the kernel and cokernel, using exactness of localization. -/
theorem idealPowerTorsion_iff_localMap_bijective
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : ℕ) (f : Fin t → R) (g : M →ₗ[R] N) :
    ((∀ x : g.ker, ∃ n : ℕ, ∀ r ∈ (Ideal.span (Set.range f)) ^ n, r • x = 0) ∧
      (∀ x : N ⧸ g.range,
        ∃ n : ℕ, ∀ r ∈ (Ideal.span (Set.range f)) ^ n, r • x = 0)) ↔
      ∀ i : Fin t, Function.Bijective
        (IsLocalizedModule.map (Submonoid.powers (f i))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N) g) := by
  rw [torsion_iff_localizations_subsingleton t f,
    torsion_iff_localizations_subsingleton t f]
  simp only [Function.Bijective, localMap_injective_iff_kernel_subsingleton,
    IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective,
    LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

end FormalGlueing
