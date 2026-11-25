/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Equalizer
import WeilConjectures.Algebra.TorDimensionShiftFree
import WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Kernel base change for a two-term complex

Source: Stacks Project, Algebra, proof of Tag 00S2, final paragraph
(blueprint: lem-weil-pbc-two-term-complex-kernel-base-change).

The algebra clause uses tensor symmetry to place the algebra factor first, where Mathlib's
`LinearMap.tensorKer` is already linear over that algebra.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace LinearMap

/-- The inclusion of the kernel tensored with `C` identifies it with the kernel after tensoring.
Source: Stacks Project, Algebra, proof of Tag 00S2, final paragraph
(blueprint: lem-weil-pbc-two-term-complex-kernel-base-change).

Proof: (1) Factor `δ` through its image `I`, giving the short exact sequences
`0 → ker δ → N₁ → I → 0` and `0 → I → N₀ → coker δ → 0`.
(2) By `lem-weil-pbc-tor-long-exact-first-variable` and the first Tor vanishing,
`I ⊗ C → N₀ ⊗ C` is injective.
(3) By `lem-weil-pbc-tor-dimension-shift-free`, freeness of `N₀` identifies
`Tor₁(I,C)` with `Tor₂(coker δ,C)`, which vanishes.
(4) Apply the first-variable Tor exact sequence to the first short exact sequence:
`ker δ ⊗ C → N₁ ⊗ C` is injective with image the kernel of `N₁ ⊗ C → I ⊗ C`.
(5) The injectivity in step 2 identifies this last kernel with `ker (δ ⊗ id)`.
Thus the displayed inclusion induces the required linear equivalence. -/
theorem exists_twoTermKernelBaseChange_equiv
    (B C N₁ N₀ : Type u) [CommRing B]
    [AddCommGroup C] [Module B C]
    [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₀] [Module B N₀]
    [Module.Free B N₀] (δ : N₁ →ₗ[B] N₀)
    (hTor₁ : IsZero (((Tor' (ModuleCat B) 1).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C)))
    (hTor₂ : IsZero (((Tor' (ModuleCat B) 2).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C))) :
    ∃ e : (LinearMap.ker δ ⊗[B] C) ≃ₗ[B] LinearMap.ker (δ.rTensor C),
      ∀ x : LinearMap.ker δ ⊗[B] C,
        (e x : N₁ ⊗[B] C) = (LinearMap.ker δ).subtype.rTensor C x := by
  let I := LinearMap.range δ
  let j : I →ₗ[B] N₀ := I.subtype
  let p : N₀ →ₗ[B] N₀ ⧸ I := I.mkQ
  have hj : Function.Injective j := I.injective_subtype
  have hp : Function.Surjective p := I.mkQ_surjective
  have hjp : Function.Exact j p := LinearMap.exact_subtype_mkQ I
  let S := ModuleCat.shortComplexOfCompEqZero j p (by ext x; simp [j, p])
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hjp hj hp
  have hI := (CategoryTheory.tor_dimension_shift_free S hS (ModuleCat.of B C)).2.mp hTor₂
  obtain ⟨d₀, hd₀, _⟩ := CategoryTheory.tor_long_exact_first_variable j p hj hp hjp
  have hjC : Function.Injective (j.rTensor C) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨t, ht⟩ := ((hd₀ C).2.1 x).mp hx
    have ht0 : t = 0 := (ModuleCat.isZero_iff_subsingleton.mp hTor₁).elim _ _
    simpa [ht0] using ht.symm
  let q : N₁ →ₗ[B] I := δ.rangeRestrict
  let k : LinearMap.ker δ →ₗ[B] N₁ := (LinearMap.ker δ).subtype
  have hq : Function.Surjective q := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hkq : Function.Exact k q := by
    intro x
    change q x = 0 ↔ ∃ y, k y = x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      exact congrArg Subtype.val hx
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact y.property
  obtain ⟨d₁, hd₁, _⟩ := CategoryTheory.tor_long_exact_first_variable
    k q (LinearMap.ker δ).injective_subtype hq hkq
  have hkC : Function.Injective (k.rTensor C) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨t, ht⟩ := ((hd₁ C).2.1 x).mp hx
    have ht0 : t = 0 := (ModuleCat.isZero_iff_subsingleton.mp hI).elim _ _
    simpa [ht0] using ht.symm
  have hδ : δ = j ∘ₗ q := rfl
  have hkδ : δ ∘ₗ k = 0 := by
    ext x
    exact x.property
  let f : (LinearMap.ker δ ⊗[B] C) →ₗ[B] LinearMap.ker (δ.rTensor C) :=
    LinearMap.codRestrict _ (k.rTensor C) (fun x => by
      change (δ.rTensor C) (k.rTensor C x) = 0
      change ((δ.rTensor C) ∘ₗ (k.rTensor C)) x = 0
      rw [← LinearMap.rTensor_comp, hkδ]
      simp)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact hkC (congrArg Subtype.val hxy)
    · intro y
      have hy : q.rTensor C y.val = 0 := by
        apply hjC
        have hδC : δ.rTensor C = (j.rTensor C) ∘ₗ (q.rTensor C) := by
          rw [hδ, LinearMap.rTensor_comp]
        have heq : δ.rTensor C y.val = 0 := y.property
        simpa only [hδC, LinearMap.comp_apply, map_zero] using heq
      obtain ⟨x, hx⟩ := ((hd₁ C).2.2.1 y.val).mp hy
      exact ⟨x, Subtype.ext hx⟩
  exact ⟨LinearEquiv.ofBijective f hf, fun _ => rfl⟩

/-- When `C` is a `B`-algebra, the same canonical kernel map is a `C`-linear isomorphism.
Tensor symmetry identifies this map with the one in `exists_twoTermKernelBaseChange_equiv`.
Source: Stacks Project, Algebra, proof of Tag 00S2, final paragraph
(blueprint: lem-weil-pbc-two-term-complex-kernel-base-change).

Proof: Steps 1--5 of the node proof give bijectivity as in the preceding statement.
On generators the map sends `c ⊗ h` to `c ⊗ h.val`, so it commutes with multiplication
on the `C` factor. Mathlib's `tensorKer C C δ` records this `C`-linearity already;
bijectivity therefore makes it a `C`-linear isomorphism. -/
theorem bijective_twoTermKernelBaseChange_algebra
    (B C N₁ N₀ : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₀] [Module B N₀]
    [Module.Free B N₀] (δ : N₁ →ₗ[B] N₀)
    (hTor₁ : IsZero (((Tor' (ModuleCat B) 1).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C)))
    (hTor₂ : IsZero (((Tor' (ModuleCat B) 2).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C))) :
    Function.Bijective (δ.tensorKer C C) := by
  obtain ⟨e, he⟩ := exists_twoTermKernelBaseChange_equiv B C N₁ N₀ δ hTor₁ hTor₂
  have hkC : Function.Injective ((LinearMap.ker δ).subtype.rTensor C) := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    simpa only [he] using hxy
  constructor
  · intro x y hxy
    apply (TensorProduct.comm B C (LinearMap.ker δ)).injective
    apply hkC
    simpa only [LinearMap.rTensor_comm, LinearMap.tensorKer_coe] using
      congrArg (fun z => TensorProduct.comm B C N₁ z.val) hxy
  · intro y
    let z : LinearMap.ker (δ.rTensor C) :=
      ⟨TensorProduct.comm B C N₁ y.val, by
        rw [LinearMap.mem_ker, LinearMap.rTensor_comm]
        have hy : δ.lTensor C y.val = 0 := y.property
        rw [hy, map_zero]⟩
    refine ⟨TensorProduct.comm B (LinearMap.ker δ) C (e.symm z), ?_⟩
    apply Subtype.ext
    rw [LinearMap.tensorKer_coe, LinearMap.lTensor_comm, ← he, e.apply_symm_apply]
    simp [z]

end LinearMap
