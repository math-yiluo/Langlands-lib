/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
import Mathlib.RingTheory.Nilpotent.Basic
import WeilConjectures.RingTheory.DerivedCompleteProductsTriangles

/-!
# Derived completeness of limits of nilpotent torsion complexes

Source: Stacks Project, More on Algebra, Tag 091W, `lemma-naive-derived-completion`,
with tensor factor `A[0]`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A derived limit of a tower on which each element of `I` acts nilpotently at each
level is derived `I`-complete. The exponent may depend on the element and the level.
Source: Stacks Project, Tag 091W, `lemma-naive-derived-completion`, with tensor factor
`A[0]` (auxiliary; not a blueprint node).

Proof:
1. Products of modules are exact: kernels are coordinatewise, and tuples lift across
products of surjections by choice. Apply `lemma-reduction-derived-nakayama` to obtain
countable products and derived limits in `D(A)`, unique up to isomorphism.
2. Fix a level and `a ∈ I`, and choose `e ≥ 1` annihilating that level. On the product
of the constant tower, its shift `s` satisfies `pr_j s^r = a^r pr_{j+r}`, by induction
and the product universal property `def-weil-category-product`. Hence `s^e = 0`, and
`1 + s + ... + s^(e-1)` inverts `1 - s` in `def-weil-derived-limit`'s Roos triangle.
3. In that triangle the first and last maps vanish since the middle map is invertible.
Rotate backwards using `def-weil-triangulated-category`. Exactness of Hom into this
triangle (`lem-weil-pbc-hom-into-triangle-exact`) factors the identity of the derived
limit through a zero map, so the derived limit is zero. Thus each level is derived
complete by `def-weil-point-derived-complete-module-complex`.
4. By clause (1) of `lem-weil-pbc-module-derived-complete-products-triangles`, the
product of all levels is derived complete. The Roos triangle for the given tower has
this product as both remaining vertices. Clause (2) of that closure lemma makes its
first vertex derived complete. No uniform exponent over levels is required. -/
theorem isDerivedComplete_of_isDerivedLimit_of_nilpotent
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (I : Ideal A) (L : ℕ → DerivedCategory (ModuleCat.{v} A)) [HasProduct L]
    (t : ∀ n : ℕ, L (n + 1) ⟶ L n)
    (h : ∀ (a : A), a ∈ I → ∀ n : ℕ, ∃ e : ℕ, 1 ≤ e ∧ (a ^ e) • 𝟙 (L n) = 0)
    (H : DerivedCategory (ModuleCat.{v} A)) (hH : IsDerivedLimit t H) :
    IsDerivedComplete I H := by
  have hL : ∀ n : ℕ, IsDerivedComplete I (L n) := by
    intro n a ha hP T hT
    obtain ⟨e, _, he⟩ := h a ha n
    obtain ⟨p, δ, hT⟩ := hT
    let K : ℕ → DerivedCategory (ModuleCat.{v} A) := fun _ ↦ L n
    let s : End (∏ᶜ K) := .of (towerProductShift (K := K) (fun _ ↦ a • 𝟙 (L n)))
    have hs (r j : ℕ) : ((s ^ r).asHom) ≫ Pi.π K j = (a ^ r) • Pi.π K (j + r) := by
      induction r generalizing j with
      | zero => simp
      | succ r ih =>
        rw [pow_succ, End.mul_asHom, Category.assoc, ih, Linear.comp_smul]
        have hsπ : (s).asHom ≫ Pi.π K (j + r) = a • Pi.π K (j + r + 1) := by
          simp [s, towerProductShift, K]
        rw [hsπ, smul_smul, pow_succ, Nat.add_assoc]
    have hnil : IsNilpotent s := by
      refine ⟨e, End.ext (Pi.hom_ext _ _ fun j ↦ ?_)⟩
      rw [hs, End.zero_asHom, zero_comp]
      simpa only [K, Linear.comp_smul, Category.comp_id, comp_zero] using
        congrArg (fun z ↦ Pi.π K (j + e) ≫ z) he
    apply Pretriangulated.Triangle.isZero₁_of_isIso₂ _ hT
    exact (isUnit_iff_isIso (1 - s)).1 hnil.isUnit_one_sub
  have hQ : IsDerivedComplete I (∏ᶜ L) :=
    (isDerivedComplete_products_and_triangles I).1 L hL |>.2
  obtain ⟨p, δ, hH⟩ := hH
  exact ((isDerivedComplete_products_and_triangles I).2
    (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism t) δ) hH).2.2 hQ hQ

end DerivedCategory
