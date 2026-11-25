/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Topology.PointwiseTruncationLimitExists
import WeilConjectures.Topology.PointwiseTruncationLimitIsIso

/-! # Pointwise bounds and the derived limit of lower truncations

Source: Stacks Project, Cohomology, Tag 0D62; Derived Categories, Remark 0H72
(blueprint: lem-pc-ringed-space-pointwise-truncation-limit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Local bounds on the cohomology of the cohomology sheaves imply that every compatible
map to a derived limit of the lower truncations is an isomorphism; such a map exists.
Source: Stacks Project, Cohomology, Tag 0D62; Derived Categories, Remark 0H72
(blueprint: lem-pc-ringed-space-pointwise-truncation-limit).

Proof:
1. The maps to the standard truncations are compatible. Their product map is killed by
`1-s`. Exactness of Hom into the Roos triangle (lem-weil-pbc-hom-into-triangle-exact)
gives the lift, as in Remark 0H72. Truncation induces an isomorphism on degree m
cohomology for n >= -m (def-sbc-standard-tstructure-derived-category).
2. For each x and m choose n(x) to be the maximum of zero and one plus the maximum of
-m, p(x,m-1)-m, p(x,m)-m-1 and p(x,m+1)-m-2. The hypothesis kills the three groups
in degrees m+n, m+n+1 and m+n+2 with coefficients H^(-n-1)(E), for n >= n(x).
3. The successive-truncation triangle (lem-pc-derived-lower-truncation-step-triangle)
and its long exact cohomology sequence make the transitions on H^(m-1)(U,-) and
H^m(U,-) isomorphisms on the fundamental system for n >= n(x).
4. By lem-pc-derived-limit-roos-abelian-groups, eventual isomorphisms kill R^1 lim:
solve b_n-g_n(b_(n+1))=a_n forwards using the inverse transitions after n(x), then
backwards before n(x). Together with lem-pc-ringed-space-rgamma-derived-limit this
allows lem-pc-ringed-space-derived-limit-stalk-injective to give injectivity of
H^m(K)_x -> H^m(K_(n(x)))_x. For any compatible c the composite with H^m(c)_x is
the truncation isomorphism; therefore H^m(c)_x is bijective. Stalkwise detection
of isomorphisms and the cohomology criterion in the derived category finish. -/
theorem pointwise_truncation_limit (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (hlocal : ∀ x : X, ∃ (b : ℤ → ℤ) (B : Set (Opens X)),
      (∀ U ∈ B, x ∈ U) ∧
      (∀ V : Opens X, x ∈ V → ∃ U ∈ B, U ≤ V) ∧
      (∀ (m : ℤ) (p : ℕ) (U : Opens X), U ∈ B → b m < (p : ℤ) →
        IsZero ((openModuleCohomology X p U).obj
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X))
            (m - (p : ℤ))).obj E))))
    [HasProduct (fun n : ℕ => (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (π : K ⟶ ∏ᶜ (fun n : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E))
    (δ : (∏ᶜ (fun n : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E) K π δ) :
    (∃ c : E ⟶ K, ∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) ∧
    (∀ c : E ⟶ K, (∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) → IsIso c) := by
  constructor
  · exact pointwise_truncation_limit_exists X E hlocal K π δ hK
  · exact pointwise_truncation_limit_isIso X E hlocal K π δ hK

end AlgebraicGeometry.RingedSpace
