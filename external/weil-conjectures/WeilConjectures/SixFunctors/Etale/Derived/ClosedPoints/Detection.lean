/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Support
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.MinimalCohomology

/-!
# Detection of complexes supported at closed points

Let `K` be a separably closed field, `X` a scheme locally of finite type over `K`, and
`Q ∈ D(X_ét, Λ)` a complex whose cohomology sheaves have vanishing stalks at all non-closed
points of `X`. If `Q` is bounded below, then `Q = 0` if and only if `H^i(X_ét, Q) = 0` for all
`i` (blueprint `corollary-open-direct-image-over-field--2`, Stacks 0F1G): if `i` is minimal with
`ℋ^i(Q) ≠ 0`, then `H^i(X_ét, Q) = Γ(X, ℋ^i(Q))` (`corollary-open-direct-image-over-field--2`), and
the globally generated sheaf `ℋ^i(Q)` (`corollary-open-direct-image-over-field--2`) has a nonzero
global section.

## Main statements

- `AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE`
  (`corollary-open-direct-image-over-field--2`, bounded below case).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `corollary-open-direct-image-over-field--2`: **detection of objects supported at
closed points** (bounded below case). Let `K` be a separably closed field, `X` a scheme locally of
finite type over `K` (structure morphism `p`), and `Q ∈ D(X_ét, Λ)` bounded below (`Q ∈ D^{≥ m}`)
such that the stalks of all cohomology sheaves `ℋ^q(Q)` at the geometric points over non-closed
points of `X` vanish. Then `Q = 0` if and only if `H^i(X_ét, Q) = 0` for all `i`.

By induction `Q ∈ D^{≥ m + k}` for all `k`: if `Q ∈ D^{≥ n}`, then
`H^n(X_ét, Q) ≅ Γ(X, ℋ^n(Q))` (`corollary-open-direct-image-over-field--2`), so `ℋ^n(Q)` has no
nonzero global sections, and being globally generated (`corollary-open-direct-image-over-field--2`)
it vanishes. -/
theorem isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE {K : Type u}
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ)
    [Q.IsGE m]
    (hQ : ∀ q : ℤ, ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj Q))) :
    IsZero Q ↔ ∀ i : ℤ,
      IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj Q)) := by
  refine ⟨fun h i ↦ (_root_.DerivedCategory.homologyFunctor _ i).map_isZero
    ((rightDerivedGlobalSections _ X).map_isZero h), fun h ↦ ?_⟩
  have key (k : ℕ) : Q.IsGE (m + k) := by
    induction k with
    | zero => simpa using ‹Q.IsGE m›
    | succ k ih =>
      obtain ⟨e⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X Q (m + k)
      have hΓ : IsZero ((Sheaf.Γ _ _).obj ((_root_.DerivedCategory.homologyFunctor _ (m + k)).obj
          Q)) := (h _).of_iso e.symm
      have hH : IsZero ((_root_.DerivedCategory.homologyFunctor _ (m + k)).obj Q) := by
        refine isZero_of_isZero_sheafFiber_of_subsingleton _ p (hQ _) ?_
        exact ModuleCat.isZero_iff_subsingleton.1 (hΓ.of_iso
          ((Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleTerminal X)).app _).symm)
      refine (_root_.DerivedCategory.isGE_iff Q (m + ↑(k + 1))).2 fun q hq ↦ ?_
      rcases lt_or_eq_of_le (show q ≤ m + k by push_cast at hq; omega) with hq' | rfl
      · exact (_root_.DerivedCategory.isGE_iff Q (m + k)).1 ih q hq'
      · exact hH
  refine (_root_.DerivedCategory.isZero_iff Q).2 fun q ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q < m + k := ⟨(q - m + 1).toNat, by omega⟩
  have := key k
  exact _root_.DerivedCategory.isZero_of_isGE Q (m + k) q hk

end Etale

end AlgebraicGeometry
