/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Support
public import WeilConjectures.SixFunctors.Finite.GlobalSections

/-!
# Vanishing of cohomology for sheaves supported on closed points

A sheaf of `Λ`-modules on a scheme `X` which vanishes off a finite set of closed points with
separably closed residue fields has no cohomology in nonzero degrees: it is the direct sum of
the pushforwards of sheaves on the points, and a separably closed point has no higher
cohomology.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_upperStar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The pushforward of a sheaf from a separably closed point along a finite morphism has no
cohomology in nonzero degrees. -/
lemma isZero_homology_rightDerivedGlobalSections_lowerStar {X : Scheme.{u}} {k : Type u}
    [Field k] [IsSepClosed k] (i : Spec (.of k) ⟶ X) [IsFinite i]
    (H : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj H)))) :=
  (isZero_cohomology_of_isSepClosed Λ H hq).of_iso
    ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).mapIso
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).mapIso
        ((((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app H).symm ≪≫
        (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ i).app _))

/-- **Sheaves supported on finitely many closed points are acyclic.** Let `U` be an open subset
of a scheme `X` whose complement is a finite set of closed points with separably closed residue
fields, and `G` an étale sheaf of `Λ`-modules on `X` whose restriction to `U` vanishes. Then
`H^q(X, G) = 0` for `q ≠ 0`: `G ≅ ⨁ₓ iₓ_* iₓ^* G`
(`AlgebraicGeometry.Etale.isIso_biproductLift_unit_of_isZero_upperStar`), and each summand is
acyclic (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_lowerStar`). -/
theorem isZero_homology_rightDerivedGlobalSections_of_isZero_upperStar {X : Scheme.{u}}
    (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite) (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (hsep : ∀ x ∉ U, IsSepClosed (X.residueField x))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj G)) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
  let ι := {x : X // x ∉ U}
  have : Finite ι := hfin.to_subtype
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have (x : ι) : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.1 (hcl x.1 x.2)
  let G' (x : ι) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (X.fromSpecResidueField x.1)_*[ModuleCat.{u + 1} Λ].obj
      ((X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ].obj G)
  have hφ := isIso_biproductLift_unit_of_isZero_upperStar Λ U hcl G hG
  let Φ := _root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0 ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X ⋙
      _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q
  have hz (x : ι) : IsZero (Φ.obj (G' x)) := by
    have := hsep x.1 x.2
    exact isZero_homology_rightDerivedGlobalSections_lowerStar Λ (k := X.residueField x.1)
      (X.fromSpecResidueField x.1) _ hq
  have : IsZero (Φ.obj (⨁ G')) := by
    rw [IsZero.iff_id_eq_zero, ← Φ.map_id, ← IsBilimit.total (biproduct.isBilimit G'),
      Φ.map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ by
      rw [Φ.map_comp, (hz j).eq_of_tgt (Φ.map (biproduct.π G' j)) 0, zero_comp]
  exact this.of_iso (Φ.mapIso (@asIso _ _ _ _ _ hφ))

end Etale

end AlgebraicGeometry
