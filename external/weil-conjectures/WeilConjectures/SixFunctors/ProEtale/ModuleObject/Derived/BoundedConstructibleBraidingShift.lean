/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.BraidingShift
public import WeilConjectures.CategoryTheory.Monoidal.SubcategoryShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift

/-!
# The Koszul braiding of bounded constructible complexes commutes with the shifts

On `Dᵇc(X)⟦Λ⟧` the tensor product commutes with the shifts
(`ObjectProperty.commShiftTensorLeft`), and the Koszul braiding
`ProEtale.CondensedRing.boundedConstructibleBraiding` is compatible with these commutations
(`ProEtale.CondensedRing.boundedConstructible_braiding_hom_commShiftIso_hom_app`), since this
holds in the ambient derived category (`DerivedCategory.braiding_hom_commShiftIso_hom_app`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

attribute [local instance] boundedConstructibleBraiding DerivedCategory.braidedCategory'

/-- The Koszul braiding of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` commutes with the shifts. -/
lemma boundedConstructible_braiding_hom_commShiftIso_hom_app (a : ℤ) (K M :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (β_ K ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).obj M)).hom ≫
        (((curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).flip.obj K).commShiftIso
            a).hom.app M =
      (((curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K).commShiftIso a).hom.app
          M ≫
        (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).map (β_ K M).hom :=
  ObjectProperty.braiding_hom_commShiftIso_hom_app_of_ι _ a
    (fun K M ↦ DerivedCategory.braiding_hom_commShiftIso_hom_app K M a) K M

end AlgebraicGeometry.ProEtale.CondensedRing
