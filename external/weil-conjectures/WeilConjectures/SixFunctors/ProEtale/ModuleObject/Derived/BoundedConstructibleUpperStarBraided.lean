/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp

/-!
# The derived pullback of bounded constructible complexes is braided

The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` with its monoidal structure
`ProEtale.CondensedRing.monoidal_boundedConstructibleUpperStar` is braided for the Koszul braidings
`ProEtale.CondensedRing.boundedConstructibleBraiding`
(`ProEtale.CondensedRing.boundedConstructibleUpperStar_μ_map_braiding_hom`): this is the lax
monoidal form of `ProEtale.CondensedRing.boundedConstructibleUpperStar_map_braiding_hom_δ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

attribute [local instance] boundedConstructibleBraiding

/-- **The derived pullback of bounded constructible complexes is braided**:
`μ_{K, M} ≫ Lf^* β_{K, M} = β_{Lf^* K, Lf^* M} ≫ μ_{M, K}`. -/
theorem boundedConstructibleUpperStar_μ_map_braiding_hom (K M :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (β_ K M).hom =
      (β_ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K)
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)).hom ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) M
            K :=
  Functor.Monoidal.μ_comp_map_braiding_hom_of_δ _ K M
    (boundedConstructibleUpperStar_map_braiding_hom_δ ℓ f K M)

end AlgebraicGeometry.ProEtale.CondensedRing
