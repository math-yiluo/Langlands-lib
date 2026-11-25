/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!

# The refinement comparison and the projection formula

The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` of a refinement of compactifications
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekRefinement`) is the abstract
restriction comparison `CategoryTheory.Adjunction.restrictionComparison` of the adjunctions
`i_! ⊣ Li^*`, `i₁_! ⊣ Li₁^*` and the triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*`
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekRefinement_app`), so that the
compatibilities of `ProjectionCoherence` apply to it.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The restriction comparison of a refinement is the abstract restriction comparison. -/
lemma boundedConstructibleOpenImmersionLowerShriekRefinement_app (w : i ≫ h = i₁)
    (M : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w).app M =
      Adjunction.restrictionComparison
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
        (boundedConstructibleUpperStarTriangleComparison Λ ℓ w) M := by
  subst w
  simp [boundedConstructibleOpenImmersionLowerShriekRefinement,
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep,
    boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep,
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep,
    Adjunction.restrictionComparison, Functor.squareTransport]

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
/-- The triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` is compatible with the multiplications of the
monoidal derived pullbacks. -/
lemma boundedConstructibleUpperStarTriangleComparison_μ (w : i ≫ h = i₁)
    (K M : Dᵇc(Z₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i₁) K M ≫
        (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ
            w).hom.app (K ⊗ M) =
      ((boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ w).hom.app
          K ⊗ₘ
          (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ
              w).hom.app M) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h ⋙
          boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i) K M := by
  subst w
  refine Adjunction.μ_comp_hom_app_eq_of_δ _ (fun K M ↦ ?_) K M
  simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.id_comp,
    Functor.OplaxMonoidal.comp_δ]
  exact boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ i h K M

end AlgebraicGeometry.ProEtale.CondensedRing
