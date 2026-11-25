/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection

/-!
# The comparison carries the étale projection map of `Rg_*` to the pro-étale one

Let `g : Z ⟶ Y` be a quasi-compact quasi-separated morphism of schemes. The comparison pullbacks
`ν^*` from étale to pro-étale sheaves commute with `Lg^*` and with the derived tensor products,
and, on bounded below complexes, with `Rg_*`. We show that they carry the étale projection map
`Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` to the pro-étale one: if the former is an isomorphism at
`(M, L)`, with `M` and `M ⊗ᴸ Lg^* L` bounded below, the latter is an isomorphism at
`(Lν^* M, Lν^* L)`. This is the step of `sk-thm-sf-pf-proetale` reducing the pro-étale
projection formula to the étale one.

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso g`: the isomorphism
  `Lg^* ∘ Lν_Y^* ≅ Lν_Z^* ∘ Lg^*`.
- `AlgebraicGeometry.ProEtale.comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso`:
  it is compatible with the tensor comparisons of `Lg^*` and `Lν^*`.
- `AlgebraicGeometry.ProEtale.isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app`:
  its mate, the base change map `Lν_Y^* Rg_* M ⟶ Rg_* Lν_Z^* M`, is invertible for bounded
  below `M`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived`: the
  transport of the projection formula for `Rg_*` from the étale to the pro-étale site.

## Implementation notes

The comparison is the general transport
`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv` of the projection map of
`Lg^* ⊣ Rg_*` along the left derived functors `Lν^*`, which are left adjoint to `Rν_*`. The
compatibility of the tensor comparisons is the general
`CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_eq_of_iso`, applied to the monoidal
isomorphism `g^* ν_Y^* ≅ ν_Z^* g^*` of
`AlgebraicGeometry.ProEtale.isMonoidal_comparisonUpperStarCompUpperStarIso_hom`. The base change
map is invertible on bounded below complexes since `ν^*` is fully faithful there and commutes
with `Rg_*` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso`).

Flatness of the pullbacks is assumed as hypotheses on the coefficient category; for finite
coefficient rings they hold by `AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj` and its
étale and pro-étale counterparts for `g^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The tensor comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of étale sheaves is the general
`CategoryTheory.Functor.leftDerivedTensorComparison` of the exact monoidal functor `g^*`. -/
lemma Etale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
    [Etale.UpperStarPreservesFlat A] :
    Etale.leftDerivedUpperStarTensorComparison A g =
      (Etale.upperStar A g).leftDerivedTensorComparison :=
  rfl

/-- The tensor comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of pro-étale sheaves is the general
`CategoryTheory.Functor.leftDerivedTensorComparison` of the exact monoidal functor `g^*`. -/
lemma ProEtale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
    [ProEtale.UpperStarPreservesFlat A] :
    ProEtale.leftDerivedUpperStarTensorComparison A g =
      (ProEtale.upperStar A g).leftDerivedTensorComparison :=
  rfl

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The derived direct image of a bounded below complex of étale sheaves is bounded below. -/
lemma Etale.plus_rightDerivedLowerStar_obj
    {M : DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    (hM : DerivedCategory.TStructure.t.plus M) :
    DerivedCategory.TStructure.t.plus ((R(Etale.lowerStar A g)).obj M) :=
  DerivedCategory.TStructure.t.plus.prop_of_iso
    (((Etale.lowerStar A g).rightDerivedFunctorPlusCompatibility).app ⟨M, hM⟩)
    ((R+(Etale.lowerStar A g)).obj ⟨M, hM⟩).property

end

namespace ProEtale

section Unit

variable {X : Scheme.{u}}

/-- The unit `M ⟶ Rν_* Lν^* M` of the derived comparison adjunction is invertible for a bounded
below complex `M` of étale sheaves. -/
lemma isIso_derivedAdjunction_comparisonAdjunction_unit_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((comparisonAdjunction A X).derivedAdjunction.unit.app M) := by
  have h := isIso_derivedComparisonAdjunction_unit_app A X M hM
  simp only [derivedComparisonAdjunction, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app] at h
  exact IsIso.of_isIso_comp_right _ ((R(ν_*(X)[A])).map
    ((ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory.hom.app M))

/-- The counit `Lν^* Rν_* N ⟶ N` of the derived comparison adjunction is invertible at an object
`N` isomorphic to `Lν^* M` for a bounded below complex `M` of étale sheaves. -/
lemma isIso_derivedAdjunction_comparisonAdjunction_counit_app_of_iso
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M) (e : N ≅ L(ν^*(X)[A]).obj M) :
    IsIso ((comparisonAdjunction A X).derivedAdjunction.counit.app N) := by
  have := isIso_derivedAdjunction_comparisonAdjunction_unit_app A M hM
  let adj := (comparisonAdjunction A X).derivedAdjunction
  have : IsIso (adj.counit.app (L(ν^*(X)[A]).obj M)) := by
    have h := adj.left_triangle_components M
    have : IsIso (L(ν^*(X)[A]).map (adj.unit.app M) ≫ adj.counit.app _) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (L(ν^*(X)[A]).map (adj.unit.app M)) _
  have h := adj.counit.naturality e.hom
  dsimp at h
  have : IsIso (adj.counit.app N ≫ e.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

end Unit

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The isomorphism `Lg^* ∘ Lν_Y^* ≅ Lν_Z^* ∘ Lg^*` of derived functors `D(Y_ét) ⥤ D(Z_proét)`,
obtained by deriving the isomorphism `g^* ν_Y^* ≅ ν_Z^* g^*` of
`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`. -/
noncomputable abbrev leftDerivedComparisonUpperStarCompUpperStarIso :
    L(ν^*(Y)[A]) ⋙ L(ProEtale.upperStar A g) ≅ L(Etale.upperStar A g) ⋙ L(ν^*(Z)[A]) :=
  Functor.leftDerivedFunctorCompNatIso (Etale.upperStar A g) ν^*(Z)[A] ν^*(Y)[A]
    (ProEtale.upperStar A g) (comparisonUpperStarCompUpperStarIso A g)

/-- For `g` quasi-compact and quasi-separated, the base change map
`Lν_Y^* Rg_* M ⟶ Rg_* Lν_Z^* M`, the mate of
`AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso`, is an isomorphism
for a bounded below complex `M` of étale sheaves. -/
lemma isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app
    [QuasiCompact g] [QuasiSeparated g]
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction A g)
      (ProEtale.derivedUpperStarLowerStarAdjunction A g)
      (leftDerivedComparisonUpperStarCompUpperStarIso A g).hom).app M) := by
  -- `Rg_*(Lν_Z^* M) ≅ Lν_Y^*(Rg_* M)`, so the counit of `Lν_Y^* ⊣ Rν_*` is invertible there
  have := isIso_derivedAdjunction_comparisonAdjunction_unit_app A M hM
  have := isIso_derivedAdjunction_comparisonAdjunction_unit_app A _
    (Etale.plus_rightDerivedLowerStar_obj A g hM)
  have := isIso_derivedAdjunction_comparisonAdjunction_counit_app_of_iso A
    ((R(Etale.lowerStar A g)).obj M) (Etale.plus_rightDerivedLowerStar_obj A g hM)
    ((R(ProEtale.lowerStar A g)).mapIso
        ((ν^*(Z)[A]).leftDerivedFunctorIsoMapDerivedCategory.app M) ≪≫
      (rightDerivedLowerStarComparisonIso A g).app ⟨M, hM⟩ ≪≫
      ((ν^*(Y)[A]).leftDerivedFunctorIsoMapDerivedCategory.app _).symm)
  exact Adjunction.isIso_mateEquiv_app_of_isIso _ _ _
    (comparisonAdjunction A Y).derivedAdjunction (comparisonAdjunction A Z).derivedAdjunction M

variable [Etale.UpperStarPreservesFlat A] [ProEtale.UpperStarPreservesFlat A]
  [∀ X : Scheme.{u}, (ν^*(X)[A]).PreservesFlat]

/-- The tensor comparisons of `Lg^*` on the étale and pro-étale sites and those of `Lν^*` are
compatible with `AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso`:
the comparison `Lν_Z^* Lg^*(K ⊗ᴸ M) ⟶ Lν_Z^* Lg^* K ⊗ᴸ Lν_Z^* Lg^* M` obtained from the étale
pullback agrees with the one obtained from the pro-étale pullback. -/
lemma comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso :
    Adjunction.ComparisonCompatible (leftDerivedComparisonUpperStarCompUpperStarIso A g)
      (Etale.leftDerivedUpperStarTensorComparison _ g)
      (ProEtale.leftDerivedUpperStarTensorComparison _ g)
      (asIso (ν^*(Z)[A]).leftDerivedTensorComparison)
      (asIso (ν^*(Y)[A]).leftDerivedTensorComparison) := by
  intro a b
  rw [Etale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    ProEtale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    asIso_hom, asIso_hom,
    Functor.map_leftDerivedTensorComparison_comp_eq_of_iso _ _ _ _
      (comparisonUpperStarCompUpperStarIso A g), tensorHom_def]
  rfl

/-- **The comparison carries the étale projection formula for `Rg_*` to the pro-étale one.**
Let `g` be quasi-compact and quasi-separated, `M` a bounded below complex of étale sheaves on
`Z` and `L` a complex of étale sheaves on `Y` such that `M ⊗ᴸ Lg^* L` is bounded below. If the
étale projection map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` is an isomorphism, so is the pro-étale
projection map at `(Lν^* M, Lν^* L)`. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived
    [QuasiCompact g] [QuasiSeparated g]
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M)
    (hML : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor A Z).obj M).obj ((L(Etale.upperStar A g)).obj L)))
    [IsIso (((Etale.rightDerivedLowerStarProjectionMap A g).app M).app L)] :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap A g).app
      ((L(ν^*(Z)[A])).obj M)).app ((L(ν^*(Y)[A])).obj L)) :=
  have : IsIso ((((Etale.derivedUpperStarLowerStarAdjunction A g).rightAdjointProjectionMap
      (Etale.leftDerivedUpperStarTensorComparison A g)).app M).app L) :=
    inferInstanceAs (IsIso (((Etale.rightDerivedLowerStarProjectionMap A g).app M).app L))
  have := isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app A g M hM
  have := isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app A g _ hML
  Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction A g)
    (ProEtale.derivedUpperStarLowerStarAdjunction A g)
    (comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso A g) M L

end ProEtale

end AlgebraicGeometry
