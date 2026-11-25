/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The comparison pullback is monoidal

Let `A` be a monoidal closed coefficient category. For a scheme `X`, the comparison pullback
`ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` along the inclusion of the small étale site into the small
pro-étale site is strong monoidal, the inclusion being representably flat. For a morphism
`g : Y ⟶ X`, the isomorphism `g^* ν_X^* ≅ ν_Y^* g^*` is a monoidal natural isomorphism.

## Main results

- `AlgebraicGeometry.ProEtale.monoidal_comparisonUpperStar`: `ν^*` is strong monoidal, its
  oplax structure being the one of the left adjoint of the lax monoidal restriction `ν_*`.
- `AlgebraicGeometry.ProEtale.isMonoidal_comparisonUpperStarCompUpperStarIso_hom`: the
  isomorphism `g^* ν_X^* ≅ ν_Y^* g^*` of
  `AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso` is monoidal.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

section

variable (X : Scheme.{u})

/-- The restriction `ν_*` from pro-étale to étale sheaves is lax monoidal, being the pushforward
along the continuous inclusion of sites. -/
noncomputable instance laxMonoidal_comparisonLowerStar : ν_*(X)[A].LaxMonoidal := by
  unfold comparisonLowerStar
  infer_instance

/-- The comparison pullback `ν^*` is oplax monoidal, being left adjoint to the lax monoidal
restriction `ν_*`. -/
noncomputable instance oplaxMonoidal_comparisonUpperStar : ν^*(X)[A].OplaxMonoidal :=
  (comparisonAdjunction A X).leftAdjointOplaxMonoidal

/-- The adjunction `ν^* ⊣ ν_*` is monoidal. -/
instance isMonoidal_comparisonAdjunction : (comparisonAdjunction A X).IsMonoidal := by
  let := (comparisonAdjunction A X).leftAdjointOplaxMonoidal
  infer_instance

/-- The comma categories of the opposite of the inclusion `ν` of the small étale site into the
small pro-étale site are filtered, `ν` being representably flat. -/
instance isFiltered_costructuredArrow_toProEt_op (K : X.ProEtᵒᵖ) :
    IsFiltered (CostructuredArrow (X.toProEt).op K) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (Opposite.unop K))

/-- The comparison map `δ : ν^*(F ⊗ G) ⟶ ν^*F ⊗ ν^*G` is an isomorphism. -/
instance isIso_comparisonUpperStar_δ (F G : Sheaf X.smallEtaleTopology A) :
    IsIso (Functor.OplaxMonoidal.δ ν^*(X)[A] F G) := by
  unfold comparisonUpperStar
  infer_instance

/-- The comparison map `η : ν^*𝟙 ⟶ 𝟙` is an isomorphism. -/
instance isIso_comparisonUpperStar_η : IsIso (Functor.OplaxMonoidal.η ν^*(X)[A]) := by
  unfold comparisonUpperStar
  infer_instance

/-- The comparison pullback `ν^*` is strong monoidal. Its oplax structure is
`AlgebraicGeometry.ProEtale.oplaxMonoidal_comparisonUpperStar`. -/
noncomputable instance monoidal_comparisonUpperStar : ν^*(X)[A].Monoidal :=
  .ofOplaxMonoidal _

end

variable {A}

variable {Y X : Scheme.{u}} (g : Y ⟶ X)

/-- The identification `g_* ⋙ ν_{X,*} ≅ ν_{Y,*} ⋙ g_*` of
`AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso` is monoidal: it is the
composite of the identifications of both sides with the pushforward along the composite of the
site functors, which are monoidal by
`CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousComp'_hom`. -/
instance isMonoidal_lowerStarCompComparisonLowerStarIso_hom :
    NatTrans.IsMonoidal (lowerStarCompComparisonLowerStarIso g A).hom := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous X.smallEtaleTopology
      Y.smallEtaleTopology := Etale.isContinuous_overPullback g
  have := ProEt.isContinuous_overPullback g
  have := isContinuous_toProEt Y
  have := isContinuous_toProEt X
  have := isContinuous_overPullback_comp_toProEt g
  have := isContinuous_toProEt_comp_overPullback g
  have h : (lowerStarCompComparisonLowerStarIso g A).hom =
      (Functor.sheafPushforwardContinuousComp' (toProEtCompOverPullbackIso g) A _ _ _).hom ≫
        (Functor.sheafPushforwardContinuousComp' (Iso.refl _) A _ _ _).inv := by
    ext F U
    simp only [Functor.comp_obj, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.refl_hom, NatTrans.id_app,
      op_id, CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).trans ((Category.comp_id _).trans (Category.comp_id _).symm)
  rw [h]
  infer_instance

/-- The isomorphism `g^* ν_X^* ≅ ν_Y^* g^*` of
`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso` is monoidal, being the
conjugate of the monoidal isomorphism `g_* ⋙ ν_{X,*} ≅ ν_{Y,*} ⋙ g_*` of the right adjoints. -/
instance isMonoidal_comparisonUpperStarCompUpperStarIso_hom :
    NatTrans.IsMonoidal (comparisonUpperStarCompUpperStarIso A g).hom := by
  have : NatTrans.IsMonoidal (lowerStarCompComparisonLowerStarIso g A).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (lowerStarCompComparisonLowerStarIso g A).inv)
  unfold comparisonUpperStarCompUpperStarIso
  exact isMonoidal_conjugateEquiv_symm _ _ _

end AlgebraicGeometry.ProEtale
