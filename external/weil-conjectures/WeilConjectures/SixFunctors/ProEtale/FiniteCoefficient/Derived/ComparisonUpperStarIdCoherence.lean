/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarCoherence

/-!
# The commutation of `ν^*` with pullbacks along the identity

For the identity of a scheme `X`, the commutation `D(ν^*) ⋙ L(𝟙)^*_{proét} ≅ L(𝟙)^*_{ét} ⋙ D(ν^*)`
(`ProEtale.derivedComparisonUpperStarUpperStarIso`) is the composite of the identity isomorphisms
`L(𝟙)^* ≅ 𝟭` of the pro-étale and the étale derived pullbacks
(`ProEtale.derivedComparisonUpperStarUpperStarIso_hom_app_id`). Together with the compatibility
with composition (`ProEtale.derivedComparisonUpperStarUpperStarIso_compCoherence`), this makes the
commutations a pseudonatural transformation.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N]
  [PreservesFiniteColimits N] {E : C ⥤ C} [E.Additive] [PreservesFiniteLimits E]
  [PreservesFiniteColimits E] {P : D ⥤ D} [P.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P]

/-- If an isomorphism `e : N ⋙ P ≅ E ⋙ N` is compatible with isomorphisms `E ≅ 𝟭` and `P ≅ 𝟭`,
then so is the induced isomorphism `D(N) ⋙ D(P) ≅ D(E) ⋙ D(N)` on derived categories, with the
induced isomorphisms `D(E) ≅ D(𝟭) ≅ 𝟭` and `D(P) ≅ D(𝟭) ≅ 𝟭`. -/
lemma mapDerivedCategoryNatIso_hom_app_id (eE : E ≅ 𝟭 C) (eP : P ≅ 𝟭 D)
    (e : N ⋙ P ≅ E ⋙ N)
    (h : ∀ M, e.hom.app M ≫ N.map (eE.hom.app M) = eP.hom.app (N.obj M))
    (K : DerivedCategory C) :
    (mapDerivedCategoryCompIso N P).hom.app K ≫ (mapDerivedCategoryNatIso e).hom.app K ≫
        (mapDerivedCategoryCompIso E N).inv.app K ≫
        N.mapDerivedCategory.map ((mapDerivedCategoryNatIso eE).hom.app K) ≫
        N.mapDerivedCategory.map ((mapDerivedCategoryIdIso C).hom.app K) =
      (mapDerivedCategoryNatIso eP).hom.app (N.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryIdIso D).hom.app (N.mapDerivedCategory.obj K) := by
  have hR := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerRight eE N) K
  have hR' := NatTrans.congr_app (mapDerivedCategoryCompIso_id_comp N) K
  have hL := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft N eP) K
  have hL' := NatTrans.congr_app (mapDerivedCategoryCompIso_comp_id N) K
  have he : e ≪≫ isoWhiskerRight eE N = isoWhiskerLeft N eP := by
    ext M
    exact h M
  have hD := NatTrans.congr_app (congrArg Iso.hom (congrArg mapDerivedCategoryNatIso he)) K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, NatTrans.id_app] at hR hR' hL hL'
  rw [mapDerivedCategoryNatIso_trans] at hD
  rw [← reassoc_of% hR, hR']
  -- the identities are those of objects which agree only up to unfolding `𝟭 C ⋙ N`
  erw [Category.comp_id]
  rw [← NatTrans.comp_app, hD, ← Iso.app_hom, ← Iso.eq_inv_comp, Iso.app_inv,
    ← reassoc_of% hL, hL']
  erw [Category.comp_id]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency true in
/-- **The commutation of `ν^*` with the pullback along the identity** is the composite of the
identity isomorphisms of the étale and the pro-étale pullbacks. -/
theorem comparisonUpperStarUpperStarIso_hom_app_id (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology A) :
    (comparisonUpperStarUpperStarIso A (𝟙 X)).hom.app M ≫
        (comparisonUpperStar A X).map ((Etale.upperStarId A X).hom.app M) =
      (ProEtale.upperStarId A X).hom.app ((comparisonUpperStar A X).obj M) := by
  have key : (comparisonUpperStarUpperStarIso A (𝟙 X)).hom ≫
      Functor.whiskerRight (Etale.upperStarId A X).hom _ ≫ (Functor.leftUnitor _).hom =
      Functor.whiskerLeft _ (ProEtale.upperStarId A X).hom ≫ (Functor.rightUnitor _).hom := by
    apply (conjugateEquiv (comparisonAdjunction A X)
      ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A (𝟙 X)))).injective
    rw [← conjugateEquiv_comp _ ((comparisonAdjunction A X).comp Adjunction.id),
      ← conjugateEquiv_comp _ ((Etale.upperStarLowerStarAdjunction A (𝟙 X)).comp
        (comparisonAdjunction A X)),
      ← conjugateEquiv_comp _ (Adjunction.id.comp (comparisonAdjunction A X)),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom,
      conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft]
    have h₀ : conjugateEquiv ((Etale.upperStarLowerStarAdjunction A (𝟙 X)).comp
        (comparisonAdjunction A X))
        ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A (𝟙 X)))
        (comparisonUpperStarUpperStarIso A (𝟙 X)).hom = 𝟙 _ :=
      congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply
        (lowerStarComparisonLowerStarIso A (𝟙 X)).symm)
    have h₁ := congrArg Iso.hom (ProEtale.conjugateIsoEquiv_upperStarId A X)
    have h₂ := congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarId A X)
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at h₁ h₂
    rw [h₀, h₁, h₂]
    ext F U
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  simpa using NatTrans.congr_app key M

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **The derived commutation of `D(ν^*)` with the pullback along the identity** is the composite
of the identity isomorphisms `L(𝟙)^* ≅ 𝟭` of the étale and the pro-étale derived pullbacks. -/
theorem derivedComparisonUpperStarUpperStarIso_hom_app_id (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedComparisonUpperStarUpperStarIso A (𝟙 X)).hom.app K ≫
        (comparisonUpperStar A X).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarId A X).hom.app K) =
      (ProEtale.leftDerivedUpperStarId A X).hom.app
        ((comparisonUpperStar A X).mapDerivedCategory.obj K) := by
  simp only [derivedComparisonUpperStarUpperStarIso, Etale.leftDerivedUpperStarId,
    ProEtale.leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    Etale.leftDerivedUpperStarIsoMapDerivedCategory,
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp,
    Functor.mapDerivedCategoryNatIso_hom_app_id _ _ _ _
      (comparisonUpperStarUpperStarIso_hom_app_id A X)]

end AlgebraicGeometry.ProEtale
