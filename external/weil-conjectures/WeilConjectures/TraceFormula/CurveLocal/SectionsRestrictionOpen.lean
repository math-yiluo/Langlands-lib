/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyExact

/-!

# Restriction of derived sections to an open subscheme

Let `j : U ⟶ X` be an open immersion. The pullback of sections `F(U ⟶ X) ⟶ (j^* F)(U)`
along `𝟙 U` (`AlgebraicGeometry.Etale.sectionsPullback`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_sectionsPullback_of_isOpenImmersion`), and hence so is the
restriction of derived sections `RΓ(U ⟶ X, K) ⟶ RΓ(U, j^* K)`
(`AlgebraicGeometry.Etale.isIso_sectionsRestriction_of_isOpenImmersion`), `j^*` preserving
K-injective complexes since it has the exact left adjoint `j_!`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U ⟶ X`, the map `U ⟶ U ×_X U` of étale `U`-schemes induced by
`𝟙 U` is an isomorphism. -/
lemma isIso_homToPullback_of_isOpenImmersion
    (h : 𝟙 U ≫ (Scheme.Etale.mk j).hom = (Scheme.Etale.mk (𝟙 U)).hom ≫ j) :
    IsIso (homToPullback j (V := Scheme.Etale.mk (𝟙 U)) (U := Scheme.Etale.mk j) (𝟙 U) h) := by
  refine isIso_of_isIso_left _ ?_
  have : IsIso (pullback.fst (Scheme.Etale.mk j).hom j) :=
    inferInstanceAs (IsIso (pullback.fst j j))
  have e := homToPullback_left_fst j (V := Scheme.Etale.mk (𝟙 U)) (U := Scheme.Etale.mk j)
    (𝟙 U) h
  have : IsIso ((homToPullback j (V := Scheme.Etale.mk (𝟙 U)) (U := Scheme.Etale.mk j)
      (𝟙 U) h).left ≫ pullback.fst (Scheme.Etale.mk j).hom j) := by
    rw [e]
    exact inferInstanceAs (IsIso (𝟙 U))
  exact IsIso.of_isIso_comp_right _ (pullback.fst (Scheme.Etale.mk j).hom j)

/-- For an open immersion `j : U ⟶ X`, the pullback of sections `F(U ⟶ X) ⟶ (j^* F)(U)` is an
isomorphism. -/
instance isIso_sectionsPullback_of_isOpenImmersion
    (h : 𝟙 U ≫ (Scheme.Etale.mk j).hom = (Scheme.Etale.mk (𝟙 U)).hom ≫ j) :
    IsIso (sectionsPullback A j (V := Scheme.Etale.mk j) (W := Scheme.Etale.mk (𝟙 U))
      (𝟙 U) h) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have := isIso_homToPullback_of_isOpenImmersion j h
  have hu := NatTrans.congr_app (Sheaf.hom_ext_iff.1 (Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction A j)
    (localizationRestrictionLowerStarAdjunction A j inferInstance) F)) (op (Scheme.Etale.mk j))
  have hc : IsIso (((localizationRestrictionLowerStarAdjunction A j inferInstance).unit.app
      F).hom.app (op (Scheme.Etale.mk j))) := by
    have : IsIso ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance
        trivial).counit.app (Scheme.Etale.mk j)) :=
      isIso_of_isIso_left _ (inferInstanceAs (IsIso (pullback.fst j j)))
    have e : ((localizationRestrictionLowerStarAdjunction A j inferInstance).unit.app
        F).hom.app (op (Scheme.Etale.mk j)) = F.obj.map ((MorphismProperty.Over.mapPullbackAdj
          @Etale ⊤ j inferInstance trivial).counit.app (Scheme.Etale.mk j)).op := by
      simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
        Adjunction.whiskerLeft]
    rw [e]
    infer_instance
  have hρ : IsIso (((j)_*[A].map ((upperStarIsoLocalizationRestriction A j
      inferInstance).hom.app F)).hom.app (op (Scheme.Etale.mk j))) :=
    inferInstanceAs (IsIso (((sheafToPresheaf _ A).map ((j)_*[A].map
      ((upperStarIsoLocalizationRestriction A j inferInstance).hom.app F))).app _))
  have : IsIso (((upperStarLowerStarAdjunction A j).unit.app F).hom.app
      (op (Scheme.Etale.mk j))) := by
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
    have : IsIso (((upperStarLowerStarAdjunction A j).unit.app F).hom.app
        (op (Scheme.Etale.mk j)) ≫ ((j)_*[A].map ((upperStarIsoLocalizationRestriction A j
          inferInstance).hom.app F)).hom.app (op (Scheme.Etale.mk j))) := by
      erw [hu]
      exact hc
    exact IsIso.of_isIso_comp_right _ (((j)_*[A].map ((upperStarIsoLocalizationRestriction A j
      inferInstance).hom.app F)).hom.app (op (Scheme.Etale.mk j)))
  exact IsIso.comp_isIso' this
    (inferInstance : IsIso (((j)^*[A].obj F).obj.map (homToPullback j
      (V := Scheme.Etale.mk (𝟙 U)) (U := Scheme.Etale.mk j) (𝟙 U) h).op))

/-- For an open immersion `j : U ⟶ X`, the restriction of derived sections
`RΓ(U ⟶ X, K) ⟶ RΓ(U, j^* K)` is an isomorphism: `j^*` preserves K-injective complexes, having
the exact left adjoint `j_!`, and the underlying pullback of sections is an isomorphism. -/
lemma isIso_sectionsRestriction_of_isOpenImmersion
    (h : 𝟙 U ≫ (Scheme.Etale.mk j).hom = (Scheme.Etale.mk (𝟙 U)).hom ≫ j)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso ((sectionsRestriction A j (V := Scheme.Etale.mk j) (W := Scheme.Etale.mk (𝟙 U))
      (𝟙 U) h).app K) := by
  have : (j)^*[A].PreservesKInjectiveComplexes :=
    (Etale.openImmersionLowerShriekUpperStarAdjunction A j).preservesKInjectiveComplexes
  exact Functor.isIso_rightDerivedPullback_app _ _ K

/-- The restriction of derived sections `RΓ(X ∖ Z, K) ⟶ RΓ(X ∖ Z, K|_{X ∖ Z})` to the open
complement of a closed immersion `i : Z ⟶ X` is an isomorphism. -/
lemma isIso_sectionsRestriction_openComplement {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (h : 𝟙 i.openComplement.toScheme ≫ (Scheme.Etale.mk i.openComplement.ι).hom =
      (Scheme.Etale.mk (𝟙 i.openComplement.toScheme)).hom ≫ i.openComplement.ι)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso ((sectionsRestriction A i.openComplement.ι (V := Scheme.Etale.mk i.openComplement.ι)
      (W := Scheme.Etale.mk (𝟙 i.openComplement.toScheme)) (𝟙 _) h).app K) :=
  isIso_sectionsRestriction_of_isOpenImmersion A i.openComplement.ι h K

end AlgebraicGeometry.Etale
