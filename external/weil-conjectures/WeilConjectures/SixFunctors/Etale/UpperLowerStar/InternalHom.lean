/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Pullback along a étale morphism commutes with internal homs

Let `g : V ⟶ X` be étale and let `A` be a symmetric monoidal closed Grothendieck abelian
coefficient category. The pullback `g^*` of étale sheaves is monoidal, so it has a comparison
map `g^* [P, Q] ⟶ [g^* P, g^* Q]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`). It is an
isomorphism (`AlgebraicGeometry.Etale.isIso_ihomComparison_upperStar`): the internal hom of
sheaves is local.

The proof identifies `g^*` with the restriction along the localization functor
`V_proét ⥤ X_proét` (`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`), as
monoidal functors: both monoidal structures are determined by the adjunctions with `g_*`, and the
units of the adjunction `j_g^* ⊣ g_*` are computed sectionwise
(`AlgebraicGeometry.Etale.localizationRestrictionLowerStarAdjunction_unit_app_tensor`). The
restriction of sheaves is in turn the restriction of presheaves, which commutes with internal homs
since the localization functor is an equivalence on slices
(`CategoryTheory.MorphismProperty.Over.isEquivalence_post_map_op`,
`CategoryTheory.isIso_ihomComparison_whiskeringLeft`), and the inclusion of sheaves into presheaves
preserves internal homs (`CategoryTheory.Monoidal.Reflective.isIso_ihomComparison`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Opposite

namespace AlgebraicGeometry

open Scheme Etale

/-- The localization functor along an étale morphism is continuous for the small étale
topologies, written with `Scheme.smallEtaleTopology`. -/
local instance {V X : Scheme.{u}} {g : V ⟶ X} (h : Etale g) :
    (MorphismProperty.Over.map ⊤ h).IsContinuous V.smallEtaleTopology X.smallEtaleTopology :=
  inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
    (V.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale))

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]
  {V X : Scheme.{u}} (g : V ⟶ X) (h : Etale g)
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [BraidedCategory A]
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal] in
/-- The unit of `j_g^* ⊣ g_*` restricts sections along the counit of the site adjunction. -/
lemma Etale.localizationRestrictionLowerStarAdjunction_unit_app_hom_app
    (P : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((sheafToPresheaf _ A).map ((localizationRestrictionLowerStarAdjunction A g h).unit.app P)).app
      U =
      P.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g h trivial).counit.app
        U.unop).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

/-- The unit of `j_g^* ⊣ g_*` is compatible with the tensor comparison maps. -/
lemma Etale.localizationRestrictionLowerStarAdjunction_unit_app_tensor
    (P Q : Sheaf X.smallEtaleTopology A) :
    (localizationRestrictionLowerStarAdjunction A g h).unit.app (P ⊗ Q) =
      ((localizationRestrictionLowerStarAdjunction A g h).unit.app P ⊗ₘ
        (localizationRestrictionLowerStarAdjunction A g h).unit.app Q) ≫
        μ (g)_*[A] _ _ ≫ (g)_*[A].map (μ ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
          A V.smallEtaleTopology X.smallEtaleTopology) P Q) := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, ← μ_natural_assoc]
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp, Monoidal.tensorHom_app,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  erw [← (μ (sheafToPresheaf (X.smallEtaleTopology) A) P Q).naturality]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ h)]
  rfl

/-- The unit of `j_g^* ⊣ g_*` is compatible with the unit comparison maps. -/
lemma Etale.localizationRestrictionLowerStarAdjunction_unit_app_unit :
    (localizationRestrictionLowerStarAdjunction A g h).unit.app (𝟙_ _) =
      ε (g)_*[A] ≫ (g)_*[A].map (ε ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
          A V.smallEtaleTopology X.smallEtaleTopology)) := by
  apply Sheaf.hom_ext_of_ε_comp
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  erw [← (ε (sheafToPresheaf (X.smallEtaleTopology) A)).naturality]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ h)]
  erw [Monoidal.tensorUnit_map, Category.id_comp]
  rfl

section

variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

open Functor.OplaxMonoidal

/-- The identification of the pullback along a étale morphism with the restriction,
as a functor to the pushforward. -/
noncomputable abbrev Etale.upperStarIsoSheafPushforward :
    (g)^*[A] ≅ (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
      V.smallEtaleTopology X.smallEtaleTopology :=
  upperStarIsoLocalizationRestriction A g h

/-- The identification of the pullback along a étale morphism with the restriction is a
monoidal natural isomorphism. -/
instance : NatTrans.IsMonoidal (Etale.upperStarIsoSheafPushforward A g h).hom where
  unit := by
    rw [← cancel_epi (η (g)^*[A])]
    simp only [Functor.Monoidal.η_ε_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    dsimp only [upperStarIsoSheafPushforward, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_app_unit_comp_map_η]
    exact localizationRestrictionLowerStarAdjunction_unit_app_unit A g h
  tensor P Q := by
    rw [← cancel_epi (δ (g)^*[A] P Q)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    dsimp only [upperStarIsoSheafPushforward, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_app_tensor_comp_map_δ, Functor.map_comp, Category.assoc,
      ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      Adjunction.unit_leftAdjointUniq_hom_app]
    exact localizationRestrictionLowerStarAdjunction_unit_app_tensor A g h P Q

end

section Closed

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
  {V X : Scheme.{u}} (g : V ⟶ X) [hg : Etale g]
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal]

open scoped MonoidalClosed.FunctorCategory

omit [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal] in
/-- **Pullback along a étale morphism commutes with internal homs**: the comparison map
`g^* [P, Q] ⟶ [g^* P, g^* Q]` is an isomorphism.
(blueprint: `lem-weil-pbc-etale-pullback-internal-hom`) -/
theorem Etale.isIso_ihomComparison_upperStar (P : Sheaf X.smallEtaleTopology A) :
    IsIso (ihomComparison (g)^*[A] P) := by
  let h : Etale g := hg
  let R := (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
    V.smallEtaleTopology X.smallEtaleTopology
  let W := (Functor.whiskeringLeft _ _ A).obj (MorphismProperty.Over.map ⊤ h).op
  have : ∀ k : V.Etaleᵒᵖ, (Under.post (MorphismProperty.Over.map ⊤ h).op (X := k)).IsEquivalence :=
    fun k ↦ MorphismProperty.Over.isEquivalence_post_map_op h k.unop
  have hW : IsIso (ihomComparison W ((sheafToPresheaf _ A).obj P)) := inferInstance
  have hι : ∀ Y : Sheaf X.smallEtaleTopology A,
      IsIso (ihomComparison (sheafToPresheaf _ A) Y) :=
    Monoidal.Reflective.isIso_ihomComparison
      (sheafificationAdjunction X.smallEtaleTopology A)
  have hιV : ∀ Y : Sheaf V.smallEtaleTopology A,
      IsIso (ihomComparison (sheafToPresheaf _ A) Y) :=
    Monoidal.Reflective.isIso_ihomComparison
      (sheafificationAdjunction V.smallEtaleTopology A)
  have h1 : IsIso (ihomComparison (sheafToPresheaf _ A ⋙ W) P) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Q
    rw [ihomComparison_comp_app]
    infer_instance
  let τ := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (MorphismProperty.Over.map ⊤ h) A V.smallEtaleTopology
    X.smallEtaleTopology
  have : NatTrans.IsMonoidal τ.symm.hom := inferInstanceAs (NatTrans.IsMonoidal τ.inv)
  have h2 : IsIso (ihomComparison (R ⋙ sheafToPresheaf _ A) P) :=
    isIso_ihomComparison_of_iso τ.symm P
  have hR : IsIso (ihomComparison R P) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Q
    have := NatIso.isIso_app_of_isIso (ihomComparison (R ⋙ sheafToPresheaf _ A) P) Q
    rw [ihomComparison_comp_app] at this
    have := IsIso.of_isIso_comp_right ((sheafToPresheaf _ A).map
      ((ihomComparison R P).app Q))
      ((ihomComparison (sheafToPresheaf _ A) (R.obj P)).app (R.obj Q))
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ A)
  exact isIso_ihomComparison_of_iso (upperStarIsoSheafPushforward A g h) P

end Closed

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
  {V X : Scheme.{u}} (g : V ⟶ X) [hg : Etale g]
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pullback along a étale morphism is braided: it is identified, as a monoidal
functor, with the restriction along the localization functor, which is lax braided. -/
noncomputable instance Etale.laxBraided_upperStar : (g)^*[A].LaxBraided where
  braided P Q := by
    let τ := Etale.upperStarIsoSheafPushforward A g hg
    rw [← cancel_mono (τ.hom.app (Q ⊗ P)), Category.assoc, NatTrans.naturality,
      ← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc,
      Functor.LaxBraided.braided, Category.assoc, NatTrans.IsMonoidal.tensor,
      ← BraidedCategory.braiding_naturality_assoc]

end AlgebraicGeometry
