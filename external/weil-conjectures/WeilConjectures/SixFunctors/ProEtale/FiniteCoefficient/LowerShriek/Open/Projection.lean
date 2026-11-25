/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The projection formula for the extension by zero along an open immersion

Let `j : U ⟶ X` be an open immersion and `L : U.ProEt ⥤ X.ProEt` the localization functor
`T ↦ (T ⟶ U ⟶ X)`. On presheaves, the extension by zero is the left Kan extension `L.op.lan`.
This file shows that the comparison

```
  L.op.lan (P ⊗ L^* Q) ⟶ L.op.lan P ⊗ L.op.lan (L^* Q) ⟶ L.op.lan P ⊗ Q
```

built from the oplax monoidal structure `δ` of `L.op.lan` and the counit `ε` of
`L.op.lan ⊣ L^*`, is an isomorphism of presheaves on `X.ProEt`, for every presheaf `P` on
`U.ProEt` and `Q` on `X.ProEt`
(`AlgebraicGeometry.ProEtale.isIso_localizationLowerShriekPresheafProjection`).

Sheafifying, the projection map `j_!(K ⊗ j^* M) ⟶ j_! K ⊗ M` of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekProjectionMap`, the projection map of the
adjunction `j_! ⊣ j^*`) is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekProjectionMap_app_app`).

## The argument

At a weakly étale `V ⟶ X`, both sides are colimits over the comma category of `V` under `L`.
That category is empty when `V` does not factor through `U`, and then both sides are initial.
When `V` factors through `U`, it has an initial object `V'` with `L V' ≅ V`, `L` being fully
faithful, so the colimits are the values at `V'`, where the comparison is an isomorphism by the
unit and triangle identities.

On sheaves, `j_!` is fully faithful and `j^*` is strong monoidal, so the projection map is an
isomorphism as soon as `j_! K ⊗ M` lies in the essential image of `j_!`; by the presheaf
statement and the monoidality of sheafification it is `j_!` of the sheafification of
`K ⊗ L^* M`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The localization functor `U.ProEt ⥤ X.ProEt` along an open immersion `j : U ⟶ X`. -/
noncomputable abbrev openImmersionLocalization : U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)

instance full_openImmersionLocalization : (openImmersionLocalization j).Full :=
  have : MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.Over.full_map (P := @WeaklyEtale) (Q := ⊤) (f := j) _

instance faithful_openImmersionLocalization : (openImmersionLocalization j).Faithful :=
  have : MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.Over.faithful_map (P := @WeaklyEtale) (Q := ⊤) (f := j) _

/-- An object of the comma category of `V` under the localization functor whose structure
morphism is an isomorphism is terminal, the localization functor being fully faithful. -/
lemma nonempty_isTerminal_costructuredArrow_of_isIso (V : X.ProEtᵒᵖ)
    (t : CostructuredArrow (openImmersionLocalization j).op V) [IsIso t.hom] :
    Nonempty (IsTerminal t) := by
  have hL : (openImmersionLocalization j).op.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (openImmersionLocalization j)).op
  refine ⟨IsTerminal.ofUniqueHom (fun s ↦ CostructuredArrow.homMk
    (hL.preimage (s.hom ≫ inv t.hom)) (by
      erw [hL.map_preimage]
      simp))
    (fun s m ↦ ?_)⟩
  apply CostructuredArrow.hom_ext
  apply hL.map_injective
  erw [hL.map_preimage]
  simp [← CostructuredArrow.w m]

/-- If the comma category of `V` under the localization functor is nonempty, that is, if
`V ⟶ X` factors through `U`, it has an object whose structure morphism is an isomorphism:
`V` itself, regarded as weakly étale over `U`. -/
lemma exists_isIso_costructuredArrow_hom (V : X.ProEtᵒᵖ)
    (s : CostructuredArrow (openImmersionLocalization j).op V) :
    ∃ t : CostructuredArrow (openImmersionLocalization j).op V, IsIso t.hom := by
  let W : U.ProEt := s.left.unop
  let g : V.unop.left ⟶ W.left := s.hom.unop.left
  have hg : g ≫ W.hom ≫ j = V.unop.hom := by
    simpa [g] using MorphismProperty.Over.w s.hom.unop
  have : WeaklyEtale ((g ≫ W.hom) ≫ j) := by
    rw [Category.assoc, hg]
    exact V.unop.prop
  have : WeaklyEtale (g ≫ W.hom) := WeaklyEtale.of_comp _ j
  let V' : U.ProEt := MorphismProperty.Over.mk ⊤ (g ≫ W.hom) inferInstance
  let e : (openImmersionLocalization j).obj V' ≅ V.unop :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa [V'] using hg.symm)
  exact ⟨CostructuredArrow.mk (Y := op V') e.inv.op, inferInstanceAs (IsIso e.inv.op)⟩

/-- The presheaf-level projection comparison
`L.op.lan (P ⊗ L^* Q) ⟶ L.op.lan P ⊗ Q` for the localization functor `L` along an open
immersion: the oplax monoidal structure of `L.op.lan` followed by the counit of
`L.op.lan ⊣ L^*` in the second factor. -/
noncomputable def localizationLowerShriekPresheafProjection (P : U.ProEtᵒᵖ ⥤ A)
    (Q : X.ProEtᵒᵖ ⥤ A) :
    (openImmersionLocalization j).op.lan.obj (P ⊗ ((openImmersionLocalization j).op ⋙ Q)) ⟶
      (openImmersionLocalization j).op.lan.obj P ⊗ Q :=
  δ (openImmersionLocalization j).op.lan P ((openImmersionLocalization j).op ⋙ Q) ≫
    ((openImmersionLocalization j).op.lan.obj P ◁
      ((openImmersionLocalization j).op.lanAdjunction A).counit.app Q)

omit [MonoidalPreadditive A] in
/-- The presheaf-level projection comparison is an isomorphism at every weakly étale `V ⟶ X`:
both sides are initial if `V` does not factor through `U`, and otherwise both are computed at
the terminal object of the comma category of `V`. -/
lemma isIso_localizationLowerShriekPresheafProjection_app (P : U.ProEtᵒᵖ ⥤ A)
    (Q : X.ProEtᵒᵖ ⥤ A) (V : X.ProEtᵒᵖ) :
    IsIso ((localizationLowerShriekPresheafProjection A j P Q).app V) := by
  by_cases h : Nonempty (CostructuredArrow (openImmersionLocalization j).op V)
  · obtain ⟨s⟩ := h
    obtain ⟨t, ht⟩ := exists_isIso_costructuredArrow_hom j V s
    obtain ⟨hT⟩ := nonempty_isTerminal_costructuredArrow_of_isIso j V t
    have h₁ := ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (P ⊗ ((openImmersionLocalization j).op ⋙ Q)) V).isIso_ι_app_of_isTerminal t hT
    have h₂ := ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      P V).isIso_ι_app_of_isTerminal t hT
    dsimp at h₁ h₂
    have key : (((openImmersionLocalization j).op.lanUnit.app
          (P ⊗ ((openImmersionLocalization j).op ⋙ Q))).app t.left ≫
        ((openImmersionLocalization j).op.lan.obj
          (P ⊗ ((openImmersionLocalization j).op ⋙ Q))).map t.hom) ≫
          (localizationLowerShriekPresheafProjection A j P Q).app V =
        (((openImmersionLocalization j).op.lanUnit.app P).app t.left ≫
          ((openImmersionLocalization j).op.lan.obj P).map t.hom) ⊗ₘ Q.map t.hom := by
      simp only [localizationLowerShriekPresheafProjection, NatTrans.comp_app,
        Category.assoc]
      have hn := (δ (openImmersionLocalization j).op.lan P
        ((openImmersionLocalization j).op ⋙ Q)).naturality t.hom
      rw [reassoc_of% hn, Functor.lanUnit_app_app_δ_app_assoc]
      have hc :=
        (((openImmersionLocalization j).op.lanAdjunction A).counit.app Q).naturality t.hom
      have hu := (openImmersionLocalization j).op.lanUnit_app_app_lanAdjunction_counit_app_app Q
        t.left
      simp only [Monoidal.tensorObj_map, Monoidal.whiskerLeft_app] at *
      dsimp at hc hu
      rw [← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1
      · simp
      · rw [hc, reassoc_of% hu]
    have h₃ : IsIso ((((openImmersionLocalization j).op.lanUnit.app P).app t.left ≫
        ((openImmersionLocalization j).op.lan.obj P).map t.hom) ⊗ₘ Q.map t.hom) := by
      infer_instance
    rw [← key] at h₃
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ h₃
  · have : IsEmpty (CostructuredArrow (openImmersionLocalization j).op V) :=
      not_nonempty_iff.mp h
    have hs := (isColimitEquivIsInitialOfIsEmpty A _).1
      ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        (P ⊗ ((openImmersionLocalization j).op ⋙ Q)) V)
    have hP := (isColimitEquivIsInitialOfIsEmpty A _).1
      ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P V)
    have ht : IsInitial ((((openImmersionLocalization j).op.lan.obj P) ⊗ Q).obj V) :=
      IsInitial.isInitialObj (tensorRight (Q.obj V)) _ hP
    exact ⟨ht.to _, hs.hom_ext _ _, ht.hom_ext _ _⟩

section Sheaf

open Functor.LaxMonoidal

/-- The projection map `j_!(K ⊗ j^* M) ⟶ j_! K ⊗ M` for the extension by zero `j_!` along an
open immersion `j : U ⟶ X` on pro-étale sheaves: `Adjunction.projectionMap` for
`j_! ⊣ j^*` and the monoidal structure of the pullback `j^*`. -/
noncomputable def openImmersionLowerShriekProjectionMap :
    (Functor.postcompose₂.obj (ProEtale.openImmersionLowerShriek A j)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (ProEtale.upperStar A j)).obj
          (curriedTensor _)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (ProEtale.openImmersionLowerShriek A j)).obj (𝟭 _)).obj
        (curriedTensor _) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction A j).projectionMap
    (ProEtale.upperStar A j) (curriedTensor _) (curriedTensor _) (μNatTrans _)

/-- The presheaf-level projection comparison is an isomorphism. -/
instance isIso_localizationLowerShriekPresheafProjection (P : U.ProEtᵒᵖ ⥤ A)
    (Q : X.ProEtᵒᵖ ⥤ A) : IsIso (localizationLowerShriekPresheafProjection A j P Q) :=
  have := isIso_localizationLowerShriekPresheafProjection_app A j P Q
  NatIso.isIso_of_isIso_app _

/-- Sheafifying the presheaf extension by zero is the sheaf extension by zero of the
sheafification: both are left adjoint to the restriction of sheaves regarded as presheaves. -/
noncomputable def lanCompPresheafToSheafIso :
    (openImmersionLocalization j).op.lan ⋙ presheafToSheaf (Scheme.ProEt.topology X) A ≅
      presheafToSheaf (Scheme.ProEt.topology U) A ⋙ ProEtale.openImmersionLowerShriek A j :=
  (conjugateIsoEquiv
    ((sheafificationAdjunction _ A).comp (ProEtale.openImmersionLowerShriekAdjunction A j))
    (((openImmersionLocalization j).op.lanAdjunction A).comp
      (sheafificationAdjunction _ A))).symm (Iso.refl _)

/-- The sheaf `j_! K ⊗ M` lies in the essential image of `j_!`: it is `j_!` of the
sheafification of `K ⊗ j^* M` computed on presheaves, by the presheaf-level projection
comparison and the monoidality of sheafification. -/
noncomputable def openImmersionLowerShriekTensorIso (K : Sheaf (Scheme.ProEt.topology U) A)
    (M : Sheaf (Scheme.ProEt.topology X) A) :
    (ProEtale.openImmersionLowerShriek A j).obj K ⊗ M ≅
      (ProEtale.openImmersionLowerShriek A j).obj ((presheafToSheaf _ A).obj
        (K.obj ⊗ ((openImmersionLocalization j).op ⋙ M.obj))) :=
  whiskerLeftIso _ (asIso ((sheafificationAdjunction _ A).counit.app M)).symm ≪≫
    Functor.Monoidal.μIso (presheafToSheaf _ A) _ _ ≪≫
    (presheafToSheaf _ A).mapIso
      (asIso (localizationLowerShriekPresheafProjection A j K.obj M.obj)).symm ≪≫
    (lanCompPresheafToSheafIso A j).app _

/-- The monoidal structure of the pullback along an open immersion is an isomorphism. -/
instance isIso_μNatTrans_upperStar :
    IsIso (μNatTrans (ProEtale.upperStar A j)) := by
  have (K : Sheaf (Scheme.ProEt.topology X) A) :
      IsIso ((μNatTrans (ProEtale.upperStar A j)).app K) := by
    have (M : Sheaf (Scheme.ProEt.topology X) A) :
        IsIso (((μNatTrans (ProEtale.upperStar A j)).app K).app M) :=
      inferInstanceAs (IsIso (Functor.LaxMonoidal.μ (ProEtale.upperStar A j) K M))
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- The projection map `j_!(K ⊗ j^* M) ⟶ j_! K ⊗ M` of the extension by zero along an open
immersion is an isomorphism. -/
instance isIso_openImmersionLowerShriekProjectionMap_app_app
    (K : Sheaf (Scheme.ProEt.topology U) A) (M : Sheaf (Scheme.ProEt.topology X) A) :
    IsIso (((openImmersionLowerShriekProjectionMap A j).app K).app M) := by
  have :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction A j).unit_isIso_of_L_fully_faithful
  exact Adjunction.isIso_projectionMap_app_app_of_iso
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction A j) _ _ _ _ K M _
    (openImmersionLowerShriekTensorIso A j K M)

end Sheaf

end AlgebraicGeometry.ProEtale
