/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso
public import WeilConjectures.Compactification.ProjectiveSpace

/-! # Changing the two homogeneous coordinates of the projective line

Source: blueprint lemma-affine-space-etale-localization, proof (1), transport of the standard model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The standard-chart coordinates give the same projective line as the finite trace model.
Source: blueprint lemma-affine-space-etale-localization, proof (1), coordinate identification.
(auxiliary; not a blueprint node)
Proof: reindex the homogeneous sections by the explicit bijection from two lifted indices
 to an optional lifted singleton. The existing coordinate reindexing theorem makes the
resulting morphism invertible, and its construction gives the equation over the base. -/
theorem exists_projectiveLinePresentation (S : Scheme.{u}) :
    ∃ e : ℙ(Option (ULift.{u} (Fin 1)); S) ≅ ProjectiveLine S,
      e.hom ≫ (ProjectiveLine S ↘ S) = (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) := by
  let b : ULift.{u} (Fin 2) ≃ Option (ULift.{u} (Fin 1)) :=
    Equiv.ulift.trans ((finSuccEquiv 1).trans (Equiv.optionCongr Equiv.ulift.symm))
  let s := fun j : ULift.{u} (Fin 2) ↦
    Scheme.Modules.pullbackSection (𝟙 ℙ(Option (ULift.{u} (Fin 1)); S))
      (ProjectiveSpace.twistOneSection _ S (b j))
  let U := fun j : ULift.{u} (Fin 2) ↦ ProjectiveSpace.standardOpen _ S (b j)
  let hs := fun j : ULift.{u} (Fin 2) ↦
    ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection
      (𝟙 ℙ(Option (ULift.{u} (Fin 1)); S)) (b j)
  let hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (ProjectiveSpace.iSup_standardOpen _ S)
  let f := ProjectiveSpace.homOfIsFreeGenerator s U hs
    (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) hU
  have : IsIso f := ProjectiveSpace.isIso_homOfIsFreeGenerator_reindex _ _ b S
  refine ⟨asIso f, ?_⟩
  exact ProjectiveSpace.homOfIsFreeGenerator_over s U hs _ hU

/-- A pullback of a presented projective line is again presented by the standard model.
Source: blueprint lemma-affine-space-etale-localization, proof (1), pullback universal property.
(auxiliary; not a blueprint node)
Proof: transport the pullback square along the given isomorphism on its upper right.
Its universal-property isomorphism to the standard projective-line square preserves
both projections, in particular the projection to the new base. -/
theorem exists_projectiveLinePullbackPresentation
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q) :
    ∃ e' : X' ≅ ProjectiveLine Y',
      e'.hom ≫ (ProjectiveLine Y' ↘ Y') = q' ∧
      e'.hom ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g = g' ≫ e.hom := by
  have sq' : IsPullback (g' ≫ e.hom) q' (ProjectiveLine Y ↘ Y) g :=
    sq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simpa using w.symm) (by simp)
  let std := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g
  refine ⟨sq'.isoIsPullback _ _ std, ?_, ?_⟩
  · exact IsPullback.isoIsPullback_hom_snd _ _ sq' std
  · exact IsPullback.isoIsPullback_hom_fst _ _ sq' std

end AlgebraicGeometry.Etale
