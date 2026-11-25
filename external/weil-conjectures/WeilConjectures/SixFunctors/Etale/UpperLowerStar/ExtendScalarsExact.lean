/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars

/-!
# Exactness of extension of scalars on étale sheaves

Extension of scalars `F ↦ Λ ⊗_ℤ F` (`AlgebraicGeometry.Etale.extendScalars`) is right exact,
being a left adjoint. Its stalks are the extensions of scalars of the stalks
(`AlgebraicGeometry.Etale.extendScalarsCompSheafFiberIso`), so it sends a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of étale sheaves of abelian groups to a short exact sequence as soon as the
stalks of `C` at the geometric points are projective abelian groups: the stalk sequences then
split (`AlgebraicGeometry.Etale.shortExact_map_extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

/-- The stalks of `Λ ⊗_ℤ F` are the extensions of scalars of the stalks of `F`. -/
noncomputable def extendScalarsCompSheafFiberIso (P : X.smallEtaleTopology.Point.{u + 1}) :
    extendScalars Λ X ⋙ P.sheafFiber ≅
      P.sheafFiber ⋙ ModuleCat.extendScalarsAddCommGrp Λ :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalarsAddCommGrp Λ))
    (P.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} Λ)) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (P.presheafFiberCompIso (ModuleCat.extendScalarsAddCommGrp Λ))

/-- Extension of scalars sends a short exact sequence of étale sheaves of abelian groups whose
third term has projective stalks at the geometric points to a short exact sequence. -/
theorem shortExact_map_extendScalars {S : ShortComplex (Sheaf X.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (hX₃ : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj S.X₃)) :
    (S.map (extendScalars Λ X)).ShortExact := by
  have := hS.epi_g
  refine { exact := hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance
           mono_f := ?_
           epi_g := inferInstanceAs (Epi ((extendScalars Λ X).map S.g)) }
  have hmono := (isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyReflectMonomorphisms
    (ModuleCat.{u + 1} Λ)
  refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _ _ (fun Φ ↦ ?_)
  obtain ⟨-, ⟨x⟩⟩ := Φ
  let P := X.uliftPointSmallEtale x
  have hP : (S.map P.sheafFiber).ShortExact := hS.map_of_exact P.sheafFiber
  have : Projective (S.map P.sheafFiber).X₃ := hX₃ x
  let σ := hP.splittingOfProjective
  have : IsSplitMono (P.sheafFiber.map S.f) := ⟨⟨σ.r, σ.f_r⟩⟩
  have : Mono ((ModuleCat.extendScalarsAddCommGrp Λ).map (P.sheafFiber.map S.f)) :=
    inferInstance
  have h := (extendScalarsCompSheafFiberIso Λ P).hom.naturality S.f
  dsimp only [Functor.comp_map] at h
  have : Mono (P.sheafFiber.map ((extendScalars Λ X).map S.f) ≫
      (extendScalarsCompSheafFiberIso Λ P).hom.app S.X₂) := by
    rw [h]
    infer_instance
  exact mono_of_mono (P.sheafFiber.map ((extendScalars Λ X).map S.f))
    ((extendScalarsCompSheafFiberIso Λ P).hom.app S.X₂)

end AlgebraicGeometry.Etale
