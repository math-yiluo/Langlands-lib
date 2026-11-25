/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeResidue

/-!

# Invertibility of the Künneth map of nearby cycles and the reduction `𝒪_E ⟶ 𝔽_E`

From the isomorphisms of arrows of
`WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeResidue`: for bounded below
`𝒪_E`-complexes `A₀`, `B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `𝔽_E ⊗ᴸ Π_{A₀,B₀}`
is invertible if and only if `Π_{𝔽_E ⊗ᴸ A₀, 𝔽_E ⊗ᴸ B₀}` is
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_residueField`), also after restriction along any
`h : W ⟶ Z'` (`NearbyCyclesModel.isIso_map_map_kunnethMap_iff_residueField`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- **The Künneth map and the reduction `𝒪_E ⟶ 𝔽_E`**: for bounded below `𝒪_E`-complexes `A₀`,
`B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `𝔽_E ⊗ᴸ Π_{A₀,B₀}` is invertible if and
only if `Π_{𝔽_E ⊗ᴸ A₀, 𝔽_E ⊗ᴸ B₀}` is. -/
theorem isIso_map_kunnethMap_iff_residueField (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))) (n m : ℤ) [A₀.IsGE n]
    [B₀.IsGE n]
    [(L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE m] :
    IsIso ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Z')).leftDerivedFunctor.map
          (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀ B₀)) ↔
      IsIso (kunnethMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) φ₁ φ₂
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj A₀)
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Y)).leftDerivedFunctor.obj
              B₀)) :=
  (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (nonempty_arrowIso_map_kunnethMap_residueField ℓ E φ₁ φ₂ A₀ B₀ n m).some

set_option maxHeartbeats 1000000 in
-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The restricted Künneth map and the reduction `𝒪_E ⟶ 𝔽_E`**: under the hypotheses of
`NearbyCyclesModel.isIso_map_kunnethMap_iff_residueField`, for every `h : W ⟶ Z'`,
`𝔽_E ⊗ᴸ Lh^* Π_{A₀,B₀}` is invertible if and only if `Lh^* Π_{𝔽_E ⊗ᴸ A₀, 𝔽_E ⊗ᴸ B₀}` is. -/
theorem isIso_map_map_kunnethMap_iff_residueField (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') {W : Scheme.{u}} (h : W ⟶ Z')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))) (n m : ℤ) [A₀.IsGE n]
    [B₀.IsGE n]
    [(L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE m] :
    IsIso ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) W)).leftDerivedFunctor.map
        (L((h)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).map
          (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀ B₀))) ↔
      IsIso (L((h)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧).map
        (kunnethMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) φ₁ φ₂
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj A₀)
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Y)).leftDerivedFunctor.obj
              B₀))) :=
  (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (nonempty_arrowIso_map_map_kunnethMap_residueField ℓ E φ₁ φ₂ h A₀ B₀ n m).some

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
