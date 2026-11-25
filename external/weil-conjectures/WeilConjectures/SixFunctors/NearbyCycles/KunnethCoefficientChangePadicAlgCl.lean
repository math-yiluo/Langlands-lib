/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeFlatComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!

# The Künneth map of nearby cycles and the coefficients `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`

We specialize the compatibility of the Künneth map `Π_{A,B}` of nearby cycles with a flat change
of coefficients (`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap_of_flat`) to
`𝒪_E ⟶ E ⟶ ℚ̄_ℓ`, whose (Push) comparisons are invertible on bounded below objects along
quasi-compact quasi-separated morphisms
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`,
`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`): for
models whose `j`s are quasi-compact and quasi-separated and bounded below `𝒪_E`-complexes `A₀`,
`B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Π_{A₀,B₀}` and
`Π_{A, B}` for `A = ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} A₀`, `B = ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} B₀` are isomorphic arrows
(`NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap_padicAlgCl`). In particular `Π_{A,B}` is
invertible if `Π_{A₀,B₀}` is, and conversely `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Π_{A₀,B₀}` is invertible if
`Π_{A,B}` is (`NearbyCyclesModel.isIso_map_map_kunnethMap_iff_padicAlgCl`).

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

set_option maxHeartbeats 2000000 in
-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The Künneth map and the coefficients `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`**: for models whose `j`s are
quasi-compact and quasi-separated and bounded below `𝒪_E`-complexes `A₀`, `B₀` such that
`Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Π_{A₀,B₀}` and the Künneth map
`Π_{A,B}` with `ℚ̄_ℓ`-coefficients at `A = ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} A₀`, `B = ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} B₀`
are isomorphic arrows. -/
theorem nonempty_arrowIso_map_map_kunnethMap_padicAlgCl [QuasiCompact M.j] [QuasiSeparated M.j]
    [QuasiCompact N.j] [QuasiSeparated N.j] [QuasiCompact P.j] [QuasiSeparated P.j]
    (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))) (n m : ℤ) [A₀.IsGE n]
    [B₀.IsGE n]
    [(L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE m] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z')).leftDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          Z')).leftDerivedFunctor.map
          (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀ B₀))) ≅
      Arrow.mk (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂
        ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
            (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj A₀))
        ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          Y)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
            (padicIntegersRingObjToContinuousMapRingObj ℓ E) Y)).leftDerivedFunctor.obj B₀)))) := by
  have k := nonempty_arrowIso_map_map_kunnethMap_of_flat_of_flat
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    (fun _ _ j _ _ K n _ ↦ by
      exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E j K n)
    (fun _ _ j _ _ K n _ ↦ by
      exact_mod_proofs isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E j K n)
    φ₁ φ₂ A₀ B₀ n m
  exact_mod_proofs k
set_option maxHeartbeats 2000000 in
-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The restricted Künneth map and the coefficients `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`**: under the hypotheses of
`NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap_padicAlgCl`, for every `h : W ⟶ Z'`,
`ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Lh^* Π_{A₀,B₀}` and `Lh^* Π_{A,B}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_map_map_kunnethMap_padicAlgCl [QuasiCompact M.j]
    [QuasiSeparated M.j] [QuasiCompact N.j] [QuasiSeparated N.j] [QuasiCompact P.j]
    [QuasiSeparated P.j] (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂') {W : Scheme.{u}}
    (h : W ⟶ Z')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))) (n m : ℤ) [A₀.IsGE n]
    [B₀.IsGE n]
    [(L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE m] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) W)).leftDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          W)).leftDerivedFunctor.map
          (L((h)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).map
            (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀ B₀)))) ≅
      Arrow.mk (L((h)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂
        ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
            (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj A₀))
        ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          Y)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
            (padicIntegersRingObjToContinuousMapRingObj ℓ E) Y)).leftDerivedFunctor.obj
              B₀))))) := by
  have k := nonempty_arrowIso_map_map_map_kunnethMap_of_flat_of_flat
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    (fun _ _ j _ _ K n _ ↦ by
      exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E j K n)
    (fun _ _ j _ _ K n _ ↦ by
      exact_mod_proofs isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E j K n)
    φ₁ φ₂ h A₀ B₀ n m
  exact_mod_proofs k

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
