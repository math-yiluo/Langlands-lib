/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-!

# Nearby cycles and change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of condensed rings and `T = Λ' ⊗ᴸ_Λ -` the derived extension of
scalars. For a model `(𝒳, j, i, ε)` of `X`, the nearby cycles `Ψ = Li^* Rj_* Lε^*` commute with `T`
at `K` as soon as the pushforward `Rj_*` does at `Lε^* K`
(`ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesExtendScalarsIso`): the derived pullbacks
commute with every change of coefficients
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`).

The same holds after precomposing with an extension by zero `Dj'_!` along an open immersion, which
commutes with every change of coefficients
(`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`), and postcomposing with two derived
pullbacks
(`NearbyCyclesModel.upperStarUpperStarNearbyCyclesLowerShriekExtendScalarsIso`,
with its consequences for vanishing).
This is the form in which nearby cycles of extensions by zero, restricted along the special fibre,
are compared for the coefficients `𝒪_E`, `E`, `ℚ̄_ℓ` and `𝔽_E`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X X' : Scheme.{u}}
  (M : NearbyCyclesModel X X')

/-- **Nearby cycles commute with a change of coefficients** at `K` as soon as a comparison `φ`
for the pushforward `Rj_*` is invertible at `Lε^* K`:
`Λ' ⊗ᴸ Ψ^Λ(K) ≅ Ψ^Λ'(Λ' ⊗ᴸ K)`. -/
noncomputable def nearbyCyclesExtendScalarsIso
    (φ : R((M.j)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a M.total)) ⟶
      L(Mod.extendScalars (coefficientMap a M.generic)) ⋙ R((M.j)_*⟦Λ'⟧))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hφ : IsIso (φ.app ((L((M.ε)^*⟦Λ⟧)).obj K))) :
    (L(Mod.extendScalars (coefficientMap a X'))).obj ((M.nearbyCycles Λ).obj K) ≅
      (M.nearbyCycles Λ').obj ((L(Mod.extendScalars (coefficientMap a X))).obj K) :=
  (derivedUpperStarExtendScalarsIso a M.i).app _ ≪≫
    (L((M.i)^*⟦Λ'⟧)).mapIso (@asIso _ _ _ _ _ hφ) ≪≫
    (L((M.i)^*⟦Λ'⟧)).mapIso
      ((R((M.j)_*⟦Λ'⟧)).mapIso ((derivedUpperStarExtendScalarsIso a M.ε).app K))


variable {U Y W : Scheme.{u}} (o : U ⟶ X) [IsOpenImmersion o] (e : Y ⟶ X') (ι : W ⟶ Y)

-- Elaborating the statement compares the coefficient rings `Λ'_X` of both sides.
/-- **Restricted nearby cycles of extensions by zero commute with a change of coefficients**: for
an open immersion `o : U ⟶ X` and morphisms `e : Y ⟶ X'`, `ι : W ⟶ Y`,
`Λ' ⊗ᴸ Lι^* Le^* Ψ^Λ(Do_! K) ≅ Lι^* Le^* Ψ^Λ'(Do_!(Λ' ⊗ᴸ K))`, given a comparison
`eΨ : Λ' ⊗ᴸ Ψ^Λ(Do_! K) ≅ Ψ^Λ'(Λ' ⊗ᴸ Do_! K)` (for instance
`ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesExtendScalarsIso`). -/
noncomputable def upperStarUpperStarNearbyCyclesLowerShriekExtendScalarsIso
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (eΨ : (L(Mod.extendScalars (coefficientMap a X'))).obj
        ((M.nearbyCycles Λ).obj (D((o)_!open⟦Λ⟧).obj K)) ≅
      (M.nearbyCycles Λ').obj ((L(Mod.extendScalars (coefficientMap a X))).obj
        (D((o)_!open⟦Λ⟧).obj K))) :
    (L(Mod.extendScalars (coefficientMap a W))).obj ((L((ι)^*⟦Λ⟧)).obj
        ((L((e)^*⟦Λ⟧)).obj ((M.nearbyCycles Λ).obj (D((o)_!open⟦Λ⟧).obj K)))) ≅
      (L((ι)^*⟦Λ'⟧)).obj ((L((e)^*⟦Λ'⟧)).obj ((M.nearbyCycles Λ').obj
        (D((o)_!open⟦Λ'⟧).obj ((L(Mod.extendScalars (coefficientMap a U))).obj K)))) :=
  (derivedUpperStarExtendScalarsIso a ι).app _ ≪≫
    (L((ι)^*⟦Λ'⟧)).mapIso ((derivedUpperStarExtendScalarsIso a e).app _ ≪≫
      (L((e)^*⟦Λ'⟧)).mapIso (eΨ ≪≫
        (M.nearbyCycles Λ').mapIso ((derivedOpenImmersionShriekIso a o).app K)))
-- Elaborating the statement compares the coefficient rings `Λ'_X` of both sides.
/-- If `Lι^* Le^* Ψ^Λ(Do_! K)` vanishes, so does `Lι^* Le^* Ψ^Λ'(Do_!(Λ' ⊗ᴸ K))`, as soon as a
comparison `φ` for the pushforward `Rj_*` is invertible at `Lε^* Do_! K`. -/
lemma isZero_upperStar_upperStar_nearbyCycles_lowerShriek_extendScalars
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (φ : R((M.j)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a M.total)) ⟶
      L(Mod.extendScalars (coefficientMap a M.generic)) ⋙ R((M.j)_*⟦Λ'⟧))
    (hφ : IsIso (φ.app ((L((M.ε)^*⟦Λ⟧)).obj (D((o)_!open⟦Λ⟧).obj K))))
    (h : IsZero ((L((ι)^*⟦Λ⟧)).obj
      ((L((e)^*⟦Λ⟧)).obj ((M.nearbyCycles Λ).obj (D((o)_!open⟦Λ⟧).obj K))))) :
    IsZero ((L((ι)^*⟦Λ'⟧)).obj ((L((e)^*⟦Λ'⟧)).obj ((M.nearbyCycles Λ').obj
        (D((o)_!open⟦Λ'⟧).obj ((L(Mod.extendScalars (coefficientMap a U))).obj K))))) := by
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a W)).isLeftAdjoint
  exact ((L(Mod.extendScalars (coefficientMap a W))).map_isZero h).of_iso
    (upperStarUpperStarNearbyCyclesLowerShriekExtendScalarsIso a M o e ι K
      (nearbyCyclesExtendScalarsIso a M φ _ hφ)).symm

-- Elaborating the statement compares the coefficient rings `Λ'_X` of both sides.
/-- If `Lι^* Le^* Ψ^Λ'(Do_!(Λ' ⊗ᴸ K))` vanishes, so does `Λ' ⊗ᴸ Lι^* Le^* Ψ^Λ(Do_! K)`, as soon as
a comparison `φ` for the pushforward `Rj_*` is invertible at `Lε^* Do_! K`. -/
lemma isZero_extendScalars_upperStar_upperStar_nearbyCycles_lowerShriek
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (φ : R((M.j)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a M.total)) ⟶
      L(Mod.extendScalars (coefficientMap a M.generic)) ⋙ R((M.j)_*⟦Λ'⟧))
    (hφ : IsIso (φ.app ((L((M.ε)^*⟦Λ⟧)).obj (D((o)_!open⟦Λ⟧).obj K))))
    (h : IsZero ((L((ι)^*⟦Λ'⟧)).obj ((L((e)^*⟦Λ'⟧)).obj ((M.nearbyCycles Λ').obj
        (D((o)_!open⟦Λ'⟧).obj ((L(Mod.extendScalars (coefficientMap a U))).obj K)))))) :
    IsZero ((L(Mod.extendScalars (coefficientMap a W))).obj ((L((ι)^*⟦Λ⟧)).obj
      ((L((e)^*⟦Λ⟧)).obj ((M.nearbyCycles Λ).obj (D((o)_!open⟦Λ⟧).obj K))))) :=
  h.of_iso (upperStarUpperStarNearbyCyclesLowerShriekExtendScalarsIso a M o e ι K
    (nearbyCyclesExtendScalarsIso a M φ _ hφ))

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
