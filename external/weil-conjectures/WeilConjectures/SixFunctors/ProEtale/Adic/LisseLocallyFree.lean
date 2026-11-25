/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-!
# Lisse `ℓ`-adic sheaves are locally free module objects

Through the equivalence `AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), the constant sheaf `ℚ̄_ℓ,X` goes to
the regular module (`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso`), and a lisse
`ℓ`-adic sheaf goes to a locally free module object
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isLocallyFree`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The equivalence `AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}` sends the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` to
the regular module over `ℚ̲̄_ℓ,X`. -/
noncomputable def adicSheafEquivCondensedModUnitIso (X : Scheme.{u}) :
    (adicSheafEquivCondensedMod l X).functor.obj (AdicSheaf.unit l X) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X) :=
  (Mod.comap (condensedRingObjIsoForgetAb l X).hom).mapIso
      ((weilCoefficientsForgetAb l X).mapModRegularIso (adicConstantSheaf l X)) ≪≫
    (Mod.regularIsoComapRegular (condensedRingObjIsoForgetAb l X).hom).symm

variable {l}

/-- If the pullback `f^* H` of an `ℓ`-adic sheaf is a finite direct sum of copies of `ℚ̄_ℓ`, then
the pullback along `f` of the module object of `H` is free of finite rank. -/
theorem isFree_upperStar_adicSheafEquivCondensedMod_obj {V X : Scheme.{u}} (f : V ⟶ X)
    {H : AdicSheaf l X} {n : ℕ} (e : (f)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) :
    Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) V)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} l) f).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)) :=
  (Mod.IsFree.map (adicSheafEquivCondensedMod l V).functor
      (adicSheafEquivCondensedModUnitIso l V) ⟨n, ⟨e⟩⟩).of_iso
    ((adicUpperStarCompCondensedModIso l f).app H)

/-- **A lisse `ℓ`-adic sheaf is a locally free module object** over `ℚ̲̄_ℓ,X`: its pullbacks to
the members of a trivialising pro-étale cover are finite direct sums of copies of `ℚ̄_ℓ`, and the
equivalence `AdicSheaf ℓ ≌ Mod_{ℚ̲̄_ℓ}` commutes with pullbacks and sends `ℚ̄_ℓ` to the regular
module. -/
theorem IsAdicLisseSheaf.isLocallyFree {X : Scheme.{u}} {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) := by
  obtain ⟨R, hR, h⟩ := hH
  obtain ⟨ι, W, g, rfl⟩ := R.exists_eq_ofArrows
  let U : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
    { I₀ := ι, X := W, f := g, mem₀ := hR }
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  refine (isLocallyFree_iff _).2 ⟨U.restrictIndexOfSmall.{u}, fun j ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := h (g (Precoverage.ZeroHypercover.Small.restrictFun U j)) (.mk _)
  exact isFree_upperStar_adicSheafEquivCondensedMod_obj _ e

end AlgebraicGeometry.ProEtale
