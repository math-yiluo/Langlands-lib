/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarCoproduct
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.WeilSheaf.UpperShriekGeometric

/-!
# Prerequisites for the condensed model of the Weil exceptional datum

Two inputs of the framework
`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_obj_iso_counit_comm`
in the condensed model, transported from the `ℓ`-adic model along
`AlgebraicGeometry.ProEtale.adicSheafDerivedEquivCondensedMod`:
- the derived direct image of condensed module objects preserves bounded below coproducts
  (`AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedFunctor_condensedLowerStar`);
- the Frobenius `(Fr_X⁻¹)_*` of the condensed model preserves bounded constructible complexes
  (`ProEtale.boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

set_option linter.style.longLine false in
/-- **The derived direct image of condensed module objects commutes with bounded below
coproducts**, transported from `preservesColimit_discrete_rightDerivedFunctor_adicLowerStar`. -/
theorem preservesColimit_discrete_rightDerivedFunctor_condensedLowerStar {Y X : Scheme.{u}}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (K : ℤ → _root_.DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)))
    (a : ℤ) (hK : ∀ n, (K n).IsGE a) :
    PreservesColimit (Discrete.functor K)
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor := by
  let EY := adicSheafDerivedEquivCondensedMod l Y
  let EX := adicSheafDerivedEquivCondensedMod l X
  have φ : (adicLowerStar l f).rightDerivedFunctor ⋙ EX.functor ≅
      EY.functor ⋙ (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor :=
    Functor.rightDerivedFunctorCompMapDerivedCategoryIsoOfEquivalence
      (adicSheafEquivCondensedMod l Y) (adicSheafEquivCondensedMod l X)
      (adicLowerStarCompCondensedModIso l f)
  have hiso : EY.inverse ⋙ (adicLowerStar l f).rightDerivedFunctor ⋙ EX.functor ≅
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor :=
    Functor.isoWhiskerLeft EY.inverse φ ≪≫ EY.invFunIdAssoc _
  have hK' : ∀ n, ((adicSheafEquivCondensedMod l Y).inverse.mapDerivedCategory.obj (K n)).IsGE a :=
    fun n ↦ by
      have := hK n
      exact Functor.isGE_mapDerivedCategory_obj _ (K n) a
  have h0 : PreservesColimit (Discrete.functor
      ((adicSheafEquivCondensedMod l Y).inverse.mapDerivedCategory.obj ∘ K))
      (adicLowerStar l f).rightDerivedFunctor :=
    preservesColimit_discrete_rightDerivedFunctor_adicLowerStar (l := l) f _ a hK'
  have h1 : PreservesColimit (Discrete.functor K ⋙ EY.inverse)
      (adicLowerStar l f).rightDerivedFunctor :=
    preservesColimit_of_iso_diagram _
      (Discrete.compNatIsoDiscrete K
        (adicSheafEquivCondensedMod l Y).inverse.mapDerivedCategory).symm
  exact preservesColimit_of_natIso (Discrete.functor K) hiso

end AlgebraicGeometry.ProEtale
