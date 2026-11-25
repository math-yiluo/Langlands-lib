/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Direct images of flat sheaves along finite morphisms are flat

For a finite morphism `π : X ⟶ Y` and a flat sheaf `F` of `Λ`-modules on `X_ét`, the direct
image `π_* F` is flat (`AlgebraicGeometry.Etale.flat_lowerStar_obj_of_isFinite`): its stalk at a
geometric point of `Y` is the finite product of the stalks of `F` at the geometric points over it
(`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), and flatness is checked on stalks
(`CategoryTheory.GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj`).
-/

@[expose] public section

universe v w u

open CategoryTheory Limits MonoidalCategory

/-- A finite product of flat modules is flat, phrased with the categorical product in
`ModuleCat`. -/
lemma ModuleCat.flat_piObj {R : Type (max v w)} [CommRing R] {ι : Type v} [Finite ι]
    (M : ι → ModuleCat.{max v w} R) (hM : ∀ i, ObjectProperty.flat (M i)) :
    ObjectProperty.flat (∏ᶜ M) := by
  have := Fintype.ofFinite ι
  have (i : ι) : Module.Flat R (M i) := (ModuleCat.flat_iff_flat _).1 (hM i)
  rw [ModuleCat.flat_iff_flat]
  have : Module.Flat R (∀ i, M i) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm
  exact Module.Flat.of_linearEquiv (ModuleCat.piIsoPi M).toLinearEquiv

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

-- Use the instance paths of the constructions for a general coefficient category, see
-- `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Degreewise`.
attribute [local instance 10000] Abelian.toPreadditive SymmetricCategory.toBraidedCategory

/-- The direct image of a flat sheaf along a finite morphism is flat. This is used in the proof
of blueprint `lemma-kunneth-field-coefficients--1` for the sheaves `π_* Λ`. -/
theorem flat_lowerStar_obj_of_isFinite {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((π)_*[ModuleCat.{u + 1} Λ].obj F) := by
  -- flatness is checked on the stalks at geometric points with algebraically closed residue
  -- field, where the stalk of `π_* F` is a finite product of stalks of `F`
  refine GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj
    (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale Y _) _ ?_
  rintro ⟨-, ⟨s⟩⟩
  refine ObjectProperty.prop_of_iso _
    (((pointSmallEtale (Y.algClosurePoint s)).uliftSheafFiberIso _).app _).symm ?_
  refine ObjectProperty.prop_of_iso _
    ((lowerStarSheafFiberIsoPi _ π (Y.algClosurePoint s)).app F).symm ?_
  refine ObjectProperty.prop_of_iso _ (piObjIso _ _).symm
    (ModuleCat.flat_piObj.{u, u + 1} _ fun t ↦ ?_)
  exact ObjectProperty.prop_of_iso _ (((pointSmallEtale t.1).uliftSheafFiberIso.{u + 1} _).app F)
    ((pointSmallEtale t.1).ulift.{u + 1}.flat_sheafFiber_obj hF)

/-- The direct image of the unit along a finite morphism is flat. -/
theorem flat_lowerStar_obj_tensorUnit_of_isFinite {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] :
    ObjectProperty.flat ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _)) :=
  flat_lowerStar_obj_of_isFinite Λ π _ (ObjectProperty.flat_of_tensorIso (λ_ _))

end Etale

end AlgebraicGeometry
