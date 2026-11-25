/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Stalks commute with direct sums of sheaves of modules

Source: Stacks Project, Sheaves on Spaces, Section 6.29, Tag 009E, items (3) and (5)
(blueprint: lem-pc-stalk-direct-sums).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DirectSum
open TopCat.Presheaf

namespace SheafOfModules

open Classical in
/-- Stacks Project, Tag 009E, item (5) (blueprint: lem-pc-stalk-direct-sums).
The stalk of the sheaf coproduct is linearly isomorphic to the direct sum of the stalks.
The equation on germs specifies the canonical comparison in the stated direction.

Proof: compose the forgetful functor to presheaf modules with the linear module stalk
functor of `def-weil-pbc-module-stalk`. After forgetting its target module structure,
this is definitionally the forgetful functor to abelian sheaves followed by the abelian
sheaf stalk functor. The former preserves coproducts by
`situation-conventions`; the latter preserves colimits by
Mathlib's stalk-skyscraper adjunction. Since forgetting a module structure reflects
colimits, the module stalk functor preserves coproducts. Compose its canonical
coproduct comparison isomorphism with `ModuleCat.coprodIsoDirectSum`, and take the
associated linear equivalence. The coproduct comparison carries each stalk injection
to the corresponding categorical injection, and `coprodIsoDirectSum` carries this to
`DirectSum.lof`. Applying this morphism identity to the germ of a section, and using
`stalkFunctor_map_germ_apply`, gives the required formula. This argument works for
arbitrary index sets, including the empty set.
-/
theorem exists_stalk_directSum_linearEquiv
    {X : TopCat.{u}} (R : X.Sheaf RingCat.{u}) (I : Type u)
    (F : I → SheafOfModules.{u} R) (x : X) :
    ∃ e : (stalk (C := AddCommGrpCat.{u}) (X := X) (∐ F).val.presheaf x)
        ≃ₗ[stalk (C := RingCat.{u}) (X := X) R.obj x]
        (⨁ i : I, (stalk (C := AddCommGrpCat.{u}) (X := X) (F i).val.presheaf x)),
      ∀ (i : I) (U : Opens X) (hx : x ∈ U) (s : (F i).val.obj (op U)),
        e (germ (∐ F).val.presheaf U x hx ((Sigma.ι F i).val.app (op U) s)) =
          DirectSum.lof (stalk (C := RingCat.{u}) (X := X) R.obj x) I
            (fun j : I => ↑(stalk (C := AddCommGrpCat.{u}) (X := X) (F j).val.presheaf x)) i
            (germ (F i).val.presheaf U x hx s) := by
  classical
  let T := SheafOfModules.forget R ⋙ PresheafOfModules.moduleStalkFunctor R.obj x
  -- The underlying abelian stalk functor preserves coproducts.
  have : PreservesColimitsOfShape (Discrete I) (SheafOfModules.toSheaf R) :=
    ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 (Discrete I)).2.1
  have : PreservesColimitsOfShape (Discrete I)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    (stalkSkyscraperSheafAdjunction x).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I)
      (T ⋙ forget₂ (ModuleCat.{u} (stalk (C := RingCat.{u}) (X := X) R.obj x)) AddCommGrpCat.{u}) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.toSheaf R ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))
  -- Forgetting the module structure reflects colimits.
  have : PreservesColimitsOfShape (Discrete I) T :=
    preservesColimitsOfShape_of_reflects_of_preserves T
      (forget₂ (ModuleCat.{u} (stalk (C := RingCat.{u}) (X := X) R.obj x)) AddCommGrpCat.{u})
  let e := PreservesCoproduct.iso T F ≪≫
    ModuleCat.coprodIsoDirectSum (fun i => T.obj (F i))
  refine ⟨e.toLinearEquiv, ?_⟩
  intro i U hx s
  -- Both categorical comparisons respect their coproduct injections.
  have h : T.map (Sigma.ι F i) ≫ e.hom =
      ModuleCat.ofHom (DirectSum.lof (stalk (C := RingCat.{u}) (X := X) R.obj x) I
        (fun j => ↑(T.obj (F j))) i) := by
    dsimp only [e, Iso.trans_hom]
    rw [← Category.assoc]
    have hh : (PreservesCoproduct.iso T F).hom = inv (sigmaComparison T F) := by
      apply (cancel_mono (sigmaComparison T F)).1
      simp only [← PreservesCoproduct.inv_hom, Iso.hom_inv_id, IsIso.inv_hom_id]
    rw [hh, map_ι_comp_inv_sigmaComparison, ModuleCat.ι_coprodIsoDirectSum_hom]
  have hg : (T.map (Sigma.ι F i)).hom (germ (F i).val.presheaf U x hx s) =
      germ (∐ F).val.presheaf U x hx ((Sigma.ι F i).val.app (op U) s) := by
    change PresheafOfModules.stalkAddMap (Sigma.ι F i).val _ = _
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
  rw [← hg]
  exact congrArg (fun f => f.hom (germ (F i).val.presheaf U x hx s)) h

end SheafOfModules
