/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!
# The pullback of module objects is braided

The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects over a commutative condensed ring
`Λ` commutes with the braidings of the relative tensor products
(`ProEtale.CondensedRing.δ_upperStar_braiding`): on underlying sheaves, after the projections
to the relative tensor products, this is the braidedness of the pullback of sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The pullback of module objects is braided**: the tensor comparison
`f^* (A ⊗ B) ⟶ f^* A ⊗ f^* B` commutes with the braidings. -/
@[reassoc]
lemma δ_upperStar_braiding
    (A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    δ (f)^*⟦Λ⟧ A B ≫ (β_ ((f)^*⟦Λ⟧.obj A) ((f)^*⟦Λ⟧.obj B)).hom =
      (f)^*⟦Λ⟧.map (β_ A B).hom ≫ δ (f)^*⟦Λ⟧ B A := by
  ext1
  rw [← cancel_epi ((f)^*[Ab.{u + 1}].map (Mod.tensorObjπ A B) ≫ upperStarUnitHom Λ f (A ⊗ B))]
  rw [Mod.comp_hom', Mod.comp_hom', Category.assoc, Category.assoc,
    map_tensorObjπ_upperStarUnitHom_δ_hom_assoc]
  erw [Mod.tensorObjπ_braidingHomX]
  rw [upperStarUnitHom_map_hom_assoc]
  have hb : Mod.tensorObjπ A B ≫ (β_ A B).hom.hom = (β_ A.X B.X).hom ≫ Mod.tensorObjπ B A :=
    Mod.tensorObjπ_braidingHomX A B
  rw [← Functor.map_comp_assoc, hb, Functor.map_comp_assoc, map_tensorObjπ_upperStarUnitHom_δ_hom,
    BraidedCategory.braiding_naturality_assoc, Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
