/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Composition of pullback maps on étale cohomology

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, pulling a cohomology class back along
`g` and then along `f` is pulling it back along `f ≫ g`, up to the canonical isomorphisms
`(f ≫ g)^* F ≅ f^* g^* F` of coefficient sheaves and an automorphism of the constant sheaf `ℤ`
on `X`. In particular the composite of the two pullback maps is bijective if and only if the
pullback map along `f ≫ g` is.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_of_comp_eq`: the composition formula.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_comp_iff`: bijectivity of the composite.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_iff_of_iso`: bijectivity of the pullback
  map only depends on the coefficient sheaf up to isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

variable {X Y Z : Scheme.{u}}

/-- The automorphism of the constant sheaf `ℤ` on `X` relating the pullback maps along `g`,
then `f`, and along `k = f ≫ g`, see
`AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_of_comp_eq`. -/
noncomputable def cohomologyMapCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app _ ≪≫
    ((f)^*[AddCommGrpCat.{u + 1}]).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app _) ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm).symm.app _ ≪≫
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).app _

/-- **Composition of pullback maps on étale cohomology.** Pulling a class back along
`g : Y ⟶ Z` and then along `f : X ⟶ Y` is pulling it back along `k = f ≫ g`, up to the
composition isomorphism `k^* F ≅ f^* g^* F` and an automorphism of the constant sheaf `ℤ`.
(blueprint: `proposition-cohomology-p-1-over-henselian--1`, composition) -/
theorem cohomologyMap_cohomologyMap_of_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : f ≫ g = k) (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ}
    (x : Sheaf.H F n) :
    cohomologyMap f _ n (cohomologyMap g F n x) =
      (Ext.mk₀ (cohomologyMapCompIso f g k hk).hom).comp
        ((cohomologyMap k F n x).comp
          (Ext.mk₀ ((upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm).hom.app F)) (add_zero n))
        (zero_add n) := by
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mapExactFunctor_of_iso _ _ _
      (upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm)]
  simp only [cohomologyMapCompIso, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_app]
  exact congrArg (fun t ↦ (Ext.mk₀ t).comp _ (zero_add n)) (by simp)

/-- Pre- and postcomposition with the classes of isomorphisms is a bijection of `Ext`-groups. -/
lemma bijective_mk₀_comp_comp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A A' B B' : C} (e : A' ⟶ A) [IsIso e] (e' : B ⟶ B') [IsIso e'] (n : ℕ) :
    Function.Bijective (fun z : Ext A B n ↦
      (Ext.mk₀ e).comp (z.comp (Ext.mk₀ e') (add_zero n)) (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z ↦ (Ext.mk₀ (inv e)).comp (z.comp (Ext.mk₀ (inv e')) (add_zero n)) (zero_add n),
      fun z ↦ ?_, fun z ↦ ?_⟩ <;>
  simp [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- The composite of the pullback maps along `g : Y ⟶ Z` and `f : X ⟶ Y` is bijective if and
only if the pullback map along `f ≫ g` is. -/
theorem bijective_cohomologyMap_comp_iff (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (cohomologyMap f _ n ∘ cohomologyMap g F n) ↔
      Function.Bijective (cohomologyMap k F n) := by
  have : (cohomologyMap f _ n ∘ cohomologyMap g F n) =
      (fun z ↦ (Ext.mk₀ (cohomologyMapCompIso f g k hk).hom).comp
        (z.comp (Ext.mk₀ ((upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm).hom.app F))
          (add_zero n)) (zero_add n)) ∘ cohomologyMap k F n :=
    funext fun x ↦ cohomologyMap_cohomologyMap_of_comp_eq f g k hk F x
  rw [this]
  exact (Function.Bijective.of_comp_iff' (bijective_mk₀_comp_comp_mk₀ _ _ n) _)

/-- The map on sheaf cohomology induced by an isomorphism of sheaves is bijective. -/
lemma _root_.CategoryTheory.Sheaf.H.map_bijective_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] {A B : Sheaf J AddCommGrpCat.{u + 1}}
    (e : A ≅ B) (n : ℕ) : Function.Bijective (Sheaf.H.map e.hom n) :=
  Function.bijective_iff_has_inverse.2 ⟨Sheaf.H.map e.inv n,
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply],
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]⟩

/-- The pullback map on étale cohomology along `f` is bijective for a sheaf `F` if and only if
it is bijective for a sheaf `G` isomorphic to `F`. -/
theorem bijective_cohomologyMap_iff_of_iso (f : X ⟶ Y)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (n : ℕ) :
    Function.Bijective (cohomologyMap f F n) ↔ Function.Bijective (cohomologyMap f G n) := by
  have h : cohomologyMap f G n ∘ Sheaf.H.map e.hom n =
      Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).mapIso e).hom n ∘ cohomologyMap f F n :=
    funext fun x ↦ cohomologyMap_map f n e.hom x
  rw [← (Sheaf.H.map_bijective_of_iso e n).of_comp_iff, h,
    (Sheaf.H.map_bijective_of_iso _ n).of_comp_iff']

end AlgebraicGeometry.Etale
