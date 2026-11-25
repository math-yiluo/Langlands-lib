/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionRestrict
public import WeilConjectures.PoincareDuality.ProjectionFormula

/-!

# The exceptional projection morphism of a compactification through adjunctions

For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of a morphism `f` over a scheme `S`, the
exceptional projection morphism `PF^c_{K,B} : Rf_!^c K ⊗ᴸ B ⟶ Rf_!^c (K ⊗ᴸ Lf^* B)`
(`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification`) is the projection
morphism of `Lp^* ⊣ Rp_*` at `Di_! K`, followed by `Rp_*` of the inverse of the projection
comparison of `Di_! ⊣ Li^*` and of the identification `Lf^* ≅ Lp^* ⋙ Li^*`, written with the
morphisms `c.overI` and `c.overG` over `S`
(`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_eq_adjunction`).
This file also identifies the composition isomorphisms of the pullbacks of bounded constructible
complexes with those of the ambient derived categories
(`ProEtale.CondensedRing.ι_map_eqToIso_trans_boundedConstructibleUpperStarComp_inv_app`).

## Implementation notes

All statements are made for a general coefficient ring `Λ`: comparing the definition of the
exceptional projection morphism with re-elaborated terms is cheap for a general `Λ` and
prohibitively expensive for the coefficient ring `ℚ̲̄_ℓ` (whose instances are synthesized along
different paths in different files). They are applied to `ℚ̲̄_ℓ` by unification.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The projection comparison of `Dj_! ⊣ Lj^*` is an isomorphism
(`ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`). It only restates that instance
for the unfolded projection comparison, so that instance search finds it in the unfolded
exceptional projection morphism. -/
instance isIso_derivedOpenImmersionProjectionComparison {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).projectionComparison
      M N) :=
  isIso_openImmersionProjectionComparison Λ j M N

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y} (c : Compactification f.left)

/-- The identification `Lf^* ≅ Lp^* ⋙ Li^*` of a compactification `c` of a morphism `f` over
`S`, through the morphisms `c.overI` and `c.overG` over `S`. It is
`leftDerivedUpperStarCompactificationIso Λ c` with its type restated through `c.overI.left` and
`c.overG.left` instead of `c.i` and `c.g`, and exists only as this typing bridge. -/
noncomputable def leftDerivedUpperStarOverCompactificationIso :
    L((f.left)^*⟦Λ⟧) ≅ L((c.overG.left)^*⟦Λ⟧) ⋙ L((c.overI.left)^*⟦Λ⟧) :=
  leftDerivedUpperStarCompactificationIso Λ c

/-- The exceptional projection morphism of a compactification of a morphism over `S`, written
with the adjunctions `Lp^* ⊣ Rp_*` and `Di_! ⊣ Li^*`. -/
lemma exceptionalProjectionMorphismOfCompactification_eq_adjunction
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))) :
    exceptionalProjectionMorphismOfCompactification Λ c K B =
      (derivedUpperStarLowerStarAdjunction Λ c.overG.left).projectionMorphism
          ((D((c.overI.left)_!open⟦Λ⟧)).obj K) B ≫
        (R((c.overG.left)_*⟦Λ⟧)).map
          (inv ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
              c.overI.left).projectionComparison K ((L((c.overG.left)^*⟦Λ⟧)).obj B)) ≫
            (D((c.overI.left)_!open⟦Λ⟧)).map
              (K ◁ (leftDerivedUpperStarOverCompactificationIso Λ c).inv.app B)) := by
  unfold exceptionalProjectionMorphismOfCompactification properProjectionMorphism
    leftDerivedUpperStarOverCompactificationIso
    openImmersionProjectionComparison
  rfl

end General

section GenericIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- On the ambient derived category, the inverse of the composition isomorphism of the derived
pullbacks on bounded constructible complexes is that of `leftDerivedUpperStarComp`. -/
lemma ι_map_boundedConstructibleUpperStarComp_inv_app {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (i : X ⟶ Z) (g : Z ⟶ Y)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructible _).ι.map ((boundedConstructibleUpperStarComp Λ ℓ i g).inv.app B) =
      (leftDerivedUpperStarComp Λ i.left g.left).inv.app B.obj := by
  simp only [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso, Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.whiskeringRight_obj_obj,
    Over.comp_left, ObjectProperty.lift_obj_obj, Category.id_comp, Category.comp_id,
    Category.assoc, ObjectProperty.ι_map, ObjectProperty.homMk_hom]
  erw [Category.id_comp]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- The composition isomorphism `Lf^* ≅ Lg^* ⋙ Li^*` along `f = i ≫ g` on bounded constructible
complexes is that of the ambient derived categories. -/
lemma ι_map_eqToIso_trans_boundedConstructibleUpperStarComp_inv_app {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (i : X ⟶ Z) (g : Z ⟶ Y)
    (w : i ≫ g = f) (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructible _).ι.map
      ((eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w.symm) ≪≫
        boundedConstructibleUpperStarComp Λ ℓ i g).inv.app B) =
      (eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h.left)^*⟦Λ⟧)) w.symm) ≪≫
        leftDerivedUpperStarComp Λ i.left g.left).inv.app B.obj := by
  subst w
  simp only [eqToIso_refl, Iso.refl_trans]
  exact ι_map_boundedConstructibleUpperStarComp_inv_app Λ ℓ i g B

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- `leftDerivedUpperStarOverCompactificationIso` as an `eqToIso` followed by the composition
isomorphism. -/
lemma leftDerivedUpperStarOverCompactificationIso_eq (c : Compactification f.left) :
    leftDerivedUpperStarOverCompactificationIso Λ c =
      eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h.left)^*⟦Λ⟧)) c.overI_overG.symm) ≪≫
        leftDerivedUpperStarComp Λ c.overI.left c.overG.left :=
  rfl


end GenericIso

end AlgebraicGeometry.ProEtale.CondensedRing
