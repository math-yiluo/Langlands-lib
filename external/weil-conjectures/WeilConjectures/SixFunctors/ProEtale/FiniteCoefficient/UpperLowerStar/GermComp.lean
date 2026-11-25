/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Germs along composites and along weakly étale morphisms

- The germ along a composite `h ≫ g` is the restriction along `h` of the germ along `g`
  (`AlgebraicGeometry.ProEtale.germ_comp`), through `(h ≫ g)^* ≅ h^* g^*`.
- For a weakly étale `g : Z ⟶ Y`, the pullback `g^*` is restriction, and the germ of a section
  over `V` along a lift `t : Z ⟶ V ×_Y Z` is its restriction along the induced morphism `Z ⟶ V`
  (`AlgebraicGeometry.ProEtale.germ_upperStarIsoLocalizationRestriction`). In particular, for an
  object `W` of the small pro-étale site of `Y`, the germ of a section over `W` along the diagonal
  of `W ⟶ Y` determines the section (`AlgebraicGeometry.ProEtale.eq_zero_of_germ_diag_eq_zero`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The unit of `(h ≫ g)^* ⊣ (h ≫ g)_*` followed by `(h ≫ g)^* ≅ h^* g^*` is the composite of the
units. -/
lemma upperStarLowerStarAdjunction_unit_app_comp_map_upperStarComp {T Z Y : Scheme.{u}}
    (h : T ⟶ Z) (g : Z ⟶ Y) (P : Sheaf (ProEt.topology Y) A) :
    (upperStarLowerStarAdjunction A (h ≫ g)).unit.app P ≫
        (h ≫ g)_*[A].map ((upperStarComp A h g).hom.app P) =
      (upperStarLowerStarAdjunction A g).unit.app P ≫
        (g)_*[A].map ((upperStarLowerStarAdjunction A h).unit.app ((g)^*[A].obj P)) ≫
        (lowerStarComp A h g).hom.app ((h)^*[A].obj ((g)^*[A].obj P)) := by
  have hu := unit_conjugateEquiv ((upperStarLowerStarAdjunction A g).comp
    (upperStarLowerStarAdjunction A h)) (upperStarLowerStarAdjunction A (h ≫ g))
    (upperStarComp A h g).hom P
  rw [conjugateEquiv_upperStarComp_hom, Adjunction.comp_unit_app] at hu
  rw [← hu, Category.assoc]
  rfl

/-- **Germs along composites.** The germ along `h ≫ g` of a section, followed by
`(h ≫ g)^* ≅ h^* g^*`, is the restriction along `h` of its germ along `g`. -/
lemma germ_comp {T Z Y : Scheme.{u}} (h : T ⟶ Z) (g : Z ⟶ Y) (P : Sheaf (ProEt.topology Y) A)
    {V : Y.ProEt}
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)
    (t' : ProEt.mk (𝟙 T) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (h ≫ g)).obj V)
    (ht : t' ≫ (MorphismProperty.Over.pullbackComp h g).hom.app V =
      (overPullbackObjMkIdIso h).inv ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map t) :
    germ A (h ≫ g) P t' ≫ (Sheaf.Γ _ A).map ((upperStarComp A h g).hom.app P) =
      germ A g P t ≫ (globalSectionsToUpperStar A h).app ((g)^*[A].obj P) := by
  have hE := congrArg (fun f ↦ f.hom.app (op V))
    (upperStarLowerStarAdjunction_unit_app_comp_map_upperStarComp A h g P)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hE
  have n₁ := ((upperStarComp A h g).hom.app P).hom.naturality t'.op
  have n₂ := (Sheaf.ΓNatIsoSheafSections _ A (ProEt.isTerminalMkId T)).inv.naturality
    ((upperStarComp A h g).hom.app P)
  have n₃ := ((upperStarLowerStarAdjunction A h).unit.app ((g)^*[A].obj P)).hom.naturality t.op
  have n₄ := (Sheaf.ΓNatIsoSheafSections _ A (ProEt.isTerminalMkId Z)).inv.naturality
    ((upperStarLowerStarAdjunction A h).unit.app ((g)^*[A].obj P))
  rw [germ, germ, globalSectionsToUpperStar_app, globalSectionsLowerStarIso_hom_app']
  simp only [Category.assoc]
  erw [← n₂, reassoc_of% n₁]
  erw [reassoc_of% hE]
  erw [← reassoc_of% n₄, Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% n₃]
  congr 2
  rw [lowerStarComp_hom_app_hom_app, ← Functor.map_comp_assoc, ← op_comp, ht, op_comp,
    Functor.map_comp_assoc]
  rfl

section WeaklyEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) (hg : WeaklyEtale g)

/-- For a weakly étale `g`, the germ along `t`, transported along `g^* ≅ j_g^*` to the
restriction, is the restriction along the morphism `Z ⟶ V` induced by `t`. -/
lemma germ_comp_upperStarIsoLocalizationRestriction (P : Sheaf (ProEt.topology Y) A)
    {V : Y.ProEt}
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    germ A g P t ≫ (Sheaf.ΓNatIsoSheafSections _ A (ProEt.isTerminalMkId Z)).hom.app _ ≫
        ((upperStarIsoLocalizationRestriction A g hg).hom.app P).hom.app
          (op (ProEt.mk (𝟙 Z))) =
      P.obj.map (((MorphismProperty.Over.map ⊤ hg).map t ≫
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g hg trivial).counit.app V).op) := by
  have hu := congrArg (fun f ↦ f.hom.app (op V))
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A g)
      (localizationRestrictionLowerStarAdjunction A g hg) P)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  have n := ((upperStarIsoLocalizationRestriction A g hg).hom.app P).hom.naturality t.op
  rw [germ, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [n, ← Category.assoc]
  erw [hu]
  simp [localizationRestrictionLowerStarAdjunction, localizationRestriction]

end WeaklyEtale

section Diagonal

variable {Y : Scheme.{u}} (W : Y.ProEt)

/-- The diagonal `W ⟶ W ×_Y W`, as a lift of `W` through the base change of `W` along
`W ⟶ Y`. -/
noncomputable def diagLift :
    ProEt.mk (𝟙 W.left) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).obj W :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 W.left) (𝟙 W.left) rfl)
    (by exact pullback.lift_snd _ _ _)

/-- **A section is determined by its germ along the diagonal.** -/
lemma eq_zero_of_germ_diagLift_eq_zero {R : Type (u + 1)} [Ring R]
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (σ : ToType (P.obj.obj (op W)))
    (hσ : germ _ W.hom P (diagLift W) σ = 0) : σ = 0 := by
  have h := congrArg (fun f ↦ f.hom σ)
    (germ_comp_upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R) W.hom W.prop P
      (diagLift W))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hσ, map_zero, map_zero] at h
  let r : W ⟶ (MorphismProperty.Over.map ⊤ W.prop).obj (ProEt.mk (𝟙 W.left)) :=
    MorphismProperty.Over.homMk (𝟙 _) (by simp only [Category.id_comp]; rfl)
  have hr : r ≫ (MorphismProperty.Over.map ⊤ W.prop).map (diagLift W) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).counit.app W =
        𝟙 W := by
    refine MorphismProperty.Over.Hom.ext ?_
    change 𝟙 _ ≫ pullback.lift (𝟙 W.left) (𝟙 W.left) rfl ≫ pullback.fst _ _ = 𝟙 _
    simp
  have e : P.obj.map ((MorphismProperty.Over.map ⊤ W.prop).map (diagLift W) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).counit.app W).op ≫
        P.obj.map r.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, hr, op_id]
    exact P.obj.map_id _
  have := congrArg (fun φ ↦ φ.hom σ) e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id] at this
  refine this.symm.trans ((congrArg (P.obj.map r.op).hom h.symm).trans (map_zero _))

end Diagonal

end AlgebraicGeometry.ProEtale
