/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Coherence of the comparison pullback with direct images

The base change morphism `ν_V^* f_* ⟶ f_* ν_U^*`
(`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`) is compatible with the
identity and composition isomorphisms of the direct images on the étale and pro-étale sites:

- `AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange_app_id`;
- `AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange_app_comp`.

Both follow, through the adjunction `ν^* ⊣ ν_*`, from the corresponding compatibilities of the
isomorphisms `f_* ν_* ≅ ν_* f_*` (`AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso`),
which are checked on sections.
-/

@[expose] public section
universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

-- the first `simp` unfolds the sections of the sheaves
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The isomorphism `(𝟙 X)_* ν_* ≅ ν_* (𝟙 X)_*` is induced by the identity isomorphisms of the
direct images. -/
lemma lowerStarCompComparisonLowerStarIso_inv_app_id (X : Scheme.{u})
    (G : Sheaf (ProEt.topology X) A) :
    (lowerStarCompComparisonLowerStarIso (𝟙 X) A).inv.app G =
      (Etale.lowerStarId A X).hom.app ((comparisonLowerStar A X).obj G) ≫
        (comparisonLowerStar A X).map ((ProEtale.lowerStarId A X).inv.app G) := by
  ext V : 3
  simp [lowerStarCompComparisonLowerStarIso, Etale.lowerStarId, ProEtale.lowerStarId,
    GrothendieckTopology.lowerStarId, comparisonLowerStar]
  simp only [← Functor.map_comp, ← op_comp]
  erw [Category.id_comp]
  refine congrArg (fun x => G.obj.map (Quiver.Hom.op x)) ?_
  apply MorphismProperty.Over.Hom.ext
  simp [toProEtCompOverPullbackIso, toProEt]
  symm
  change pullback.fst (unop V).hom (𝟙 X) ≫
    ((MorphismProperty.Over.pullbackId @Etale ⊤ X).inv.app (unop V)).left = 𝟙 _
  apply pullback.hom_ext <;> simp [pullback.condition]

-- the first `simp` unfolds the sections of the sheaves
set_option linter.flexible false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The isomorphisms `f_* ν_* ≅ ν_* f_*` are compatible with the composition isomorphisms of the
direct images. -/
lemma lowerStarCompComparisonLowerStarIso_inv_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (G : Sheaf (ProEt.topology T) A) :
    (Etale.lowerStarComp A h₁ h₂).inv.app ((comparisonLowerStar A T).obj G) ≫
        (Etale.lowerStar A h₂).map ((lowerStarCompComparisonLowerStarIso h₁ A).inv.app G) ≫
        (lowerStarCompComparisonLowerStarIso h₂ A).inv.app ((ProEtale.lowerStar A h₁).obj G) =
      (lowerStarCompComparisonLowerStarIso (h₁ ≫ h₂) A).inv.app G ≫
        (comparisonLowerStar A R).map ((ProEtale.lowerStarComp A h₁ h₂).inv.app G) := by
  ext V : 3
  simp [lowerStarCompComparisonLowerStarIso, Etale.lowerStarComp, ProEtale.lowerStarComp,
    comparisonLowerStar, Etale.lowerStar, ProEtale.lowerStar]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  simp [toProEtCompOverPullbackIso, toProEt]
  dsimp [MorphismProperty.Over.changeProp]
  change ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h₁ h₂).inv.app
    (unop V)).left = _
  rw [MorphismProperty.Over.pullbackComp_inv_app_left]
  rw [pullback.map_id, Category.comp_id]

/-- The base change morphism `ν^* f_* ⟶ f_* ν^*` is the mate of `f_* ν_* ≅ ν_* f_*`. -/
@[reassoc]
lemma unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app {U V : Scheme.{u}} (f : U ⟶ V)
    (F : Sheaf U.smallEtaleTopology A) :
    (comparisonAdjunction A V).unit.app ((Etale.lowerStar A f).obj F) ≫
        (comparisonLowerStar A V).map ((lowerStarComparisonUpperStarBaseChange f A).app F) =
      (Etale.lowerStar A f).map ((comparisonAdjunction A U).unit.app F) ≫
        (lowerStarCompComparisonLowerStarIso f A).inv.app ((comparisonUpperStar A U).obj F) := by
  simp [lowerStarComparisonUpperStarBaseChange]

/-- The base change morphism `ν^* (𝟙 X)_* ⟶ (𝟙 X)_* ν^*` is induced by the identity
isomorphisms of the direct images. -/
lemma lowerStarComparisonUpperStarBaseChange_app_id (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology A) :
    (lowerStarComparisonUpperStarBaseChange (𝟙 X) A).app F =
      (comparisonUpperStar A X).map ((Etale.lowerStarId A X).hom.app F) ≫
        (ProEtale.lowerStarId A X).inv.app ((comparisonUpperStar A X).obj F) := by
  apply ((comparisonAdjunction A X).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app,
    lowerStarCompComparisonLowerStarIso_inv_app_id]
  have hn := (Etale.lowerStarId A X).hom.naturality ((comparisonAdjunction A X).unit.app F)
  simp only [Functor.id_map] at hn
  rw [reassoc_of% hn]
  have hu := (comparisonAdjunction A X).unit.naturality ((Etale.lowerStarId A X).hom.app F)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [reassoc_of% hu]

/-- The base change morphisms `ν^* f_* ⟶ f_* ν^*` are compatible with the composition
isomorphisms of the direct images. -/
lemma lowerStarComparisonUpperStarBaseChange_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (F : Sheaf T.smallEtaleTopology A) :
    (comparisonUpperStar A R).map ((Etale.lowerStarComp A h₁ h₂).inv.app F) ≫
        (lowerStarComparisonUpperStarBaseChange h₂ A).app ((Etale.lowerStar A h₁).obj F) ≫
        (ProEtale.lowerStar A h₂).map ((lowerStarComparisonUpperStarBaseChange h₁ A).app F) =
      (lowerStarComparisonUpperStarBaseChange (h₁ ≫ h₂) A).app F ≫
        (ProEtale.lowerStarComp A h₁ h₂).inv.app ((comparisonUpperStar A T).obj F) := by
  apply ((comparisonAdjunction A R).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := (comparisonAdjunction A R).unit.naturality ((Etale.lowerStarComp A h₁ h₂).inv.app F)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← reassoc_of% hu]
  erw [unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app_assoc,
    unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app_assoc]
  have hi := (lowerStarCompComparisonLowerStarIso h₂ A).inv.naturality
    ((lowerStarComparisonUpperStarBaseChange h₁ A).app F)
  simp only [Functor.comp_map] at hi
  erw [← hi]
  rw [← Functor.map_comp_assoc, unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app,
    ← lowerStarCompComparisonLowerStarIso_inv_app_comp]
  have hc := (Etale.lowerStarComp A h₁ h₂).inv.naturality ((comparisonAdjunction A T).unit.app F)
  simp only [Functor.comp_map] at hc
  rw [reassoc_of% hc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale
