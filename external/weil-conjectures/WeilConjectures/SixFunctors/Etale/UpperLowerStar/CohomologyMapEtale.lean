/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The comparison map on étale cohomology: composition and degree zero

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, pulling a cohomology class back along `g`
and then along `f` kills it exactly when pulling it back along `f ≫ g` does, in every degree.
For an étale `f`, the comparison map `AlgebraicGeometry.Etale.cohomologyMap f F 0` in degree
`0` is the restriction of global sections of `F` to the étale `Y`-scheme `X`, the sections of
`f^* F` over `X` being identified with the sections of `F` over `X ⟶ Y` through
`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_eq_zero_iff_comp`: the vanishing of a
  class pulled back in two steps.
- `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap`:
  in degree `0` and for étale `f`, the comparison map is the restriction of sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian Opposite

namespace AlgebraicGeometry.Etale

variable {X Y Z : Scheme.{u}}

/-- A class of any degree on `Z` dies after pulling back along `g : Y ⟶ Z` and then along
`f : X ⟶ Y` exactly when it dies after pulling back along `f ≫ g`. -/
theorem cohomologyMap_cohomologyMap_eq_zero_iff_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n) :
    cohomologyMap f _ n (cohomologyMap g F n x) = 0 ↔ cohomologyMap (f ≫ g) F n x = 0 := by
  rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mapExactFunctor_of_iso _ _ _
      (upperStarComp AddCommGrpCat.{u + 1} f g), Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_eq_zero_iff, Ext.mk₀_comp_eq_zero_iff,
    Ext.comp_mk₀_eq_zero_iff]

/-- A class dies after pulling back along a composite `k ≫ g` as soon as it dies after pulling
back along `g`. -/
lemma cohomologyMap_comp_eq_zero (k : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n)
    (hx : cohomologyMap g F n x = 0) : cohomologyMap (k ≫ g) F n x = 0 := by
  rw [← cohomologyMap_cohomologyMap_eq_zero_iff_comp, hx, map_zero]

section Zero

variable (f : X ⟶ Y) (hf : AlgebraicGeometry.Etale f)

/-- The unit of `f^* ⊣ f_*` at the terminal object, followed by the identification of sections
of `f^* B` over `X` with sections of `B` over the étale `Y`-scheme `X`, is the restriction of
sections of `B` along `X ⟶ Y`. -/
lemma unit_app_comp_lowerStarCompSheafSectionsTerminalIso_hom_app_comp
    (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app B).hom.app
        (op (⊤_ Y.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f).hom.app
        ((f)^*[AddCommGrpCat.{u + 1}].obj B) ≫
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf).hom.app B).hom.app
        (op (⊤_ X.Etale)) =
    B.obj.map (terminal.from ((MorphismProperty.Over.map ⊤ hf).obj (⊤_ X.Etale))).op := by
  let ι := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf
  let P : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj (⊤_ Y.Etale) ≅
      ⊤_ X.Etale := PreservesTerminal.iso _
  have h₁ : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app B).hom.app
        (op (⊤_ Y.Etale)) ≫ (ι.hom.app B).hom.app
          (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj
            (⊤_ Y.Etale))) =
      ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f hf).unit.app
        B).hom.app (op (⊤_ Y.Etale)) :=
    congrArg (fun φ ↦ φ.hom.app (op (⊤_ Y.Etale)))
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit_leftAdjointUniq_hom_app
        (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f hf) B)
  obtain ⟨m, hm⟩ : ∃ m, ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f
      hf).unit.app B).hom.app (op (⊤_ Y.Etale)) = B.obj.map (Quiver.Hom.op m) := ⟨_, rfl⟩
  have h₂ := (ι.hom.app B).hom.naturality P.inv.op
  have h₃ : (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f).hom.app
      ((f)^*[AddCommGrpCat.{u + 1}].obj B) =
        ((f)^*[AddCommGrpCat.{u + 1}].obj B).obj.map P.inv.op := rfl
  rw [h₃, h₂, ← Category.assoc, h₁, hm]
  change B.obj.map _ ≫ B.obj.map _ = _
  rw [← Functor.map_comp]
  congr 1
  exact Quiver.Hom.unop_inj (terminal.hom_ext _ _)

/-- **The comparison map in degree `0` along an étale morphism.** For an étale `f : X ⟶ Y`
and an abelian sheaf `F` on `Y_ét`, the comparison map
`AlgebraicGeometry.Etale.cohomologyMap f F 0 : H⁰(Y, F) ⟶ H⁰(X, f^* F)` is the restriction of
global sections of `F` to the étale `Y`-scheme `X`, the sections of `f^* F` over `X` being the
sections of `F` over `X ⟶ Y` via `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`. -/
theorem upperStarIsoLocalizationRestriction_hom_app_equiv₀_cohomologyMap
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (x : Sheaf.H F 0) :
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf).hom.app F).hom.app
        (op (⊤_ X.Etale)) (Sheaf.H.equiv₀ _ terminalIsTerminal (cohomologyMap f F 0 x)) =
      F.obj.map (terminal.from ((MorphismProperty.Over.map ⊤ hf).obj (⊤_ X.Etale))).op
        (Sheaf.H.equiv₀ F terminalIsTerminal x) := by
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let ι := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf
  let e := Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f
  -- the global sections of a morphism out of the constant sheaf `ℤ`
  have key {S : Scheme.{u}} (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ψ : (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ⟶ G) :
      Sheaf.H.equiv₀ G terminalIsTerminal (Ext.mk₀ ψ) =
        ((constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).homEquiv _ _ ψ) (ULift.up 1) := by
    have h : Ext.addEquiv₀ (Ext.mk₀ ψ) = ψ := Ext.addEquiv₀.apply_symm_apply ψ
    simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
    erw [h]
    rfl
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ F).2 x
  have hc : cohomologyMap f F 0 (Ext.mk₀ φ) =
      Ext.mk₀ (e.inv.app M ≫ (f)^*[AddCommGrpCat.{u + 1}].map φ) := by
    rw [cohomologyMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    rfl
  -- the comparison of constant sheaves, on global sections
  have hB : (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).homEquiv _ _ (e.inv.app M ≫ ι.hom.app _) =
      (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
          M ≫ ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj.map
            (terminal.from ((MorphismProperty.Over.map ⊤ hf).obj (⊤_ X.Etale))).op := by
    rw [Adjunction.homEquiv_naturality_right]
    simp only [e, Scheme.upperStarConstantSheafIso, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← unit_app_comp_lowerStarCompSheafSectionsTerminalIso_hom_app_comp f hf]
    simp [Adjunction.comp_unit_app]
    rfl
  rw [hc, key, key]
  have hn : e.inv.app M ≫ (f)^*[AddCommGrpCat.{u + 1}].map φ ≫ ι.hom.app F =
      (e.inv.app M ≫ ι.hom.app _) ≫ (localizationRestriction AddCommGrpCat.{u + 1} f hf).map φ := by
    rw [Category.assoc, ι.hom.naturality]
  have h₁ := congrArg (fun g ↦ ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv _ _ g) (ULift.up 1)) hn
  simp only at h₁
  have hB' := hB
  rw [Adjunction.homEquiv_naturality_right] at hB'
  simp only [Adjunction.homEquiv_naturality_right, Functor.map_comp, Category.assoc] at h₁
  erw [reassoc_of% hB'] at h₁
  refine h₁.trans ?_
  rw [Adjunction.homEquiv_unit]
  simp only [ConcreteCategory.comp_apply]
  exact NatTrans.naturality_apply φ.hom _ _

end Zero

end AlgebraicGeometry.Etale
