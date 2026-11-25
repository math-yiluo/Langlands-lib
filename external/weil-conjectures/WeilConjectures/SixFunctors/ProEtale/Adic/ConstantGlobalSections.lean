/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialRepresentation

/-!
# Global sections of the constant `ℓ`-adic sheaf

On a connected scheme `Z` the global sections of the constant `ℓ`-adic sheaf `ℚ̄_ℓ` are the
locally finite functions, which are constant; so they form a line, spanned by the section `1`.

## Main statements

- `AlgebraicGeometry.ProEtale.finrank_globalSections_adicConstantSheaf`: `Γ(Z, ℚ̄_ℓ)` is
  one-dimensional for `Z` connected.
- `AlgebraicGeometry.ProEtale.oneGlobalSection_ne_zero`: the section `1` is nonzero.
- `AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso_hom_app_globalSectionOfHom`: the
  identification `Γ(W, g_* G) ≅ Γ(Z, G)` on global sections coming from units.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The global sections of the constant `ℓ`-adic sheaf on a connected scheme form a line: they
are the locally finite functions, which are constant. -/
lemma finrank_globalSections_adicConstantSheaf (Z : Scheme.{u}) [ConnectedSpace Z] :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj
        (adicConstantSheaf l Z))) = 1 := by
  let e₃ : (WeilCoefficients.toModuleCat l).obj
      (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l Z))) ≃ₗ[PadicAlgCl l]
      PadicAlgCl.locallyFiniteFunctions l Z :=
    { toFun x := x.down
      invFun x := ULift.up x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  exact ((WeilCoefficients.linearEquivOfIso ((Sheaf.ΓNatIsoSheafSections _ _
    (Scheme.ProEt.isTerminalMkId Z)).app (adicConstantSheaf l Z))).trans
    (e₃.trans (PadicAlgCl.locallyFiniteFunctionsEquiv l Z).toLinearEquiv)).finrank_eq.trans
    (Module.finrank_self _)

/-- The global section `1` of the constant `ℓ`-adic sheaf on a connected scheme is nonzero. -/
lemma oneGlobalSection_ne_zero (Z : Scheme.{u}) [ConnectedSpace Z] :
    oneGlobalSection (l := l) Z ≠ 0 := by
  intro h
  have h₁ := finrank_globalSections_adicConstantSheaf (l := l) Z
  have : Subsingleton ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj
        (adicConstantSheaf l Z))) := by
    refine ⟨fun s t ↦ ?_⟩
    obtain ⟨v, rfl⟩ := (bijective_globalSectionOfModHom (AdicSheaf.unit l Z)).2 s
    obtain ⟨w, rfl⟩ := (bijective_globalSectionOfModHom (AdicSheaf.unit l Z)).2 t
    change globalSectionOfModHom v = globalSectionOfModHom w
    rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq, h, map_zero, map_zero]
  rw [Module.finrank_zero_of_subsingleton] at h₁
  exact zero_ne_one h₁

open MonoidalCategory Functor.LaxMonoidal in
/-- The identification `Γ(W, g_* G) ≅ Γ(Z, G)` carries the global section of the pushforward
`𝟙 ⟶ g_* 𝟙 ⟶ g_* G` of a unit `f : 𝟙 ⟶ G` to the global section of `f`. -/
lemma globalSectionsLowerStarIso_hom_app_globalSectionOfHom {Z W : Scheme.{u}} (g : Z ⟶ W)
    {G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) ⟶ G) :
    ((globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom.app G).hom
      (globalSectionOfHom (ε (g)_*[WeilCoefficients.{u} l] ≫ (g)_*[_].map f)) =
      globalSectionOfHom f := by
  have hε := NatTrans.IsMonoidal.unit
    (τ := (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom)
  have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom.naturality f
  rw [Functor.LaxMonoidal.comp_ε] at hε
  simp only [Category.assoc] at hε
  have key : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫
      (Sheaf.Γ _ _).map (ε (g)_*[WeilCoefficients.{u} l] ≫ (g)_*[_].map f) ≫
        (globalSectionsLowerStarIso _ g).hom.app G =
      ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map f := by
    rw [Functor.map_comp, Category.assoc]
    erw [n]
    rw [reassoc_of% hε]
  exact congrArg (fun m ↦ m.hom (1 : ULift.{u + 1} (PadicAlgCl l))) key

end AlgebraicGeometry.ProEtale
