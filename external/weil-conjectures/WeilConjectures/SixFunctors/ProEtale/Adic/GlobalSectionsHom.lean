/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.SectionsMonoidal

/-!
# Global sections as morphisms out of the unit

A morphism `f : 𝟙 ⟶ N` of pro-étale sheaves of `ℚ̄_ℓ`-modules out of the unit sheaf is
determined by the global section `f(1)` of `N`, and every global section arises in this way
(`AlgebraicGeometry.ProEtale.bijective_globalSectionOfHom`): the unit sheaf is the sheafification
of the constant presheaf, and a morphism out of the constant presheaf on a site with a terminal
object is determined by its value on the terminal object.

Consequently, for a sheaf `M` of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ`, the morphisms
of modules `ℚ̄_ℓ ⟶ M` correspond to the global sections of `M`
(`AlgebraicGeometry.ProEtale.bijective_globalSectionOfModHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Opposite Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Z : Scheme.{u}}

/-- The global section `f(1)` of a morphism `f : 𝟙 ⟶ N` out of the unit sheaf. -/
noncomputable def globalSectionOfHom
    {N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) ⟶ N) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj N :=
  (ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map f).hom (1 : ULift (PadicAlgCl l))

variable (Z) in
/-- The sections over the terminal object `Z` of the pro-étale site. -/
noncomputable abbrev terminalSections :
    Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l) ⥤ WeilCoefficients.{u} l :=
  (sheafSections _ _).obj (op (Scheme.ProEt.mk (𝟙 Z)))

lemma globalSectionOfHom_eq {N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) ⟶ N) :
    globalSectionOfHom f =
      ((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Z)).inv.app N).hom
        ((ε (sheafToPresheaf _ (WeilCoefficients.{u} l)) ≫
          (sheafToPresheaf _ _).map f).app (op (Scheme.ProEt.mk (𝟙 Z))) |>.hom
            (1 : ULift.{u + 1} (PadicAlgCl l))) := by
  rw [globalSectionOfHom, ε_Γ, Category.assoc,
    ← (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Z)).inv.naturality f]
  rfl

/-- The morphism `U₀ ⟶ U` of the opposite pro-étale site from the terminal object. -/
noncomputable abbrev fromTerminal (U : (Scheme.ProEt Z)ᵒᵖ) :
    op (Scheme.ProEt.mk (𝟙 Z)) ⟶ U :=
  ((Scheme.ProEt.isTerminalMkId Z).from U.unop).op

/-- A morphism out of the unit presheaf is determined by its value on `1` over the terminal
object. -/
lemma unitPresheaf_hom_ext_of_section {P : (Scheme.ProEt Z)ᵒᵖ ⥤ WeilCoefficients.{u} l}
    {φ ψ : 𝟙_ ((Scheme.ProEt Z)ᵒᵖ ⥤ WeilCoefficients.{u} l) ⟶ P}
    (h : (φ.app (op (Scheme.ProEt.mk (𝟙 Z)))).hom (1 : ULift.{u + 1} (PadicAlgCl l)) =
      (ψ.app (op (Scheme.ProEt.mk (𝟙 Z)))).hom (1 : ULift.{u + 1} (PadicAlgCl l))) :
    φ = ψ := by
  ext U : 2
  have hφ := φ.naturality (fromTerminal U)
  have hψ := ψ.naturality (fromTerminal U)
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  have e₁ := congrArg (fun m ↦ m.hom (1 : ULift (PadicAlgCl l))) hφ
  have e₂ := congrArg (fun m ↦ m.hom (1 : ULift (PadicAlgCl l))) hψ
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at e₁ e₂
  change _ = (P.map _).hom _ at e₁ e₂
  erw [h] at e₁
  exact e₁.trans e₂.symm

/-- The global section `f(1)` determines `f`. -/
lemma globalSectionOfHom_injective {N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)} :
    Function.Injective (globalSectionOfHom (N := N)) := by
  intro f g h
  rw [globalSectionOfHom_eq, globalSectionOfHom_eq] at h
  refine Sheaf.unit_hom_ext (unitPresheaf_hom_ext_of_section ?_)
  exact ((ConcreteCategory.injective_of_mono_of_preservesPullback
    ((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Z)).inv.app N))) h

/-- The morphism out of the unit presheaf sending `1` to the restrictions of a section over the
terminal object. -/
@[simps]
noncomputable def unitPresheafHomOfSection {P : (Scheme.ProEt Z)ᵒᵖ ⥤ WeilCoefficients.{u} l}
    (a : P.obj (op (Scheme.ProEt.mk (𝟙 Z)))) :
    𝟙_ ((Scheme.ProEt Z)ᵒᵖ ⥤ WeilCoefficients.{u} l) ⟶ P where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{u + 1} (PadicAlgCl l)) _
    ((P.map (fromTerminal U)).hom a))
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (r : ULift.{u + 1} (PadicAlgCl l)) ↦ ?_)
    change r • (P.map (fromTerminal V)).hom a = (P.map g).hom (r • (P.map (fromTerminal U)).hom a)
    have hg : fromTerminal U ≫ g = fromTerminal V :=
      Quiver.Hom.unop_inj ((Scheme.ProEt.isTerminalMkId Z).hom_ext _ _)
    rw [map_smul, ← ModuleCat.comp_apply, ← P.map_comp, hg]

/-- Every global section is `f(1)` for a morphism `f : 𝟙 ⟶ N`. -/
lemma globalSectionOfHom_surjective
    {N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)} :
    Function.Surjective (globalSectionOfHom (N := N)) := by
  intro a
  let e := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)
    (Scheme.ProEt.isTerminalMkId Z)
  let adj := sheafificationAdjunction (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)
  let p := unitPresheafHomOfSection (P := N.obj) ((e.hom.app N).hom a)
  refine ⟨inv (Functor.OplaxMonoidal.η (presheafToSheaf _ _)) ≫ (adj.homEquiv _ _).symm p, ?_⟩
  have hε : ε (sheafToPresheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) =
      adj.homEquiv _ _ (Functor.OplaxMonoidal.η (presheafToSheaf _ _)) := rfl
  have hp : ε (sheafToPresheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) ≫
      (sheafToPresheaf _ _).map (inv (Functor.OplaxMonoidal.η (presheafToSheaf _ _)) ≫
        (adj.homEquiv _ _).symm p) = p := by
    rw [hε]
    erw [← adj.homEquiv_naturality_right]
    rw [IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  rw [globalSectionOfHom_eq, hp]
  have h₀ : fromTerminal (op (Scheme.ProEt.mk (𝟙 Z))) = 𝟙 _ :=
    Quiver.Hom.unop_inj ((Scheme.ProEt.isTerminalMkId Z).hom_ext _ _)
  have h₁ : (p.app (op (Scheme.ProEt.mk (𝟙 Z)))).hom (1 : ULift.{u + 1} (PadicAlgCl l)) =
      (e.hom.app N).hom a := by
    change (1 : ULift.{u + 1} (PadicAlgCl l)) •
      (N.obj.map (fromTerminal _)).hom ((e.hom.app N).hom a) = _
    rw [one_smul, h₀, N.obj.map_id, ModuleCat.id_apply]
  erw [h₁]
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id_app, ModuleCat.id_apply]

/-- `f ↦ f(1)` is a bijection between the morphisms `𝟙 ⟶ N` and the global sections of `N`. -/
lemma bijective_globalSectionOfHom
    (N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    Function.Bijective (globalSectionOfHom (N := N)) :=
  ⟨globalSectionOfHom_injective, globalSectionOfHom_surjective⟩

lemma globalSectionOfHom_comp {N N' : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) ⟶ N) (g : N ⟶ N') :
    globalSectionOfHom (f ≫ g) = ((Sheaf.Γ _ _).map g).hom (globalSectionOfHom f) := by
  rw [globalSectionOfHom, globalSectionOfHom, Functor.map_comp, ← Category.assoc,
    ModuleCat.comp_apply]

/-- The unit global section `1` of the constant `ℓ`-adic sheaf. -/
noncomputable def oneGlobalSection (Z : Scheme.{u}) :
    (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj (adicConstantSheaf l Z) :=
  globalSectionOfHom (MonObj.one (X := adicConstantSheaf l Z))

/-- The global section `v(1)` of a morphism of sheaves of modules `v : ℚ̄_ℓ ⟶ M` out of the
constant `ℓ`-adic sheaf. -/
noncomputable def globalSectionOfModHom {M : AdicSheaf l Z} (v : AdicSheaf.unit l Z ⟶ M) :
    (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj M.X :=
  globalSectionOfHom (MonObj.one (X := adicConstantSheaf l Z) ≫ v.hom)

lemma globalSectionOfModHom_eq {M : AdicSheaf l Z} (v : AdicSheaf.unit l Z ⟶ M) :
    globalSectionOfModHom v = ((Sheaf.Γ _ _).map v.hom).hom (oneGlobalSection (l := l) Z) :=
  globalSectionOfHom_comp _ _

/-- The morphisms of sheaves of modules `ℚ̄_ℓ ⟶ M` correspond to the global sections of `M`. -/
lemma bijective_globalSectionOfModHom (M : AdicSheaf l Z) :
    Function.Bijective (globalSectionOfModHom (M := M)) :=
  (bijective_globalSectionOfHom M.X).comp (Mod.bijective_one_comp_hom M)

end AlgebraicGeometry.ProEtale
