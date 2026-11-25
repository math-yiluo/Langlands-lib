/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm
public import WeilConjectures.SixFunctors.ProEtale.Adic.StalkIhomDual

/-!
# Products of sections with sections of a lisse sheaf

For sheaves of `ℚ̄_ℓ,Y`-modules `F` and `N` on a scheme `Y` and sections `σ` of `F` and `τ` of `N`
over `W`, let `σ ⊗ τ` be the image of `σ ⊗ τ` under `F ⊗ N ⟶ 𝓗om(F^∨, N)`
(`AlgebraicGeometry.ProEtale.toIhomDualSection`); these are the building blocks of the tensor
powers of sections of Weil sheaves. Its formation commutes with restriction
(`AlgebraicGeometry.ProEtale.map_toIhomDualSection`), and its germ at a geometric point is the
image of the tensor product of the germs (`AlgebraicGeometry.ProEtale.germ_toIhomDualSection`).
For `F` lisse it is nonzero at a geometric point as soon as the germs of `σ` and `τ` are
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.germ_toIhomDualSection_ne_zero`). The germ of the
unit section `1` of `ℚ̄_ℓ,Y` is the unit of the stalk
(`AlgebraicGeometry.ProEtale.germ_adicUnitSection`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

/-- The unit section `1` of `ℚ̄_ℓ,Y` over `W`. -/
noncomputable def adicUnitSection (W : Y.ProEt) :
    ToType ((adicConstantSheaf l Y).obj.obj (op W)) :=
  (MonObj.one (X := adicConstantSheaf l Y)).hom.app (op W)
    ((ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).app (op W)
      (1 : ULift.{u + 1} (PadicAlgCl l)))

/-- The unit section commutes with restriction. -/
lemma map_adicUnitSection {W W' : Y.ProEt} (f : W' ⟶ W) :
    (adicConstantSheaf l Y).obj.map f.op (adicUnitSection W) = adicUnitSection W' := by
  have e : (ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).app (op W) ≫
      (MonObj.one (X := adicConstantSheaf l Y)).hom.app (op W) ≫
        (adicConstantSheaf l Y).obj.map f.op =
      (ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).app (op W') ≫
        (MonObj.one (X := adicConstantSheaf l Y)).hom.app (op W') := by
    rw [← (MonObj.one (X := adicConstantSheaf l Y)).hom.naturality]
    erw [← reassoc_of% ((ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).naturality
        f.op)]
    exact Category.id_comp _
  exact congrArg (fun φ ↦ φ.hom (1 : ULift.{u + 1} (PadicAlgCl l))) e

/-- The section `σ ⊗ τ` of `𝓗om(F^∨, N)`, image of `σ ⊗ τ` under `F ⊗ N ⟶ 𝓗om(F^∨, N)`. -/
noncomputable def toIhomDualSection {F N : AdicSheaf l Y} {W : Y.ProEt}
    (σ : ToType (F.X.obj.obj (op W))) (τ : ToType (N.X.obj.obj (op W))) :
    ToType (((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l Y))).obj N).X.obj.obj (op W)) :=
  (Mod.toIhomDual F N).hom.app (op W)
    ((μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) F.X N.X).app (op W)
      (σ ⊗ₜ τ))

/-- The formation of `σ ⊗ τ` commutes with restriction. -/
lemma map_toIhomDualSection {F N : AdicSheaf l Y} {W W' : Y.ProEt} (f : W' ⟶ W)
    (σ : ToType (F.X.obj.obj (op W))) (τ : ToType (N.X.obj.obj (op W))) :
    ((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l Y))).obj N).X.obj.map f.op
        (toIhomDualSection σ τ) =
      toIhomDualSection (F.X.obj.map f.op σ) (N.X.obj.map f.op τ) := by
  have e : (μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) F.X N.X).app (op W) ≫
      (Mod.toIhomDual F N).hom.app (op W) ≫
        ((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l Y))).obj N).X.obj.map f.op =
      (F.X.obj.map f.op ⊗ₘ N.X.obj.map f.op) ≫
        (μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) F.X N.X).app (op W') ≫
        (Mod.toIhomDual F N).hom.app (op W') := by
    rw [← (Mod.toIhomDual F N).hom.naturality]
    erw [← reassoc_of% ((μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) F.X
        N.X).naturality f.op)]
    rfl
  have := congrArg (fun φ ↦ φ.hom (σ ⊗ₜ τ)) e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

variable {K : Type u} [Field K]

/-- The germ of the unit section is the unit section of the stalk of `ℚ̄_ℓ`. -/
lemma germ_adicUnitSection (s : Spec (.of K) ⟶ Y) {W : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W) :
    germ _ s (adicConstantSheaf l Y) t (adicUnitSection W) =
      (unitSection l s).hom (1 : ULift.{u + 1} (PadicAlgCl l)) := by
  have e : (ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).app (op W) ≫
      (MonObj.one (X := adicConstantSheaf l Y)).hom.app (op W) ≫
        germ _ s (adicConstantSheaf l Y) t = unitSection l s := by
    rw [germ_naturality, unitSection, germ_unit (l := l) t, Category.assoc]
    rfl
  exact congrArg (fun φ ↦ φ.hom (1 : ULift.{u + 1} (PadicAlgCl l))) e

/-- The germ of `σ ⊗ τ` is the image of the tensor product of the germs under
`F ⊗ N ⟶ 𝓗om(F^∨, N)`. -/
lemma germ_toIhomDualSection {F N : AdicSheaf l Y} (s : Spec (.of K) ⟶ Y) {W : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W)
    (σ : ToType (F.X.obj.obj (op W))) (τ : ToType (N.X.obj.obj (op W))) :
    germ (WeilCoefficients.{u} l) s
      ((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l Y))).obj N).X t (toIhomDualSection σ τ) =
      ((stalkFunctor l s).map (Mod.toIhomDual F N)).hom
        ((μ (stalkFunctor l s) F.X N.X).hom (germ (WeilCoefficients.{u} l) s F.X t σ ⊗ₜ
          germ (WeilCoefficients.{u} l) s N.X t τ)) := by
  have h₁ := congrArg (fun f ↦ f.hom (σ ⊗ₜ τ)) (germ_tensor F.X N.X t)
  have h₂ := congrArg (fun f ↦ f.hom ((μ (sheafToPresheaf (ProEt.topology Y)
    (WeilCoefficients.{u} l)) F.X N.X).app (op W) (σ ⊗ₜ τ)))
    (germ_naturality (Mod.toIhomDual F N) t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h₁ h₂
  unfold toIhomDualSection
  erw [h₂, ← h₁]
  rfl

variable [IsAlgClosed K]

/-- If `F` is lisse and the germs of `σ` and `τ` at a geometric point are nonzero, so is the germ
of `σ ⊗ τ`. -/
lemma IsAdicLisseSheaf.germ_toIhomDualSection_ne_zero {F : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) {N : AdicSheaf l Y} (s : Spec (.of K) ⟶ Y) {W : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W)
    {σ : ToType (F.X.obj.obj (op W))} {τ : ToType (N.X.obj.obj (op W))}
    (hσ : germ (WeilCoefficients.{u} l) s F.X t σ ≠ 0)
    (hτ : germ (WeilCoefficients.{u} l) s N.X t τ ≠ 0) :
    germ (WeilCoefficients.{u} l) s ((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l Y))).obj N).X
      t (toIhomDualSection σ τ) ≠ 0 := by
  rw [germ_toIhomDualSection]
  exact hF.toIhomDual_stalk_ne_zero N s hσ hτ

end AlgebraicGeometry.ProEtale
