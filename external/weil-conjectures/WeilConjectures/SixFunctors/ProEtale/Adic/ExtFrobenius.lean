/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Injective.ExtMap
public import WeilConjectures.CategoryTheory.Abelian.Injective.ExtMapExactFunctor
public import WeilConjectures.CategoryTheory.Preadditive.Injective.ResolutionMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsExt

/-!
# The Frobenius on pro-étale `Ext` from a resolution

Let `g : X ⟶ X` be an automorphism, `G = g_*` the pushforward of abelian pro-étale sheaves, and
`s : G B ⟶ B` a structure morphism on an abelian sheaf `B`. For an injective resolution `R` of
`B` and a lift `ψ : G R ⟶ R` of `s`, the map
`f ↦ (ℤ ⟶ G ℤ) ≫ G f ≫ ψ` on the cocycles `ℤ ⟶ Rⁿ` induces a Frobenius on
`Hⁿ(X, B) = Ext^n(ℤ, B)` (`AlgebraicGeometry.ProEtale.extFrobeniusOfResolution`). It does not
depend on the lift, and it is natural in `B`: for `ι : B ⟶ B'` with `G ι ≫ s' = s ≫ ι`, it
commutes with `ι_*` (`AlgebraicGeometry.ProEtale.extFrobeniusOfResolution_comp_mk₀`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
  {B : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
  {s : (g)_*[AddCommGrpCat.{u + 1}].obj B ⟶ B} {R : InjectiveResolution B}
  (ψ : InjectiveResolution.Hom (R.map (g)_*[AddCommGrpCat.{u + 1}]) R s)

/-- The Frobenius on the cocycles `ℤ ⟶ Rⁿ`: `f ↦ (ℤ ⟶ g_* ℤ) ≫ g_* f ≫ ψ`. -/
noncomputable def resolutionFrobeniusCocycle (n : ℕ) :
    (constantIntSheaf X ⟶ R.cocomplex.X n) →+ (constantIntSheaf X ⟶ R.cocomplex.X n) :=
  AddMonoidHom.mk' (fun f ↦ constantIntSheafToLowerStar g ≫
    (g)_*[AddCommGrpCat.{u + 1}].map f ≫ ψ.hom.f n) fun f f' ↦ by
      simp [Preadditive.comp_add, Preadditive.add_comp]

lemma resolutionFrobeniusCocycle_apply (n : ℕ) (f : constantIntSheaf X ⟶ R.cocomplex.X n) :
    resolutionFrobeniusCocycle g ψ n f =
      constantIntSheafToLowerStar g ≫ (g)_*[AddCommGrpCat.{u + 1}].map f ≫ ψ.hom.f n :=
  rfl

lemma resolutionFrobeniusCocycle_comp_d (n m : ℕ) (f : constantIntSheaf X ⟶ R.cocomplex.X n) :
    resolutionFrobeniusCocycle g ψ m (f ≫ R.cocomplex.d n m) =
      resolutionFrobeniusCocycle g ψ n f ≫ R.cocomplex.d n m := by
  simp only [resolutionFrobeniusCocycle_apply, Functor.map_comp, Category.assoc]
  have hc := ψ.hom.comm n m
  rw [InjectiveResolution.map_cocomplex_d] at hc
  rw [hc]

/-- The Frobenius on `Hⁿ(X, B) = Ext^n(ℤ, B)` induced by a structure morphism `s : g_* B ⟶ B`,
computed with an injective resolution `R` of `B` and a lift `ψ` of `s`. -/
noncomputable def extFrobeniusOfResolution (n : ℕ) :
    Ext (constantIntSheaf X) B n →+ Ext (constantIntSheaf X) B n :=
  R.extMap R (resolutionFrobeniusCocycle g ψ) (resolutionFrobeniusCocycle_comp_d g ψ) n

lemma extFrobeniusOfResolution_extMk {n : ℕ} (f : constantIntSheaf X ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    extFrobeniusOfResolution g ψ n (R.extMk f (n + 1) rfl hf) =
      R.extMk (resolutionFrobeniusCocycle g ψ n f) (n + 1) rfl
        (by rw [← resolutionFrobeniusCocycle_comp_d, hf, map_zero]) :=
  R.extMap_extMk _ _ _ f hf

/-- **The Frobenius on `Ext` is intrinsic.** The Frobenius computed with a resolution is
`x ↦ (ℤ ⟶ g_* ℤ) ∘ g_*(x) ∘ s`, the image of `x` under the exact functor `g_*` read through
`ℤ ⟶ g_* ℤ` and `s : g_* B ⟶ B`. -/
theorem extFrobeniusOfResolution_eq {n : ℕ} (x : Ext (constantIntSheaf X) B n) :
    extFrobeniusOfResolution g ψ n x =
      (Ext.mk₀ (constantIntSheafToLowerStar g)).comp
        ((x.mapExactFunctor (g)_*[AddCommGrpCat.{u + 1}]).comp (Ext.mk₀ s) (add_zero n))
        (zero_add n) := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  rw [extFrobeniusOfResolution_extMk, ← Ext.comp_assoc_of_third_deg_zero,
    InjectiveResolution.mk₀_comp_mapExactFunctor_extMk,
    InjectiveResolution.extMk_comp_mk₀ _ _ _ _ ψ]
  rfl

variable {B' : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
  {s' : (g)_*[AddCommGrpCat.{u + 1}].obj B' ⟶ B'} {R' : InjectiveResolution B'}
  (ψ' : InjectiveResolution.Hom (R'.map (g)_*[AddCommGrpCat.{u + 1}]) R' s')

/-- **Naturality of the Frobenius on `Ext`.** For `ι : B ⟶ B'` compatible with the structure
morphisms, `ι_*` commutes with the Frobenius. -/
theorem extFrobeniusOfResolution_comp_mk₀ (ι : B ⟶ B')
    (hι : (g)_*[AddCommGrpCat.{u + 1}].map ι ≫ s' = s ≫ ι) {n : ℕ}
    (x : Ext (constantIntSheaf X) B n) :
    extFrobeniusOfResolution g ψ' n (x.comp (Ext.mk₀ ι) (add_zero n)) =
      (extFrobeniusOfResolution g ψ n x).comp (Ext.mk₀ ι) (add_zero n) := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  let θ := InjectiveResolution.descHom ι R R'
  have hε : (constantIntSheafToLowerStar g ≫ (g)_*[AddCommGrpCat.{u + 1}].map f) ≫
      (R.map (g)_*[AddCommGrpCat.{u + 1}]).cocomplex.d n (n + 1) = 0 := by
    rw [InjectiveResolution.map_cocomplex_d, Category.assoc, ← Functor.map_comp, hf,
      Functor.map_zero, Limits.comp_zero]
  rw [R.extMk_comp_mk₀ f (n + 1) rfl hf θ, extFrobeniusOfResolution_extMk,
    extFrobeniusOfResolution_extMk, R.extMk_comp_mk₀ _ (n + 1) rfl _ θ]
  have h₁ := (R.map (g)_*[AddCommGrpCat.{u + 1}]).extMk_comp_mk₀ _ (n + 1) rfl hε
    ((InjectiveResolution.Hom.map (g)_*[AddCommGrpCat.{u + 1}] θ).comp ψ')
  have h₂ := (R.map (g)_*[AddCommGrpCat.{u + 1}]).extMk_comp_mk₀ _ (n + 1) rfl hε
    ((ψ.comp θ).ofEq hι.symm)
  simp only [InjectiveResolution.Hom.comp_hom, InjectiveResolution.Hom.map_hom,
    InjectiveResolution.Hom.ofEq_hom, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Category.assoc] at h₁ h₂
  simp only [resolutionFrobeniusCocycle_apply, Functor.map_comp, Category.assoc]
  exact h₁.symm.trans h₂

end AlgebraicGeometry.ProEtale
