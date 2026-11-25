/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.WeilSheaf.StalkTensor

/-!
# Morphisms into internal homs of Weil sheaves

A morphism `q : M ⊗ D ⟶ N` of sheaves of `ℚ̄_ℓ`-modules which is `ℚ̄_ℓ`-linear in both variables
curries to a morphism of `ℓ`-adic sheaves `M ⟶ 𝓗om(D, N)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.curryHom`). If `M`, `D`, `N` are pro-étale Weil sheaves
and the uncurried form of a morphism `κ : M ⟶ 𝓗om(D, N)` is compatible with the Weil structures,
then `κ` is a morphism of pro-étale Weil sheaves `M ⟶ [D, N]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.homToIhom`): morphisms into an internal hom are determined
by their uncurried form, and the evaluation `[D, N] ⊗ D ⟶ N` is compatible with the Weil
structures (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom_evaluation_str`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

namespace ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

/-- **Currying of `ℓ`-adic sheaves.** A morphism `q : M ⊗ D ⟶ N` of sheaves of `ℚ̄_ℓ`-modules
which is `ℚ̄_ℓ,Y`-linear in `D` and in `M` is the uncurried form of a morphism of `ℓ`-adic
sheaves `M ⟶ 𝓗om(D, N)`. -/
noncomputable def curryHom {M D N : AdicSheaf l Y} (q : M.X ⊗ D.X ⟶ N.X)
    (hq : Mod.IsLinearRight q)
    (hq' : Mod.act M.X ▷ D.X ≫ q =
      (α_ (adicConstantSheaf l Y) M.X D.X).hom ≫ adicConstantSheaf l Y ◁ q ≫ Mod.act N.X) :
    M ⟶ (AdicSheaf.ihom D).obj N :=
  Mod.homMk (Mod.curry q hq) (by
    apply Mod.hom_ext_of_evaluation (D := D)
    rw [comp_whiskerRight, Category.assoc, Mod.curry_evaluation, hq', comp_whiskerRight,
      Category.assoc, Mod.act_whiskerRight_evaluation, associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Mod.curry_evaluation])

/-- The underlying morphism of `curryHom q` is the currying `Mod.curry q`. -/
@[simp]
lemma curryHom_hom {M D N : AdicSheaf l Y} (q : M.X ⊗ D.X ⟶ N.X) (hq : Mod.IsLinearRight q)
    (hq' : Mod.act M.X ▷ D.X ≫ q =
      (α_ (adicConstantSheaf l Y) M.X D.X).hom ≫ adicConstantSheaf l Y ◁ q ≫ Mod.act N.X) :
    (curryHom q hq hq').hom = Mod.curry q hq :=
  rfl

/-- The uncurried form of `curryHom q` is `q`. -/
lemma curryHom_evaluation {M D N : AdicSheaf l Y} (q : M.X ⊗ D.X ⟶ N.X)
    (hq : Mod.IsLinearRight q)
    (hq' : Mod.act M.X ▷ D.X ≫ q =
      (α_ (adicConstantSheaf l Y) M.X D.X).hom ≫ adicConstantSheaf l Y ◁ q ≫ Mod.act N.X) :
    (curryHom q hq hq').hom ▷ D.X ≫ Mod.evaluation D N = q :=
  Mod.curry_evaluation q hq

end ProEtale.AdicSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open ProEtale

/-- A morphism `κ : M ⟶ 𝓗om(D, N)` of `ℓ`-adic sheaves whose uncurried form
`M ⊗ D ⟶ N` is compatible with the Weil structures intertwines the Weil structures of `M` and of
the internal hom `[D, N]`. -/
theorem ProEtaleWeilSheaf.homToIhom_comm (M D N : ProEtaleWeilSheaf k₀ l X)
    (κ : M.carrier ⟶ (AdicSheaf.ihom D.carrier).obj N.carrier)
    (hκ : (M.str.hom.hom ⊗ₘ D.str.hom.hom) ≫ (κ.hom ▷ D.carrier.X ≫
        Mod.evaluation D.carrier N.carrier) =
      μ ((X ↘ Spec
        (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
          M.carrier.X D.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (κ.hom ▷ D.carrier.X ≫ Mod.evaluation D.carrier N.carrier) ≫ N.str.hom.hom) :
    (WeilSheaf.frobeniusPullback k₀ l X).map κ ≫ (ProEtaleWeilSheaf.ihom k₀ l X D N).str.hom =
      M.str.hom ≫ κ := by
  set Fr :=
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
  have : IsIso D.str.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map D.str.hom))
  have he := ProEtaleWeilSheaf.ihom_evaluation_str D N
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom]
  apply Mod.hom_ext_of_evaluation (D := D.carrier)
  rw [← cancel_epi (Fr.obj M.carrier.X ◁ D.str.hom.hom), comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← tensorHom_def'_assoc, he, comp_whiskerRight_assoc,
    ← tensorHom_def'_assoc]
  erw [hκ]
  rw [Fr.map_comp_assoc, ← reassoc_of% (μ_natural_left Fr κ.hom D.carrier.X)]
  rfl

/-- **Morphisms into internal homs of pro-étale Weil sheaves.** A morphism
`κ : M ⟶ 𝓗om(D, N)` of `ℓ`-adic sheaves whose uncurried form `M ⊗ D ⟶ N` is compatible with the
Weil structures, as a morphism of pro-étale Weil sheaves `M ⟶ [D, N]`. -/
noncomputable def ProEtaleWeilSheaf.homToIhom (M D N : ProEtaleWeilSheaf k₀ l X)
    (κ : M.carrier ⟶ (AdicSheaf.ihom D.carrier).obj N.carrier)
    (hκ : (M.str.hom.hom ⊗ₘ D.str.hom.hom) ≫ (κ.hom ▷ D.carrier.X ≫
        Mod.evaluation D.carrier N.carrier) =
      μ ((X ↘ Spec
        (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
          M.carrier.X D.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (κ.hom ▷ D.carrier.X ≫ Mod.evaluation D.carrier N.carrier) ≫ N.str.hom.hom) :
    M ⟶ ProEtaleWeilSheaf.ihom k₀ l X D N :=
  ObjectProperty.homMk ⟨κ, ProEtaleWeilSheaf.homToIhom_comm M D N κ hκ⟩

/-- The underlying morphism of `homToIhom κ` is `κ`. -/
@[simp]
lemma ProEtaleWeilSheaf.homToIhom_hom_f (M D N : ProEtaleWeilSheaf k₀ l X)
    (κ : M.carrier ⟶ (AdicSheaf.ihom D.carrier).obj N.carrier)
    (hκ : (M.str.hom.hom ⊗ₘ D.str.hom.hom) ≫ (κ.hom ▷ D.carrier.X ≫
        Mod.evaluation D.carrier N.carrier) =
      μ ((X ↘ Spec
        (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
          M.carrier.X D.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (κ.hom ▷ D.carrier.X ≫ Mod.evaluation D.carrier N.carrier) ≫ N.str.hom.hom) :
    (ProEtaleWeilSheaf.homToIhom M D N κ hκ).hom.f = κ :=
  rfl

end AlgebraicGeometry
