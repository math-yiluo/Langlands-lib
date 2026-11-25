/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitSection
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.StalkMonoidal

/-!
# Iterated Weil structures and monoidal structures

A morphism `e : P ⊗ Q ⟶ R` of the underlying sheaves of Weil sheaves which is compatible with
the Weil structures, `(φ_P ⊗ φ_Q) ≫ e = μ ≫ Fr^* e ≫ φ_R`, is compatible with the iterated Weil
structures `φ_m` (`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`), and similarly for a unit
`𝟙 ⟶ R`. Together with `AlgebraicGeometry.WeilSheaf.stalkPairing_frobenius`, such a pairing
induces a pairing of stalks compatible with the local Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section IteratedWeilStructure

lemma frobeniusPowIso_zero_hom_hom (F : WeilSheaf k₀ l X) :
    (F.frobeniusPowIso 0).hom.hom =
      (lowerStarCongr (WeilCoefficients.{u} l) (by rw [pow_zero]; rfl)).hom.app
          F.obj.carrier.X ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom.app F.obj.carrier.X := by
  simp [frobeniusPowIso, adicLowerStarId, adicLowerStarCongr_hom_app_hom]
  rfl

lemma frobeniusPowIso_succ_hom_hom (F : WeilSheaf k₀ l X) (m : ℕ) :
    (F.frobeniusPowIso (m + 1)).hom.hom =
      (lowerStarCongr (WeilCoefficients.{u} l)
          (by rw [pow_succ, Aut.mul_asIso, Iso.trans_inv])).hom.app F.obj.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l) _ _).inv.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (F.frobeniusPowIso m).hom.hom ≫ F.obj.str.hom.hom := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Mod.comp_hom',
    adicLowerStarCongr_hom_app_hom, Iso.symm_hom, adicLowerStarComp_inv_app_hom,
    Functor.mapIso_hom, adicLowerStar_map_hom]

/-- A pairing of the underlying sheaves of Weil sheaves compatible with the Weil structures is
compatible with the iterated Weil structures. -/
theorem frobeniusPowIso_tensor (P Q R : WeilSheaf k₀ l X)
    (e : P.obj.carrier.X ⊗ Q.obj.carrier.X ⟶ R.obj.carrier.X)
    (h : (P.obj.str.hom.hom ⊗ₘ Q.obj.str.hom.hom) ≫ e =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u}
          l]
          P.obj.carrier.X Q.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map e ≫
          R.obj.str.hom.hom) (m : ℕ) :
    ((P.frobeniusPowIso m).hom.hom ⊗ₘ (Q.frobeniusPowIso m).hom.hom) ≫ e =
      μ (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_]
          P.obj.carrier.X Q.obj.carrier.X ≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].map e ≫
          (R.frobeniusPowIso m).hom.hom := by
  induction m with
  | zero =>
    rw [frobeniusPowIso_zero_hom_hom, frobeniusPowIso_zero_hom_hom,
      frobeniusPowIso_zero_hom_hom]
    have hc := NatTrans.IsMonoidal.tensor
      (τ := (lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom) P.obj.carrier.X Q.obj.carrier.X
    simp only [NatTrans.comp_app, Functor.LaxMonoidal.id_μ, Category.comp_id] at hc
    rw [← hc, Category.assoc]
    congr 1
    have := ((lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫ (lowerStarId (WeilCoefficients.{u} l) _).hom).naturality e
    simp only [NatTrans.comp_app, Functor.id_map, Category.assoc] at this
    exact this.symm
  | succ m ih =>
    rw [frobeniusPowIso_succ_hom_hom, frobeniusPowIso_succ_hom_hom,
      frobeniusPowIso_succ_hom_hom, ← tensorHom_comp_tensorHom_assoc,
      ← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc, h, μ_natural_assoc,
      ← Functor.map_comp_assoc, ih]
    have hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.inv =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv ≫
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv := by
      rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
    have h₁ := NatTrans.IsMonoidal.tensor (τ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv) P.obj.carrier.X
        Q.obj.carrier.X
    have h₂ := NatTrans.IsMonoidal.tensor (τ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom)
      P.obj.carrier.X Q.obj.carrier.X
    have n₁ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality e
    have n₂ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.naturality e
    simp only [Functor.comp_map] at n₁
    have hμ := Functor.LaxMonoidal.comp_μ
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[
        WeilCoefficients.{u} l]
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
      P.obj.carrier.X Q.obj.carrier.X
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hμ, ← reassoc_of% h₁, ← reassoc_of% h₂, reassoc_of% n₂, reassoc_of% n₁]

/-- A unit of the underlying sheaf of a Weil sheaf compatible with the Weil structure is
compatible with the iterated Weil structures. -/
theorem frobeniusPowIso_unit (R : WeilSheaf k₀ l X) (η : 𝟙_ _ ⟶ R.obj.carrier.X)
    (h : ε ((X ↘ Spec
          (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l] ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map η ≫
          R.obj.str.hom.hom = η) (m : ℕ) :
    ε (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[
        WeilCoefficients.{u} l] ≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].map η ≫
          (R.frobeniusPowIso m).hom.hom = η := by
  induction m with
  | zero =>
    rw [frobeniusPowIso_zero_hom_hom]
    have hc := NatTrans.IsMonoidal.unit
      (τ := (lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom)
    have := ((lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫ (lowerStarId (WeilCoefficients.{u} l) _).hom).naturality η
    simp only [NatTrans.comp_app, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.assoc] at hc this
    rw [this, reassoc_of% hc]
  | succ m ih =>
    have hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.inv =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv ≫
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv := by
      rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
    have h₁ := NatTrans.IsMonoidal.unit (τ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv)
    have h₂ := NatTrans.IsMonoidal.unit (τ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom)
    have n₁ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality η
    have n₂ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.naturality η
    simp only [Functor.comp_map] at n₁
    simp only [Functor.LaxMonoidal.comp_ε] at h₁
    rw [frobeniusPowIso_succ_hom_hom, reassoc_of% n₂, reassoc_of% h₂, reassoc_of% n₁,
      reassoc_of% h₁, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, ih, h]

end IteratedWeilStructure

section Constant

open MonObj
open scoped Obj

/-- The Weil structure of the constant Weil sheaf preserves the unit section. -/
lemma adicConstant_unit_str :
    ε ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l] ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          η[adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] ≫
        (adicConstant k₀ l X).obj.str.hom.hom =
      η[adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] := by
  have : IsMonHom (adicConstantSheafLowerStarIso l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l _))
  rw [adicConstant_str_hom_hom, ← Category.assoc, ← Functor.obj.η_def,
    ← IsMonHom.one_hom (f := (adicConstantSheafLowerStarIso l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).inv), Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The local Frobenius of the stalks of the constant Weil sheaf is the identity. -/
theorem adicConstant_stalkAt_frobenius
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    ((adicConstant k₀ l X).stalkAt s m hs).frobenius = LinearEquiv.refl _ _ := by
  have h := stalkUnit_frobenius s m hs _ _
    (frobeniusPowIso_unit (adicConstant k₀ l X) _ adicConstant_unit_str m)
  have h' : (stalkFrobeniusIso k₀ l X s m hs).app (adicConstant k₀ l X).obj.carrier.X ≪≫
      (stalkSheafFunctor k₀ l X s).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso ((adicConstant k₀ l X).frobeniusPowIso m)) =
        Iso.refl _ := by
    ext : 1
    rw [← cancel_epi (ProEtale.unitSection l s)]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.refl_hom]
    erw [Category.comp_id]
    exact h
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, h']
  rfl

end Constant

end AlgebraicGeometry.WeilSheaf
