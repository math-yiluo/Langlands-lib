/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Pushforwards of pairings of Weil sheaves

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pushforward `φ̄_*` along its base change to the
geometric fibres is lax monoidal, and the exchange isomorphism `φ̄_* ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_*`
defining the Weil structure of `φ_* F` is monoidal. Hence a pairing `e : P ⊗ Q ⟶ R` of the
underlying sheaves of Weil sheaves which is compatible with the Weil structures induces a pairing
`φ_* P ⊗ φ_* Q ⟶ φ_* (P ⊗ Q) ⟶ φ_* R` compatible with the Weil structures of the pushforwards
(`AlgebraicGeometry.WeilSheaf.lowerStar_pairing_str`), and similarly for units
(`AlgebraicGeometry.WeilSheaf.lowerStar_unit_str`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The exchange isomorphism of pushforwards along the base change and along the Frobenii is
monoidal. -/
instance isMonoidal_lowerStarGeometricFiberMapCompFrobeniusIso_hom :
    NatTrans.IsMonoidal (lowerStarGeometricFiberMapCompFrobeniusIso (WeilCoefficients.{u} l) φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).hom := by
  dsimp only [lowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The Weil structure of the pushforward, on underlying sheaves. -/
lemma lowerStar_obj_obj_str_hom_hom (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.str.hom.hom =
      (lowerStarGeometricFiberMapCompFrobeniusIso (WeilCoefficients.{u} l) φ
          (comp_over φ (Spec (CommRingCat.of k₀)))).hom.app F.obj.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map F.obj.str.hom.hom := by
  rw [lowerStar_obj_obj_str, Iso.trans_hom, Mod.comp_hom', Iso.app_hom, Functor.mapIso_hom,
    adicLowerStar_map_hom, adicLowerStarGeometricFiberMapCompFrobeniusIso,
    lowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Mod.comp_hom', Mod.comp_hom', Iso.symm_hom, Iso.symm_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom]

/-- **Pushforwards of compatible pairings are compatible.** -/
theorem lowerStar_pairing_str (P Q R : WeilSheaf k₀ l X)
    (e : P.obj.carrier.X ⊗ Q.obj.carrier.X ⟶ R.obj.carrier.X)
    (h : (P.obj.str.hom.hom ⊗ₘ Q.obj.str.hom.hom) ≫ e =
      μ ((X ↘ Spec
          (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
          P.obj.carrier.X Q.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map e ≫
          R.obj.str.hom.hom) :
    (((lowerStar φ).obj P).obj.str.hom.hom ⊗ₘ ((lowerStar φ).obj Q).obj.str.hom.hom) ≫
        (μ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l]
          P.obj.carrier.X Q.obj.carrier.X ≫
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map e) =
      μ ((Y ↘ Spec
          (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj P.obj.carrier.X)
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj Q.obj.carrier.X) ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (μ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l]
            P.obj.carrier.X Q.obj.carrier.X ≫
            (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map e) ≫
          ((lowerStar φ).obj R).obj.str.hom.hom := by
  set ψ := lowerStarGeometricFiberMapCompFrobeniusIso (WeilCoefficients.{u} l) φ
    (comp_over φ (Spec (CommRingCat.of k₀)))
  have hψ := NatTrans.IsMonoidal.tensor (τ := ψ.hom) P.obj.carrier.X Q.obj.carrier.X
  have nψ := ψ.hom.naturality e
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj] at hψ nψ
  rw [lowerStar_obj_obj_str_hom_hom, lowerStar_obj_obj_str_hom_hom,
    lowerStar_obj_obj_str_hom_hom, ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc,
    ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hψ, reassoc_of% nψ]

omit [Fact l.Prime] in
/-- The unit compatibility in an abstract monoidal setting. -/
private lemma unit_str_aux {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) (GC : C ⥤ C) (GD : D ⥤ D) [F.LaxMonoidal]
    [GC.LaxMonoidal] [GD.LaxMonoidal] (ψ : F ⋙ GD ⟶ GC ⋙ F) [NatTrans.IsMonoidal ψ]
    (R : C) (s : GC.obj R ⟶ R) (η : 𝟙_ C ⟶ R) (h : ε GC ≫ GC.map η ≫ s = η) :
    ε GD ≫ GD.map (ε F ≫ F.map η) ≫ (ψ.app R ≫ F.map s) = ε F ≫ F.map η := by
  have hψ := NatTrans.IsMonoidal.unit (τ := ψ)
  have nψ := ψ.naturality η
  simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Functor.comp_obj] at hψ nψ
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nψ, reassoc_of% hψ, ← Functor.map_comp, ← Functor.map_comp, h]

/-- **Pushforwards of compatible units are compatible.** -/
theorem lowerStar_unit_str (R : WeilSheaf k₀ l X) (η : 𝟙_ _ ⟶ R.obj.carrier.X)
    (h : ε ((X ↘ Spec
          (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l] ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map η ≫
        R.obj.str.hom.hom = η) :
    ε ((Y ↘ Spec
          (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l] ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (ε (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l] ≫
            (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map η) ≫
        ((lowerStar φ).obj R).obj.str.hom.hom =
      ε (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l] ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map η := by
  rw [lowerStar_obj_obj_str_hom_hom]
  exact unit_str_aux _ _ _ (lowerStarGeometricFiberMapCompFrobeniusIso (WeilCoefficients.{u} l) φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom R.obj.carrier.X R.obj.str.hom.hom η h

end AlgebraicGeometry.WeilSheaf
