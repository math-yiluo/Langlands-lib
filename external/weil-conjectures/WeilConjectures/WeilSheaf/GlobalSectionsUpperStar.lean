/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.MiddleExtension
public import WeilConjectures.WeilSheaf.StalkConstantSheaf
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Restriction of global sections of Weil sheaves

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes and `F` a Weil sheaf on `Y`. Restriction of global
sections along the base change `φ̄ : X̄ ⟶ Ȳ` is a map `Γ(Ȳ, F) → Γ(X̄, φ^* F)`
(`AlgebraicGeometry.WeilSheaf.globalSectionsRestrict`), which commutes with the Frobenius of the
global sections (`AlgebraicGeometry.WeilSheaf.globalSectionsRestrict_frobenius`). It is the
composite of the global sections of the unit `F ⟶ φ_* φ^* F` with `Γ(Ȳ, φ̄_* G) ≅ Γ(X̄, G)`, so
it is bijective as soon as the unit is an isomorphism
(`AlgebraicGeometry.WeilSheaf.bijective_globalSectionsRestrict`); this is the case for a lisse
Weil sheaf on a smooth curve and a dense open immersion
(`AlgebraicGeometry.WeilSheaf.IsLisse.bijective_globalSectionsRestrict_of_isOpenImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The inverse of the invariance `Γ(X̄, (Fr⁻¹)_* G) ≅ Γ(X̄, G)` of global sections is the
restriction along `Fr` followed by `Fr^* ≅ (Fr⁻¹)_*`. -/
lemma globalSectionsToUpperStar_comp_upperStarIsoLowerStarInv {Z : Scheme.{u}} (e : Z ≅ Z)
    (G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    (globalSectionsToUpperStar _ e.hom).app G ≫
      (Sheaf.Γ _ _).map ((upperStarIsoLowerStarInv _ e).hom.app G) =
    (globalSectionsLowerStarIso _ e.inv).inv.app G := by
  have h' := globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
    (WeilCoefficients.{u} l) e G
  simp only [globalSectionsUpperStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at h'
  rw [← Category.assoc] at h'
  exact (Iso.comp_hom_eq_id ((globalSectionsLowerStarIso _ e.inv).app _)).1 h'

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

/-- The Frobenius of the global sections of a Weil sheaf is the restriction along `Fr` followed
by the global sections of the Weil structure `Fr^* F ⟶ F`. -/
lemma globalSections_frobenius_eq_frobeniusStr [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (a : F.globalSections.carrier) :
    F.globalSections.frobenius a = ((WeilCoefficients.toModuleCat l).map
      ((globalSectionsToUpperStar _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).app
        F.obj.carrier.X ≫ (Sheaf.Γ _ _).map F.frobeniusStr)).hom a := by
  have h : (globalSectionsToUpperStar _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).app F.obj.carrier.X ≫
        (Sheaf.Γ _ _).map F.frobeniusStr =
      (globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app F.obj.carrier.X ≫
        (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map F.obj.str.hom) := by
    rw [frobeniusStr, Functor.map_comp, ← Category.assoc,
      globalSectionsToUpperStar_comp_upperStarIsoLowerStarInv]
  rw [h]
  rfl

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The restriction `Γ(Ȳ, F) → Γ(X̄, φ^* F)` of global sections of a Weil sheaf along the base
change `φ̄` of `φ`. -/
noncomputable def globalSectionsRestrict [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y) :
    F.globalSections.carrier →ₗ[PadicAlgCl l] ((upperStar φ).obj F).globalSections.carrier :=
  ((WeilCoefficients.toModuleCat l).map
    ((globalSectionsToUpperStar _ (φ̄)).app F.obj.carrier.X)).hom

/-- Restriction of global sections commutes with the Frobenius, on the underlying sheaves. -/
lemma globalSectionsToUpperStar_comp_frobeniusStr (F : WeilSheaf k₀ l Y) :
    (globalSectionsToUpperStar _ (φ̄)).app F.obj.carrier.X ≫
      (globalSectionsToUpperStar _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).app
        ((upperStar φ).obj F).obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((upperStar φ).obj F).frobeniusStr =
    (globalSectionsToUpperStar _
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).app
        F.obj.carrier.X ≫ (Sheaf.Γ _ _).map F.frobeniusStr ≫
      (globalSectionsToUpperStar _ (φ̄)).app F.obj.carrier.X := by
  have e₁ : (globalSectionsToUpperStar _ (φ̄)).app F.obj.carrier.X ≫
      (globalSectionsToUpperStar _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).app
        ((upperStar φ).obj F).obj.carrier.X =
      (globalSectionsToUpperStar _
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≫ (φ̄))).app
        F.obj.carrier.X ≫ (Sheaf.Γ _ _).map ((upperStarComp _
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom (φ̄)).hom.app
            F.obj.carrier.X) :=
    (globalSectionsToUpperStar_comp (WeilCoefficients.{u} l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom (φ̄) F.obj.carrier.X).symm
  have e₂ := globalSectionsToUpperStar_comp (WeilCoefficients.{u} l) (φ̄)
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom F.obj.carrier.X
  have e₃ := globalSectionsToUpperStar_app_comp_upperStarCongr (A := WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm F.obj.carrier.X
  have e₄ := (globalSectionsToUpperStar (WeilCoefficients.{u} l) (φ̄)).naturality F.frobeniusStr
  simp only [Functor.comp_map] at e₄
  rw [frobeniusStr_upperStar]
  simp only [Functor.map_comp]
  rw [reassoc_of% e₁]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% e₃, reassoc_of% e₂, e₄]

/-- **Restriction of global sections commutes with the Frobenius**. -/
theorem globalSectionsRestrict_frobenius [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y)
    (a : F.globalSections.carrier) :
    globalSectionsRestrict φ F (F.globalSections.frobenius a) =
      ((upperStar φ).obj F).globalSections.frobenius (globalSectionsRestrict φ F a) := by
  rw [globalSections_frobenius_eq_frobeniusStr, globalSections_frobenius_eq_frobeniusStr]
  have h := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom a)
    (globalSectionsToUpperStar_comp_frobeniusStr φ F)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h ⊢
  exact h.symm

/-- Restriction of global sections is bijective as soon as the unit `F ⟶ φ_* φ^* F` is an
isomorphism: it is the global sections of the unit followed by `Γ(Ȳ, φ̄_* G) ≅ Γ(X̄, G)`. -/
theorem bijective_globalSectionsRestrict [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] (F : WeilSheaf k₀ l Y)
    [IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app F)] :
    Function.Bijective (globalSectionsRestrict φ F) := by
  have : IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app F).hom.hom.f :=
    inferInstanceAs (IsIso ((Endofunctor.IsoAlgebra.forget _).map
      ((ObjectProperty.ι _).map ((upperStarLowerStarAdjunction φ).unit.app F))))
  have h := Functor.map_isIso (Mod.forget _)
    ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app F).hom.hom.f
  have : IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app
      F).hom.hom.f.hom := h
  rw [upperStarLowerStarAdjunction_unit_app_hom_hom_f, adicUpperStarLowerStarAdjunction,
    Adjunction.modAdjunction_unit_app_hom] at this
  have : IsIso ((globalSectionsToUpperStar _ (φ̄)).app F.obj.carrier.X) := by
    rw [globalSectionsToUpperStar_app]
    infer_instance
  exact ((WeilCoefficients.linearEquivOfIso
    (asIso ((globalSectionsToUpperStar _ (φ̄)).app F.obj.carrier.X))).bijective)

end AlgebraicGeometry.WeilSheaf
