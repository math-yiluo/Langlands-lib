/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateIdealFrame
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorYonedaSign

/-! # The framed integral coordinate pole extension

Source: the rank-one paragraph of the current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md
(blueprint: lem-pur-coordinate-pole-sign).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open Scheme.Modules

attribute [local implicit_reducible] MorphismProperty Scheme.Etale Scheme.instCategoryEtale
  catToReflQuiver Category.opposite Quiver.opposite CategoryStruct.opposite

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate pole extension is the inverse-coordinate pushout of the
integral localization extension, with the closed constant comparison included.
Source: Stacks 03AJ and the blueprint's coordinate frame calculation
(blueprint: lem-pur-coordinate-pole-sign).

Proof: use the unique pole extension's specified complementary frame. The global
dual coordinate frame identifies it with the coordinate acting on a global frame.
Identify the closed term of the localization sequence with the integral constant
on the zero section. Transport the pole extension's quotient through that
isomorphism. Its torsor map still kills the complementary frame and lies over the
localization image of one, by naturality of the constant unit. The framed-torsor
formula now gives the inverse-coordinate pushout. Naturality of extension classes
under the quotient isomorphism gives the displayed equality. -/
theorem coordinatePoleSign (T : Scheme.{u}) (hI : (zeroSection T).ker.IsInvertible) :
    ∃ C : Etale.PrincipalTorsorComparisons.{u}, C.Normalized ∧
      ∃ hL : (Etale.principalTorsorLocalization (zeroSection T)
          ((Line T).basicOpen (coordinate T))
          (coordinateLocalization_complement T)).ShortExact,
        Etale.cartierPoleBoundary (zeroSection T) hI =
          (Ext.mk₀ ((Etale.lowerStar AddCommGrpCat.{u + 1} (zeroSection T)).map
            ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
              (zeroSection T)).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).comp
            (hL.extClass.comp (Ext.mk₀ ((C.openSection (Line T) T (zeroSection T)
              ((Line T).basicOpen (coordinate T))
              (coordinateLocalization_complement T) (Line T).gmSheaf).symm
                (-(ULift.up (Additive.ofMul (coordinateUnit T)))))) (add_zero 1))
            (zero_add 1) := by
  have := hI.isInvertible_dual_toModules
  have := IsInvertible.sheafOfModules_isInvertible (dual (zeroSection T).ker.toModules)
  let W := (Line T).basicOpen (coordinate T)
  let S := Etale.principalTorsorLocalization (zeroSection T) W
    (coordinateLocalization_complement T)
  let Q := (Etale.lowerStar AddCommGrpCat.{u + 1} (zeroSection T)).mapIso
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (zeroSection T)).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  have hW : (W : Set (Line T)) = (Set.range (zeroSection T).base)ᶜ := by
    rw [← Scheme.Opens.range_ι W]
    change Set.range (openImmersion T).base = _
    simpa only [compl_compl] using
      (congrArg compl (coordinateLocalization_complement T)).symm
  obtain ⟨e, τ, hτ, hframe⟩ := coordinateDualTorsorFrame T hI
  have hβ := (Classical.choose_spec
    (Etale.cartierPoleBoundary_existsUnique (zeroSection T) hI)).1
  obtain ⟨τ', E, a, b, hab, hE, f, hτ', hf, hb, hzero, hclass⟩ := hβ W hW
  have hττ : τ' = τ := etaleIsoTorsorVal_injective _ (hτ'.trans hτ.symm)
  subst τ'
  let b' := b ≫ Q.inv
  have hab' : a ≫ b' = 0 := by simp [b', ← Category.assoc, hab]
  let S' := ShortComplex.mk a b' hab'
  let φ : S' ≅ ShortComplex.mk a b hab :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) Q (by simp [S']) (by simp [S', b'])
  have hE' : S'.ShortExact := ShortComplex.shortExact_of_iso φ.symm hE
  have hunit : Etale.supportedIntegralUnit (zeroSection T) ≫ Q.inv = S.g := by
    simp only [Etale.supportedIntegralUnit, Adjunction.homEquiv_unit, S,
      Etale.principalTorsorLocalization, Etale.openClosedShortComplex, Q,
      Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    exact (congrArg (fun f ↦
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (zeroSection T)).unit.app (Etale.supportedIntegralConstant (Line T)) ≫ f)
      ((Etale.lowerStar AddCommGrpCat.{u + 1} (zeroSection T)).map_id _)).trans
        (Category.comp_id _)
  have hbf : ∀ U p, b'.hom.app U (f.hom.app U p) =
      S.g.hom.app U (Etale.torsorExtensionOne (Line T) U.unop) := by
    intro U p
    change Q.inv.hom.app U (b.hom.app U (f.hom.app U p)) = _
    rw [hb]
    let v : op (Scheme.Etale.mk (𝟙 (Line T))) ⟶ U :=
      (MorphismProperty.Over.homMk U.unop.hom).op
    have hn := ConcreteCategory.congr_hom (Q.inv.hom.naturality v)
      ((Etale.supportedIntegralUnit (zeroSection T)).hom.app
        (op (Scheme.Etale.mk (𝟙 (Line T)))) (Etale.supportedIntegralOne (Line T)))
    simp only [ConcreteCategory.comp_apply] at hn
    refine hn.trans ?_
    change S.X₃.obj.map v
      ((Etale.supportedIntegralUnit (zeroSection T) ≫ Q.inv).hom.app
        (op (Scheme.Etale.mk (𝟙 (Line T)))) (Etale.supportedIntegralOne (Line T))) = _
    rw [hunit]
    have hs := ConcreteCategory.congr_hom (S.g.hom.naturality v)
      (Etale.supportedIntegralOne (Line T))
    have h1 := ConcreteCategory.congr_hom
      ((toSheafify (Line T).smallEtaleTopology
        ((Functor.const (Line T).Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality v) (ULift.up 1)
    simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hs h1
    exact hs.symm.trans (congrArg (S.g.hom.app U) h1.symm)
  obtain ⟨C, hC, _, hF⟩ := Etale.principal_torsor_yoneda_sign.{u}
  obtain ⟨⟨hL, hsign⟩, _⟩ := hF (Line T) T (zeroSection T) W
    (coordinateLocalization_complement T) (Line T).gmSheaf
    (etaleIsoTorsor (X := Line T) (dual (zeroSection T).ker.toModules)) e τ
    (ULift.up (Additive.ofMul (coordinateUnit T))) hframe E a b' hab' hE' f.hom
    (fun U g p ↦ (hf U g p).trans (add_comm _ _)) hbf hzero
  refine ⟨C, hC, hL, ?_⟩
  have hn : hE'.extClass = (Ext.mk₀ Q.hom).comp hE.extClass (zero_add 1) := by
    have hn := hE'.extClass_naturality hE φ.hom
    change hE'.extClass.comp (Ext.mk₀ (𝟙 _)) (add_zero 1) =
      (Ext.mk₀ Q.hom).comp hE.extClass (zero_add 1) at hn
    simpa only [Ext.comp_mk₀_id] using hn
  change Etale.cartierPoleBoundary (zeroSection T) hI = hE.extClass at hclass
  rw [hclass]
  calc
    hE.extClass = (Ext.mk₀ Q.inv).comp hE'.extClass (zero_add 1) := by
      rw [hn, ← Ext.comp_assoc (a₁₂ := 0) _ _ _ (by decide) (by decide) (by decide),
        Ext.mk₀_comp_mk₀, Q.inv_hom_id, Ext.mk₀_id_comp]
    _ = _ := congrArg (fun e ↦ (Ext.mk₀ Q.inv).comp e (zero_add 1)) hsign

end WeilConjectures.PurityFiniteSetting
