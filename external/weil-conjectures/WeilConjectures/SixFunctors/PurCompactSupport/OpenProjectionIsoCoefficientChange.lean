/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullTensorCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

set_option linter.privateModule false

/-! The open projection square before the compactification pullback compositor.
(blueprint: lem-sf-open-projection-iso-coefficient-change).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction HasDerivedCategory.standard
  Functor.leftAdjoint proEtaleRingModulePullback proEtaleCanonicalTensorComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensor_square
    {UA XA UB XB : Type*}
    [Category UA] [Category XA] [Category UB] [Category XB]
    {eA : UA ⥤ XA} {rA : XA ⥤ UA} {eB : UB ⥤ XB} {rB : XB ⥤ UB}
    (a : eA ⊣ rA) (b : eB ⊣ rB) (SX : XA ⥤ XB) (SU : UA ⥤ UB)
    (TA : XA × XA ⥤ XA) (TU : UA × UA ⥤ UA)
    (TB : XB × XB ⥤ XB) (TV : UB × UB ⥤ UB)
    (tX : TA ⋙ SX ≅ SX.prod SX ⋙ TB)
    (tU : TU ⋙ SU ≅ SU.prod SU ⋙ TV)
    (aA : TA ⋙ rA ≅ rA.prod rA ⋙ TU)
    (aB : TB ⋙ rB ≅ rB.prod rB ⋙ TV)
    (lam : SX ⋙ rB ≅ rA ⋙ SU) (bet : eA ⋙ SX ≅ SU ⋙ eB)
    (pA : ∀ K Q, TA.obj (eA.obj K, Q) ≅ eA.obj (TU.obj (K, rA.obj Q)))
    (pB : ∀ K Q, TB.obj (eB.obj K, Q) ≅ eB.obj (TV.obj (K, rB.obj Q)))
    (hb : ∀ K, b.homEquiv _ _ (bet.inv.app K) =
      SU.map (a.unit.app K) ≫ lam.inv.app (eA.obj K))
    (hpA : ∀ K Q, a.homEquiv _ _ ((pA K Q).inv) =
      TU.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ aA.inv.app (eA.obj K, Q))
    (hpB : ∀ K Q, b.homEquiv _ _ ((pB K Q).inv) =
      TV.map (Prod.mkHom (b.unit.app K) (𝟙 _)) ≫ aB.inv.app (eB.obj K, Q))
    (hm : ∀ F Q,
      TV.map (Prod.mkHom (lam.inv.app F) (lam.inv.app Q)) ≫
        aB.inv.app (SX.obj F, SX.obj Q) ≫ rB.map (tX.inv.app (F, Q)) =
      tU.inv.app (rA.obj F, rA.obj Q) ≫ SU.map (aA.inv.app (F, Q)) ≫
        lam.inv.app (TA.obj (F, Q))) (K : UA) (Q : XA) :
    SX.map ((pA K Q).hom) ≫ bet.hom.app (TU.obj (K, rA.obj Q)) ≫
        eB.map (tU.hom.app (K, rA.obj Q) ≫
          TV.map (Prod.mkHom (𝟙 _) (lam.inv.app Q))) =
      tX.hom.app (eA.obj K, Q) ≫ TB.map (Prod.mkHom (bet.hom.app K) (𝟙 _)) ≫
        (pB (SU.obj K) (SX.obj Q)).hom := by
  let L := SX.mapIso (pA K Q) ≪≫ bet.app (TU.obj (K, rA.obj Q)) ≪≫
    eB.mapIso (tU.app (K, rA.obj Q) ≪≫
      TV.mapIso ((Iso.refl (SU.obj K)).prod (lam.symm.app Q)))
  let R := tX.app (eA.obj K, Q) ≪≫
    TB.mapIso ((bet.app K).prod (Iso.refl (SX.obj Q))) ≪≫
      pB (SU.obj K) (SX.obj Q)
  have hi : L.inv = R.inv := by
    apply (b.homEquiv _ _).injective
    simp only [L, R, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Iso.prod_inv, Iso.refl_inv, Iso.symm_inv, Category.assoc]
    change b.homEquiv _ _
        (eB.map (TV.map (Prod.mkHom (𝟙 _) (lam.hom.app Q)) ≫
          tU.inv.app (K, rA.obj Q)) ≫ bet.inv.app _ ≫
            SX.map ((pA K Q).inv)) =
      b.homEquiv _ _ ((pB (SU.obj K) (SX.obj Q)).inv ≫
        TB.map (Prod.mkHom (bet.inv.app K) (𝟙 _)) ≫ tX.inv.app (eA.obj K, Q))
    simp only [Adjunction.homEquiv_unit, rB.map_comp]
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.prod_obj, Prod.fst, Prod.snd]
    have hu := b.unit.naturality
      (TV.map (Prod.mkHom (𝟙 (SU.obj K)) (lam.hom.app Q)) ≫
        tU.inv.app (K, rA.obj Q))
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
    rw [← reassoc_of% hu]
    have hbeta := hb (TU.obj (K, rA.obj Q))
    rw [Adjunction.homEquiv_unit] at hbeta
    rw [reassoc_of% hbeta]
    have hn := lam.inv.naturality ((pA K Q).inv)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hn
    rw [← hn, ← SU.map_comp_assoc]
    have hpa := hpA K Q
    rw [Adjunction.homEquiv_unit] at hpa
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hpa
    rw [hpa, SU.map_comp]
    simp only [Category.assoc]
    have ht := tU.inv.naturality (Prod.mkHom (a.unit.app K) (𝟙 (rA.obj Q)))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_map, Functor.id_obj] at ht
    rw [← reassoc_of% ht, ← hm]
    rw [SU.map_id]
    simp only [← TV.map_comp_assoc]
    have hp : Prod.mkHom (𝟙 (SU.obj K)) (lam.hom.app Q) ≫
        Prod.mkHom (SU.map (a.unit.app K)) (𝟙 (SU.obj (rA.obj Q))) ≫
          Prod.mkHom (lam.inv.app (eA.obj K)) (lam.inv.app Q) =
        Prod.mkHom (SU.map (a.unit.app K) ≫ lam.inv.app (eA.obj K))
          (𝟙 (rB.obj (SX.obj Q))) := by
      ext <;> simp
    rw [hp]
    have hbk := hb K
    rw [Adjunction.homEquiv_unit] at hbk
    rw [← hbk]
    have hp' : Prod.mkHom (b.unit.app (SU.obj K) ≫ rB.map (bet.inv.app K))
        (𝟙 (rB.obj (SX.obj Q))) =
        Prod.mkHom (b.unit.app (SU.obj K)) (𝟙 _) ≫
          (rB.prod rB).map (Prod.mkHom (bet.inv.app K) (𝟙 (SX.obj Q))) := by
      ext <;> simp
    rw [hp', TV.map_comp, Category.assoc]
    have htB := aB.inv.naturality (Prod.mkHom (bet.inv.app K) (𝟙 (SX.obj Q)))
    dsimp only [Functor.comp_map, Functor.comp_obj] at htB
    rw [reassoc_of% htB]
    dsimp only [Functor.comp_obj, Prod.snd]
    have hpb := hpB (SU.obj K) (SX.obj Q)
    rw [Adjunction.homEquiv_unit] at hpb
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hpb
    rw [← reassoc_of% hpb]
  have he : L.symm = R.symm := Iso.ext hi
  have he' := congrArg (fun e ↦ e.inv) he
  simpa only [L, R, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Iso.prod_hom, Iso.symm_hom, Iso.refl_hom] using he'

end WeilConjectures.PurCompactSupport
