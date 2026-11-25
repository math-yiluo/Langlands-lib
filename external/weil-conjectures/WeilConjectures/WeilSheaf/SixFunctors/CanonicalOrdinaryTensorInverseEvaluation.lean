/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality

import all WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomEvaluation
import all WeilConjectures.AlgebraicGeometry.Adic.AdicModuleHomComparisonCore
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionPureTripleExt
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Pure-tensor evaluation of the inverse Hom comparison

Source: Stacks 03EK and 03EO, pure tensors and evaluation-normalized inverse mates.
Auxiliary lemmas for `canonical_ordinary_tensor_inverse_associativity`
(blueprint: new-sf-canonical-ordinary-tensor-inverse-associativity).
-/

-- This module only keeps private helpers for the inverse associativity theorem.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
open CategoryTheory.TwistedActionRingedSite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private def nativePair {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    (P Q : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (V : Y.ProEtᵒᵖ) (x : P.obj.obj V) (y : Q.obj.obj V) : (P ⊗ Q).obj.obj V :=
  (Sheaf.tensorObjComparison (Scheme.ProEt.topology Y) P Q).app V
    (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y)

private theorem nativePair_map {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {P Q P' Q' : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)}
    (f : P ⟶ P') (g : Q ⟶ Q') (V : Y.ProEtᵒᵖ)
    (x : P.obj.obj V) (y : Q.obj.obj V) :
    (f ⊗ₘ g).hom.app V (nativePair P Q V x y) =
      nativePair P' Q' V (f.hom.app V x) (g.hom.app V y) := by
  exact ConcreteCategory.congr_hom
    (congr_app (Sheaf.tensorObjComparison_naturality f g) V) (x ⊗ₜ[_] y)

private def nativePure {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    (P Q : ProEtale.AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (x : P.X.obj.obj V) (y : Q.X.obj.obj V) : (P ⊗ Q).X.obj.obj V :=
  (Mod.tensorObjπ P Q).hom.app V (nativePair P.X Q.X V x y)

-- Explicit native and small-site module comparisons require substantial elaboration.
-- Coefficient and site universes differ in the two module models.
private theorem nativePure_associator {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    (P Q N : ProEtale.AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (x : P.X.obj.obj V) (y : Q.X.obj.obj V) (z : N.X.obj.obj V) :
    (α_ P Q N).hom.hom.hom.app V
      (nativePure (P ⊗ Q) N V (nativePure P Q V x y) z) =
        nativePure P (Q ⊗ N) V x (nativePure Q N V y z) := by
  let G := sheafToPresheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)
  have ha := congrArg (fun f ↦ f.app V
    ((x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y) ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] z))
      (Functor.LaxMonoidal.associativity G P.X Q.X N.X)
  change (α_ P.X Q.X N.X).hom.hom.app V
    (nativePair (P.X ⊗ Q.X) N.X V (nativePair P.X Q.X V x y) z) =
      nativePair P.X (Q.X ⊗ N.X) V x (nativePair Q.X N.X V y z) at ha
  have he := congrArg (fun f ↦ f.hom.app V
    (nativePair (P.X ⊗ Q.X) N.X V (nativePair P.X Q.X V x y) z))
      (Mod.tensorObjπ_associator_hom P Q N)
  have hl := nativePair_map (Mod.tensorObjπ P Q) (𝟙 N.X) V
    (nativePair P.X Q.X V x y) z
  have hr := nativePair_map (𝟙 P.X) (Mod.tensorObjπ Q N) V x
    (nativePair Q.X N.X V y z)
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] at hl hr
  change (α_ P Q N).hom.hom.hom.app V
    ((Mod.tensorObjπ (P ⊗ Q) N).hom.app V
      (((Mod.tensorObjπ P Q) ▷ N.X).hom.app V
        (nativePair (P.X ⊗ Q.X) N.X V (nativePair P.X Q.X V x y) z))) =
    (Mod.tensorObjπ P (Q ⊗ N)).hom.app V
      ((P.X ◁ Mod.tensorObjπ Q N).hom.app V
        ((α_ P.X Q.X N.X).hom.hom.app V
          (nativePair (P.X ⊗ Q.X) N.X V (nativePair P.X Q.X V x y) z))) at he
  rw [ha] at he
  rw [tensorHom_id] at hl
  rw [id_tensorHom] at hr
  change ((Mod.tensorObjπ P Q) ▷ N.X).hom.app V _ = _ at hl
  change (P.X ◁ Mod.tensorObjπ Q N).hom.app V _ = _ at hr
  rw [hl, hr] at he
  exact he

private theorem ringed_uncurry_pure
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M Q N : Modules R) (f : Q ⟶ SheafOfModules.homObj (R := R) M N)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : Q.val.obj U) :
    (((SheafOfModules.tensorHomAdjunction R M).homEquiv Q N).symm f).val.app U
      (pureTensor M Q U x y) = (f.val.app U y).app (op (Over.mk (𝟙 U.unop))) x := by
  delta SheafOfModules.tensorHomAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ring R).obj)
  let q := ((PresheafOfModules.homObjEquiv (R := R.obj) M.val Q.val N.val).symm f.val)
  let k := (adj.homEquiv (M.val ⊗ Q.val) N).symm q
  let t := (adj.unit.app (M.val ⊗ Q.val)).app U (x ⊗ₜ[R.obj.obj U] y)
  let e := SheafOfModules.tensorObjIsoSheafification M Q
  have h := (adj.homEquiv (M.val ⊗ Q.val) N).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun z ↦ z.app U (x ⊗ₜ[R.obj.obj U] y)) h
  have hi := congrArg (fun z ↦ z.val.app U t) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U t) = t at hi
  change k.val.app U (e.hom.val.app U (e.inv.val.app U t)) = _
  rw [hi]
  exact hh

/-- The Hom comparison of the two module models, as a natural isomorphism of bifunctors.
The sheaf-compose instance is a parameter so that the body keeps the instance supplied at the use
site instead of an auxiliary proof; the kernel then compares it with the inline comparison of
`canonical_ordinary_tensor_inverse_associativity` without unfolding. -/
private def hIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [(WeilFrobeniusAction.topology Y).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :
    Functor.uncurry.obj (SheafOfModules.homFunctor
      (R := ProEtale.NativeFrobenius.ring Y l)) ⋙
        (ProEtale.NativeFrobenius.equivalence Y l).functor ≅
    (ProEtale.NativeFrobenius.equivalence Y l).functor.op.prod
      (ProEtale.NativeFrobenius.equivalence Y l).functor ⋙
        Functor.uncurry.obj (ordinaryIhomBifunctor l Y) :=
  NatIso.ofComponents
    (fun MN ↦ ProEtale.NativeFrobenius.homComparison Y l H MN.1.unop MN.2)
    (fun fg ↦ ProEtale.NativeFrobenius.homComparison_naturality Y l H fg.1.unop fg.2)

/-- The inverse Hom comparison transported along the equivalence. -/
private def kIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [(WeilFrobeniusAction.topology Y).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :=
  HomComparison.inverseHomComparison (ProEtale.NativeFrobenius.equivalence Y l)
    (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
    (Functor.uncurry.obj (SheafOfModules.homFunctor
      (R := ProEtale.NativeFrobenius.ring Y l))) (hIso l Y H)

-- Explicit native and small-site module comparisons require substantial elaboration.
-- Coefficient and site universes differ in the two module models.
private theorem unit_sections (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (M : Modules (ProEtale.NativeFrobenius.ring Y l)) (V : Y.ProEtᵒᵖ)
    (x : ((ProEtale.NativeFrobenius.equivalence Y l).functor.obj M).X.obj.obj V) :
    ((ProEtale.NativeFrobenius.equivalence Y l).unitIso.inv.app M).val.app
        (op (AsSmall.up.obj V.unop)) x =
      ((ProEtale.NativeFrobenius.sectionCounit Y l).hom.app M).val.app V x := by
  let Q := SheafOfModules.SmallSite.equivalence (Scheme.ProEt.topology Y)
    (ProEtale.comparisonRing l Y)
  let N := ProEtale.adicSectionModuleEquivalence l Y
  have h : Functor.isoWhiskerRight
      (eqToIso (SheafOfModules.SmallSite.equivalence_functor (Scheme.ProEt.topology Y)
        (ProEtale.comparisonRing l Y))) N.inverse = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    change N.inverse.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  unfold ProEtale.NativeFrobenius.equivalence
  rw [h]
  simp only [Equivalence.changeFunctor, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, NatTrans.comp_app, Iso.refl_inv, NatTrans.id_app]
  change (Q.unitIso.inv.app M).val.app (op (AsSmall.up.obj V.unop))
    ((Q.inverse.map (N.counitIso.hom.app (Q.functor.obj M))).val.app
      (op (AsSmall.up.obj V.unop)) x) =
    (N.counitIso.hom.app (Q.functor.obj M)).val.app V x
  change M.val.map (𝟙 _) ((N.counitIso.hom.app (Q.functor.obj M)).val.app V x) = _
  exact ConcreteCategory.congr_hom (M.val.presheaf.map_id _) _

private theorem counit_sections (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (M : ProEtale.AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (x : ((ProEtale.NativeFrobenius.equivalence Y l).functor.obj
      ((ProEtale.NativeFrobenius.equivalence Y l).inverse.obj M)).X.obj.obj V) :
    ((ProEtale.NativeFrobenius.sectionCounit Y l).hom.app
      ((ProEtale.NativeFrobenius.equivalence Y l).inverse.obj M)).val.app V x =
      ((ProEtale.NativeFrobenius.equivalence Y l).counitIso.hom.app M).hom.hom.app V x := by
  rw [← unit_sections]
  rw [Equivalence.unitInv_app_inverse]
  rfl

-- Explicit native and small-site module comparisons require substantial elaboration.
-- Coefficient and site universes differ in the two module models.
private theorem inverse_comparison_evaluation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : ProEtale.AdicModuleHomComparisonCore l Y) (P I : ProEtale.AdicSheaf l Y)
    (V : Y.ProEtᵒᵖ) (z : ((ProEtale.AdicSheaf.ihom P).obj I).X.obj.obj V)
    (x : P.X.obj.obj V) :
    (((kIso l Y H).hom.app (op P, I)).val.app (op (AsSmall.up.obj V.unop)) z).app
        (op (Over.mk (𝟙 _))) x = ProEtale.adicComparisonEval P I V z x := by
  let E := ProEtale.NativeFrobenius.equivalence Y l
  let M := (ProEtale.AdicSheaf.ihom P).obj I
  let w := (E.counitIso.inv.app M).hom.hom.app V z
  let y := (E.counitIso.inv.app P).hom.hom.app V x
  let K : E.inverse.obj M ⟶ SheafOfModules.homObj
      (R := ProEtale.NativeFrobenius.ring Y l) (E.inverse.obj P) (E.inverse.obj I) :=
    (kIso l Y H).hom.app (op P, I)
  have he := ProEtale.NativeFrobenius.comparison_evaluation Y l H
    (E.inverse.obj P) (E.inverse.obj I) V
    ((E.functor.map K).hom.hom.app V w) y
  have hn := (ProEtale.NativeFrobenius.sectionCounit Y l).hom.naturality K
  have hn' := congrArg (fun f ↦ f.val.app V w) hn
  change ((ProEtale.NativeFrobenius.sectionCounit Y l).hom.app _).val.app V
    ((E.functor.map K).hom.hom.app V w) =
      K.val.app (op (AsSmall.up.obj V.unop))
        (((ProEtale.NativeFrobenius.sectionCounit Y l).hom.app (E.inverse.obj M)).val.app V w)
    at hn'
  rw [hn', counit_sections, counit_sections, counit_sections] at he
  have hz : (E.counitIso.hom.app M).hom.hom.app V w = z := by
    exact congrArg (fun f ↦ f.hom.hom.app V z) (E.counitIso.app M).inv_hom_id
  have hx : (E.counitIso.hom.app P).hom.hom.app V y = x := by
    exact congrArg (fun f ↦ f.hom.hom.app V x) (E.counitIso.app P).inv_hom_id
  rw [hz, hx] at he
  have hk := ProEtale.NativeFrobenius.inverseComparison_map E
    (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
    (Functor.uncurry.obj (SheafOfModules.homFunctor
      (R := ProEtale.NativeFrobenius.ring Y l))) (hIso l Y H) P I
  have hk' := congrArg (fun f ↦ f.hom.hom.app V w) hk
  change ((ProEtale.NativeFrobenius.homComparison Y l H
      (E.inverse.obj P) (E.inverse.obj I)).hom.hom.hom.app V
        ((E.functor.map K).hom.hom.app V w)) =
    (((Mod.ihomMap (E.counitIso.hom.app P)).app I ≫
      (ProEtale.AdicSheaf.ihom (E.functor.obj (E.inverse.obj P))).map
        (E.counitIso.inv.app I)).hom.hom.app V
          ((E.counitIso.hom.app M).hom.hom.app V w)) at hk'
  rw [hk', hz] at he
  change (E.counitIso.hom.app I).hom.hom.app V
    (ProEtale.adicComparisonEval _ _ V
      (((ProEtale.AdicSheaf.ihom _).map (E.counitIso.inv.app I)).hom.hom.app V
        (((Mod.ihomMap (E.counitIso.hom.app P)).app I).hom.hom.app V z)) y) = _ at he
  have hs := (ProEtale.evaluation_map_source (E.counitIso.hom.app P) I V z y).trans
    (congrArg (ProEtale.adicComparisonEval P I V z) hx)
  have ht := (ProEtale.evaluation_map_target (E.functor.obj (E.inverse.obj P))
    (E.counitIso.inv.app I) V
      (((Mod.ihomMap (E.counitIso.hom.app P)).app I).hom.hom.app V z) y).trans
    (congrArg ((E.counitIso.inv.app I).hom.hom.app V) hs)
  have hi : (E.counitIso.hom.app I).hom.hom.app V
      ((E.counitIso.inv.app I).hom.hom.app V (ProEtale.adicComparisonEval P I V z x)) =
        ProEtale.adicComparisonEval P I V z x := by
    exact congrArg (fun f ↦ f.hom.hom.app V
      (ProEtale.adicComparisonEval P I V z x)) (E.counitIso.app I).inv_hom_id
  exact he.symm.trans ((congrArg ((E.counitIso.hom.app I).hom.hom.app V) ht).trans hi)

private theorem relative_uncurry_pure (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (P Q N : ProEtale.AdicSheaf l Y) (f : Q ⟶ (ProEtale.AdicSheaf.ihom P).obj N)
    (V : Y.ProEtᵒᵖ) (y : Q.X.obj.obj V) (x : P.X.obj.obj V) :
    (((Mod.ihomAdjunction P).homEquiv Q N).symm f).hom.hom.app V
      ((Mod.tensorπ Q P).hom.app V (nativePair Q.X P.X V y x)) =
        ProEtale.adicComparisonEval P N V (f.hom.hom.app V y) x := by
  have he := congrArg (fun k ↦ k.hom.app V (nativePair Q.X P.X V y x))
    (Mod.uncurryHom_eq f).symm
  have hm := nativePair_map f.hom (𝟙 P.X) V y x
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] at hm
  change _ = (Mod.evaluation P N).hom.app V
    ((f.hom ▷ P.X).hom.app V (nativePair Q.X P.X V y x)) at he
  rw [tensorHom_id] at hm
  exact he.trans (congrArg ((Mod.evaluation P N).hom.app V) hm)

end AlgebraicGeometry.ProEtaleWeilSheaf
