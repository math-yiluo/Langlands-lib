/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import all WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionIdentifiers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

set_option linter.privateModule false

/-! # Binary normalization of the transported immersion compositor

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md, (1)--(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 2000] proEtaleRingModulePullback_preservesFiniteLimits
  proEtaleRingModulePullback_preservesFiniteColimits
attribute [local irreducible] proEtaleRingModulePullback
  Functor.mapDerivedCategory DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  exchangeModuleComposition

-- The comparison involves many nested functor constructions.
private theorem restriction_eq (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :
    D.restriction a = E.derivedRestriction a := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules S.scheme S.ring) (.up ℤ))
  intro K
  exact (D.restrictionTermwise a K).trans (E.restrictionTermwise a K).symm

-- The comparison involves many nested functor constructions.
private theorem gamma_eq (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    {T S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    D.gamma a b = Functor.mapDerivedCategoryCompNatIso (E.gamma a b) := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules T.scheme T.ring) (.up ℤ))
  intro K
  apply (cancel_mono ((E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K)).mp
  exact (D.gammaTermwise a b K).trans (E.gammaTermwise a b K).symm

-- The comparison involves many nested functor constructions.
private theorem transportRestriction_forward
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (F : C ⥤ D) (R : B ⥤ A) (Q : D ⥤ C)
    (d : R ⋙ e.functor ≅ e'.functor ⋙ Q) (rho : F ⋙ Q ≅ 𝟭 C) (M : A) :
    e.functor.map ((scalarSixTransportRestriction e e' F R Q d rho).hom.app M) =
      d.hom.app (e'.inverse.obj (F.obj (e.functor.obj M))) ≫
        Q.map (e'.counitIso.hom.app (F.obj (e.functor.obj M))) ≫
        rho.hom.app (e.functor.obj M) := by
  simp only [scalarSixTransportRestriction, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj,
    Category.id_comp, Functor.map_comp]
  simp only [e.fun_inv_map, ← e.counit_app_functor, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc, e.functor_unitIso_comp, Category.id_comp]
  simp only [Category.assoc, Category.comp_id, Equivalence.counitIso_inv_hom_id_app]
  simp only [Functor.id_obj, Category.comp_id]

-- The comparison involves many nested functor constructions.
private theorem exact_normalized
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) (G : A ⥤ B) (H : A ⥤ C)
    (R : C ⥤ B) (S : B ⥤ A) (U : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive] [R.Additive] [S.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (rF : F ⋙ R ≅ 𝟭 B) (rG : G ⋙ S ≅ 𝟭 A) (rH : H ⋙ U ≅ 𝟭 A)
    (c : U ≅ R ⋙ S) (gamma : G ⋙ F ≅ H)
    (hn : ∀ M, U.map (gamma.hom.app M) ≫ rH.hom.app M =
      c.hom.app (F.obj (G.obj M)) ≫ S.map (rF.hom.app (G.obj M)) ≫ rG.hom.app M)
    (M : DerivedCategory A) :
    U.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso gamma).hom.app M) ≫
        (Functor.mapDerivedCategoryCompNatIso rH ≪≫
          Functor.mapDerivedCategoryIdIso A).hom.app M =
      (Functor.mapDerivedCategoryNatIso c ≪≫
          (Functor.mapDerivedCategoryCompIso R S).symm).hom.app
          (F.mapDerivedCategory.obj (G.mapDerivedCategory.obj M)) ≫
        S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso rF ≪≫
          Functor.mapDerivedCategoryIdIso B).hom.app (G.mapDerivedCategory.obj M)) ≫
        (Functor.mapDerivedCategoryCompNatIso rG ≪≫
          Functor.mapDerivedCategoryIdIso A).hom.app M := by
  let q : F ⋙ U ≅ S := Functor.isoWhiskerLeft F c ≪≫
    Functor.isoWhiskerRight rF S ≪≫ Functor.leftUnitor S
  have hq (N : B) :
      S.map (rF.hom.app N) ≫ (Functor.leftUnitor S).hom.app N =
        c.inv.app (F.obj N) ≫ q.hom.app N := by
    simp [q]
  have hdq := Functor.mapDerivedCategoryCompNatIso_cocycle rF
    (Functor.leftUnitor S) c.symm q hq (G.mapDerivedCategory.obj M)
  have hunit := AlgebraicGeometry.Scheme.derived_left_unit (𝟭 B) S (Iso.refl _)
  have hunit' : Functor.mapDerivedCategoryCompNatIso (Functor.leftUnitor S) =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryIdIso B) S.mapDerivedCategory ≪≫
        Functor.leftUnitor S.mapDerivedCategory := by
    apply Iso.ext
    have hu := congrArg Iso.hom hunit
    simpa only [Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.mapDerivedCategoryNatIso_refl,
      Category.id_comp] using hu
  rw [hunit'] at hdq
  have hc : Functor.mapDerivedCategoryCompNatIso c.symm =
      (Functor.mapDerivedCategoryNatIso c ≪≫
        (Functor.mapDerivedCategoryCompIso R S).symm).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm]
  rw [hc] at hdq
  have hdq' := congrArg (fun z ↦
    (Functor.mapDerivedCategoryNatIso c ≪≫
      (Functor.mapDerivedCategoryCompIso R S).symm).hom.app
      (F.mapDerivedCategory.obj (G.mapDerivedCategory.obj M)) ≫ z) hdq
  simp only [Iso.symm_hom, Iso.hom_inv_id_app_assoc] at hdq'
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app,
    Functor.id_obj, Category.assoc] at hdq'
  have hn' (N : A) : U.map (gamma.hom.app N) ≫ rH.hom.app N =
      q.hom.app (G.obj N) ≫ rG.hom.app N := by
    simpa [q, Category.assoc] using hn N
  have hd := Functor.mapDerivedCategoryCompNatIso_cocycle gamma rH q rG hn' M
  have hd' := congrArg (fun z ↦ z ≫ (Functor.mapDerivedCategoryIdIso A).hom.app M) hd
  rw [← hdq'] at hd'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hd' ⊢
  simpa using hd'

private theorem normalization_congr
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : B ⥤ C} {G : A ⥤ B} {H : A ⥤ C}
    {R : C ⥤ B} {S : B ⥤ A} {U : C ⥤ A}
    {rF rF' : F ⋙ R ≅ 𝟭 B} {rG rG' : G ⋙ S ≅ 𝟭 A} {rH rH' : H ⋙ U ≅ 𝟭 A}
    {c c' : U ≅ R ⋙ S} {gamma gamma' : G ⋙ F ≅ H}
    (hF : rF = rF') (hG : rG = rG') (hH : rH = rH')
    (hc : c = c') (hg : gamma = gamma')
    (hn : ∀ M, U.map (gamma'.hom.app M) ≫ rH'.hom.app M =
      c'.hom.app (F.obj (G.obj M)) ≫ S.map (rF'.hom.app (G.obj M)) ≫ rG'.hom.app M) :
    ∀ M, U.map (gamma.hom.app M) ≫ rH.hom.app M =
      c.hom.app (F.obj (G.obj M)) ≫ S.map (rF.hom.app (G.obj M)) ≫ rG.hom.app M := by
  cases hF
  cases hG
  cases hH
  cases hc
  cases hg
  exact hn

-- Specialize the abstract localization equation without equality induction.
private theorem canonical_normalized (E : LocallyClosedExtensionData.{u})
    (hE : E.Coherent) {T S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : DerivedCategory (proEtaleRingModules T.scheme T.ring)) :
    (a.comp b).pull.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompNatIso (E.gamma a b)).hom.app M) ≫
        (E.derivedRestriction (a.comp b)).hom.app M =
      (Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
        (Functor.mapDerivedCategoryCompIso a.pull b.pull).symm).hom.app
          ((E.derived a).obj ((E.derived b).obj M)) ≫
        b.pull.mapDerivedCategory.map
          ((E.derivedRestriction a).hom.app ((E.derived b).obj M)) ≫
        (E.derivedRestriction b).hom.app M := by
  exact exact_normalized
    (A := proEtaleRingModules T.scheme T.ring)
    (B := proEtaleRingModules S.scheme S.ring)
    (C := proEtaleRingModules X.scheme X.ring)
    (E.extension a) (E.extension b) (E.extension (a.comp b))
    a.pull b.pull (a.comp b).pull (E.restriction a) (E.restriction b)
    (E.restriction (a.comp b)) (a.pullComp b) (E.gamma a b) (hE.normalized a b) M

private def BinaryNormalized
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : B ⥤ C) (G : A ⥤ B) (H : A ⥤ C)
    (R : C ⥤ B) (S : B ⥤ A) (U : C ⥤ A)
    (rF : F ⋙ R ≅ 𝟭 B) (rG : G ⋙ S ≅ 𝟭 A) (rH : H ⋙ U ≅ 𝟭 A)
    (gamma : G ⋙ F ≅ H) (c : U ≅ R ⋙ S) : Prop :=
  ∀ M, U.map (gamma.hom.app M) ≫ rH.hom.app M =
    c.hom.app (F.obj (G.obj M)) ≫ S.map (rF.hom.app (G.obj M)) ≫ rG.hom.app M

private theorem normalization_transport
    {A B C : Type*} {I : Sort*} [Category A] [Category B] [Category C]
    (F : B ⥤ C) (G : A ⥤ B) (R : C ⥤ B) (S : B ⥤ A)
    (H : I → A ⥤ C) (U : I → C ⥤ A)
    (rF : F ⋙ R ≅ 𝟭 B) (rG : G ⋙ S ≅ 𝟭 A)
    (rH : ∀ i, H i ⋙ U i ≅ 𝟭 A)
    (i j : I) (h : i = j) (gamma : G ⋙ F ≅ H j) (c : U j ≅ R ⋙ S)
    (hn : BinaryNormalized F G (H j) R S (U j) rF rG (rH j) gamma c) :
    BinaryNormalized F G (H i) R S (U i) rF rG (rH i)
      (gamma ≪≫ eqToIso (congrArg H h.symm)) (eqToIso (congrArg U h) ≪≫ c) := by
  subst i
  simpa only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans] using hn

set_option maxHeartbeats 200000 in
-- Keep the comparison replacement separate from the equality transport.
private theorem chosen_normalized (E : LocallyClosedExtensionData.{u})
    (hE : E.Coherent) (D : E.DerivedCoherence) {T S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    BinaryNormalized (E.derived a) (E.derived b) (E.derived (a.comp b))
      a.pull.mapDerivedCategory b.pull.mapDerivedCategory (a.comp b).pull.mapDerivedCategory
      (D.restriction a) (D.restriction b) (D.restriction (a.comp b)) (D.gamma a b)
      (Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
        (Functor.mapDerivedCategoryCompIso a.pull b.pull).symm) := by
  exact normalization_congr
    (A := DerivedCategory (proEtaleRingModules T.scheme T.ring))
    (B := DerivedCategory (proEtaleRingModules S.scheme S.ring))
    (C := DerivedCategory (proEtaleRingModules X.scheme X.ring))
    (F := E.derived a) (G := E.derived b) (H := E.derived (a.comp b))
    (R := a.pull.mapDerivedCategory) (S := b.pull.mapDerivedCategory)
    (U := (a.comp b).pull.mapDerivedCategory)
    (rF := D.restriction a) (rF' := E.derivedRestriction a)
    (rG := D.restriction b) (rG' := E.derivedRestriction b)
    (rH := D.restriction (a.comp b)) (rH' := E.derivedRestriction (a.comp b))
    (c := Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
      (Functor.mapDerivedCategoryCompIso a.pull b.pull).symm)
    (gamma := D.gamma a b)
    (restriction_eq E D a) (restriction_eq E D b) (restriction_eq E D (a.comp b))
    rfl (gamma_eq E D a b) (canonical_normalized E hE a b)

-- The comparison involves many nested functor constructions.
private theorem derived_normalized (E : LocallyClosedExtensionData.{u})
    (hE : E.Coherent) (D : E.DerivedCoherence) {T S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (c : LocallyClosedCoefficientImmersion T X) (h : c = a.comp b) :
    BinaryNormalized (E.derived a) (E.derived b) (E.derived c)
      a.pull.mapDerivedCategory b.pull.mapDerivedCategory c.pull.mapDerivedCategory
      (D.restriction a) (D.restriction b) (D.restriction c)
      (D.gamma a b ≪≫ eqToIso (congrArg E.derived h.symm))
      (eqToIso (congrArg (fun z ↦ z.pull.mapDerivedCategory) h) ≪≫
        Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
        (Functor.mapDerivedCategoryCompIso a.pull b.pull).symm) := by
  exact normalization_transport
    (I := LocallyClosedCoefficientImmersion T X)
    (E.derived a) (E.derived b) a.pull.mapDerivedCategory b.pull.mapDerivedCategory
    (fun z ↦ E.derived z) (fun z ↦ z.pull.mapDerivedCategory)
    (D.restriction a) (D.restriction b) (fun z ↦ D.restriction z)
    c (a.comp b) h (D.gamma a b)
    (Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
      (Functor.mapDerivedCategoryCompIso a.pull b.pull).symm)
    (chosen_normalized E hE D a b)

private theorem inverse_square {C : Type*} [Category C] {W X V Y Z : C}
    (e : W ≅ X) (d : Y ≅ Z) (r : W ⟶ Y) (l₁ : X ⟶ V) (l₂ : V ⟶ Z)
    (h : e.inv ≫ r = l₁ ≫ l₂ ≫ d.inv) : e.hom ≫ l₁ ≫ l₂ = r ≫ d.hom := by
  have hh := congrArg (fun z ↦ e.hom ≫ z ≫ d.hom) h
  simpa [Category.assoc] using hh.symm

private theorem iso_transport_property
    {A B : Type*} {I : Sort*} [Category A] [Category B]
    (F : I → A ⥤ B) (G : A ⥤ B) (P : ∀ i, (F i ≅ G) → Prop)
    (i j : I) (h : i = j) (e : F j ≅ G) (he : P j e) :
    P i (eqToIso (congrArg F h) ≪≫ e) := by
  subst i
  simpa only [eqToIso_refl, Iso.refl_trans] using he

private theorem exchange_normalized {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX) :
    ExchangeModuleCompositionNormalized f g RZ RY RX cg cf
      (exchangeModuleComposition f g RZ RY RX cg cf) := by
  unfold exchangeModuleComposition
  exact (exchangeModuleComposition_existsUnique f g RZ RY RX cg cf).choose_spec.1

private def ringPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cc : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
    (hc : cc = proEtaleRingCompositeCoefficients f g RZ RY RX cg cf) :
    proEtaleRingModulePullback (f ≫ g) RZ RX cc ≅
      proEtaleRingModulePullback g RZ RY cg ⋙ proEtaleRingModulePullback f RY RX cf :=
  eqToIso (congrArg (proEtaleRingModulePullback (f ≫ g) RZ RX) hc) ≪≫
    exchangeModuleComposition f g RZ RY RX cg cf

private def RightCompNormalized {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cc : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
    (delta : proEtaleRingModuleDirectImage f RY RX cf ⋙
      proEtaleRingModuleDirectImage g RZ RY cg ≅
      proEtaleRingModuleDirectImage (f ≫ g) RZ RX cc) : Prop :=
  ∀ (N : proEtaleRingModules X RX) (V : Z.ProEt)
    (m : ((proEtaleRingModuleDirectImage f RY RX cf ⋙
      proEtaleRingModuleDirectImage g RZ RY cg).obj N).val.obj (Opposite.op V)),
    (delta.hom.app N).val.app (Opposite.op V) m =
      N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m

private def RingPullCompNormalized {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cc : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
    (e : proEtaleRingModulePullback (f ≫ g) RZ RX cc ≅
      proEtaleRingModulePullback g RZ RY cg ⋙ proEtaleRingModulePullback f RY RX cf) : Prop :=
  RightCompNormalized f g RZ RY RX cg cf cc
    (conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction g RZ RY cg).comp
        (proEtaleRingModuleAdjunction f RY RX cf))
      (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cc) e)

set_option maxHeartbeats 200000 in
-- Use the named normalization predicate before evaluating sections.
private theorem ringPullComp_normalized {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cc : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
    (hc : cc = proEtaleRingCompositeCoefficients f g RZ RY RX cg cf) :
    RingPullCompNormalized f g RZ RY RX cg cf cc
      (ringPullComp f g RZ RY RX cg cf cc hc) := by
  exact iso_transport_property
    (fun z ↦ proEtaleRingModulePullback (f ≫ g) RZ RX z)
    (proEtaleRingModulePullback g RZ RY cg ⋙ proEtaleRingModulePullback f RY RX cf)
    (RingPullCompNormalized f g RZ RY RX cg cf)
    cc (proEtaleRingCompositeCoefficients f g RZ RY RX cg cf) hc
    (exchangeModuleComposition f g RZ RY RX cg cf)
    (exchange_normalized f g RZ RY RX cg cf)

private def PushCompSquare
    {A B C Ab Bb Cb : Type*}
    [Category A] [Category B] [Category C] [Category Ab] [Category Bb] [Category Cb]
    (E0 : A ⥤ Ab) (E1 : B ⥤ Bb) (E2 : C ⥤ Cb)
    (R10 : B ⥤ A) (R21 : C ⥤ B) (R20 : C ⥤ A)
    (Rb10 : Bb ⥤ Ab) (Rb21 : Cb ⥤ Bb) (Rb20 : Cb ⥤ Ab)
    (r01 : R10 ⋙ E0 ≅ E1 ⋙ Rb10) (r12 : R21 ⋙ E1 ≅ E2 ⋙ Rb21)
    (r02 : R20 ⋙ E0 ≅ E2 ⋙ Rb20)
    (delta : R21 ⋙ R10 ≅ R20) (deltab : Rb21 ⋙ Rb10 ≅ Rb20) : Prop :=
  ∀ N, r01.hom.app (R21.obj N) ≫ Rb10.map (r12.hom.app N) ≫
      deltab.hom.app (E2.obj N) = E0.map (delta.hom.app N) ≫ r02.hom.app N

private def PushCompCompatible (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (delta : proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f) ⋙
      proEtaleRingModuleDirectImage g (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ Y) (G.coefficient Λ g) ≅
      proEtaleRingModuleDirectImage (f ≫ g) (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ X) (G.coefficient Λ (f ≫ g))) : Prop :=
  PushCompSquare
    (ModuleRingedComparison.equivalence Λ.X Z).functor
    (ModuleRingedComparison.equivalence Λ.X Y).functor
    (ModuleRingedComparison.equivalence Λ.X X).functor
    (lowerStar Λ.X g) (lowerStar Λ.X f) (lowerStar Λ.X (f ≫ g))
    (proEtaleRingModuleDirectImage g (scalarSixSectionRing Λ Z)
      (scalarSixSectionRing Λ Y) (G.coefficient Λ g))
    (proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
      (scalarSixSectionRing Λ X) (G.coefficient Λ f))
    (proEtaleRingModuleDirectImage (f ≫ g) (scalarSixSectionRing Λ Z)
      (scalarSixSectionRing Λ X) (G.coefficient Λ (f ≫ g)))
    (G.push Λ g) (G.push Λ f) (G.push Λ (f ≫ g)) (lowerStarComp Λ.X f g) delta

-- Use an abstract right compositor to avoid expanding its adjunction mate.
private theorem push_comp_from_right_normalized
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (delta : proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f) ⋙
      proEtaleRingModuleDirectImage g (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ Y) (G.coefficient Λ g) ≅
      proEtaleRingModuleDirectImage (f ≫ g) (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ X) (G.coefficient Λ (f ≫ g)))
    (hc : RightCompNormalized f g (scalarSixSectionRing Λ Z)
      (scalarSixSectionRing Λ Y) (scalarSixSectionRing Λ X)
      (G.coefficient Λ g) (G.coefficient Λ f) (G.coefficient Λ (f ≫ g)) delta) :
    PushCompCompatible G Λ f g delta := by
  intro N
  ext V m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  change (delta.hom.app
    ((ModuleRingedComparison.equivalence Λ.X X).functor.obj N)).val.app V
    (((G.push Λ f).hom.app N).val.app ((proEtaleBaseChange g).op.obj V)
      (((G.push Λ g).hom.app ((lowerStar Λ.X f).obj N)).val.app V m)) = _
  rw [G.pushNormalization Λ g ((lowerStar Λ.X f).obj N) V m]
  rw [G.pushNormalization Λ f N ((proEtaleBaseChange g).op.obj V) m]
  dsimp only [RightCompNormalized] at hc
  rw [hc]
  change _ = ((G.push Λ (f ≫ g)).hom.app N).val.app V
    (((lowerStarComp Λ.X f g).hom.app N).hom.hom.app V m)
  rw [G.pushNormalization, lowerStarComp_hom_app_hom]
  rfl

-- The comparison involves many nested functor constructions.
private def ForwardCompSquare
    {A B C Ab Bb Cb : Type*}
    [Category A] [Category B] [Category C] [Category Ab] [Category Bb] [Category Cb]
    (E0 : A ⥤ Ab) (E1 : B ⥤ Bb) (E2 : C ⥤ Cb)
    (L01 : A ⥤ B) (L12 : B ⥤ C) (L02 : A ⥤ C)
    (Lb01 : Ab ⥤ Bb) (Lb12 : Bb ⥤ Cb) (Lb02 : Ab ⥤ Cb)
    (c01 : L01 ⋙ E1 ≅ E0 ⋙ Lb01) (c12 : L12 ⋙ E2 ≅ E1 ⋙ Lb12)
    (c02 : L02 ⋙ E2 ≅ E0 ⋙ Lb02)
    (a : L02 ≅ L01 ⋙ L12) (ab : Lb02 ≅ Lb01 ⋙ Lb12) : Prop :=
  ∀ M, E2.map (a.hom.app M) ≫ c12.hom.app (L01.obj M) ≫
      Lb12.map (c01.hom.app M) = c02.hom.app M ≫ ab.hom.app (E0.obj M)

private theorem forward_comp_from_push
    {A B C Ab Bb Cb : Type*}
    [Category A] [Category B] [Category C] [Category Ab] [Category Bb] [Category Cb]
    (E0 : A ≌ Ab) (E1 : B ≌ Bb) (E2 : C ≌ Cb)
    {L01 : A ⥤ B} {R10 : B ⥤ A} {L12 : B ⥤ C} {R21 : C ⥤ B}
    {L02 : A ⥤ C} {R20 : C ⥤ A}
    {Lb01 : Ab ⥤ Bb} {Rb10 : Bb ⥤ Ab} {Lb12 : Bb ⥤ Cb} {Rb21 : Cb ⥤ Bb}
    {Lb02 : Ab ⥤ Cb} {Rb20 : Cb ⥤ Ab}
    (adj01 : L01 ⊣ R10) (adj12 : L12 ⊣ R21) (adj02 : L02 ⊣ R20)
    (adjb01 : Lb01 ⊣ Rb10) (adjb12 : Lb12 ⊣ Rb21) (adjb02 : Lb02 ⊣ Rb20)
    (r01 : R10 ⋙ E0.functor ≅ E1.functor ⋙ Rb10)
    (r12 : R21 ⋙ E1.functor ≅ E2.functor ⋙ Rb21)
    (r02 : R20 ⋙ E0.functor ≅ E2.functor ⋙ Rb20)
    (c01 : L01 ⋙ E1.functor ≅ E0.functor ⋙ Lb01)
    (c12 : L12 ⋙ E2.functor ≅ E1.functor ⋙ Lb12)
    (c02 : L02 ⋙ E2.functor ≅ E0.functor ⋙ Lb02)
    (h01 : (mateEquiv adj01 adjb01 c01.inv) = r01.hom)
    (h12 : (mateEquiv adj12 adjb12 c12.inv) = r12.hom)
    (h02 : (mateEquiv adj02 adjb02 c02.inv) = r02.hom)
    (delta : R21 ⋙ R10 ≅ R20)
    (a : L02 ≅ L01 ⋙ L12) (ab : Lb02 ≅ Lb01 ⋙ Lb12)
    (ha : conjugateIsoEquiv (adj01.comp adj12) adj02 a = delta)
    (hdelta : PushCompSquare E0.functor E1.functor E2.functor
      R10 R21 R20 Rb10 Rb21 Rb20 r01 r12 r02 delta
      (conjugateIsoEquiv (adjb01.comp adjb12) adjb02 ab)) :
    ForwardCompSquare E0.functor E1.functor E2.functor L01 L12 L02 Lb01 Lb12 Lb02
      c01 c12 c02 a ab := by
  intro M
  have he := equivalenceAdjunctionComparison_compositor E0 E1 E2
    adj01 adj12 adj02 adjb01 adjb12 adjb02 r01 r12 r02 c01 c12 c02 h01 h12 h02
    delta (conjugateIsoEquiv (adjb01.comp adjb12) adjb02 ab) hdelta a.symm ab.symm
    (congrArg Iso.inv ha) (by rfl) M
  exact inverse_square (E2.functor.mapIso (a.app M)) (ab.app (E0.functor.obj M))
    (c02.hom.app M) (c12.hom.app (L01.obj M)) (Lb12.map (c01.hom.app M)) he

private theorem ordinary_pull_comp (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    : ForwardCompSquare
      (ModuleRingedComparison.equivalence Λ.X Z).functor
      (ModuleRingedComparison.equivalence Λ.X Y).functor
      (ModuleRingedComparison.equivalence Λ.X X).functor
      (upperStar Λ.X g) (upperStar Λ.X f) (upperStar Λ.X (f ≫ g))
      (proEtaleRingModulePullback g (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ Y) (G.coefficient Λ g))
      (proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f))
      (proEtaleRingModulePullback (f ≫ g) (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ X) (G.coefficient Λ (f ≫ g)))
      (G.pull Λ g) (G.pull Λ f) (G.pull Λ (f ≫ g)) (upperStarComp Λ.X f g)
      (ringPullComp f g (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ g) (G.coefficient Λ f)
        (G.coefficient Λ (f ≫ g)) (coefficient_comp G Λ f g)) := by
  let c := ringPullComp f g (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y)
    (scalarSixSectionRing Λ X) (G.coefficient Λ g) (G.coefficient Λ f)
    (G.coefficient Λ (f ≫ g)) (coefficient_comp G Λ f g)
  let delta := conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction g (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y)
      (G.coefficient Λ g)).comp
      (proEtaleRingModuleAdjunction f (scalarSixSectionRing Λ Y) (scalarSixSectionRing Λ X)
        (G.coefficient Λ f)))
    (proEtaleRingModuleAdjunction (f ≫ g) (scalarSixSectionRing Λ Z)
      (scalarSixSectionRing Λ X) (G.coefficient Λ (f ≫ g))) c
  have hd : PushCompCompatible G Λ f g delta :=
    push_comp_from_right_normalized G Λ f g delta
      (ringPullComp_normalized f g (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ g) (G.coefficient Λ f)
        (G.coefficient Λ (f ≫ g)) (coefficient_comp G Λ f g))
  exact forward_comp_from_push
    (ModuleRingedComparison.equivalence Λ.X Z) (ModuleRingedComparison.equivalence Λ.X Y)
    (ModuleRingedComparison.equivalence Λ.X X)
    (upperStarLowerStarAdjunction Λ.X g) (upperStarLowerStarAdjunction Λ.X f)
    (upperStarLowerStarAdjunction Λ.X (f ≫ g))
    (proEtaleRingModuleAdjunction g _ _ (G.coefficient Λ g))
    (proEtaleRingModuleAdjunction f _ _ (G.coefficient Λ f))
    (proEtaleRingModuleAdjunction (f ≫ g) _ _ (G.coefficient Λ (f ≫ g)))
    (G.push Λ g) (G.push Λ f) (G.push Λ (f ≫ g))
    (G.pull Λ g) (G.pull Λ f) (G.pull Λ (f ≫ g))
    (G.pullNormalization Λ g) (G.pullNormalization Λ f) (G.pullNormalization Λ (f ≫ g))
    (lowerStarComp Λ.X f g) (upperStarComp Λ.X f g) c
    (conjugateIsoEquiv_upperStarComp Λ.X f g) hd

-- The comparison involves many nested functor constructions.
private theorem derived_forward_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits (F₀₁ ⋙ F₁₂)] [PreservesFiniteColimits (F₀₁ ⋙ F₁₂)]
  [PreservesFiniteLimits (G₀₁ ⋙ G₁₂)] [PreservesFiniteColimits (G₀₁ ⋙ G₁₂)]
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁)
    (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ForwardCompSquare U₀ U₁ U₂ F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ q₀₁ q₁₂ q₀₂ cF cG) :
    ForwardCompSquare U₀.mapDerivedCategory U₁.mapDerivedCategory U₂.mapDerivedCategory
      F₀₁.mapDerivedCategory F₁₂.mapDerivedCategory F₀₂.mapDerivedCategory
      G₀₁.mapDerivedCategory G₁₂.mapDerivedCategory G₀₂.mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso q₀₁) (Functor.mapDerivedCategorySquareIso q₁₂)
      (Functor.mapDerivedCategorySquareIso q₀₂)
      (Functor.mapDerivedCategoryNatIso cF ≪≫ (Functor.mapDerivedCategoryCompIso F₀₁ F₁₂).symm)
      (Functor.mapDerivedCategoryNatIso cG ≪≫
        (Functor.mapDerivedCategoryCompIso G₀₁ G₁₂).symm) := by
  intro K
  exact Functor.exactSquare_comp_forward F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂
    q₀₁ q₁₂ q₀₂ cF cG hq K

private theorem derived_pull_comp (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    : ForwardCompSquare
      (scalarSixForward Λ Z) (scalarSixForward Λ Y) (scalarSixForward Λ X)
      (scalarSixPull Λ g) (scalarSixPull Λ f) (scalarSixPull Λ (f ≫ g))
      (proEtaleRingModulePullback g (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ Y) (G.coefficient Λ g)).mapDerivedCategory
      (proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (G.coefficient Λ f)).mapDerivedCategory
      (proEtaleRingModulePullback (f ≫ g) (scalarSixSectionRing Λ Z)
        (scalarSixSectionRing Λ X) (G.coefficient Λ (f ≫ g))).mapDerivedCategory
      (scalarSixPullSection G Λ g) (scalarSixPullSection G Λ f)
      (scalarSixPullSection G Λ (f ≫ g)) (scalarSixPullComp Λ f g)
      (Functor.mapDerivedCategoryNatIso
        (ringPullComp f g (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) (G.coefficient Λ g) (G.coefficient Λ f)
          (G.coefficient Λ (f ≫ g)) (coefficient_comp G Λ f g)) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (proEtaleRingModulePullback g (scalarSixSectionRing Λ Z)
            (scalarSixSectionRing Λ Y) (G.coefficient Λ g))
          (proEtaleRingModulePullback f (scalarSixSectionRing Λ Y)
            (scalarSixSectionRing Λ X) (G.coefficient Λ f))).symm) := by
  have hd := derived_forward_comp
    (upperStar Λ.X g) (upperStar Λ.X f) (upperStar Λ.X (f ≫ g))
    (proEtaleRingModulePullback g _ _ (G.coefficient Λ g))
    (proEtaleRingModulePullback f _ _ (G.coefficient Λ f))
    (proEtaleRingModulePullback (f ≫ g) _ _ (G.coefficient Λ (f ≫ g)))
    (ModuleRingedComparison.equivalence Λ.X Z).functor
    (ModuleRingedComparison.equivalence Λ.X Y).functor
    (ModuleRingedComparison.equivalence Λ.X X).functor
    (G.pull Λ g) (G.pull Λ f) (G.pull Λ (f ≫ g)) (upperStarComp Λ.X f g)
    (ringPullComp f g (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y)
      (scalarSixSectionRing Λ X) (G.coefficient Λ g) (G.coefficient Λ f)
      (G.coefficient Λ (f ≫ g)) (coefficient_comp G Λ f g))
    (ordinary_pull_comp G Λ f g)
  exact hd

-- The comparison involves many nested functor constructions.
private theorem pullComp_transport (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (h : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g)) :
    Functor.mapDerivedCategoryNatIso
      (ringPullComp g.left f.left (scalarSixSectionRing Λ X.left)
        (scalarSixSectionRing Λ S.left) (scalarSixSectionRing Λ T.left)
        (G.coefficient Λ f.left) (G.coefficient Λ g.left)
        (G.coefficient Λ (g ≫ f).left) (coefficient_comp G Λ g.left f.left)) =
      eqToIso (congrArg (fun z ↦ z.pull.mapDerivedCategory) h) ≪≫
        Functor.mapDerivedCategoryNatIso
          ((scalarSixImmersion G Λ f).pullComp (scalarSixImmersion G Λ g)) := by
  have h' : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g) := h
  have hh : ringPullComp g.left f.left (scalarSixSectionRing Λ X.left)
      (scalarSixSectionRing Λ S.left) (scalarSixSectionRing Λ T.left)
      (G.coefficient Λ f.left) (G.coefficient Λ g.left)
      (G.coefficient Λ (g ≫ f).left) (coefficient_comp G Λ g.left f.left) =
    eqToIso (congrArg (fun z ↦ z.pull) h') ≪≫
      (scalarSixImmersion G Λ f).pullComp (scalarSixImmersion G Λ g) := by
    unfold ringPullComp LocallyClosedCoefficientImmersion.pullComp
    congr 1
  rw [hh]
  apply Iso.ext
  rw [Functor.mapDerivedCategoryNatIso_trans]
  rw [AlgebraicGeometry.Scheme.derived_eqToIso (fun z ↦ z.pull) h']
  rfl

-- The comparison involves many nested functor constructions.
private theorem transportComposition_forward
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    (eA : A ≌ A') (eB : B ≌ B') (eC : C ≌ C')
    (F : B' ⥤ C') (G : A' ⥤ B') (H : A' ⥤ C') (gamma : G ⋙ F ≅ H) (M : A) :
    eC.functor.map ((scalarSixTransportComposition eA eB eC F G H gamma).hom.app M) ≫
        eC.counitIso.hom.app (H.obj (eA.functor.obj M)) =
      eC.counitIso.hom.app (F.obj (eB.functor.obj (eB.inverse.obj (G.obj
        (eA.functor.obj M))))) ≫
        F.map (eB.counitIso.hom.app (G.obj (eA.functor.obj M))) ≫
        gamma.hom.app (eA.functor.obj M) := by
  simp only [scalarSixTransportComposition, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.map_comp, eC.fun_inv_map, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.id_obj]
  simp only [Equivalence.counitIso_inv_hom_id_app, Category.comp_id]

-- The comparison involves many nested functor constructions.
private theorem transport_normalized
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    (eA : A ≌ A') (eB : B ≌ B') (eC : C ≌ C')
    (F : B' ⥤ C') (G : A' ⥤ B') (H : A' ⥤ C')
    (R : C ⥤ B) (S : B ⥤ A) (U : C ⥤ A)
    (R' : C' ⥤ B') (S' : B' ⥤ A') (U' : C' ⥤ A')
    (dF : R ⋙ eB.functor ≅ eC.functor ⋙ R')
    (dG : S ⋙ eA.functor ≅ eB.functor ⋙ S')
    (dH : U ⋙ eA.functor ≅ eC.functor ⋙ U')
    (rF : F ⋙ R' ≅ 𝟭 B') (rG : G ⋙ S' ≅ 𝟭 A') (rH : H ⋙ U' ≅ 𝟭 A')
    (gamma : G ⋙ F ≅ H) (c : U ≅ R ⋙ S) (c' : U' ≅ R' ⋙ S')
    (hn : BinaryNormalized F G H R' S' U' rF rG rH gamma c')
    (hq : ForwardCompSquare eC.functor eB.functor eA.functor R S U R' S' U'
      dF dG dH c c')
    : BinaryNormalized
      (eB.functor ⋙ F ⋙ eC.inverse) (eA.functor ⋙ G ⋙ eB.inverse)
      (eA.functor ⋙ H ⋙ eC.inverse) R S U
      (scalarSixTransportRestriction eB eC F R R' dF rF)
      (scalarSixTransportRestriction eA eB G S S' dG rG)
      (scalarSixTransportRestriction eA eC H U U' dH rH)
      (scalarSixTransportComposition eA eB eC F G H gamma) c := by
  intro M
  apply eA.functor.map_injective
  simp only [Functor.map_comp, transportRestriction_forward]
  let N := (eB.functor ⋙ F ⋙ eC.inverse).obj ((eA.functor ⋙ G ⋙ eB.inverse).obj M)
  have ndH := dH.hom.naturality
    ((scalarSixTransportComposition eA eB eC F G H gamma).hom.app M)
  simp only [Functor.comp_map] at ndH
  simp only [Functor.comp_obj] at ndH
  rw [reassoc_of% ndH]
  rw [← U'.map_comp_assoc, transportComposition_forward]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  have nc := c'.hom.naturality
    (eC.counitIso.hom.app (F.obj (eB.functor.obj (eB.inverse.obj (G.obj (eA.functor.obj M))))))
  have nc' := c'.hom.naturality (F.map (eB.counitIso.hom.app (G.obj (eA.functor.obj M))))
  simp only [Functor.comp_map, Functor.comp_obj] at nc nc'
  rw [reassoc_of% nc', reassoc_of% nc]
  have hqN := hq N
  simp only [N, Functor.comp_obj] at hqN
  rw [← reassoc_of% hqN]
  have ndG := dG.hom.naturality
    ((scalarSixTransportRestriction eB eC F R R' dF rF).hom.app
      ((eA.functor ⋙ G ⋙ eB.inverse).obj M))
  simp only [Functor.comp_map, Functor.comp_obj] at ndG
  simp only [Functor.comp_obj]
  rw [reassoc_of% ndG, transportRestriction_forward, S'.map_comp, S'.map_comp]
  have nr := rF.hom.naturality (eB.counitIso.hom.app (G.obj (eA.functor.obj M)))
  simp only [Functor.comp_map, Functor.id_map] at nr
  have hnr := congrArg S'.map nr
  simp only [Functor.map_comp] at hnr
  rw [reassoc_of% hnr]
  simp only [Category.assoc]

private theorem iso_trans_assoc_congr
    {C : Type*} [Category C] {W X Y Z : C}
    {a : W ≅ Y} {b : W ≅ X} {c : X ≅ Y} (h : a = b ≪≫ c) (d : Y ≅ Z) :
    a ≪≫ d = b ≪≫ c ≪≫ d := by
  rw [h, Iso.trans_assoc]

private theorem forward_comp_congr
    {A B C Ab Bb Cb : Type*}
    [Category A] [Category B] [Category C] [Category Ab] [Category Bb] [Category Cb]
    (E0 : A ⥤ Ab) (E1 : B ⥤ Bb) (E2 : C ⥤ Cb)
    (L01 : A ⥤ B) (L12 : B ⥤ C) (L02 : A ⥤ C)
    (Lb01 : Ab ⥤ Bb) (Lb12 : Bb ⥤ Cb) (Lb02 : Ab ⥤ Cb)
    (c01 : L01 ⋙ E1 ≅ E0 ⋙ Lb01) (c12 : L12 ⋙ E2 ≅ E1 ⋙ Lb12)
    (c02 : L02 ⋙ E2 ≅ E0 ⋙ Lb02)
    (a : L02 ≅ L01 ⋙ L12) {ab ab' : Lb02 ≅ Lb01 ⋙ Lb12}
    (h : ab = ab')
    (hn : ForwardCompSquare E0 E1 E2 L01 L12 L02 Lb01 Lb12 Lb02 c01 c12 c02 a ab) :
    ForwardCompSquare E0 E1 E2 L01 L12 L02 Lb01 Lb12 Lb02 c01 c12 c02 a ab' := by
  cases h
  exact hn

private theorem scalar_pull_comp
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (h : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g))
    : ForwardCompSquare
      (scalarSixForward Λ X.left) (scalarSixForward Λ S.left) (scalarSixForward Λ T.left)
      (scalarSixPull Λ f.left) (scalarSixPull Λ g.left) (scalarSixPull Λ (g ≫ f).left)
      (scalarSixImmersion G Λ f).pull.mapDerivedCategory
      (scalarSixImmersion G Λ g).pull.mapDerivedCategory
      (scalarSixImmersion G Λ (g ≫ f)).pull.mapDerivedCategory
      (scalarSixPullSection G Λ f.left) (scalarSixPullSection G Λ g.left)
      (scalarSixPullSection G Λ (g ≫ f).left) (scalarSixPullComp Λ g.left f.left)
      (eqToIso (congrArg (fun z ↦ z.pull.mapDerivedCategory) h) ≪≫
        Functor.mapDerivedCategoryNatIso
          ((scalarSixImmersion G Λ f).pullComp (scalarSixImmersion G Λ g)) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (scalarSixImmersion G Λ f).pull (scalarSixImmersion G Λ g).pull).symm) := by
  have ht := pullComp_transport G Λ f g h
  simp only [Over.comp_left] at ht
  exact forward_comp_congr _ _ _ _ _ _ _ _ _ _ _ _ _
    (iso_trans_assoc_congr ht
      (Functor.mapDerivedCategoryCompIso
        (scalarSixImmersion G Λ f).pull (scalarSixImmersion G Λ g).pull).symm)
    (derived_pull_comp G Λ g.left f.left)

private theorem scalar_normalized
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {T S X : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) (g : T ⟶ S) [IsImmersion f.left] [IsImmersion g.left]
    (h : scalarSixImmersion G Λ (g ≫ f) =
      (scalarSixImmersion G Λ f).comp (scalarSixImmersion G Λ g))
    : BinaryNormalized
      (scalarSixExtension E G Λ f) (scalarSixExtension E G Λ g)
      (scalarSixExtension E G Λ (g ≫ f))
      (scalarSixPull Λ f.left) (scalarSixPull Λ g.left) (scalarSixPull Λ (g ≫ f).left)
      (scalarSixRestriction E D G Λ f) (scalarSixRestriction E D G Λ g)
      (scalarSixRestriction E D G Λ (g ≫ f))
      (scalarSixExtensionComp E D G Λ f g h) (scalarSixPullComp Λ g.left f.left) := by
  let a := scalarSixImmersion G Λ f
  let b := scalarSixImmersion G Λ g
  let c := scalarSixImmersion G Λ (g ≫ f)
  let cp := eqToIso (congrArg (fun z ↦ z.pull.mapDerivedCategory) h) ≪≫
    Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
    (Functor.mapDerivedCategoryCompIso a.pull b.pull).symm
  have hn := derived_normalized E hE D a b c h
  have hq := scalar_pull_comp G Λ f g h
  exact transport_normalized
    (scalarSixEquivalence Λ T.left) (scalarSixEquivalence Λ S.left)
    (scalarSixEquivalence Λ X.left) (E.derived a) (E.derived b) (E.derived c)
    (scalarSixPull Λ f.left) (scalarSixPull Λ g.left) (scalarSixPull Λ (g ≫ f).left)
    a.pull.mapDerivedCategory b.pull.mapDerivedCategory c.pull.mapDerivedCategory
    (scalarSixPullSection G Λ f.left) (scalarSixPullSection G Λ g.left)
    (scalarSixPullSection G Λ (g ≫ f).left)
    (D.restriction a) (D.restriction b) (D.restriction c)
    (D.gamma a b ≪≫ eqToIso (congrArg E.derived h.symm))
    (scalarSixPullComp Λ g.left f.left) cp hn hq

end AlgebraicGeometry.ProEtale.CondensedRing
