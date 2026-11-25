/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRingModel

/-! # Ordinary restriction and direct image under a coefficient-ring presentation

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites,
Tag 0D6E; blueprint scalar direct-image proof, Formal properties.
(blueprint: def-sf-native-scalar-ordinary-restriction-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarRestriction
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale
open TwoSquare

universe v uC vC uD vD
section GenericRingTransport
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {RV A : Sheaf J RingCat.{u}} {RU B : Sheaf K RingCat.{u}}
  (i : RV ⟶ A) (j : RU ⟶ B)
  (a : RV ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj RU)
  (b : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
  (h : i ≫ b = a ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map j)

private def transport :
    SheafOfModules.pushforward.{v} b ⋙ SheafOfModules.pushforward (F := 𝟭 C) i ≅
      SheafOfModules.pushforward (F := 𝟭 D) j ⋙ SheafOfModules.pushforward a :=
  SheafOfModules.pushforwardComp.{v} (F := 𝟭 C) (G := F) i b ≪≫
    SheafOfModules.pushforwardCongr.{v} h ≪≫
      (SheafOfModules.pushforwardComp.{v} (F := F) (G := 𝟭 D) a j).symm

private theorem transport_apply (M : SheafOfModules.{v} B) (W : Cᵒᵖ)
    (m : M.val.obj (F.op.obj W)) :
    ((transport F i j a b h).hom.app M).val.app W m = m := by
  rfl

end GenericRingTransport

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def ringRestrictionOfIso (T : Scheme.{u})
    {R S A B : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    (a : R ⟶ S) (b : A ⟶ B) (i : R ≅ A) (j : S ≅ B)
    (h : a ≫ j.hom = i.hom ≫ b) :
    SheafOfModules.restrictScalars b ⋙
        (CondensedRing.ringModuleEquivalenceOfIso T i.symm).inverse ≅
      (CondensedRing.ringModuleEquivalenceOfIso T j.symm).inverse ⋙
        SheafOfModules.restrictScalars a := by
  exact transport (𝟭 T.ProEt) i.hom j.hom a b h.symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Comparing concrete section-module functors requires elaborating the site transports.
@[irreducible] private def ringPushforwardOfIso (R : PurCompactSupport.Coefficients.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
      InternalModuleOperations.ring Λ T)
    (hi : NativeScalarRingNaturality R Λ i)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    letI := InternalModuleOperations.siteMap_continuous g
    SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
        (InternalModuleOperations.coefficientMap Λ g) ⋙
      SheafOfModules.pushforward.{u + 1} (F := 𝟭 V.ProEt) (i V).hom ≅
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.ProEt) (i U).hom ⋙
      proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g) := by
  let := InternalModuleOperations.siteMap_continuous g
  let φ := (sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap g (R.ring V) (R.ring U) (R.pull g))
  have h : (i V).hom ≫ InternalModuleOperations.coefficientMap Λ g =
      φ ≫ ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology V) (ProEt.topology U)).map (i U).hom := by
    ext W r
    exact (hi g W r).symm
  change SheafOfModules.pushforward.{u + 1}
      (F := proEtaleBaseChange g) (InternalModuleOperations.coefficientMap Λ g) ⋙
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 _) (i V).hom ≅
      SheafOfModules.pushforward.{u + 1} (F := 𝟭 _) (i U).hom ⋙
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) φ
  exact transport (proEtaleBaseChange g) (i V).hom (i U).hom φ
    (InternalModuleOperations.coefficientMap Λ g) h
/-- The two ordinary condensed restrictions in order.
Source: blueprint scalar direct-image proof, Formal properties.
(blueprint: def-sf-native-scalar-ordinary-restriction-comparisons). -/
def ordinaryCompositeRestriction (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) T) ⥤
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T) :=
  Mod.comap (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T) ⋙
    Mod.comap (padicIntegersToPadicSubfield T l E)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def internalRestrictionSections
    (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    ordinaryCompositeRestriction l E T ⋙
        (InternalModuleOperations.equivalence (Profinite.padicIntegersRingObj l E.1) T).functor ≅
      (InternalModuleOperations.equivalence (Profinite.padicAlgClRingObj l) T).functor ⋙
        SheafOfModules.restrictScalars (nativeScalarSectionMap l E T) := by
  let φ := coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) T ≫
    coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T
  exact Functor.isoWhiskerRight
      (Mod.comapComp (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) T)
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T)).symm
      (InternalModuleOperations.equivalence (Profinite.padicIntegersRingObj l E.1) T).functor ≪≫
    CondensedRing.sectionModuleComapIso T φ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def inverseRestriction (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} {a : PurCompactSupport.Change R S}
    (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    ordinaryCompositeRestriction l E T ⋙ (P.integralEquivalence T).inverse ≅
      (P.closureEquivalence T).inverse ⋙ proEtaleRingRestrictScalars (a.map T) := by
  exact Functor.isoWhiskerRight (internalRestrictionSections l E T)
      (CondensedRing.ringModuleEquivalenceOfIso T (P.integral T).symm).inverse ≪≫
    Functor.isoWhiskerLeft
      (InternalModuleOperations.equivalence (Profinite.padicAlgClRingObj l) T).functor
      (ringRestrictionOfIso T ((adicLisseForget T).map (a.map T))
        (nativeScalarSectionMap l E T) (P.integral T) (P.closure T) (P.scalar T))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def inversePushforward (R : PurCompactSupport.Coefficients.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
      InternalModuleOperations.ring Λ T)
    (hi : NativeScalarRingNaturality R Λ i)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    CondensedRing.lowerStar Λ g ⋙
        ((CondensedRing.ringModuleEquivalenceOfIso V (i V).symm).trans
          (InternalModuleOperations.equivalence Λ V).symm).inverse ≅
      ((CondensedRing.ringModuleEquivalenceOfIso U (i U).symm).trans
          (InternalModuleOperations.equivalence Λ U).symm).inverse ⋙
        proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g) :=
  Functor.isoWhiskerRight (InternalModuleOperations.lowerComparison Λ g)
    (CondensedRing.ringModuleEquivalenceOfIso V (i V).symm).inverse ≪≫
  Functor.isoWhiskerLeft (InternalModuleOperations.equivalence Λ U).functor
    (ringPushforwardOfIso R Λ i hi g)

/-- The composite ordinary restriction/direct-image comparison.
Source: blueprint scalar direct-image proof, Formal properties.
(blueprint: def-sf-native-scalar-ordinary-restriction-comparisons). -/
def ordinaryCompositeSquare (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {U V : Scheme.{u}} (g : U ⟶ V) :
    CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g ⋙
        ordinaryCompositeRestriction l E V ≅
      ordinaryCompositeRestriction l E U ⋙
        CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g :=
  Functor.isoWhiskerRight
    (CondensedRing.comapLowerStarIso (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g)
    (Mod.comap (padicIntegersToPadicSubfield V l E)) ≪≫
  Functor.isoWhiskerLeft
    (Mod.comap (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) U))
    (CondensedRing.comapLowerStarIso (padicIntegersRingObjToContinuousMapRingObj l E) g)

private theorem ringRestrictionOfIso_apply (T : Scheme.{u})
    {R S A B : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    (a : R ⟶ S) (b : A ⟶ B) (i : R ≅ A) (j : S ≅ B)
    (h : a ≫ j.hom = i.hom ≫ b) (M : SheafOfModules.{u + 1} B)
    (W : T.ProEtᵒᵖ) (m : M.val.obj W) :
    ((ringRestrictionOfIso T a b i j h).hom.app M).val.app W m = m := by
  unfold ringRestrictionOfIso
  exact transport_apply (𝟭 T.ProEt) i.hom j.hom a b h.symm M W m

private theorem internalRestrictionSections_apply
    (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T))
    (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W) :
    ((internalRestrictionSections l E T).hom.app M).val.app W m = m := by
  unfold internalRestrictionSections
  rfl

private theorem inverseRestriction_apply (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {R S : PurCompactSupport.Coefficients.{u}}
    {a : PurCompactSupport.Change R S} (P : NativeScalarRingModel l E a) (T : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T))
    (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W) :
    ((inverseRestriction l E P T).hom.app M).val.app W m = m := by
  unfold inverseRestriction
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change ((ringRestrictionOfIso T ((adicLisseForget T).map (a.map T))
    (nativeScalarSectionMap l E T) (P.integral T) (P.closure T) (P.scalar T)).hom.app
    ((InternalModuleOperations.equivalence (Profinite.padicAlgClRingObj l) T).functor.obj M)
    ).val.app W (((internalRestrictionSections l E T).hom.app M).val.app W m) = m
  erw [ringRestrictionOfIso_apply, internalRestrictionSections_apply]

private theorem inversePushforward_apply (R : PurCompactSupport.Coefficients.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
      InternalModuleOperations.ring Λ T)
    (hi : NativeScalarRingNaturality R Λ i)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (W : V.ProEtᵒᵖ) (m : M.X.obj.obj ((proEtaleBaseChange g).op.obj W)) :
    ((inversePushforward R Λ i hi g).hom.app M).val.app W m = m := by
  unfold inversePushforward
  dsimp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change ((ringPushforwardOfIso R Λ i hi g).hom.app
    ((InternalModuleOperations.equivalence Λ U).functor.obj M)).val.app W
      (((InternalModuleOperations.lowerComparison Λ g).hom.app M).val.app W m) = m
  erw [(InternalModuleOperations.lowerComparison_existsUnique Λ g).exists.choose_spec M W m]
  unfold ringPushforwardOfIso
  exact transport_apply (proEtaleBaseChange g) (i V).hom (i U).hom _ _ _
    ((InternalModuleOperations.equivalence Λ U).functor.obj M) W m

private theorem ordinaryCompositeSquare_apply (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {U V : Scheme.{u}} (g : U ⟶ V)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (W : V.ProEtᵒᵖ) (m : M.X.obj.obj ((proEtaleBaseChange g).op.obj W)) :
    ((ordinaryCompositeSquare l E g).hom.app M).hom.hom.app W m = m := by
  rfl

end WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarRestriction
