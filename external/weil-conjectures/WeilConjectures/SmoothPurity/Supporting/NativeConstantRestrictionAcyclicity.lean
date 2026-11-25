/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.SemilinearCompactSupportCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology

/-! # Direct-image acyclicity of native systems restricted to constant scalars

Source: Stacks Project, Cohomology on Sites, Tag 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures

namespace NativeConstantModel

universe c v w

private local instance sliceContinuous {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous K (coefficientSequenceTopology K) :=
  sequenceInclusion_continuous K n

private def sequenceRing {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    Sheaf (coefficientSequenceTopology K) RingCat.{w} :=
  ⟨(CategoryTheory.Prod.snd ℕ C).op ⋙ O.obj, by
    intro A
    apply sequence_isSheaf_of_slices
    intro n
    exact O.property A⟩

private theorem sequenceSheaf_iff {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Presheaf.IsSheaf (coefficientSequenceTopology K) P ↔
      ∀ n : ℕ, Presheaf.IsSheaf K ((Prod.sectR n C).op ⋙ P) := by
  have h : coefficientSequenceTopology K = verticalDiagramSiteTopology ℕ C K := by
    apply GrothendieckTopology.ext
    rfl
  rw [h]
  exact verticalDiagramSite_isSheaf_iff ℕ C K P

/-- Restriction of a product module to a vertical component. -/
private noncomputable def sequenceComponent
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : SheafOfModules.{w} (sequenceRing K O)) (j : ℕᵒᵖ) :
    SheafOfModules.{w} O where
  val := PresheafOfModules.pushforward₀Obj (Prod.sectR j.unop C)
    (sequenceRing K O).obj F.val
  isSheaf := (sequenceSheaf_iff K F.val.presheaf).1 F.isSheaf j.unop

set_option linter.unnecessarySimpa false in
/-- Horizontal structure map on the component modules. -/
private noncomputable def sequenceArrow
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : SheafOfModules.{w} (sequenceRing K O))
    {j k : ℕᵒᵖ} (a : j ⟶ k) :
    sequenceComponent K O F j ⟶ sequenceComponent K O F k where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := F.val.map (Prod.mkHom a.unop (𝟙 U.unop)).op
          map_add' := map_add _
          map_smul' := by
            intro r x
            have H := F.val.map_smul (Prod.mkHom a.unop (𝟙 U.unop)).op r x
            simpa [sequenceRing, CategoryTheory.Prod.snd] using H }
      naturality := by
        intro U V f
        ext x
        simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
        change F.val.map (Prod.mkHom a.unop (𝟙 V.unop)).op
          (F.val.map ((Prod.sectR j.unop C).op.map f) x) =
          F.val.map ((Prod.sectR k.unop C).op.map f)
            (F.val.map (Prod.mkHom a.unop (𝟙 U.unop)).op x)
        have H : ((Prod.sectR j.unop C).op.map f) ≫
            (Prod.mkHom a.unop (𝟙 V.unop)).op =
            (Prod.mkHom a.unop (𝟙 U.unop)).op ≫ (Prod.sectR k.unop C).op.map f := by
          apply Quiver.Hom.unop_inj
          ext <;> simp
        have HH := F.val.presheaf.congr_map H
        rw [Functor.map_comp, Functor.map_comp] at HH
        exact ConcreteCategory.congr_hom HH x }

/-- The functor restricting module sheaves to component modules. -/
private noncomputable def sequenceCurry
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    SheafOfModules.{w} (sequenceRing K O) ⥤ ℕᵒᵖ ⥤ SheafOfModules.{w} O where
  obj F :=
    { obj j := sequenceComponent K O F j
      map a := sequenceArrow K O F a
      map_id j := by
        ext U x
        change F.val.map (𝟙 (op (j.unop, U.unop))) x = x
        simp
      map_comp {j k l} a b := by
        ext U x
        change F.val.map (Prod.mkHom (a ≫ b).unop (𝟙 U.unop)).op x =
          F.val.map (Prod.mkHom b.unop (𝟙 U.unop)).op
            (F.val.map (Prod.mkHom a.unop (𝟙 U.unop)).op x)
        rw [← F.val.map_comp_apply]
        apply F.val.congr_map_apply
        apply Quiver.Hom.unop_inj
        ext <;> simp }
  map f :=
    { app j :=
        { val :=
            { app U := f.val.app ((Prod.sectR j.unop C).op.obj U)
              naturality a := f.val.naturality ((Prod.sectR j.unop C).op.map a) } }
      naturality := by
        intro j k a
        ext U x
        exact (PresheafOfModules.naturality_apply f.val (Prod.mkHom a.unop (𝟙 U.unop)).op x) }
  map_id F := by ext j U x; rfl
  map_comp f g := by ext j U x; rfl

/-- Assembly of presheaf modules along the two product coordinates. -/
private noncomputable def sequenceUncurryVal
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : ℕᵒᵖ ⥤ SheafOfModules.{w} O) :
    PresheafOfModules.{w} (sequenceRing K O).obj where
  obj X := (F.obj (op X.unop.1)).val.obj (op X.unop.2)
  map {X Y} f := (F.map f.unop.1.op).val.app (op X.unop.2) ≫
    (F.obj (op Y.unop.1)).val.map f.unop.2.op
  map_id X := by
    ext x
    simp [sequenceRing, CategoryTheory.Prod.snd]
  map_comp {X Y Z} f g := by
    ext x
    change (F.obj (op Z.unop.1)).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map (f.unop.1.op ≫ g.unop.1.op)).val.app (op X.unop.2)) x) =
      (F.obj (op Z.unop.1)).val.map g.unop.2.op
        (((F.map g.unop.1.op).val.app (op Y.unop.2))
          ((F.obj (op Y.unop.1)).val.map f.unop.2.op
            (((F.map f.unop.1.op).val.app (op X.unop.2)) x)))
    rw [F.map_comp]
    change (F.obj (op Z.unop.1)).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map g.unop.1.op).val.app (op X.unop.2))
        (((F.map f.unop.1.op).val.app (op X.unop.2)) x)) = _
    rw [PresheafOfModules.naturality_apply (F.map g.unop.1.op).val]
    exact (F.obj (op Z.unop.1)).val.map_comp_apply _ _ _

/-- Assembly of a diagram of module sheaves to a sheaf on the product site. -/
private noncomputable def sequenceUncurryObj
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : ℕᵒᵖ ⥤ SheafOfModules.{w} O) :
    SheafOfModules.{w} (sequenceRing K O) where
  val := sequenceUncurryVal K O F
  isSheaf := by
    apply (sequenceSheaf_iff K _).2
    intro j
    let e : (Prod.sectR j C).op ⋙ (sequenceUncurryVal K O F).presheaf ≅
        (F.obj (op j)).val.presheaf :=
      NatIso.ofComponents (fun U ↦ Iso.refl _) (by
        intro U V f
        ext x
        change (F.obj (op j)).val.map f
          (((F.map (𝟙 (op j))).val.app U) x) = (F.obj (op j)).val.map f x
        simp)
    exact (Presheaf.isSheaf_of_iso_iff e).2 (F.obj (op j)).isSheaf

/-- Assembly is functorial on module morphisms. -/
private noncomputable def sequenceUncurry
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    (ℕᵒᵖ ⥤ SheafOfModules.{w} O) ⥤ SheafOfModules.{w} (sequenceRing K O) where
  obj F := sequenceUncurryObj K O F
  map {F G} f :=
    { val :=
        { app X := (f.app (op X.unop.1)).val.app (op X.unop.2)
          naturality := by
            intro X Y a
            ext x
            change ((f.app (op Y.unop.1)).val.app (op Y.unop.2))
              (((F.obj (op Y.unop.1)).val.map a.unop.2.op)
                (((F.map a.unop.1.op).val.app (op X.unop.2)) x)) =
              ((G.obj (op Y.unop.1)).val.map a.unop.2.op)
                (((G.map a.unop.1.op).val.app (op X.unop.2))
                  (((f.app (op X.unop.1)).val.app (op X.unop.2)) x))
            rw [PresheafOfModules.naturality_apply (f.app (op Y.unop.1)).val]
            have H := congrArg (fun t ↦ t.val.app (op X.unop.2))
              (f.naturality a.unop.1.op)
            exact congrArg ((G.obj (op Y.unop.1)).val.map a.unop.2.op)
              (ConcreteCategory.congr_hom H x) } }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- A module-sheaf isomorphism from an isomorphism of its module presheaves. -/
private def sequenceIso {C : Type c} [Category.{v} C] {K : GrothendieckTopology C}
    {O : Sheaf K RingCat.{w}} {F G : SheafOfModules.{w} O}
    (e : F.val ≅ G.val) : F ≅ G where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id

/-- The explicit equivalence for modules on the vertical product site. -/
private noncomputable def sequenceEquivalence
    {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    SheafOfModules.{w} (sequenceRing K O) ≌ (ℕᵒᵖ ⥤ SheafOfModules.{w} O) where
  functor := sequenceCurry K O
  inverse := sequenceUncurry K O
  unitIso := NatIso.ofComponents (fun F ↦ sequenceIso
    (PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by
      intro X Y f
      ext x
      change F.val.map f x = F.val.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
        (F.val.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
      have H : f = (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op ≫
          (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op := by
        apply Quiver.Hom.unop_inj
        ext <;> simp
      exact (F.val.congr_map_apply H x).trans (F.val.map_comp_apply _ _ x)))) (by
    intro F G f
    ext X x
    rfl)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ sequenceIso (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      change (F.obj j).val.map f (((F.map (𝟙 j)).val.app U) x) =
        (F.obj j).val.map f x
      simp))) (by
      intro j k a
      ext U x
      change (F.obj k).val.map (𝟙 U) (((F.map a).val.app U) x) =
        ((F.map a).val.app U) x
      simp)) (by
    intro F G f
    ext j U x
    rfl)
  functor_unitIso_comp F := by
    ext j U x
    rfl

private theorem curry_evaluation {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) (n : ℕ) :
    sequenceCurry K O ⋙ (evaluation ℕᵒᵖ _).obj (op n) =
      SheafOfModules.pushforward.{w} (F := Prod.sectR n C)
        (J := K) (K := coefficientSequenceTopology K)
        (R := sequenceRing K O) (S := O) (𝟙 O) := rfl

private def sequenceCommRing {C : Type c} [Category.{v} C]
    (K : GrothendieckTopology C) (O : Sheaf K CommRingCat.{w}) :
    Sheaf (coefficientSequenceTopology K) CommRingCat.{w} :=
  ⟨(CategoryTheory.Prod.snd ℕ C).op ⋙ O.obj, by
    intro A
    apply sequence_isSheaf_of_slices
    intro n
    exact O.property A⟩

/-- Section maps with their target carrier fixed before specializing the ring. -/
private def moduleSectionMap
    {C : Type c} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    M.obj U → M.obj V := fun x ↦ M.map f x

private theorem moduleSectionMap_heq
    {C : Type c} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    HEq (moduleSectionMap M f) (fun x : M.obj U ↦ M.map f x) := by
  unfold moduleSectionMap
  rfl

attribute [local irreducible] constantSheaf Functor.leftAdjoint limit
  coefficientSequenceRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def quotient (X : Scheme.{u}) (n : ℕ) :
    coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X ⟶
      integralCoefficientCommRingSheaf l E X n :=
  (constantSheaf _ CommRingCat.{u + 1}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)))

private def quotientCone (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj
        (coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) ⟶
      coefficientSequenceCommRingSystem l E X :=
  NatTrans.ofOpSequence (quotient l E X) (by
    intro n
    apply (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
    simp only [Functor.map_comp, Functor.const_obj_map,
      coefficientSequenceCommRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    change integralConstantQuotientOfUniverses l E X n =
      integralConstantQuotientOfUniverses l E X (n + 1) ≫
        integralCoefficientSheafTransition l E X n
    have h := integralConstantQuotientOfUniverses_compatibility l E X n
    simp only [Functor.const_obj_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    exact (Category.id_comp _).symm.trans h)

private def scalarMap (X : Scheme.{u}) :
    sequenceCommRing (Scheme.ProEt.topology X)
        (coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) ⟶
      coefficientSequenceCommRingSheaf l E X where
  hom :=
    { app U := ((quotientCone l E X).app (op U.unop.1)).hom.app (op U.unop.2)
      naturality := by
        intro U V f
        have hn := congrArg (fun t ↦ t.hom.app (op U.unop.2))
          ((quotientCone l E X).naturality f.unop.1.op)
        change ((quotientCone l E X).app (op V.unop.1)).hom.app (op U.unop.2) =
          ((quotientCone l E X).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            ((coefficientSequenceCommRingSystem l E X).map f.unop.1.op).hom.app
              (op U.unop.2) at hn
        change (coefficients (ULift.{u + 1}
            (Padic.coefficientExtensionIntegers l E)) X).obj.map f.unop.2.op ≫
            ((quotientCone l E X).app (op V.unop.1)).hom.app (op V.unop.2) =
          ((quotientCone l E X).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            (((coefficientSequenceCommRingSystem l E X).map f.unop.1.op).hom.app
              (op U.unop.2) ≫
              ((coefficientSequenceCommRingSystem l E X).obj (op V.unop.1)).obj.map
                f.unop.2.op)
        rw [← Category.assoc, ← hn]
        exact ((quotientCone l E X).app (op V.unop.1)).hom.naturality f.unop.2.op }

private local instance geometricContinuous {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ProEtale.VaryingRing.baseChange g).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) :=
  ProEtale.VaryingRing.baseChange_continuous g

private def geometricMap
    (B : Type (u + 1)) [CommRing B] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    sequenceCommRing (Scheme.ProEt.topology Y) (coefficients B Y) ⟶
      ((ProEtale.VaryingRing.baseChange g).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (sequenceCommRing (Scheme.ProEt.topology X) (coefficients B X)) where
  hom := Functor.whiskerLeft (CategoryTheory.Prod.snd ℕ Y.ProEt).op
    (Scheme.proEtaleRingDirectImageMap g (coefficients B Y) (coefficients B X)
      (constantRingIso B g)).hom

private abbrev nativeRestriction (X : Scheme.{u}) :=
  coefficientSequenceRestriction.{u, u} l E X ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.restrictScalars.{u + 1}
        (integralConstantToCompletionOfUniverses.{u, u} l E X))

private abbrev nativeScalarRestriction (X : Scheme.{u}) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarMap l E X))

/-- Fix the integral scalar category in the type of the concrete tower functor. -/
private def nativeScalarTower (X : Scheme.{u}) :
    coefficientSequenceModules l E X ⥤
      ℕᵒᵖ ⥤ SheafOfModules.{u + 1} (integralConstantRingOfUniverses l E X) :=
  nativeScalarRestriction l E X ⋙
    sequenceCurry (Scheme.ProEt.topology X) (integralConstantRingOfUniverses l E X)

private theorem restriction_composite
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {A B D : Sheaf J RingCat.{w}} (c : A ⟶ B) (p : B ⟶ D) (q : A ⟶ D)
    (h : c ≫ p = q) :
    ∃ d : SheafOfModules.restrictScalars.{w} q ≅
        SheafOfModules.restrictScalars.{w} p ⋙ SheafOfModules.restrictScalars.{w} c,
      ∀ (M : SheafOfModules.{w} D) (U : Cᵒᵖ) (x : M.val.obj U),
        (d.hom.app M).val.app U x = x := by
  let d : SheafOfModules.restrictScalars.{w} q ≅
      SheafOfModules.restrictScalars.{w} p ⋙ SheafOfModules.restrictScalars.{w} c :=
    (SheafOfModules.pushforwardCongr.{w} (F := 𝟭 C) h).symm ≪≫
      (SheafOfModules.pushforwardComp.{w} (F := 𝟭 C) (G := 𝟭 C)
        (J := J) (K := J) (K' := J) (R := B) (S := A) (R' := D) c p).symm
  exact ⟨d, fun _ _ _ ↦ rfl⟩

private theorem restriction_push_heq
    {A B : Type*} [Category A] [Category B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (T : A ⥤ B) [T.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{u + 1}} {RY SY : Sheaf J RingCat.{u + 1}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj RX)
    (bB : SY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj SX)
    (h : bA ≫ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).map aX = aY ≫ bB) :
    ∃ d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bA ≅
        SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY,
      ∀ M U, HEq (fun x ↦ (d.hom.app M).val.app U x)
        (fun x : M.val.obj (T.op.obj U) ↦ x) := by
  let d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bA ≅
      SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY :=
    SheafOfModules.pushforwardComp (F := T) (G := 𝟭 B) bA aX ≪≫
      SheafOfModules.pushforwardCongr h ≪≫
        (SheafOfModules.pushforwardComp (F := 𝟭 A) (G := T) aY bB).symm
  exact ⟨d, fun _ _ ↦ heq_of_eq rfl⟩

private theorem restriction_trans_sections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {A B D : Sheaf J RingCat.{w}} (c : A ⟶ B) (p : B ⟶ D) (q : A ⟶ D)
    {Z : Type*} [Category Z] (F : Z ⥤ SheafOfModules.{w} D)
    {G : Z ⥤ SheafOfModules.{w} A}
    (d₁ : G ≅ F ⋙ SheafOfModules.restrictScalars.{w} q)
    (d₂ : SheafOfModules.restrictScalars.{w} q ≅
      SheafOfModules.restrictScalars.{w} p ⋙ SheafOfModules.restrictScalars.{w} c)
    (V : Z → Cᵒᵖ → Type w)
    (h₁ : ∀ M U, HEq (fun x ↦ (d₁.hom.app M).val.app U x) (fun x : V M U ↦ x))
    (h₂ : ∀ M U (x : M.val.obj U), (d₂.hom.app M).val.app U x = x) :
    ∀ M U, HEq (fun x ↦ ((d₁ ≪≫ Functor.isoWhiskerLeft F d₂).hom.app M).val.app U x)
      (fun x : V M U ↦ x) := by
  intro M U
  exact CompactSupportCondensedRealization.normalized_postcomp
    (fun x ↦ (d₁.hom.app M).val.app U x)
    (fun x ↦ (d₂.hom.app (F.obj M)).val.app U x)
    (h₁ M U) (h₂ (F.obj M) U)

private theorem restrictionLevel (X : Scheme.{u}) (n : ℕ) :
    ∃ d : (nativeScalarTower l E X) ⋙
            (evaluation ℕᵒᵖ _).obj (op n) ≅
        nativeRestriction l E X ⋙ (evaluation ℕᵒᵖ _).obj (op n),
      ∀ M U, HEq (fun x ↦ (d.hom.app M).val.app U x)
        (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  let J := Scheme.ProEt.topology X
  let S := (sheafCompose (coefficientSequenceTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X)
  let A := integralConstantRingOfUniverses l E X
  let a := (sheafCompose (coefficientSequenceTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarMap l E X)
  let q := integralConstantQuotientOfUniverses l E X n
  let p : completedIntegralCoefficientSheafUnrestricted l E X ⟶
      integralCoefficientSheaf l E X n :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
  let c := integralConstantToCompletionOfUniverses l E X
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm
  let ι := Prod.sectR n X.ProEt
  have he : (𝟙 A) ≫ (ι.sheafPushforwardContinuous RingCat.{u + 1} J
      (coefficientSequenceTopology J)).map a = q ≫ φ := by
    ext U x
    dsimp only [φ]
    change _ = ((eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm).hom.app U)
      ((q.hom.app U) x)
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  obtain ⟨d₁, hd₁⟩ := restriction_push_heq ι a q (𝟙 A) φ he
  have hcp : c ≫ p = q := by
    exact limit.lift_π (integralConstantConeOfUniverses l E X) (op n)
  obtain ⟨d₂, hd₂⟩ := restriction_composite c p q hcp
  let d := d₁ ≪≫ Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E X n) d₂
  have hd := restriction_trans_sections c p q (coefficientSequenceEvaluation l E X n)
    d₁ d₂ (fun M U ↦ M.val.obj (op (n, U.unop))) hd₁ hd₂
  have hF : (nativeScalarTower l E X) ⋙ (evaluation ℕᵒᵖ _).obj (op n) =
      nativeScalarRestriction l E X ⋙
        SheafOfModules.pushforward.{u + 1} (F := ι) (J := J)
          (K := coefficientSequenceTopology J)
          (R := sequenceRing J A) (S := A) (𝟙 A) :=
    (Functor.assoc (nativeScalarRestriction l E X) (sequenceCurry J A)
      ((evaluation ℕᵒᵖ _).obj (op n))).trans
        (congrArg (nativeScalarRestriction l E X ⋙ ·) (curry_evaluation J A n))
  have hR : nativeRestriction l E X ⋙ (evaluation ℕᵒᵖ _).obj (op n) =
      (coefficientSequenceEvaluation l E X n ⋙ SheafOfModules.restrictScalars.{u + 1} p) ⋙
        SheafOfModules.restrictScalars.{u + 1} c :=
    congrArg (· ⋙ SheafOfModules.restrictScalars.{u + 1} c)
      (coefficientSequenceRestriction_evaluation l E X n)
  exact CompactSupportCondensedRealization.iso_section_transport hF hR d
    (fun M U ↦ M.val.obj (op (n, U.unop))) hd

private theorem normalized_square
    {A B D E M N : Type w} (hA : A = M) (hB : B = N) (hD : D = M) (hE : E = N)
    (a : A → B) (b : B → E) (c : A → D) (d : D → E) (t : M → N)
    (ha : HEq a t) (hb : HEq b (fun x : N ↦ x))
    (hc : HEq c (fun x : M ↦ x)) (hd : HEq d t) :
    (fun x ↦ b (a x)) = (fun x ↦ d (c x)) := by
  subst A B D E
  rw [eq_of_heq ha, eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]

private theorem tower_section_type (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ) :
    ((((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.obj U : Type (u + 1)) =
      (M.val.obj (op (n, U.unop)) : Type (u + 1)) := by
  unfold coefficientSequenceRestriction
  exact congrArg (fun N : scalarReductionSource l E X ↦ (N.val.obj U : Type (u + 1)))
    ((coefficientSequenceRestriction_exists l E X).exists.choose_spec.1 M n)

private theorem tower_transition_sections (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (m n : ℕ) (h : n ≤ m) (U : X.ProEtᵒᵖ) :
    HEq (fun x : (((coefficientSequenceRestriction l E X).obj M).obj (op m)).val.obj U ↦
      ((((coefficientSequenceRestriction l E X).obj M).map (homOfLE h).op).val.app U) x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  unfold coefficientSequenceRestriction
  exact (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.1 M m n h U

private theorem scalar_section_type (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ) :
    ((((nativeScalarTower l E X).obj M).obj (op n)).val.obj U : Type (u + 1)) =
      (M.val.obj (op (n, U.unop)) : Type (u + 1)) := rfl

private theorem scalar_transition_sections (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (m n : ℕ) (h : n ≤ m) (U : X.ProEtᵒᵖ) :
    HEq (fun x ↦ ((((nativeScalarTower l E X).obj M).map
      (homOfLE h).op).val.app U) x)
      (moduleSectionMap M.val (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) := by
  unfold moduleSectionMap
  rfl

private theorem assemble_section_isos
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {D : Type*} [Category D] (A B : D ⥤ ℕᵒᵖ ⥤ SheafOfModules.{w} R)
    (V : D → ℕ → Cᵒᵖ → Type w)
    (t : ∀ M m n, n ≤ m → ∀ U, V M m U → V M n U)
    (hA : ∀ M n U, (((A.obj M).obj (op n)).val.obj U : Type w) = V M n U)
    (hB : ∀ M n U, (((B.obj M).obj (op n)).val.obj U : Type w) = V M n U)
    (htA : ∀ M m n (h : n ≤ m) U,
      HEq (fun x ↦ ((A.obj M).map (homOfLE h).op).val.app U x) (t M m n h U))
    (htB : ∀ M m n (h : n ≤ m) U,
      HEq (fun x ↦ ((B.obj M).map (homOfLE h).op).val.app U x) (t M m n h U))
    (d : ∀ n, A ⋙ (evaluation ℕᵒᵖ _).obj (op n) ≅
      B ⋙ (evaluation ℕᵒᵖ _).obj (op n))
    (hd : ∀ n M U, HEq (fun x ↦ ((d n).hom.app M).val.app U x)
      (fun x : V M n U ↦ x)) : Nonempty (A ≅ B) := by
  have hn (M : D) (m n : ℕ) (h : n ≤ m) :
      (A.obj M).map (homOfLE h).op ≫ (d n).hom.app M =
        (d m).hom.app M ≫ (B.obj M).map (homOfLE h).op := by
    ext U x
    exact congrFun (normalized_square (hA M m U) (hA M n U) (hB M m U) (hB M n U)
      (fun x ↦ ((A.obj M).map (homOfLE h).op).val.app U x)
      (fun x ↦ ((d n).hom.app M).val.app U x)
      (fun x ↦ ((d m).hom.app M).val.app U x)
      (fun x ↦ ((B.obj M).map (homOfLE h).op).val.app U x)
      (t M m n h U) (htA M m n h U) (hd n M U) (hd m M U) (htB M m n h U)) x
  have hn' (M : D) (m n : ℕᵒᵖ) (h : m ⟶ n) :
      (A.obj M).map h ≫ (d n.unop).hom.app M =
        (d m.unop).hom.app M ≫ (B.obj M).map h := by
    have hh : (homOfLE (leOfHom h.unop)).op = h := Subsingleton.elim _ _
    simpa only [hh] using hn M m.unop n.unop (leOfHom h.unop)
  obtain ⟨e, -⟩ := CompactSupportCondensedRealization.assemble_level_isos
    A B (fun n ↦ d n.unop) hn'
  exact ⟨e⟩

private theorem restrict_tower_section_type
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{w}} (a : R ⟶ S)
    (F : ℕᵒᵖ ⥤ SheafOfModules.{w} S) (n : ℕᵒᵖ) (U : Cᵒᵖ) :
    (((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.restrictScalars.{w} a)).obj F).obj n).val.obj U : Type w) =
      ((F.obj n).val.obj U : Type w) := rfl

private theorem restrict_tower_transition_sections_heq
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{w}} (a : R ⟶ S)
    (F : ℕᵒᵖ ⥤ SheafOfModules.{w} S) {m n : ℕᵒᵖ} (h : m ⟶ n) (U : Cᵒᵖ)
    {V W : Type w} (t : V → W)
    (ht : HEq (fun x ↦ (F.map h).val.app U x) t) :
    HEq (fun x ↦ (((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.restrictScalars.{w} a)).obj F).map h).val.app U) x) t := ht

private theorem native_tower_section_type (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ) :
    ((((nativeRestriction l E X).obj M).obj (op n)).val.obj U : Type (u + 1)) =
      (M.val.obj (op (n, U.unop)) : Type (u + 1)) :=
  (restrict_tower_section_type (integralConstantToCompletionOfUniverses l E X)
    ((coefficientSequenceRestriction l E X).obj M) (op n) U).trans
      (tower_section_type l E X M n U)

private theorem native_tower_transition_sections (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (m n : ℕ) (h : n ≤ m) (U : X.ProEtᵒᵖ) :
    HEq (fun x ↦ ((((nativeRestriction l E X).obj M).map
      (homOfLE h).op).val.app U) x)
      (moduleSectionMap M.val (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) :=
  restrict_tower_transition_sections_heq
    (integralConstantToCompletionOfUniverses l E X)
    ((coefficientSequenceRestriction l E X).obj M) (homOfLE h).op U _
    ((tower_transition_sections l E X M m n h U).trans
      (moduleSectionMap_heq M.val (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).symm)

private theorem restrictionTower (X : Scheme.{u}) :
    Nonempty (nativeScalarTower l E X ≅
        nativeRestriction l E X) := by
  let A := nativeScalarTower l E X
  let B := nativeRestriction l E X
  obtain ⟨d, hd⟩ := Classical.axiomOfChoice (restrictionLevel l E X)
  apply assemble_section_isos (R := integralConstantRingOfUniverses l E X) A B
    (fun M n U ↦ M.val.obj (op (n, U.unop)))
    (fun M _ _ h U ↦ moduleSectionMap M.val (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    (scalar_section_type l E X)
    (native_tower_section_type l E X)
    (scalar_transition_sections l E X)
    (native_tower_transition_sections l E X) d hd

private abbrev sequencePush (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1}
    (F := ProEtale.VaryingRing.baseChange g)
    (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (R := sequenceRing (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)))
    (S := sequenceRing (Scheme.ProEt.topology Y)
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B Y)))
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (geometricMap B g))

private theorem sequencePush_additive (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (sequencePush B g).Additive :=
  CompactSupportCondensedRealization.pushforward_additive_explicit.{u}
    (R := sequenceRing (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)))
    (S := sequenceRing (Scheme.ProEt.topology Y)
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B Y)))
    (ProEtale.VaryingRing.baseChange g)
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (geometricMap B g))

private def pushComparison (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    sequenceUncurry (Scheme.ProEt.topology X)
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)) ⋙
      sequencePush B g ≅
    towerDirectImage B g ⋙ sequenceUncurry (Scheme.ProEt.topology Y)
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B Y)) :=
  NatIso.ofComponents (fun M ↦ sequenceIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      rfl))) (by
    intro M N f
    ext U x
    rfl)

private local instance (priority := 100000) sequenceSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) := essentiallySmallSelf.{0, u, u + 1} _

private local instance sequenceAbSheafify (X : Scheme.{u}) :
    HasSheafify (coefficientSequenceTopology (Scheme.ProEt.topology X))
      AddCommGrpCat.{u + 1} :=
  SemilinearSections.abelianSheafify.{u + 1, u, u + 1} _

private local instance sequenceAbLocallyBijective (X : Scheme.{u}) :
    (coefficientSequenceTopology (Scheme.ProEt.topology X)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  SemilinearSections.locallyBijective.{u + 1, u, u + 1} _

private local instance (priority := 100000) siteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private local instance (priority := 100000) siteAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, 0} X

private local instance (priority := 100000) siteAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, 0} X

end NativeConstantModel

attribute [local instance 200000] SheafOfModules.instAbelian

attribute [local instance 100000] NativeConstantModel.sequenceSmall
  NativeConstantModel.sequenceAbSheafify NativeConstantModel.sequenceAbLocallyBijective
  NativeConstantModel.geometricContinuous NativeConstantModel.siteSmall
  NativeConstantModel.siteAbSheafify NativeConstantModel.siteAbLocallyBijective

/-- Whole-tower direct image preserves a K-injective resolution map of a native
K-injective system after restriction to constant integral scalars.

Source: Stacks Project, `sites-cohomology.tex`, Tag 0D6E,
`lemma-derived-pushforward-composition`, on the ringed sequence sites.
(blueprint: lem-pur-native-constant-restriction-acyclicity).

Proof: realize strict constant-ring towers as modules on the constant ringed
sequence site. The maps from constant integral scalars to the finite quotients
form a ring-sheaf map: the limit-cone equations identify the composite through
the completed coefficient sheaf with the actual constant quotient maps.
Under the sequence-site equivalence, restriction along this map is precisely
the displayed composite, on sections, horizontal transitions and module maps.
It is exact since restriction changes only scalar actions. Regard it as the
direct image r_* of the identity morphism of ringed topoi, and whole-tower
direct image as g_*. The normalized composition theorem identifies
Rg_* Rr_* with R(g r)_*. For a K-injective I, the units for r_* and (g r)_*
are invertible. Their composition-unit equation and exactness of r_* imply
that the unit for g_* on r_* I is invertible. For a K-injective resolution
j : r_* I ⟶ T, naturality of this unit, its invertibility on T, and invertibility
of Q(j) show that Q(g_* j) is invertible. Localization reflects quasi-isomorphisms,
so g_* j is a quasi-isomorphism. Transport through the exact sequence-site
equivalences, which preserve the sectionwise direct image and j, gives the claim.
This uses no preservation of K-injectivity by restriction. Empty schemes, zero
complexes and nonflat quotient maps satisfy the same argument. -/
theorem nativeConstantRestriction_push_quasiIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (I : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    [I.IsKInjective]
    (T : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) ℤ)
    [T.IsKInjective]
    (j : ((coefficientSequenceRestriction.{u, u} l E X ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (SheafOfModules.restrictScalars.{u + 1}
          (integralConstantToCompletionOfUniverses.{u, u} l E X))).mapHomologicalComplex
            (.up ℤ)).obj I ⟶ T) [QuasiIso j] :
    QuasiIso (((towerDirectImage
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).mapHomologicalComplex
        (.up ℤ)).map j) := by
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let H := NativeConstantModel.nativeRestriction l E X
  let G := towerDirectImage B g
  let r := NativeConstantModel.nativeScalarRestriction l E X
  let p := NativeConstantModel.sequencePush B g
  let eX := NativeConstantModel.sequenceEquivalence.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (integralConstantRingOfUniverses l E X)
  let eY := NativeConstantModel.sequenceEquivalence.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
    (integralConstantRingOfUniverses l E Y)
  let FA := eX.inverse
  let FB := eY.inverse
  let : FA.IsEquivalence := inferInstanceAs eX.inverse.IsEquivalence
  let : FB.IsEquivalence := inferInstanceAs eY.inverse.IsEquivalence
  let : FA.Additive := FA.additive_of_preserves_binary_products
  let : FB.Additive := FB.additive_of_preserves_binary_products
  let : FA.PreservesHomology := inferInstance
  let : FB.PreservesHomology := inferInstance
  let : FB.ReflectsIsomorphisms := inferInstance
  let : FA.PreservesKInjectiveComplexes := inferInstance
  let : p.Additive := NativeConstantModel.sequencePush_additive B g
  obtain ⟨d⟩ := NativeConstantModel.restrictionTower l E X
  let α : (𝟭 _) ⋙ r ≅ H ⋙ FA :=
    Functor.leftUnitor r ≪≫ (Functor.rightUnitor r).symm ≪≫
      Functor.isoWhiskerLeft r eX.unitIso ≪≫
        (Functor.associator r eX.functor FA).symm ≪≫ Functor.isoWhiskerRight d FA
  let β : FA ⋙ p ≅ G ⋙ FB := NativeConstantModel.pushComparison B g
  let : RepresentablyFlat (ProEtale.VaryingRing.baseChange g) := by
    let : RepresentablyFlat (Scheme.proEtaleBaseChange g) :=
      flat_of_preservesFiniteLimits _
    constructor
    intro U
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange g)).symm
  apply Scheme.quasiIso_map_of_models (𝟭 _) FA FB r p H G α β ?_ I T j
  intro I hI T hT j hj
  let : I.IsKInjective := hI
  let : T.IsKInjective := hT
  let : QuasiIso j := hj
  exact CompactSupportCondensedRealization.continuous_scalar_resolution.{u}
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (ProEtale.VaryingRing.baseChange g)
    (coefficientSequenceCommRingSheaf l E X)
    (NativeConstantModel.sequenceCommRing (Scheme.ProEt.topology X) (coefficients B X))
    (NativeConstantModel.sequenceCommRing (Scheme.ProEt.topology Y) (coefficients B Y))
    (NativeConstantModel.scalarMap l E X) (NativeConstantModel.geometricMap B g) I T j

end WeilConjectures
