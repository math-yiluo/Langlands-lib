/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels

/-! # Ordinary direct image of strict coefficient systems

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, on sequence ringed topoi.
(blueprint: lem-pur-completed-coefficient-ordinary-strict-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w a av b bv r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary strict direct image and its comparison with completed-module towers.
No derived functor, resolution or acyclicity assertion is included.
Source: Zheng, Construction 4.1; Stacks Project, Tag 03DA
(blueprint: def-pur-completed-coefficient-ordinary-strict-image-data). -/
structure OrdinaryStrictImageData {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) where
  systemPush : Systems l E X ⥤ Systems l E Y
  [systemPushAdditive : systemPush.Additive]
  systemPushEvaluation : ∀ n,
    systemPush ⋙
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology Y)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
        model l E Y n (C.target.finiteIso n) ≅
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          model l E X n (C.source.finiteIso n) ⋙ push f (finiteStructure l E f n)
  systemPushEvaluation_identity : ∀ n,
    IsSectionwiseIdentity Y (N l E Y n) (systemPushEvaluation n).hom
  diagramOrdinary : systemPush ⋙ C.target.systemRestriction ≅
    C.source.systemRestriction ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap)
  diagramOrdinary_identity : ∀ (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((C.target.systemRestriction.obj (systemPush.obj M)).obj (op n)).val.obj U),
      HEq ((((diagramOrdinary.hom.app M).app (op n)).val.app U) x) x

attribute [instance] OrdinaryStrictImageData.systemPushAdditive

private instance coefficientSheafify (W : Scheme.{t}) :
    HasSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  integralCoefficientRingSheafify.{t, u} W

private def commConstantPush {X Y : Scheme.{t}} (f : X ⟶ Y)
    (B : CommRingCat.{max u (t + 1)}) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj B ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj B) :=
  ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj B) _).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)))

private theorem constantPush_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {B D : CommRingCat.{max u (t + 1)}} (h : B ⟶ D) :
    (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map h) ≫
        constantPush.{t, u} f D =
      constantPush.{t, u} f B ≫ (ringPush.{t, u} f).map
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map h)) := by
  have hc : (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map h ≫
      commConstantPush f D = commConstantPush f B ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map h) := by
    apply (Adjunction.homEquiv_naturality_right_square_iff
      (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)})
      ((Functor.const Y.ProEtᵒᵖ).map h) _ _ _).mpr
    apply NatTrans.ext
    funext U
    exact congrArg (fun k ↦ k.app ((proEtaleBaseChange f).op.obj U))
      (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map h))
  have hh := congrArg ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map) hc
  ext U x
  exact congrArg (fun z ↦ z.hom.app U x) hh

private abbrev quotientRing (n : ℕ) : CommRingCat.{max u (t + 1)} :=
  CommRingCat.of (systemRing.{t, u} l E ⧸
    (Ideal.span ({systemUniformizer.{t, u} l E} : Set (systemRing.{t, u} l E))) ^ (n + 1))

private abbrev modelTransition (W : Scheme.{t}) (n : ℕ) :
    modelRing l E W (n + 1) ⟶ modelRing l E W n :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (SheafOfModules.coefficientQuotientMap (J := ProEt.topology W)
        (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) (Nat.le_succ n))

private def modelStructure {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    modelRing l E Y n ⟶ (ringPush.{t, u} f).obj (modelRing l E X n) :=
  constantPush.{t, u} f (quotientRing.{t, u} l E n)

private theorem modelStructure_transition {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    modelStructure l E f (n + 1) ≫ (ringPush.{t, u} f).map (modelTransition l E X n) =
      modelTransition l E Y n ≫ modelStructure l E f n :=
  (constantPush_naturality.{t, u} f
    (show quotientRing.{t, u} l E (n + 1) ⟶ quotientRing.{t, u} l E n from
      CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1))))).symm

private abbrev modelPush {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    Mod X (modelRing l E X n) ⥤ Mod Y (modelRing l E Y n) :=
  push f (modelStructure l E f n)

private def restrictionPushIso
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (F : A ⥤ B) [F.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{r}} {RY SY : Sheaf J RingCat.{r}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj RX)
    (bB : SY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj SX)
    (h : bA ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map aX = aY ≫ bB) :
    SheafOfModules.restrictScalars.{w} aX ⋙ SheafOfModules.pushforward bA ≅
      SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY :=
  SheafOfModules.pushforwardComp (F := F) (G := 𝟭 B) (J := J) (K := K) (K' := K)
      bA aX ≪≫
    SheafOfModules.pushforwardCongr h ≪≫
    (SheafOfModules.pushforwardComp (F := 𝟭 A) (G := F) (J := J) (K := J) (K' := K)
      aY bB).symm

private theorem restrictionPushIso_hom
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (F : A ⥤ B) [F.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{r}} {RY SY : Sheaf J RingCat.{r}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj RX)
    (bB : SY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj SX)
    (h : bA ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map aX = aY ≫ bB)
    (M : SheafOfModules.{w} SX) (U : Aᵒᵖ) (x : M.val.obj (F.op.obj U)) :
    ((restrictionPushIso F aX aY bA bB h).hom.app M).val.app U x = x := rfl

private theorem restrictionPushIso_inv
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (F : A ⥤ B) [F.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{r}} {RY SY : Sheaf J RingCat.{r}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj RX)
    (bB : SY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj SX)
    (h : bA ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map aX = aY ≫ bB)
    (M : SheafOfModules.{w} SX) (U : Aᵒᵖ) (x : M.val.obj (F.op.obj U)) :
    ((restrictionPushIso F aX aY bA bB h).inv.app M).val.app U x = x := rfl

attribute [local irreducible] SheafOfModules.coefficientQuotientSheaf
  SheafOfModules.coefficientQuotientMap integralCoefficientSheaf modelStructure

private def modelPushRestriction {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    SheafOfModules.coefficientRestriction.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) (Nat.le_succ n) ⋙
      modelPush l E f (n + 1) ≅
    modelPush l E f n ⋙
      SheafOfModules.coefficientRestriction.{t + 1, t, max u (t + 1)}
        (J := ProEt.topology Y) (systemRing.{t, u} l E)
        (systemUniformizer.{t, u} l E) (Nat.le_succ n) :=
  restrictionPushIso (proEtaleBaseChange f) (modelTransition l E X n)
    (modelTransition l E Y n) (modelStructure l E f (n + 1)) (modelStructure l E f n)
    (modelStructure_transition l E f n)

private def restrictedSections
    {A : Type a} [Category.{av} A] {J : GrothendieckTopology A}
    {R S : Sheaf J RingCat.{r}} (c : R ⟶ S)
    {M : SheafOfModules.{w} R} {N : SheafOfModules.{w} S}
    (h : M ⟶ (SheafOfModules.restrictScalars c).obj N) (U : Aᵒᵖ) :
    M.val.obj U → N.val.obj U := fun x ↦ h.val.app U x

private theorem restrictedSections_heq
    {A : Type a} [Category.{av} A] {J : GrothendieckTopology A}
    {R S : Sheaf J RingCat.{r}} (c : R ⟶ S)
    {M : SheafOfModules.{w} R} {N : SheafOfModules.{w} S}
    (h : M ⟶ (SheafOfModules.restrictScalars c).obj N) (U : Aᵒᵖ) :
    HEq (fun x ↦ h.val.app U x) (restrictedSections c h U) := HEq.rfl

section SystemAssembly

variable {A : Type a} [Category.{av} A] {J : GrothendieckTopology A}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  {B : Type b} [Category.{bv} B] {K : GrothendieckTopology B}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}]
  {O : Type w} [CommRing O] {ell : O}
  (F : ∀ n, SheafOfModules.coefficientLevelModules (J := K) O ell n ⥤
    SheafOfModules.coefficientLevelModules (J := J) O ell n)
  (e : ∀ n, SheafOfModules.coefficientRestriction (J := K) O ell (Nat.le_succ n) ⋙
    F (n + 1) ≅ F n ⋙
      SheafOfModules.coefficientRestriction (J := J) O ell (Nat.le_succ n))

private theorem genericSystemHom_ext
    {M N : SheafOfModules.CoefficientSystem (J := J) O ell}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def assembleSystemPush :
    SheafOfModules.CoefficientSystem (J := K) O ell ⥤
      SheafOfModules.CoefficientSystem (J := J) O ell where
  obj M := {
    level := fun n ↦ (F n).obj (M.level n)
    transition := fun n ↦ (F (n + 1)).map (M.transition n) ≫ (e n).hom.app (M.level n) }
  map {M N} h := {
    app := fun n ↦ (F n).map (h.app n)
    comm := by
      intro n
      dsimp
      rw [← Category.assoc, ← Functor.map_comp, h.comm, Functor.map_comp, Category.assoc]
      exact congrArg ((F (n + 1)).map (M.transition n) ≫ ·)
        ((e n).hom.naturality (h.app n)) }
  map_id M := by
    apply genericSystemHom_ext
    funext n
    exact (F n).map_id _
  map_comp h k := by
    apply genericSystemHom_ext
    funext n
    exact (F n).map_comp _ _

private instance assembleSystemPush_additive [∀ n, (F n).Additive] :
    (assembleSystemPush F e).Additive where
  map_add {M N} h k := by
    apply genericSystemHom_ext
    funext n
    change (F n).map ((SheafOfModules.coefficientEvaluation (J := K) n).map (h + k)) =
      (SheafOfModules.coefficientEvaluation (J := J) n).map
        ((assembleSystemPush F e).map h + (assembleSystemPush F e).map k)
    simp only [Functor.map_add]
    rfl

private def assembleSystemPushEvaluation (n : ℕ) :
    assembleSystemPush F e ⋙
      SheafOfModules.coefficientEvaluation (J := J) (O := O) (ell := ell) n ≅
    SheafOfModules.coefficientEvaluation (J := K) (O := O) (ell := ell) n ⋙ F n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

private def transitionSections
    (M : SheafOfModules.CoefficientSystem (J := J) O ell) (n : ℕ) (U : Aᵒᵖ) :
    (M.level (n + 1)).val.obj U → (M.level n).val.obj U :=
  restrictedSections
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
      (SheafOfModules.coefficientQuotientMap O ell (Nat.le_succ n)))
    (M.transition n) U

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem transitionSections_heq
    (M : SheafOfModules.CoefficientSystem (J := J) O ell) (n : ℕ) (U : Aᵒᵖ) :
    HEq (fun x ↦ (M.transition n).val.app U x) (transitionSections M n U) :=
  restrictedSections_heq _ (M.transition n) U

end SystemAssembly

attribute [local irreducible] transitionSections

private instance modelPush_additive {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (modelPush l E f n).Additive where
  map_add := by intros; rfl

private def strictPush {X Y : Scheme.{t}} (f : X ⟶ Y) :
    Systems l E X ⥤ Systems l E Y :=
  assembleSystemPush (J := ProEt.topology Y) (K := ProEt.topology X)
    (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E)
    (fun n ↦ modelPush l E f n) (modelPushRestriction l E f)

private instance strictPush_additive {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (strictPush l E f).Additive :=
  assembleSystemPush_additive (J := ProEt.topology Y) (K := ProEt.topology X)
    (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E)
    (fun n ↦ modelPush l E f n) (modelPushRestriction l E f)

private theorem strictPush_transition {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((strictPush l E f).obj M).level (n + 1) |>.val.obj U) :
    (((strictPush l E f).obj M).transition n).val.app U x =
      (M.transition n).val.app ((proEtaleBaseChange f).op.obj U) x := by
  change ((modelPushRestriction l E f n).hom.app (M.level n)).val.app U
    ((M.transition n).val.app ((proEtaleBaseChange f).op.obj U) x) = _
  exact restrictionPushIso_hom (proEtaleBaseChange f) (modelTransition l E X n)
    (modelTransition l E Y n) (modelStructure l E f (n + 1)) (modelStructure l E f n)
    (modelStructure_transition l E f n) (M.level n) U _

private def finiteCoefficientEquiv (n : ℕ) :
    quotientRing.{t, u} l E n ≃+* ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)) :=
  (Ideal.quotientEquiv _ (Padic.coefficientExtensionIdeal l E (n + 1))
    ULift.ringEquiv (by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
      rfl)).trans ULift.ringEquiv.symm

attribute [local semireducible] SheafOfModules.coefficientQuotientSheaf
  integralCoefficientSheaf

private def finiteCoefficientIso (W : Scheme.{t}) (n : ℕ) :
    modelRing l E W n ≅ N l E W n :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).mapIso
        (finiteCoefficientEquiv.{t, u} l E n).toCommRingCatIso)

private theorem finiteIso_eq (W : Scheme.{t}) (S : SiteCoefficientData l E W) (n : ℕ) :
    S.finiteIso n = finiteCoefficientIso.{t, u} l E W n := by
  apply Iso.ext
  let V := sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let g := V.preimage (S.finiteIso n).hom
  have hg : V.map g = (S.finiteIso n).hom := V.map_preimage _
  suffices g = (constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).map
      (finiteCoefficientEquiv.{t, u} l E n).toCommRingCatIso.hom by
    rw [← hg, this]
    rfl
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology W) _ _
    ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).property
  ext U x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hh := S.finiteIso_generator n U a
  rw [← hg] at hh
  exact hh.trans (congrArg (fun k ↦ k.app U (Ideal.Quotient.mk _ a))
    (toSheafify_naturality (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map
        (finiteCoefficientEquiv.{t, u} l E n).toCommRingCatIso.hom)))

private theorem modelStructure_finite {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (n : ℕ) :
    (C.target.finiteIso n).inv ≫ modelStructure l E f n =
      finiteStructure l E f n ≫ (ringPush.{t, u} f).map (C.source.finiteIso n).inv := by
  unfold modelStructure
  rw [finiteIso_eq l E Y C.target.toSiteCoefficientData,
    finiteIso_eq l E X C.source.toSiteCoefficientData]
  apply (cancel_epi (finiteCoefficientIso.{t, u} l E Y n).hom).mp
  apply (cancel_mono ((ringPush.{t, u} f).map (finiteCoefficientIso.{t, u} l E X n).hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    Iso.inv_hom_id]
  exact (constantPush_naturality f (finiteCoefficientEquiv.{t, u} l E n).toCommRingCatIso.hom).symm

attribute [local irreducible] SheafOfModules.coefficientQuotientSheaf
  finiteCoefficientIso

private def strictPushEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    strictPush l E f ⋙
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)}
        (J := ProEt.topology Y) (O := systemRing.{t, u} l E)
        (ell := systemUniformizer.{t, u} l E) n ≅
    SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)}
        (J := ProEt.topology X) (O := systemRing.{t, u} l E)
        (ell := systemUniformizer.{t, u} l E) n ⋙ modelPush l E f n :=
  assembleSystemPushEvaluation (J := ProEt.topology Y) (K := ProEt.topology X)
    (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E)
    (fun n ↦ modelPush l E f n) (modelPushRestriction l E f) n

private theorem strictPush_section_type {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    ((((strictPush l E f).obj M).level n).val.obj U : Type (max u (t + 1))) =
      ((M.level n).val.obj ((proEtaleBaseChange f).op.obj U) : Type (max u (t + 1))) := rfl

private theorem strictPush_transition_heq {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ (((strictPush l E f).obj M).transition n).val.app U x)
      (fun x : (M.level (n + 1)).val.obj ((proEtaleBaseChange f).op.obj U) ↦
        (M.transition n).val.app ((proEtaleBaseChange f).op.obj U) x) :=
  heq_of_eq (funext (strictPush_transition l E f M n U))

private theorem strictPushEvaluation_identity {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : (((strictPush l E f).obj M).level n).val.obj U) :
    HEq (((strictPushEvaluation l E f n).hom.app M).val.app U x) x := HEq.rfl

attribute [local irreducible] strictPush

private def pushEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (n : ℕ) :
    strictPush l E f ⋙
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology Y)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
      model l E Y n (C.target.finiteIso n) ≅
    SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
      model l E X n (C.source.finiteIso n) ⋙ push f (finiteStructure l E f n) :=
  Functor.isoWhiskerRight (strictPushEvaluation l E f n)
      (model l E Y n (C.target.finiteIso n)) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)}
        (J := ProEt.topology X) (O := systemRing.{t, u} l E)
        (ell := systemUniformizer.{t, u} l E) n)
      (restrictionPushIso (proEtaleBaseChange f)
        (C.source.finiteIso n).inv (C.target.finiteIso n).inv
        (finiteStructure l E f n) (modelStructure l E f n)
        (modelStructure_finite l E f C n).symm).symm

private theorem pushEvaluation_identity {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (n : ℕ) :
    IsSectionwiseIdentity Y (N l E Y n) (pushEvaluation l E f C n).hom := by
  intro M U x
  exact (heq_of_eq (restrictionPushIso_inv (proEtaleBaseChange f)
    (C.source.finiteIso n).inv (C.target.finiteIso n).inv
    (finiteStructure l E f n) (modelStructure l E f n)
    (modelStructure_finite l E f C n).symm (M.level n) U
    (((strictPushEvaluation l E f n).hom.app M).val.app U x))).trans
      (strictPushEvaluation_identity l E f M n U x)

private theorem inverse_identity (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)})
    {D : Type*} [Category D] {F G : D ⥤ Mod W B} (e : F ≅ G)
    (h : IsSectionwiseIdentity W B e.hom) :
    IsSectionwiseIdentity W B e.inv := by
  intro M U x
  have hi : (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x :=
    congrArg (fun k ↦ k.val.app U x) (e.inv_hom_id_app M)
  exact (hi ▸ h M U ((e.inv.app M).val.app U x)).symm

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private def diagramEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (n : ℕ) :
    (strictPush l E f ⋙ C.target.systemRestriction) ⋙
        (evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n) ≅
      (C.source.systemRestriction ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap)) ⋙
          (evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n) := by
  letI := C.finiteAdditive n
  exact Functor.isoWhiskerLeft (strictPush l E f) (C.target.systemEvaluation n) ≪≫
    Functor.isoWhiskerRight (pushEvaluation l E f C n)
      (SheafOfModules.restrictScalars (projection l E Y n)) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          model l E X n (C.source.finiteIso n)) (C.finiteSquare n).ordinary ≪≫
    Functor.isoWhiskerRight (C.source.systemEvaluation n).symm (push f C.structureMap)

private theorem diagramEvaluation_identity {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (n : ℕ) :
    IsSectionwiseIdentity Y (R l E Y) (diagramEvaluation l E f C n).hom := by
  intro M U x
  exact (inverse_identity X (R l E X) (C.source.systemEvaluation n)
      (C.source.systemEvaluation_identity n) M ((proEtaleBaseChange f).op.obj U) _).trans
    ((C.finiteOrdinary_identity n _ U _).trans
      ((pushEvaluation_identity l E f C n M U _).trans
        (C.target.systemEvaluation_identity n ((strictPush l E f).obj M) U x)))

private theorem identity_section_type
    {A : Type a} [Category.{av} A] {J : GrothendieckTopology A}
    {R S : Sheaf J RingCat.{r}} (M : SheafOfModules.{w} R) (N : SheafOfModules.{w} S)
    (f : ∀ U, M.val.obj U → N.val.obj U) (h : ∀ U x, HEq (f U x) x) (U : Aᵒᵖ) :
    (M.val.obj U : Type w) = (N.val.obj U : Type w) :=
  (type_eq_of_heq (h U 0)).symm

private theorem system_section_type (W : Scheme.{t}) (S : SystemRestrictionData l E W)
    (M : Systems l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (((S.systemRestriction.obj M).obj (op n)).val.obj U : Type (max u (t + 1))) =
      ((M.level n).val.obj U : Type (max u (t + 1))) :=
  identity_section_type ((S.systemRestriction.obj M).obj (op n)) (M.level n)
    (fun V x ↦ ((S.systemEvaluation n).hom.app M).val.app V x)
    (S.systemEvaluation_identity n M) U

private theorem normalized_function {A B V : Type w} (hA : A = V) (hB : B = V)
    (f : A → B) (h : ∀ x, HEq (f x) x) : HEq f (fun x : V ↦ x) := by
  subst A B
  apply heq_of_eq
  funext x
  exact eq_of_heq (h x)

private theorem normalized_square
    {A B D E M N : Type w} (hA : A = M) (hB : B = N) (hD : D = M) (hE : E = N)
    (a : A → B) (b : B → E) (c : A → D) (d : D → E) (t : M → N)
    (ha : HEq a t) (hb : HEq b (fun x : N ↦ x))
    (hc : HEq c (fun x : M ↦ x)) (hd : HEq d t) :
    (fun x ↦ b (a x)) = (fun x ↦ d (c x)) := by
  subst A B D E
  rw [eq_of_heq ha, eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]

private theorem module_normalized_square
    {A : Type a} [Category.{av} A] {J : GrothendieckTopology A}
    {R : Sheaf J RingCat.{r}} {P Q S T : SheafOfModules.{w} R}
    (V W : Aᵒᵖ → Type w)
    (hP : ∀ U, (P.val.obj U : Type w) = V U)
    (hQ : ∀ U, (Q.val.obj U : Type w) = W U)
    (hS : ∀ U, (S.val.obj U : Type w) = V U)
    (hT : ∀ U, (T.val.obj U : Type w) = W U)
    (a : P ⟶ Q) (b : Q ⟶ T) (c : P ⟶ S) (d : S ⟶ T)
    (t : ∀ U, V U → W U)
    (ha : ∀ U, HEq (fun x ↦ a.val.app U x) (t U))
    (hb : ∀ U, HEq (fun x ↦ b.val.app U x) (fun x : W U ↦ x))
    (hc : ∀ U, HEq (fun x ↦ c.val.app U x) (fun x : V U ↦ x))
    (hd : ∀ U, HEq (fun x ↦ d.val.app U x) (t U)) : a ≫ b = c ≫ d := by
  ext U x
  exact congrFun (normalized_square (hP U) (hQ U) (hS U) (hT U)
    (fun x ↦ a.val.app U x) (fun x ↦ b.val.app U x)
    (fun x ↦ c.val.app U x) (fun x ↦ d.val.app U x)
    (t U) (ha U) (hb U) (hc U) (hd U)) x

private theorem pushed_section_type
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (F : A ⥤ B) [F.IsContinuous J K]
    {RX : Sheaf K RingCat.{r}} {RY : Sheaf J RingCat.{r}}
    (c : RY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj RX)
    (M : SheafOfModules.{w} RX) (U : Aᵒᵖ) :
    (((SheafOfModules.pushforward c).obj M).val.obj U : Type w) =
      (M.val.obj (F.op.obj U) : Type w) := rfl

private theorem pushed_map_heq
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (F : A ⥤ B) [F.IsContinuous J K]
    {RX : Sheaf K RingCat.{r}} {RY : Sheaf J RingCat.{r}}
    (c : RY ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj RX)
    {M N : SheafOfModules.{w} RX} (h : M ⟶ N) (U : Aᵒᵖ) :
    HEq (fun x ↦ ((SheafOfModules.pushforward c).map h).val.app U x)
      (fun x ↦ h.val.app (F.op.obj U) x) := HEq.rfl

private theorem diagram_target_section_type {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    (((C.target.systemRestriction.obj ((strictPush l E f).obj M)).obj (op n)).val.obj U :
      Type (max u (t + 1))) =
    ((M.level n).val.obj ((proEtaleBaseChange f).op.obj U) : Type (max u (t + 1))) :=
  (system_section_type l E Y C.target.toSystemRestrictionData
    ((strictPush l E f).obj M) n U).trans (strictPush_section_type l E f M n U)

private theorem diagram_source_section_type {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    (((push f C.structureMap).obj ((C.source.systemRestriction.obj M).obj (op n))).val.obj U :
      Type (max u (t + 1))) =
    ((M.level n).val.obj ((proEtaleBaseChange f).op.obj U) : Type (max u (t + 1))) :=
  (pushed_section_type (proEtaleBaseChange f) C.structureMap
    ((C.source.systemRestriction.obj M).obj (op n)) U).trans
      (system_section_type l E X C.source.toSystemRestrictionData M n
        ((proEtaleBaseChange f).op.obj U))

private theorem diagramEvaluation_normalized {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ ((diagramEvaluation l E f C n).hom.app M).val.app U x)
      (fun x : (M.level n).val.obj ((proEtaleBaseChange f).op.obj U) ↦ x) :=
  normalized_function (diagram_target_section_type l E f C M n U)
    (diagram_source_section_type l E f C M n U)
    (fun x ↦ ((diagramEvaluation l E f C n).hom.app M).val.app U x)
    (diagramEvaluation_identity l E f C n M U)

private theorem diagram_target_transition {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ ((C.target.systemRestriction.obj ((strictPush l E f).obj M)).map
      (homOfLE (Nat.le_succ n)).op).val.app U x)
      (transitionSections M n ((proEtaleBaseChange f).op.obj U)) :=
  (C.target.systemTransition ((strictPush l E f).obj M) n U).trans
    ((strictPush_transition_heq l E f M n U).trans
      (transitionSections_heq M n ((proEtaleBaseChange f).op.obj U)))

private theorem diagram_source_transition {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ ((push f C.structureMap).map ((C.source.systemRestriction.obj M).map
      (homOfLE (Nat.le_succ n)).op)).val.app U x)
      (transitionSections M n ((proEtaleBaseChange f).op.obj U)) :=
  (pushed_map_heq (proEtaleBaseChange f) C.structureMap
    ((C.source.systemRestriction.obj M).map (homOfLE (Nat.le_succ n)).op) U).trans
      ((C.source.systemTransition M n ((proEtaleBaseChange f).op.obj U)).trans
        (transitionSections_heq M n ((proEtaleBaseChange f).op.obj U)))

private theorem diagramEvaluation_successor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) (M : Systems l E X) (n : ℕ) :
    (C.target.systemRestriction.obj ((strictPush l E f).obj M)).map
        (homOfLE (Nat.le_succ n)).op ≫ (diagramEvaluation l E f C n).hom.app M =
      (diagramEvaluation l E f C (n + 1)).hom.app M ≫
        (push f C.structureMap).map ((C.source.systemRestriction.obj M).map
          (homOfLE (Nat.le_succ n)).op) :=
  module_normalized_square
    (R := R l E Y)
    (P := (C.target.systemRestriction.obj ((strictPush l E f).obj M)).obj (op (n + 1)))
    (Q := (C.target.systemRestriction.obj ((strictPush l E f).obj M)).obj (op n))
    (S := (push f C.structureMap).obj ((C.source.systemRestriction.obj M).obj (op (n + 1))))
    (T := (push f C.structureMap).obj ((C.source.systemRestriction.obj M).obj (op n)))
    (fun U ↦ (M.level (n + 1)).val.obj ((proEtaleBaseChange f).op.obj U))
    (fun U ↦ (M.level n).val.obj ((proEtaleBaseChange f).op.obj U))
    (diagram_target_section_type l E f C M (n + 1))
    (diagram_target_section_type l E f C M n)
    (diagram_source_section_type l E f C M (n + 1))
    (diagram_source_section_type l E f C M n)
    ((C.target.systemRestriction.obj ((strictPush l E f).obj M)).map
      (homOfLE (Nat.le_succ n)).op)
    ((diagramEvaluation l E f C n).hom.app M)
    ((diagramEvaluation l E f C (n + 1)).hom.app M)
    ((push f C.structureMap).map ((C.source.systemRestriction.obj M).map
      (homOfLE (Nat.le_succ n)).op))
    (fun U ↦ transitionSections M n ((proEtaleBaseChange f).op.obj U))
    (diagram_target_transition l E f C M n)
    (diagramEvaluation_normalized l E f C M n)
    (diagramEvaluation_normalized l E f C M (n + 1))
    (diagram_source_transition l E f C M n)

private def diagramIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) :
    strictPush l E f ⋙ C.target.systemRestriction ≅
      C.source.systemRestriction ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap) := by
  let h (M : Systems l E X) :
      C.target.systemRestriction.obj ((strictPush l E f).obj M) ⟶
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f C.structureMap)).obj
          (C.source.systemRestriction.obj M) := NatTrans.ofOpSequence
    (fun n ↦ (diagramEvaluation l E f C n).hom.app M)
    (diagramEvaluation_successor l E f C M)
  haveI (M : Systems l E X) (n : ℕᵒᵖ) : IsIso ((h M).app n) :=
    inferInstanceAs (IsIso ((diagramEvaluation l E f C n.unop).hom.app M))
  haveI (M : Systems l E X) : IsIso (h M) := NatIso.isIso_of_isIso_app _
  exact NatIso.ofComponents (fun M ↦ asIso (h M)) (fun {M N} k ↦ by
    apply NatTrans.ext
    funext n
    exact (diagramEvaluation l E f C n.unop).hom.naturality k)

/-- Construct direct image on strict systems before passing to derived categories.
Source: Zheng, Construction 4.1; Stacks Project, Tags 03DA and 0D6E
(blueprint: lem-pur-completed-coefficient-ordinary-strict-image).

Proof: At level n use sheaf-module pushforward along the constant structural map
of the quotient of systemRing by the (n+1)-st power of systemUniformizer. Naturality
of constant sheafification with respect to the quotient homomorphism identifies
pushforward followed by coefficient restriction with coefficient restriction followed
by pushforward; the comparison is identity on sections. Map each successive transition
through this comparison. Applying the level functors to component maps defines the
system functor: the transition square follows from the old square and naturality of
the comparison. Functoriality and additivity hold componentwise.
Transport the level coefficient rings by source.finiteIso and target.finiteIso. Their
generator equations identify the two transported structural maps with finiteStructure:
precompose with the constant-sheafification unit and check on quotient generators.
The resulting evaluation isomorphisms have identity sections. Combine these with
source.systemEvaluation, target.systemEvaluation and the finite ordinary square to
obtain the components of diagramOrdinary. Each comparison has identity sections. The
transition equations source.systemTransition and target.systemTransition, together
with the construction of the image transition, make these components natural in n.
Naturality of the constituent comparisons gives naturality in the system. They form a natural
isomorphism of strict completed-module towers with the displayed section identity.
This argument imposes no cartesianness on the transitions. -/
theorem ordinaryStrictImage_exists {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientComparisonData l E f) :
    Nonempty (OrdinaryStrictImageData l E f C) := by
  exact ⟨{
    systemPush := strictPush l E f
    systemPushEvaluation := pushEvaluation l E f C
    systemPushEvaluation_identity := pushEvaluation_identity l E f C
    diagramOrdinary := diagramIso l E f C
    diagramOrdinary_identity := fun M n U x ↦
      diagramEvaluation_identity l E f C n M U x }⟩

end WeilConjectures.CompletedCoefficientPushforward
