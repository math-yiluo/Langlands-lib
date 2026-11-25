/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingIdentityCompatibility
import WeilConjectures.PoincareDuality.Pod.Reindexing.Composition.PodReindexingCompositionCompatibility

/-! # Identity and composition laws for a normalized tensor family

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL and 07A4
(blueprint: lem-pod-reindexing-tensor-family-identity-composition).

This is the identity/composition part of the fixed-family coherence argument. The
remaining tensor associator, braiding and unitor equations are isolated in the
companion tensor-constraints statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance (priority := 100001) ringSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} W

private instance (priority := 100002) ringWeakSheafify (W : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  HasSheafify.isRightAdjoint

private instance (priority := 100002) identityContinuous (W : Scheme.{u}) :
    (𝟭 W.ProEt).IsContinuous (ProEt.topology W) (ProEt.topology W) :=
  Functor.isContinuous_id (ProEt.topology W)

private theorem completedProjection {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f] (n : ℕ) :
    (isoReductionCompletedMap l E f).hom ≫
        limit.π (integralCoefficientSheafSystem l E V) (op n) =
      (isoSectionwiseInverseImage f RingCat).map
        (limit.π (integralCoefficientSheafSystem l E W) (op n)) ≫
      isoSectionwiseConstantMap.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  (isoReductionCompletedMap_existsUnique l E f).exists.choose_spec n

private theorem constantIdentity (W : Scheme.{u})
    (R : CommRingCat.{u + 1}) :
    isoSectionwiseConstantMap.{u, u} (𝟙 W) R =
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl) RingCat.{u + 1}
        (ProEt.topology W)).hom.app
          ((sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj R)) := by
  apply (isoSectionwiseConstantMap_existsUnique.{u, u} (𝟙 W) R).unique
    (isoSectionwiseConstantMap_existsUnique.{u, u} (𝟙 W) R).exists.choose_spec
  intro U a
  exact congrArg (fun f ↦ f a)
    ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj R)).naturality
      ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl).inv.app U).op).symm

private theorem completedIdentity (W : Scheme.{u}) :
    (isoReductionCompletedMap l E (𝟙 W)).hom =
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl) RingCat.{u + 1}
        (ProEt.topology W)).hom.app
          (completedIntegralCoefficientSheafUnrestricted l E W) := by
  apply limit.hom_ext
  intro n
  erw [completedProjection l E (𝟙 W) n.unop]
  rw [constantIdentity]
  exact (Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl) RingCat.{u + 1}
      (ProEt.topology W)).hom.naturality
        (limit.π (integralCoefficientSheafSystem l E W) n)

private def ordinaryIdentity (W : Scheme.{u}) :
    isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _ := by
  let e := MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl
  let c := isoReductionCompletedMap l E (𝟙 W)
  let a := SheafOfModules.pushforwardNatIso
    (J := ProEt.topology W) (K := ProEt.topology W)
    (F := 𝟭 W.ProEt) (G := proEtaleIsoPostcompose (𝟙 W)) c.inv e.symm
  let b : isoReductionIntegralInverse l E (𝟙 W) ≅ SheafOfModules.pushforward c.inv :=
    SheafOfModules.pushforwardCongr (IsIso.inv_eq_of_hom_inv_id c.hom_inv_id)
  refine b ≪≫ a ≪≫ SheafOfModules.pushforwardCongr ?_ ≪≫
    SheafOfModules.pushforwardId _
  change c.inv ≫ _ = 𝟙 _
  erw [← completedIdentity l E W]
  exact c.inv_hom_id

private theorem moduleComp_apply {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) RingCat.{u + 1}} {M N P : SheafOfModules.{u + 1} R}
    (a : M ⟶ N) (b : N ⟶ P) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (a ≫ b).val.app U x = b.val.app U (a.val.app U x) := rfl

private theorem ordinaryIdentity_sections (W : Scheme.{u})
    (M : scalarReductionSource l E W) (U : W.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))) :
    ((ordinaryIdentity l E W).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
        (𝟙 W) rfl).hom.app U).op x := by
  simp only [ordinaryIdentity, Iso.trans_hom, NatTrans.comp_app, moduleComp_apply,
    SheafOfModules.pushforwardCongr_hom_app_val_app, SheafOfModules.pushforwardNatIso_hom,
    SheafOfModules.pushforwardNatTrans_app_val_app, SheafOfModules.pushforwardId]
  rfl

private def sectionComposition {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
    [IsIso h] [IsIso f] (D : Type*) [Category D] :
    isoSectionwiseInverseImage (h ≫ f) D ≅
      isoSectionwiseInverseImage f D ⋙ isoSectionwiseInverseImage h D :=
  (Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).symm
    D (ProEt.topology Z) (ProEt.topology W) (ProEt.topology V)).symm

private theorem constantComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] (R : CommRingCat.{u + 1}) :
    isoSectionwiseConstantMap.{u, u} (h ≫ f) R =
      (sectionComposition h f RingCat).hom.app
          ((sheafCompose (ProEt.topology V)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj R)) ≫
        (isoSectionwiseInverseImage h RingCat).map (isoSectionwiseConstantMap.{u, u} f R) ≫
          isoSectionwiseConstantMap.{u, u} h R := by
  apply (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ f) R).unique
    (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ f) R).exists.choose_spec
  intro U a
  change (isoSectionwiseConstantMap.{u, u} h R).hom.app (op U)
    ((isoSectionwiseConstantMap.{u, u} f R).hom.app (op ((proEtaleIsoPostcompose h).obj U))
      (((constantSheaf (ProEt.topology V) CommRingCat).obj R).obj.map
        ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op
        ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).app
          (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)) a))) = _
  have hn :
      ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj R).obj.map
          ((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op
          ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).app
            (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)) a) =
        (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).app
          (op ((proEtaleIsoPostcompose f).obj ((proEtaleIsoPostcompose h).obj U))) a :=
    congrArg (fun q ↦ q a)
      ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).naturality
        ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op).symm
  erw [hn]
  erw [show (isoSectionwiseConstantMap.{u, u} f R).hom.app
      (op ((proEtaleIsoPostcompose h).obj U)) _ = _ from
    (isoSectionwiseConstantMap_existsUnique.{u, u} f R).exists.choose_spec
      ((proEtaleIsoPostcompose h).obj U) a]
  exact (isoSectionwiseConstantMap_existsUnique.{u, u} h R).exists.choose_spec U a

private theorem completedComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] :
    (isoReductionCompletedMap l E (h ≫ f)).hom =
      (sectionComposition h f RingCat).hom.app
          (completedIntegralCoefficientSheafUnrestricted l E V) ≫
        (isoSectionwiseInverseImage h RingCat).map (isoReductionCompletedMap l E f).hom ≫
          (isoReductionCompletedMap l E h).hom := by
  apply limit.hom_ext
  intro n
  let H := isoSectionwiseInverseImage h RingCat.{u + 1}
  let HF := isoSectionwiseInverseImage (h ≫ f) RingCat.{u + 1}
  let a := sectionComposition h f RingCat.{u + 1}
  have hh := completedProjection l E h n.unop
  have hf := completedProjection l E f n.unop
  have hhf := completedProjection l E (h ≫ f) n.unop
  erw [hhf, constantComposition]
  change HF.map _ ≫ (a.hom.app _ ≫ H.map _ ≫ _) =
    (a.hom.app _ ≫ H.map _ ≫ _) ≫ _
  rw [Category.assoc, Category.assoc, hh, ← H.map_comp_assoc, hf, H.map_comp]
  rw [← Category.assoc, ← Category.assoc, a.hom.naturality]
  simp only [Functor.comp_map, Category.assoc, H]

private def ordinaryComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] :
    isoReductionIntegralInverse l E (h ≫ f) ≅
      isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h := by
  let H := isoSectionwiseInverseImage h RingCat.{u + 1}
  let e := MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)
  letI : (proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose f).IsContinuous
      (ProEt.topology Z) (ProEt.topology V) :=
    Functor.isContinuous_comp (proEtaleIsoPostcompose h) (proEtaleIsoPostcompose f)
      (ProEt.topology Z) (ProEt.topology W) (ProEt.topology V)
  let c := isoReductionCompletedMap l E (h ≫ f)
  let d := (H.mapIso (isoReductionCompletedMap l E f)) ≪≫ isoReductionCompletedMap l E h
  let a := SheafOfModules.pushforwardNatIso
    (J := ProEt.topology Z) (K := ProEt.topology V)
    (F := proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose f)
    (G := proEtaleIsoPostcompose (h ≫ f)) c.inv e.symm
  let b : isoReductionIntegralInverse l E (h ≫ f) ≅ SheafOfModules.pushforward c.inv :=
    SheafOfModules.pushforwardCongr (IsIso.inv_eq_of_hom_inv_id c.hom_inv_id)
  refine b ≪≫ a ≪≫ SheafOfModules.pushforwardCongr ?_ ≪≫
    (SheafOfModules.pushforwardComp (inv (isoReductionCompletedMap l E h).hom)
      (inv (isoReductionCompletedMap l E f).hom)).symm
  simp only [IsIso.inv_eq_of_hom_inv_id (isoReductionCompletedMap l E h).hom_inv_id,
    IsIso.inv_eq_of_hom_inv_id (isoReductionCompletedMap l E f).hom_inv_id]
  change c.inv ≫ (sectionComposition h f RingCat).hom.app _ = d.inv
  apply (cancel_mono d.hom).1
  rw [Category.assoc]
  change c.inv ≫ ((sectionComposition h f RingCat).hom.app _ ≫
    H.map (isoReductionCompletedMap l E f).hom ≫ (isoReductionCompletedMap l E h).hom) = _
  rw [← completedComposition l E h f, c.inv_hom_id, d.inv_hom_id]

private theorem ordinaryComposition_sections {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    (M : scalarReductionSource l E V) (U : Z.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))) :
    ((ordinaryComposition l E h f).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x := by
  rfl

/--
Section-normalized identity and composition comparisons exist for every fixed family
of completion and tensor reindexings satisfying their component laws. The identity
comparison is induced by `MorphismProperty.Over.mapId` on sections. The compositor
is induced by `MorphismProperty.Over.mapComp`. Their coefficient maps agree after
each quotient projection, and the projections jointly detect completed sections;
therefore both are module isomorphisms. Localization gives the reduction and limit
equations, while the tensor generator formula gives the tensor equation. Naturality
and inverse laws follow from the site isomorphism identities. Empty sites and zero
objects are covered by the same formulas.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 (blueprint: lem-pod-reindexing-tensor-family-identity-composition).
-/
theorem podReindexingTensorFamilyIdentityComposition
    (completion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)], PodCompletionReindex l E f)
    (tensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex l E f (completion f))
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (completion f) (tensor f)) :
    ∃ identity : ∀ W : Scheme.{u}, isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _,
    ∃ composition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f], isoReductionIntegralInverse l E (h ≫ f) ≅
        isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h,
      let A : PodReindexFamily l E := ⟨completion, tensor, identity, composition⟩
      A.Relabelling l E ∧ A.Identity l E ∧ A.Composition l E := by
  let A : PodReindexFamily l E :=
    ⟨completion, tensor, ordinaryIdentity l E, ordinaryComposition l E⟩
  have hr : A.Relabelling l E :=
    ⟨ordinaryIdentity_sections l E, fun h f ↦ ordinaryComposition_sections l E h f⟩
  refine ⟨A.identity, A.composition, hr, ?_, ?_⟩
  · exact podReindexingIdentityCompatibility l E A hcompletion htensor hr.1
  · exact podReindexingCompositionCompatibility l E A hcompletion htensor hr.2

end WeilConjectures
