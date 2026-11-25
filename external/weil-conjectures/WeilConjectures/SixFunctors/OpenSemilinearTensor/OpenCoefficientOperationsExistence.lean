/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Coefficient transport for the ordinary open operations

Source: Stacks Project, Tags 03DI, 03DJ, 0941 and 098K.
(blueprint: lem-sf-open-coefficient-operations-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections

namespace WeilConjectures.OpenSemilinearTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

private local instance sliceRingSheafify :
    HasSheafify ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      CommRingCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over (IntegralOpenReduction.openObject j)) :=
    essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

private local instance (priority := 20000) baseRingSheafify (Y : Scheme.{t}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  integralCoefficientRingSheafify Y

private local instance inverseSliceContinuous :
    (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm.functor.IsContinuous
      (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) := by
  have : (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).inverse.IsDenseSubsite
      (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) :=
    ProEt.sliceDense X (IntegralOpenReduction.openObject j)
  exact inferInstanceAs
    ((ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).inverse.IsContinuous
      (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j)))

private local instance sliceCocontinuous : (IntegralOpenReduction.sliceSite j).IsCocontinuous
    ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
  by
    let e := ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)
    exact (e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
      (ProEt.sliceFrom_cover X (IntegralOpenReduction.openObject j))

private def constantSliceComparison :
    constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)} ⋙
        (ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject j) ≅
      constantSheaf (ProEt.topology U) CommRingCat.{max u (t + 1)} ⋙
        (IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)}
          ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
  Functor.isoWhiskerLeft (Functor.const X.ProEtᵒᵖ)
    ((Over.forget
      (IntegralOpenReduction.openObject j)).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology X)).symm ≪≫
    Functor.isoWhiskerLeft (Functor.const U.ProEtᵒᵖ)
      ((IntegralOpenReduction.sliceSite j).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U))

private def constantSliceIso (A : CommRingCat.{max u (t + 1)}) :=
  (constantSliceComparison j).app A

private theorem constantSliceIso_unit (A : CommRingCat.{max u (t + 1)})
    (V : Over (IntegralOpenReduction.openObject j)) :
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op V.left) ≫
        (constantSliceIso j A).hom.hom.app (op V) =
      (toSheafify (ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj A)).app
        (op ((IntegralOpenReduction.sliceSite j).obj V)) := by
  let α := ((Over.forget (IntegralOpenReduction.openObject
    j)).pushforwardContinuousSheafificationCompatibility CommRingCat.{max u (t + 1)}
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology X)).app
        ((Functor.const X.ProEtᵒᵖ).obj A)
  let β := ((IntegralOpenReduction.sliceSite j).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      (ProEt.topology U)).app ((Functor.const U.ProEtᵒᵖ).obj A)
  have h₁ := NatTrans.congr_app ((Over.forget (IntegralOpenReduction.openObject
    j)).toSheafify_pullbackSheafificationCompatibility CommRingCat.{max u (t + 1)}
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj A)) (op V)
  have h₂ := NatTrans.congr_app ((IntegralOpenReduction.sliceSite
    j).toSheafify_pullbackSheafificationCompatibility CommRingCat.{max u (t + 1)}
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj A)) (op V)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂
  have h₁' : (toSheafify
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      ((Over.forget (IntegralOpenReduction.openObject j)).op ⋙
        (Functor.const X.ProEtᵒᵖ).obj A)).app (op V) ≫ α.hom.hom.app (op V) =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op V.left) := h₁
  have hid := congrArg (fun f ↦ f.hom.app (op V)) α.hom_inv_id
  change α.hom.hom.app (op V) ≫ α.inv.hom.app (op V) = 𝟙 _ at hid
  change _ ≫ (α.inv.hom.app (op V) ≫ β.hom.hom.app (op V)) = _
  calc
    _ = (((toSheafify ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      ((Over.forget (IntegralOpenReduction.openObject j)).op ⋙
        (Functor.const X.ProEtᵒᵖ).obj A)).app (op V) ≫ α.hom.hom.app (op V)) ≫
          α.inv.hom.app (op V)) ≫ β.hom.hom.app (op V) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ (f ≫ α.inv.hom.app (op V)) ≫ β.hom.hom.app (op V)) h₁'.symm)
    _ = _ := by
      have hc := (Category.assoc
        ((toSheafify ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
          ((Over.forget (IntegralOpenReduction.openObject j)).op ⋙
            (Functor.const X.ProEtᵒᵖ).obj A)).app (op V))
        (α.hom.hom.app (op V)) (α.inv.hom.app (op V))).trans
          ((congrArg (fun f ↦ (toSheafify
            ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
            ((Over.forget (IntegralOpenReduction.openObject j)).op ⋙
              (Functor.const X.ProEtᵒᵖ).obj A)).app (op V) ≫ f) hid).trans
                (Category.comp_id _))
      exact (congrArg (fun f ↦ f ≫ β.hom.hom.app (op V)) hc).trans h₂

private theorem constantSliceIso_naturality
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
      (IntegralOpenReduction.openObject j)).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f) ≫
        (constantSliceIso j B).hom =
      (constantSliceIso j A).hom ≫
        ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).map
            ((constantSheaf (ProEt.topology U) CommRingCat.{max u (t + 1)}).map f) :=
  (constantSliceComparison j).hom.naturality f

attribute [local irreducible] constantSliceIso

private def finiteSliceIso (n : ℕ) :
    (integralCoefficientCommRingSheaf l E X n).over (IntegralOpenReduction.openObject j) ≅
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).obj
          (integralCoefficientCommRingSheaf l E U n) :=
  constantSliceIso j
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

private def finiteSliceSystemMap :
    integralCoefficientSheafSystem l E X ⋙
        (ProEt.topology X).overPullback RingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject j) ⟶
      integralCoefficientSheafSystem l E U ⋙
        (IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
  NatTrans.ofOpSequence
    (F := integralCoefficientSheafSystem l E X ⋙
      (ProEt.topology X).overPullback RingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j))
    (G := integralCoefficientSheafSystem l E U ⋙
      (IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U))
    (fun n ↦ (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
    RingCat.{max u (t + 1)})).map
    (finiteSliceIso l E j n).hom) (by
      intro n
      simp only [Functor.comp_map, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply RingCat.hom_ext
      exact congrArg (fun f ↦ (f.hom.app V).hom)
        (constantSliceIso_naturality j (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))))

private local instance overRingLimits : PreservesLimitsOfShape ℕᵒᵖ
    ((ProEt.topology X).overPullback RingCat.{max u (t + 1)}
      (IntegralOpenReduction.openObject j)) :=
  preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)

private def completedSliceRingIso :
    (completedIntegralCoefficientSheafUnrestricted l E X).over
        (IntegralOpenReduction.openObject j) ≅
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).obj
          (completedIntegralCoefficientSheafUnrestricted l E U) := by
  have (n : ℕᵒᵖ) : IsIso ((finiteSliceSystemMap l E j).app n) :=
    inferInstanceAs (IsIso ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u
      (t + 1)})).map
      (finiteSliceIso l E j n.unop).hom))
  have : IsIso (finiteSliceSystemMap l E j) := NatIso.isIso_of_isIso_app _
  exact preservesLimitIso ((ProEt.topology X).overPullback RingCat.{max u (t + 1)}
      (IntegralOpenReduction.openObject j)) (integralCoefficientSheafSystem l E X) ≪≫
    lim.mapIso (asIso (finiteSliceSystemMap l E j)) ≪≫
      (preservesLimitIso ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
          (ProEt.topology U)) (integralCoefficientSheafSystem l E U)).symm

private def completedSliceIso :
    (completedIntegralCommRingSheafUnrestricted l E X).over
        (IntegralOpenReduction.openObject j) ≅
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).obj
          (completedIntegralCommRingSheafUnrestricted l E U) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimageIso
    (completedSliceRingIso l E j)

private theorem completedSliceIso_projection (n : ℕ) :
    (completedSliceIso l E j).hom ≫
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).map
          (completedIntegralCommRingProjectionUnrestricted l E U n) =
    ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
      (IntegralOpenReduction.openObject j)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n) ≫ (finiteSliceIso l E j n).hom := by
  apply (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map_injective
  simp only [Functor.map_comp, completedSliceIso, Functor.preimageIso_hom,
    Functor.map_preimage]
  change (completedSliceRingIso l E j).hom ≫
      ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U)).map
          (limit.π (integralCoefficientSheafSystem l E U) (op n)) = _
  simp only [completedSliceRingIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    preservesLimitIso_inv_π, lim_map, limMap_π, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, preservesLimitIso_hom_π]
  rfl

section ModuleTransport
universe v
variable {C : Type*} [Category C] {H : Type*} [Category H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology H)
  (e : C ≌ H) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  (R : Sheaf J RingCat.{v}) (S : Sheaf K RingCat.{v})
  (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{v} K J).obj R)

private def inverseStructuralMap :
    R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{v} J K).obj S :=
  { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
      Functor.whiskerLeft e.functor.op c.inv.hom }

private theorem inverseStructuralMap_counit :
    Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      (inverseStructuralMap J K e R S c).hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
  apply NatTrans.ext
  funext U
  change R.obj.map _ =
    (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
  rw [Category.assoc]
  have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
  have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
      c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
  change R.obj.map (e.unitInv.app U.unop).op =
    R.obj.map (e.unitInv.app U.unop).op ≫
      (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
  exact (Category.comp_id _).symm.trans
    (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)

private theorem inverseStructuralMap_unit :
    c.hom.hom ≫ e.inverse.op.whiskerLeft (inverseStructuralMap J K e R S c).hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
  apply NatTrans.ext
  funext U
  change c.hom.hom.app U ≫
    (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
      S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
  rw [Category.assoc]
  have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
  change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
    c.inv.hom.app U =
    c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
      S.obj.map (e.counitInv.app U.unop).op at hn
  rw [← hn]
  have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
      R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp]
    simp
  rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
  change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
  have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
  exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
    (Category.id_comp (c.inv.hom.app U))).trans hc

/-- Keep the inverse map and its proofs out of forward-functor computation. -/
private def moduleSiteEquivalence : SheafOfModules.{v} R ≌ SheafOfModules.{v} S := by
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom
    (inverseStructuralMap J K e R S c)
    (inverseStructuralMap_counit J K e R S c) (inverseStructuralMap_unit J K e R S c)

end ModuleTransport

section SequenceContinuity
universe c d vc vd
private theorem sequenceContinuous {C : Type c} {D : Type d}
    [Category.{vc} C] [Category.{vd} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) (he : CoverPreserving J K e.functor) :
    ((𝟭 ℕ).prod e.functor).IsContinuous
      (coefficientSequenceTopology J) (coefficientSequenceTopology K) := by
  have : ((𝟭 ℕ).prod e.functor).IsEquivalence :=
    inferInstanceAs ((CategoryTheory.Equivalence.refl (C := ℕ)).prod e).functor.IsEquivalence
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro V S hS
  change (S.functorPushforward ((𝟭 ℕ).prod e.functor)).functorPullback
    (Prod.sectR V.1 D) ∈ K (e.functor.obj V.2)
  apply K.superset_covering _ (he.cover_preserve hS)
  intro W a ha
  obtain ⟨V', g, k, hg, rfl⟩ := ha
  exact ⟨(V.1, V'), Prod.mkHom (𝟙 V.1) g, Prod.mkHom (𝟙 V.1) k, hg, by
    ext <;> simp⟩
end SequenceContinuity

private local instance systemContinuous :
    ((𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j)).IsContinuous
      (coefficientSequenceTopology ((ProEt.topology X).over
        (IntegralOpenReduction.openObject j))) (coefficientSequenceTopology (ProEt.topology U))
          := by
  have : (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).inverse.IsDenseSubsite
      (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) :=
    ProEt.sliceDense X (IntegralOpenReduction.openObject j)
  exact sequenceContinuous _ _ (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j))
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

private local instance inverseSystemContinuous :
    ((𝟭 ℕ).prod (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).inverse).IsContinuous
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology ((ProEt.topology X).over
        (IntegralOpenReduction.openObject j))) :=
  sequenceContinuous _ _ (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm
    (ProEt.sliceFrom_cover X (IntegralOpenReduction.openObject j))

private def commFiniteSliceSystemMap :
    SemilinearSections.rings ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
        (fun n ↦ (IntegralOpenReduction.rings l E X n).over (IntegralOpenReduction.openObject j))
        (fun n ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject j)).map (IntegralOpenReduction.transitions l E X n)) ⟶
      coefficientSequenceCommRingSystem l E U ⋙
        (IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
  NatTrans.ofOpSequence (fun n ↦ (finiteSliceIso l E j n).hom) (by
    intro n
    simp only [Functor.comp_map, SemilinearSections.rings, coefficientSequenceCommRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply (sheafCompose _
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map_injective
    have h := (finiteSliceSystemMap l E j).naturality (homOfLE (Nat.le_succ n)).op
    simp only [Functor.comp_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    convert h using 1 <;> ext V x <;> rfl)

private def systemSliceMap : IntegralOpenReduction.sliceRing l E j ⟶
    (((𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j)).sheafPushforwardContinuous
      CommRingCat.{max u (t + 1)}
      (coefficientSequenceTopology ((ProEt.topology X).over (IntegralOpenReduction.openObject j)))
      (coefficientSequenceTopology (ProEt.topology U))).obj
        (coefficientSequenceCommRingSheaf l E U) where
  hom :=
    { app V := (finiteSliceIso l E j V.unop.1).hom.hom.app (op V.unop.2)
      naturality {_ _} a := by
        let ε := Functor.whiskerLeft
          (prodOpEquiv (C := ℕ) (D := Over (IntegralOpenReduction.openObject j))).functor
          (Functor.uncurry.map (Functor.whiskerRight (commFiniteSliceSystemMap l E j)
            (sheafToPresheaf _ CommRingCat.{max u (t + 1)})))
        exact ε.naturality a }

private def systemSliceIso : IntegralOpenReduction.sliceRing l E j ≅
    (((𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j)).sheafPushforwardContinuous
      CommRingCat.{max u (t + 1)}
      (coefficientSequenceTopology ((ProEt.topology X).over (IntegralOpenReduction.openObject j)))
      (coefficientSequenceTopology (ProEt.topology U))).obj
        (coefficientSequenceCommRingSheaf l E U) := by
  have (V : (ℕ × Over (IntegralOpenReduction.openObject j))ᵒᵖ) :
      IsIso ((systemSliceMap l E j).hom.app V) :=
    inferInstanceAs (IsIso ((finiteSliceIso l E j V.unop.1).hom.hom.app (op V.unop.2)))
  have : IsIso (systemSliceMap l E j).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ CommRingCat.{max u (t + 1)}).map
      (systemSliceMap l E j)) := inferInstanceAs (IsIso (systemSliceMap l E j).hom)
  have : IsIso (systemSliceMap l E j) :=
    isIso_of_reflects_iso (systemSliceMap l E j)
      (sheafToPresheaf _ CommRingCat.{max u (t + 1)})
  exact asIso (systemSliceMap l E j)

private def integralModules := by
  have : (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm.functor.IsContinuous
      (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) :=
    inverseSliceContinuous j
  have : (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm.inverse.IsContinuous
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
    IntegralOpenReduction.sliceContinuous j
  exact moduleSiteEquivalence
    (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
    (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm
    (completedIntegralCoefficientSheafUnrestricted l E U)
    ((completedIntegralCoefficientSheafUnrestricted l E X).over
      (IntegralOpenReduction.openObject j))
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
      (completedSliceIso l E j))

private def finiteModules (n : ℕ) := by
  have : (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm.functor.IsContinuous
      (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) :=
    inverseSliceContinuous j
  have : (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm.inverse.IsContinuous
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j)) (ProEt.topology U) :=
    IntegralOpenReduction.sliceContinuous j
  exact moduleSiteEquivalence
    (ProEt.topology U) ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
    (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j)).symm
    (integralCoefficientSheaf l E U n)
    ((integralCoefficientSheaf l E X n).over (IntegralOpenReduction.openObject j))
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
      (finiteSliceIso l E j n))

private def systemModules :
    coefficientSequenceModules l E U ≌ IntegralOpenReduction.SliceSystems l E j := by
  let e := (CategoryTheory.Equivalence.refl (C := ℕ)).prod
    (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j))
  have : e.symm.functor.IsContinuous (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology ((ProEt.topology X).over
        (IntegralOpenReduction.openObject j))) :=
    inverseSystemContinuous j
  have : e.symm.inverse.IsContinuous
      (coefficientSequenceTopology ((ProEt.topology X).over (IntegralOpenReduction.openObject j)))
      (coefficientSequenceTopology (ProEt.topology U)) := systemContinuous j
  exact moduleSiteEquivalence
    (coefficientSequenceTopology (ProEt.topology U))
    (coefficientSequenceTopology ((ProEt.topology X).over (IntegralOpenReduction.openObject j)))
    ((CategoryTheory.Equivalence.refl (C := ℕ)).prod
      (ProEt.sliceEquiv X (IntegralOpenReduction.openObject j))).symm
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E U))
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (IntegralOpenReduction.sliceRing l E j))
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso
      (systemSliceIso l E j))

private def evaluationComparison (n : ℕ) :
    (systemModules l E j).functor ⋙ SemilinearSections.evaluation
      ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
      (fun k ↦ (IntegralOpenReduction.rings l E X k).over (IntegralOpenReduction.openObject j))
      (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j)).map (IntegralOpenReduction.transitions l E X k)) n ≅
      coefficientSequenceEvaluation l E U n ⋙ (finiteModules l E j n).functor := by
  letI := systemContinuous j
  letI := IntegralOpenReduction.sliceContinuous j
  letI := Functor.isContinuous_comp
    (Prod.sectR n (Over (IntegralOpenReduction.openObject j)))
    ((𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j))
    ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
    (coefficientSequenceTopology ((ProEt.topology X).over (IntegralOpenReduction.openObject j)))
    (coefficientSequenceTopology (ProEt.topology U))
  let φ := eqToHom (SemilinearSections.evaluation_ring
    ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
    (fun k ↦ (IntegralOpenReduction.rings l E X k).over (IntegralOpenReduction.openObject j))
    (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
      (IntegralOpenReduction.openObject j)).map (IntegralOpenReduction.transitions l E X k)) n).symm
  let ψ := eqToHom (coefficientSequenceEvaluationRing_eq l E U n).symm
  let a := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    (systemSliceMap l E j)
  let b := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    (finiteSliceIso l E j n).hom
  have he : φ ≫ ((Prod.sectR n _).sheafPushforwardContinuous RingCat.{max u (t + 1)} _ _).map a =
      b ≫ ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous RingCat.{max u (t +
        1)} _ _).map ψ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hφ : φ.hom.app V = 𝟙 _ := by
      dsimp only [φ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hψ : ψ.hom.app (op ((IntegralOpenReduction.sliceSite j).obj V.unop)) = 𝟙 _ := by
      dsimp only [ψ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change φ.hom.app V ≫ _ = b.hom.app V ≫
      ψ.hom.app (op ((IntegralOpenReduction.sliceSite j).obj V.unop))
    exact ((congrArg (fun f ↦ f ≫ _) hφ).trans (Category.id_comp _)).trans
      (((congrArg (fun f ↦ b.hom.app V ≫ f) hψ).trans
        (Category.comp_id _)).symm)
  exact SheafOfModules.pushforwardComp
      (F := Prod.sectR n (Over (IntegralOpenReduction.openObject j)))
      (G := (𝟭 ℕ).prod (IntegralOpenReduction.sliceSite j))
      (K' := coefficientSequenceTopology (ProEt.topology U))
      (R' := (sheafCompose _
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E U)) φ a ≪≫
    SheafOfModules.pushforwardCongr he ≪≫
    (SheafOfModules.pushforwardComp (F := IntegralOpenReduction.sliceSite j)
      (G := Prod.sectR n U.ProEt)
      (K := ProEt.topology U) (K' := coefficientSequenceTopology (ProEt.topology U))
      (R := integralCoefficientSheaf l E U n)
      (R' := (sheafCompose _
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E U)) b ψ).symm

private theorem evaluationComparison_sections (n : ℕ)
    (M : coefficientSequenceModules l E U)
    (V : (Over (IntegralOpenReduction.openObject j))ᵒᵖ)
    (x : M.val.obj (op (n, (IntegralOpenReduction.sliceSite j).obj V.unop))) :
    HEq (((evaluationComparison l E j n).hom.app M).val.app V x) x := by
  simp only [evaluationComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.pushforwardCongr_hom_app_val_app]
  rfl

/-- Transport the quotient tower and its completed ring to the literal open slice.
This constructs only the coefficient/module transports; it asserts no tensor or
scalar projection formula.
Source: Stacks 03DI, 03DJ, 0941 and 098K
(blueprint: lem-sf-open-coefficient-operations-existence).

Proof: identify `cbcSliceFunctor` with the concrete slice equivalence supplied by
weakly-etale localization. Continuous precomposition along this equivalence commutes
with ring sheafification. Apply its unit comparison to each constant quotient ring,
oriented from the ambient restricted sheaf to the precomposition of the open sheaf.
The unit equation is `finiteConstants`. Naturality in the quotient ring maps gives
the transition squares, first for consecutive indices and then by composition.
Take the limit of this diagram of isomorphisms. Restriction and equivalence
precomposition preserve limits, so the resulting completed map is invertible and
satisfies `projections`. For both completed and finite rings use the two inverse
site functors and inverse ring maps in `pushforwardPushforwardEquivalence`; its
forward functor is the prescribed pushforward, and addition of morphisms is
sectionwise. On the product with the coefficient index category, the transition
squares define `systemMap` with exactly the finite maps as its components. The
product site equivalence is continuous because covers are vertical covers, and
the same module pushforward construction gives `systems`. Evaluation commutes with
this pushforward by the identity on every underlying section and morphism. These
identity identifications are `transportEvaluation` and `transportSections`.
Finally insert the supplied localization as `openSystems`; no property of its
chosen adjunction or evaluation is needed for this coefficient construction. -/
theorem openCoefficientOperationsExistence
    (sections : SemilinearDerivedSectionsData.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X)) :
    ∃ o : Operations l E j,
      o.openSystems = sections.localization (IntegralOpenReduction.openObject j) ∧
        IsIso o.completedMap := by
  let o : Operations l E j :=
    { finiteMap := fun n ↦ (finiteSliceIso l E j n).hom
      finiteConstants := fun n V ↦ constantSliceIso_unit j _ V
      completedMap := (completedSliceIso l E j).hom
      projections := completedSliceIso_projection l E j
      integral := integralModules l E j
      integralFunctor := rfl
      finite := finiteModules l E j
      finiteFunctor := fun _ ↦ rfl
      systemContinuous := systemContinuous j
      systemMap := systemSliceMap l E j
      systemComponents := fun _ _ ↦ rfl
      systems := systemModules l E j
      systemsFunctor := rfl
      integralAdditive := Functor.additive_of_preserves_binary_products _
      finiteAdditive := fun _ ↦ Functor.additive_of_preserves_binary_products _
      systemsAdditive := Functor.additive_of_preserves_binary_products _
      openSystems := sections.localization (IntegralOpenReduction.openObject j)
      transportEvaluation := evaluationComparison l E j
      transportSections := evaluationComparison_sections l E j }
  exact ⟨o, rfl, inferInstanceAs (IsIso (completedSliceIso l E j).hom)⟩

end WeilConjectures.OpenSemilinearTensor
