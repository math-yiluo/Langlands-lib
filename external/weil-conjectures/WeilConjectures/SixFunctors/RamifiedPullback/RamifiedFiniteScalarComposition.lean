/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SixFunctors.RamifiedPullback.TensorProof.RamifiedFiniteTensorSections
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of finite scalar extension and module pullback

Source: Stacks Project, Tags 03CZ and 03EL. Composition of left adjoints
normalizes the two scalar-extension comparison maps on unit generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback

private theorem module_comp_apply
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) := rfl

private theorem pushforward_map_apply
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward φ).obj M).val.obj U) :
    ((SheafOfModules.pushforward φ).map f).val.app U x =
      f.val.app (F.op.obj U) x := rfl

private def squareIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A} {I : C ⥤ D} {Z : D ⥤ C}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : I ⊣ Z)
    (e : V ⋙ U ≅ Z ⋙ W) : F ⋙ G ≅ H ⋙ I :=
  Adjunction.leftAdjointUniq (a.comp b) ((c.comp d).ofNatIsoRight e.symm)

private theorem squareIso_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A} {I : C ⥤ D} {Z : D ⥤ C}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : I ⊣ Z)
    (e : V ⋙ U ≅ Z ⋙ W) (M : A) :
    a.unit.app M ≫ U.map (b.unit.app (F.obj M)) ≫
        U.map (V.map ((squareIso a b c d e).hom.app M)) =
      c.unit.app M ≫ W.map (d.unit.app (H.obj M)) ≫
        e.inv.app ((H ⋙ I).obj M) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (a.comp b) ((c.comp d).ofNatIsoRight e.symm) M
  simpa only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    Functor.comp_map, squareIso] using h

attribute [local irreducible] squareIso

section Tensor
variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
  (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings c N)

private theorem tensorSection_one
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    TensorProof.tensorSection c F h N U s x =
      s • TensorProof.tensorSection c F h N U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf c N)
  have ht := (ModuleCat.ExtendScalars.smul_tmul (c.hom.app U).hom
    (M := N.val.obj U) s 1 x).symm
  rw [mul_one] at ht
  have hη := (η.app U).hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)
  have he := ((eqToHom (h N).symm).val.app U).hom.map_smul s
    ((η.app U) ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
  unfold TensorProof.tensorSection
  with_unfolding_all
    exact (congrArg (fun z ↦ (eqToHom (h N).symm).val.app U z)
      ((congrArg (fun z ↦ (η.app U) z) ht).trans hη)).trans he
end Tensor

private theorem scalar_tensor_one {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    tensor.{t, u} c M U s x = s • tensor.{t, u} c M U 1 x := by
  with_unfolding_all
    exact tensorSection_one c (scalar.{t, u} c)
      (scalarWitness.{t, u} c).choose_spec.choose M U s x

private theorem scalar_tensor_smul {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    tensor.{t, u} c M U 1 (a • x) =
      (c.hom.app U a) • tensor.{t, u} c M U 1 x := by
  rw [← scalarAdjunction_unit, ← scalarAdjunction_unit]
  exact (((scalarAdjunction.{t, u} c).unit.app M).val.app U).hom.map_smul a x

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard scalarWitness
  completedIntegralCoefficientSheafUnrestricted
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback
  Functor.leftAdjoint

private def reductionAdjunction (W : Scheme.{t}) (n : ℕ) :=
  (CategoryTheory.CochainPullback.extensionAdjunction
    (completedIntegralCommRingProjectionUnrestricted l E W n)).ofNatIsoLeft
      (TensorProof.tensorPresentation
        (completedIntegralCommRingProjectionUnrestricted l E W n)
        (unrestrictedIntegralReductionFunctor l E W n)
        (unrestrictedReduction_obj l E W n)
        (fun {A B : integralTowerModules l E W} (f : A ⟶ B) ↦
          unrestrictedReduction_map l E W n f)).symm

private theorem reductionAdjunction_unit (W : Scheme.{t}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((reductionAdjunction l E W n).unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  with_unfolding_all
    exact TensorProof.tensorAdjunction_unit
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (unrestrictedIntegralReductionFunctor l E W n) (unrestrictedReduction_obj l E W n)
      (fun {A B : integralTowerModules l E W} (f : A ⟶ B) ↦
        unrestrictedReduction_map l E W n f) M U x

private theorem reduction_tensor_one (W : Scheme.{t}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    unrestrictedIntegralTensorSection l E W n M U a x =
      a • unrestrictedIntegralTensorSection l E W n M U 1 x := by
  with_unfolding_all
    exact tensorSection_one (completedIntegralCommRingProjectionUnrestricted l E W n)
      (unrestrictedIntegralReductionFunctor l E W n) (unrestrictedReduction_obj l E W n)
      M U a x

private def restrictionCompIso {W : Scheme.{t}}
    {R S T : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (κ : R ⟶ T) (h : φ ≫ ψ = κ) :
    CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} ψ ⋙
      CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} φ ≅
        CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} κ :=
  NatIso.ofComponents (fun N ↦
    { hom := { val := {
        app := fun U ↦ (ModuleCat.restrictScalarsComp'App
          (φ.hom.app U).hom (ψ.hom.app U).hom (κ.hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) h.symm) (N.val.obj U)).inv
        naturality := by intros; ext; rfl } }
      inv := { val := {
        app := fun U ↦ (ModuleCat.restrictScalarsComp'App
          (φ.hom.app U).hom (ψ.hom.app U).hom (κ.hom.app U).hom
          (congrArg (fun f ↦ (f.hom.app U).hom) h.symm) (N.val.obj U)).hom
        naturality := by intros; ext; rfl } }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }) (by intros; ext; rfl)

private def restrictionSquare {W : Scheme.{t}}
    {R S B T : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}}
    (π : R ⟶ B) (j : B ⟶ T) (c : R ⟶ S) (q : S ⟶ T) (h : π ≫ j = c ≫ q) :
    CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} j ⋙
      CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} π ≅
    CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} q ⋙
      CategoryTheory.CochainPullback.restrictionFunctor.{max u (t + 1)} c :=
  restrictionCompIso π j (c ≫ q) h ≪≫ (restrictionCompIso c q (c ≫ q) rfl).symm

private def reductionSquareIso (W : Scheme.{t}) (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (data : Coefficients l E L ι e j W) (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E W n ⋙
        scalar.{t, u} (ramifiedMap l E L W e n (j n)) ≅
      scalar.{t, u} data.completedMap ⋙
        unrestrictedIntegralReductionFunctor l L W (index e n) :=
  squareIso (reductionAdjunction l E W n)
    (scalarAdjunction.{t, u} (ramifiedMap l E L W e n (j n)))
    (scalarAdjunction.{t, u} data.completedMap)
    (reductionAdjunction l L W (index e n))
    (restrictionSquare _ _ _ _ (data.ramified_projection n).symm)

private theorem reductionSquareIso_unit (W : Scheme.{t}) (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (data : Coefficients l E L ι e j W) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((reductionSquareIso l E L ι W e j data n).hom.app M).val.app U
      (tensor.{t, u} (ramifiedMap l E L W e n (j n)) _ U 1
        (unrestrictedIntegralTensorSection l E W n M U 1 x)) =
      unrestrictedIntegralTensorSection l L W (index e n)
        ((scalar.{t, u} data.completedMap).obj M) U 1
        (tensor.{t, u} data.completedMap M U 1 x) := by
  have h := congrArg (fun k ↦ k.val.app U x)
    (squareIso_unit (reductionAdjunction l E W n)
      (scalarAdjunction.{t, u} (ramifiedMap l E L W e n (j n)))
      (scalarAdjunction.{t, u} data.completedMap)
      (reductionAdjunction l L W (index e n))
      (restrictionSquare _ _ _ _ (data.ramified_projection n).symm) M)
  change ((reductionSquareIso l E L ι W e j data n).hom.app M).val.app U
    (((scalarAdjunction.{t, u} (ramifiedMap l E L W e n (j n))).unit.app
      ((unrestrictedIntegralReductionFunctor l E W n).obj M)).val.app U
        (((reductionAdjunction l E W n).unit.app M).val.app U x)) =
    ((reductionAdjunction l L W (index e n)).unit.app _).val.app U
      (((scalarAdjunction.{t, u} data.completedMap).unit.app M).val.app U x) at h
  simpa only [scalarAdjunction_unit, reductionAdjunction_unit] using h

private theorem finiteSquare {X Y : Scheme.{t}} (g : X ⟶ Y) (e n : ℕ)
    (j : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) :
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (ramifiedMap l E L Y e n j) ≫
        integralOperationsDirectRingMap l L g (index e n) =
      integralOperationsDirectRingMap l E g n ≫
        ((integralOperationsBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (ramifiedMap l E L X e n j)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact congrArg (fun k ↦
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map (k.hom.app V))
      (Scheme.directRingMap_naturality.{t, u} g
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
            (j.comp (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))

private theorem pullback_unit_apply {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ)
    (N : integralOperationsFiniteModules l E Y n) (V : Y.ProEt)
    (x : N.val.obj (op V)) :
    ((integralOperationsPullbackAdjunction l E g n).unit.app N).val.app (op V) x =
      integralOperationsPullbackGenerator l E g n N V x := rfl

section FinitePullback
attribute [local irreducible] integralOperationsPullbackAdjunction

private def finitePullbackSquareIso {X Y : Scheme.{t}} (g : X ⟶ Y) (e n : ℕ)
    (j : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) :
    integralOperationsLevelPullback l E g n ⋙
        scalar.{t, u} (ramifiedMap l E L X e n j) ≅
      scalar.{t, u} (ramifiedMap l E L Y e n j) ⋙
        integralOperationsLevelPullback l L g (index e n) :=
  squareIso (integralOperationsPullbackAdjunction l E g n)
    (scalarAdjunction.{t, u} (ramifiedMap l E L X e n j))
    (scalarAdjunction.{t, u} (ramifiedMap l E L Y e n j))
    (integralOperationsPullbackAdjunction l L g (index e n))
    (SheafOfModules.IntegralPullbackProof.pushRestrictionIso (integralOperationsBaseChange g)
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (ramifiedMap l E L X e n j))
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (ramifiedMap l E L Y e n j))
      _ _ (finiteSquare l E L g e n j))

private theorem finitePullbackSquareIso_unit {X Y : Scheme.{t}} (g : X ⟶ Y) (e n : ℕ)
    (j : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (N : Mod.{t, u} (integralCoefficientCommRingSheaf l E Y n))
    (V : Y.ProEt) (x : N.val.obj (op V)) :
    ((finitePullbackSquareIso l E L g e n j).hom.app N).val.app _
      (tensor.{t, u} (ramifiedMap l E L X e n j) _ _ 1
        (integralOperationsPullbackGenerator l E g n N V x)) =
      integralOperationsPullbackGenerator l L g (index e n)
        ((scalar.{t, u} (ramifiedMap l E L Y e n j)).obj N) V
        (tensor.{t, u} (ramifiedMap l E L Y e n j) N (op V) 1 x) := by
  have h := congrArg (fun k ↦ k.val.app (op V) x)
    (squareIso_unit (integralOperationsPullbackAdjunction l E g n)
      (scalarAdjunction.{t, u} (ramifiedMap l E L X e n j))
      (scalarAdjunction.{t, u} (ramifiedMap l E L Y e n j))
      (integralOperationsPullbackAdjunction l L g (index e n))
      (SheafOfModules.IntegralPullbackProof.pushRestrictionIso (integralOperationsBaseChange g)
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (ramifiedMap l E L X e n j))
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (ramifiedMap l E L Y e n j))
        _ _ (finiteSquare l E L g e n j)) N)
  have he := SheafOfModules.IntegralPullbackProof.pushRestrictionIso_apply
    (integralOperationsBaseChange g)
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (ramifiedMap l E L X e n j))
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (ramifiedMap l E L Y e n j))
    _ _ (finiteSquare l E L g e n j)
    ((integralOperationsLevelPullback l L g (index e n)).obj
      ((scalar.{t, u} (ramifiedMap l E L Y e n j)).obj N)) (op V)
    (((integralOperationsPullbackAdjunction l L g (index e n)).unit.app _).val.app (op V)
      (((scalarAdjunction.{t, u} (ramifiedMap l E L Y e n j)).unit.app N).val.app
        (op V) x))
  have hh := h.trans he
  simp only [module_comp_apply, pushforward_map_apply,
    scalarAdjunction_unit, pullback_unit_apply] at hh
  change ((finitePullbackSquareIso l E L g e n j).hom.app N).val.app _
    (((scalarAdjunction.{t, u} (ramifiedMap l E L X e n j)).unit.app
      ((integralOperationsLevelPullback l E g n).obj N)).val.app _
        (integralOperationsPullbackGenerator l E g n N V x)) = _ at hh
  simpa only [scalarAdjunction_unit] using hh

end FinitePullback

private theorem reductionSquareIso_tensor (W : Scheme.{t}) (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (data : Coefficients l E L ι e j W) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    ((reductionSquareIso l E L ι W e j data n).hom.app M).val.app U
      (tensor.{t, u} (ramifiedMap l E L W e n (j n)) _ U 1
        (unrestrictedIntegralTensorSection l E W n M U a x)) =
      unrestrictedIntegralTensorSection l L W (index e n)
        ((scalar.{t, u} data.completedMap).obj M) U
        ((ramifiedMap l E L W e n (j n)).hom.app U a)
        (tensor.{t, u} data.completedMap M U 1 x) := by
  rw [reduction_tensor_one l E W n M U a x, scalar_tensor_smul, map_smul,
    reductionSquareIso_unit]
  exact (reduction_tensor_one l L W (index e n)
    ((scalar.{t, u} data.completedMap).obj M) U _ _).symm

/-- Finite scalar extension commutes with reduction followed by geometric pullback.
Source: Stacks Project, Tags 03CZ and 03EL.
(blueprint: lem-weil-ramified-finite-scalar-composition).

Proof: the scalar-restriction square on the source site commutes by
source.ramified_projection. Compose the two scalar adjunctions along either
path and use uniqueness of left adjoints. Their unit equation gives the
normalized reduction comparison. Next the constant finite coefficient square
commutes by naturality in the ring homomorphism j. Composing scalar and
pullback adjunctions along either path gives a second isomorphism by uniqueness
of left adjoints. Its unit equation sends 1 tensor g*(z) to g*(1 tensor z).
Compose this isomorphism with pullback of the reduction comparison. Naturality
of the pullback adjunction unit gives its value on generators. Finally source
and target linearity of scalar tensor sections and the finite reduction tensor
formula give the displayed arbitrary-coefficient formula. No completed scalar
extension on X or coefficient base-change isomorphism is used. -/
theorem finiteScalarComposition_exists {X Y : Scheme.{t}} (g : X ⟶ Y)
    (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (source : Coefficients l E L ι e j Y) (n : ℕ) :
    ∃ d : ∀ M : integralTowerModules l E Y,
      (scalar.{t, u} (ramifiedMap l E L X e n (j n))).obj
          ((integralOperationsLevelPullback l E g n).obj
            ((unrestrictedIntegralReductionFunctor l E Y n).obj M)) ≅
        (integralOperationsLevelPullback l L g (index e n)).obj
          ((unrestrictedIntegralReductionFunctor l L Y (index e n)).obj
            ((scalar.{t, u} source.completedMap).obj M)),
      ∀ (M : integralTowerModules l E Y) (V : Y.ProEt)
        (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
        (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((Scheme.proEtaleBaseChange g).obj V)))
        (c : (integralCoefficientCommRingSheaf l L X (index e n)).obj.obj
          (op ((Scheme.proEtaleBaseChange g).obj V))) (p : M.val.obj (op V)),
        (d M).hom.val.app _
          (tensor.{t, u} (ramifiedMap l E L X e n (j n)) _ _ c
            (b • @id (((integralOperationsLevelPullback l E g n).obj
              ((unrestrictedIntegralReductionFunctor l E Y n).obj M)).val.obj
                (op ((Scheme.proEtaleBaseChange g).obj V)))
              (integralOperationsPullbackGenerator l E g n _ V
                (unrestrictedIntegralTensorSection l E Y n M (op V) a p)))) =
          (c * (ramifiedMap l E L X e n (j n)).hom.app _ b) •
            @id (((integralOperationsLevelPullback l L g (index e n)).obj
              ((unrestrictedIntegralReductionFunctor l L Y (index e n)).obj
                ((scalar.{t, u} source.completedMap).obj M))).val.obj
                  (op ((Scheme.proEtaleBaseChange g).obj V)))
              (integralOperationsPullbackGenerator l L g (index e n) _ V
                (unrestrictedIntegralTensorSection l L Y (index e n)
                  ((scalar.{t, u} source.completedMap).obj M) (op V)
                  ((ramifiedMap l E L Y e n (j n)).hom.app (op V) a)
                  (tensor.{t, u} source.completedMap M (op V) 1 p))) := by
  let P := integralOperationsLevelPullback l L g (index e n)
  let d (M : integralTowerModules l E Y) :=
    (finitePullbackSquareIso l E L g e n (j n)).app
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M) ≪≫
      P.mapIso ((reductionSquareIso l E L ι Y e j source n).app M)
  refine ⟨d, ?_⟩
  intro M V a b c p
  have hu : (d M).hom.val.app _
      (tensor.{t, u} (ramifiedMap l E L X e n (j n)) _ _ 1
        (integralOperationsPullbackGenerator l E g n _ V
          (unrestrictedIntegralTensorSection l E Y n M (op V) a p))) =
      integralOperationsPullbackGenerator l L g (index e n) _ V
        (unrestrictedIntegralTensorSection l L Y (index e n)
          ((scalar.{t, u} source.completedMap).obj M) (op V)
          ((ramifiedMap l E L Y e n (j n)).hom.app (op V) a)
          (tensor.{t, u} source.completedMap M (op V) 1 p)) := by
    change (P.map ((reductionSquareIso l E L ι Y e j source n).hom.app M)).val.app _
      (((finitePullbackSquareIso l E L g e n (j n)).hom.app _).val.app _ _) = _
    rw [finitePullbackSquareIso_unit]
    have hn := congrArg (fun k ↦ k.val.app (op V)
      (tensor.{t, u} (ramifiedMap l E L Y e n (j n)) _ (op V) 1
        (unrestrictedIntegralTensorSection l E Y n M (op V) a p)))
      ((integralOperationsPullbackAdjunction l L g (index e n)).unit.naturality
        ((reductionSquareIso l E L ι Y e j source n).hom.app M))
    change integralOperationsPullbackGenerator l L g (index e n) _ V
      (((reductionSquareIso l E L ι Y e j source n).hom.app M).val.app (op V) _) = _ at hn
    exact hn.symm.trans (congrArg
      (integralOperationsPullbackGenerator l L g (index e n) _ V)
      (reductionSquareIso_tensor l E L ι Y e j source n M (op V) a p))
  simp only [P, Functor.comp_obj, Functor.op_obj, unop_op] at hu
  rw [scalar_tensor_one, scalar_tensor_smul, map_smul, map_smul]
  simpa only [id_eq, smul_smul, Functor.op_obj, unop_op] using congrArg
    (fun z : (((integralOperationsLevelPullback l L g (index e n)).obj
        ((unrestrictedIntegralReductionFunctor l L Y (index e n)).obj
          ((scalar.{t, u} source.completedMap).obj M))).val.obj
            (op ((Scheme.proEtaleBaseChange g).obj V))) ↦
      c • (ramifiedMap l E L X e n (j n)).hom.app _ b • z) hu

end WeilConjectures.RamifiedPullback
