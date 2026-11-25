/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbRootTowerPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Invertibility of discrete integral tensor transport

Source: Stacks Project, `sites-modules.tex`, Tags 03EK and 03EL.
(blueprint: new-weil-frobenius-integral-discrete-transport-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures

attribute [local irreducible] MorphismProperty.Over.pullback constantSheaf Padic

private theorem tensorMap_bijective
    {R S M N M' N' : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module S M'] [Module S N']
    (ρ : R →+* S) (hρ : Function.Bijective ρ)
    (f : M →ₛₗ[ρ] M') (g : N →ₛₗ[ρ] N')
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (TensorProduct.map f g) := by
  let e := RingEquiv.ofBijective ρ hρ
  let : RingHomInvPair ρ e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom ρ := RingHomInvPair.of_ringEquiv_symm e
  exact (TensorProduct.congr (LinearEquiv.ofBijective f hf)
    (LinearEquiv.ofBijective g hg)).bijective

private abbrev integralDiscrete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)

private abbrev integralRaw
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap T l E) (integralDiscrete l E T)

private def rawTransportApp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.ProEtᵒᵖ) :
    (integralRaw l E Y).presheaf.obj U ⟶
      (integralRaw l E X).presheaf.obj ((proEtaleBaseChange g).op.obj U) := by
  let V := (proEtaleBaseChange g).op.obj U
  let RY := (purTwistZlConstant Y l).obj.obj U
  let RX := (purTwistZlConstant X l).obj.obj V
  let BY := (purTwistIntegralConstant Y l E).obj.obj U
  let BX := (purTwistIntegralConstant X l E).obj.obj V
  let : Module RY BY := Module.compHom BY
    ((purTwistConstantIntegersMap Y l E).hom.app U).hom
  let : Module RX BX := Module.compHom BX
    ((purTwistConstantIntegersMap X l E).hom.app V).hom
  let ρ : RY →+* RX := ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).hom.app U).hom
  let σ : BY →+* BX := ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app U).hom
  let fB : BY →ₛₗ[ρ] BX :=
    { toFun := σ
      map_add' := map_add σ
      map_smul' := by
        intro a b
        change σ (((purTwistConstantIntegersMap Y l E).hom.app U a) * b) =
          ((purTwistConstantIntegersMap X l E).hom.app V (ρ a)) * σ b
        rw [map_mul]
        congr 1
        let k : CommRingCat.of (ULift.{u + 1} ℤ_[l]) ⟶
            CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
          CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            ((purTwistIntegersMap l E).comp ULift.ringEquiv.toRingHom))
        exact congrArg (fun k ↦ k.hom.app U a)
          (AlgebraicGeometry.Scheme.constant_naturality g k) }
  let fM : (integralDiscrete l E Y).val.obj U →ₛₗ[ρ]
      (integralDiscrete l E X).val.obj V :=
    { toFun := (AlgebraicGeometry.Scheme.root_direct l g).hom.app U
      map_add' := map_add _
      map_smul' := fun a x ↦ AlgebraicGeometry.Scheme.root_limit_linear l g U.unop a x }
  exact AddCommGrpCat.ofHom (TensorProduct.map fB fM).toAddMonoidHom

private theorem rawTransportApp_tmul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.ProEtᵒᵖ)
    (b : (purTwistIntegralConstant Y l E).obj.obj U)
    (x : (integralDiscrete l E Y).val.obj U) :
    rawTransportApp l E g U (b ⊗ₜ[(purTwistZlConstant Y l).obj.obj U,
      ((purTwistConstantIntegersMap Y l E).hom.app U).hom] x) =
      (show (purTwistIntegralConstant X l E).obj.obj ((proEtaleBaseChange g).op.obj U)
        from (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app U b)
        ⊗ₜ[(purTwistZlConstant X l).obj.obj ((proEtaleBaseChange g).op.obj U),
          ((purTwistConstantIntegersMap X l E).hom.app
            ((proEtaleBaseChange g).op.obj U)).hom]
        (show (integralDiscrete l E X).val.obj ((proEtaleBaseChange g).op.obj U) from
          (AlgebraicGeometry.Scheme.root_direct l g).hom.app U x) := by
  rfl

attribute [local irreducible] rawTransportApp AlgebraicGeometry.Scheme.root_direct

private theorem rawTransportApp_naturality_tmul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) {U V : Y.ProEtᵒᵖ} (i : U ⟶ V)
    (b : (purTwistIntegralConstant Y l E).obj.obj U)
    (x : (integralDiscrete l E Y).val.obj U) :
    rawTransportApp l E g V
        ((integralRaw l E Y).presheaf.map i (b ⊗ₜ[_, _] x)) =
      (integralRaw l E X).presheaf.map ((proEtaleBaseChange g).op.map i)
        (rawTransportApp l E g U (b ⊗ₜ[_, _] x)) := by
  change rawTransportApp l E g V
      (SheafOfModules.changeOfRingsMapOfUniverses (purTwistConstantIntegersMap Y l E)
        (integralDiscrete l E Y) i (b ⊗ₜ[_, _] x)) =
    SheafOfModules.changeOfRingsMapOfUniverses (purTwistConstantIntegersMap X l E)
      (integralDiscrete l E X) ((proEtaleBaseChange g).op.map i)
      (rawTransportApp l E g U (b ⊗ₜ[_, _] x))
  have hY := SheafOfModules.changeOfRingsMap_tmulOfUniverses
    (purTwistConstantIntegersMap Y l E) (integralDiscrete l E Y) i b x
  have hX := SheafOfModules.changeOfRingsMap_tmulOfUniverses
    (purTwistConstantIntegersMap X l E) (integralDiscrete l E X)
    ((proEtaleBaseChange g).op.map i)
    (show (purTwistIntegralConstant X l E).obj.obj ((proEtaleBaseChange g).op.obj U)
      from (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
          U b)
    (show (integralDiscrete l E X).val.obj ((proEtaleBaseChange g).op.obj U) from
      (AlgebraicGeometry.Scheme.root_direct l g).hom.app U x)
  refine (congrArg (rawTransportApp l E g V) hY).trans ?_
  refine (rawTransportApp_tmul l E g V _ _).trans ?_
  refine Eq.trans ?_ ((congrArg
    (SheafOfModules.changeOfRingsMapOfUniverses (purTwistConstantIntegersMap X l E)
      (integralDiscrete l E X) ((proEtaleBaseChange g).op.map i))
    (rawTransportApp_tmul l E g U b x)).trans hX).symm
  apply congrArg₂ (fun
    (s : (purTwistIntegralConstant X l E).obj.obj ((proEtaleBaseChange g).op.obj V))
    (y : (integralDiscrete l E X).val.obj ((proEtaleBaseChange g).op.obj V)) ↦
    s ⊗ₜ[(purTwistZlConstant X l).obj.obj ((proEtaleBaseChange g).op.obj V),
      ((purTwistConstantIntegersMap X l E).hom.app
        ((proEtaleBaseChange g).op.obj V)).hom] y)
  · exact (ConcreteCategory.congr_hom
      ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionIntegers l E)))).hom.naturality i) b)
  · change (AlgebraicGeometry.Scheme.root_direct l g).hom.app V
        ((purTwistZlOne Y l).obj.map i x) =
      (purTwistZlOne X l).obj.map ((proEtaleBaseChange g).op.map i)
        ((AlgebraicGeometry.Scheme.root_direct l g).hom.app U x)
    exact ConcreteCategory.congr_hom
      ((AlgebraicGeometry.Scheme.root_direct l g).hom.naturality i) x

private def rawTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (integralRaw l E Y).presheaf ⟶
      (proEtaleBaseChange g).op ⋙ (integralRaw l E X).presheaf where
  app := rawTransportApp l E g
  naturality := by
    intro U V i
    ext z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b x => exact rawTransportApp_naturality_tmul l E g i b x

attribute [local semireducible] AlgebraicGeometry.Scheme.root_direct

private theorem rawTransportApp_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsIso (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} ℤ_[l])))]
    [IsIso (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))]
    [IsIso (AlgebraicGeometry.Scheme.root_direct l g)] (U : Y.ProEtᵒᵖ) :
    IsIso (rawTransportApp l E g U) := by
  let : Module ((purTwistZlConstant Y l).obj.obj U)
      ((purTwistIntegralConstant Y l E).obj.obj U) := Module.compHom _
    ((purTwistConstantIntegersMap Y l E).hom.app U).hom
  let : Module ((purTwistZlConstant X l).obj.obj ((proEtaleBaseChange g).op.obj U))
      ((purTwistIntegralConstant X l E).obj.obj ((proEtaleBaseChange g).op.obj U)) :=
    Module.compHom _ ((purTwistConstantIntegersMap X l E).hom.app
      ((proEtaleBaseChange g).op.obj U)).hom
  unfold rawTransportApp
  apply (ConcreteCategory.isIso_iff_bijective _).2
  apply tensorMap_bijective
  · exact ConcreteCategory.bijective_of_isIso
      ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).hom.app U)
  · exact ConcreteCategory.bijective_of_isIso
      ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app U)
  · exact ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.Scheme.root_direct l g).hom.app U)

private theorem constantDirect_isIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{u + 1}) :
    IsIso (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A) := by
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
    g CommRingCat.{u + 1}).2.1
  let := (proEtaleIso_constantComparison g CommRingCat.{u + 1}).1 A
  have h : proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A =
      adj.unit.app _ ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} A) :=
    (adj.homEquiv _ _).apply_symm_apply
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A) |>.symm
  rw [h]
  infer_instance

/-- Invertibility of the discrete scalar-extension comparison.

Source: Stacks Project, `sites-modules.tex`, Tag 03EL, and the inverse-image site
comparison for a scheme isomorphism.
Proof: the adjunction unit and the direct image of r are isomorphisms, so
its adjunct on the root limit is invertible. The constant Z_l and O_E comparisons
are invertible for the same reason. Their component ring and semilinear module
maps induce a bijective map of sectionwise tensor products by TensorProduct.congr.
Naturality holds on pure tensors and then by tensor induction. The sheafification
unit on X is locally bijective, and precomposition by the cocontinuous base-change
site equivalence preserves local bijectivity. The given formula identifies the
composite of the sheafification unit on Y with phi with the raw tensor isomorphism
followed by this precomposed unit. Both unit maps and the raw tensor map belong to
the sheafification equivalences W. Their two-out-of-three property puts phi in W;
a map between sheaves in W is an isomorphism. This argument also covers zero
section rings and the empty scheme. The construction and scalar compatibility
of phi are separate from this invertibility assertion.
(blueprint: new-weil-frobenius-integral-discrete-transport-invertible). -/
theorem frobeniusIntegralDiscreteTransport_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose))
    (hrIso : IsIso r)
    (φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)))
    (hform : ∀ (V : Y.ProEt) (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
        (x : (purTwistZlOne Y l).obj.obj (op V)),
        φ.hom.app (op V) (purTwistIntegralTensor Y l E (op V) b x) =
          purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V))
            ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
              (op V) b)
            (r.hom.app (op ((proEtaleBaseChange g).obj V))
              (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
                (purTwistZlOne Y l)).hom.app (op V) x))) : IsIso φ := by
  let := hrIso
  let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
    g AddCommGrpCat.{u + 1}).2.1
  have hroot : AlgebraicGeometry.Scheme.root_direct l g =
      ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
        (purTwistZlOne Y l)) ≫
        (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map r := by
    rw [hr]
    rfl
  have : IsIso (AlgebraicGeometry.Scheme.root_direct l g) := by
    rw [hroot]
    infer_instance
  have := constantDirect_isIso g (CommRingCat.of (ULift.{u + 1} ℤ_[l]))
  have := constantDirect_isIso g
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
  have : IsIso (rawTransport l E g) :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun U ↦ rawTransportApp_isIso l E g U)
  let ηY : (integralRaw l E Y).presheaf ⟶
      ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E)).obj :=
    toSheafify (ProEt.topology Y) (integralRaw l E Y).presheaf
  let ηX : (proEtaleBaseChange g).op ⋙ (integralRaw l E X).presheaf ⟶
      ((proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E))).obj :=
    Functor.whiskerLeft (proEtaleBaseChange g).op
      (toSheafify (ProEt.topology X) (integralRaw l E X).presheaf)
  have hη : (ProEt.topology Y).W ηX := by
    let e := AlgebraicGeometry.Scheme.isoBaseChangeEquivalence g
    have : e.inverse.IsContinuous (ProEt.topology X) (ProEt.topology Y) := by
      change (proEtaleIsoPostcompose g).IsContinuous _ _
      exact AlgebraicGeometry.Scheme.isoPostcompose_continuous g
    let : (proEtaleBaseChange g).IsCocontinuous (ProEt.topology Y) (ProEt.topology X) :=
      (e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
        (CoverPreserving.of_isContinuous e.inverse _ _)
    let := Presheaf.isLocallyInjective_whisker (ProEt.topology Y) (ProEt.topology X)
      (proEtaleBaseChange g)
      (toSheafify (ProEt.topology X) (integralRaw l E X).presheaf)
    let := Presheaf.isLocallySurjective_whisker (ProEt.topology Y) (ProEt.topology X)
      (proEtaleBaseChange g)
      (toSheafify (ProEt.topology X) (integralRaw l E X).presheaf)
    exact (ProEt.topology Y).W_of_isLocallyBijective ηX
  have heq : ηY ≫ φ.hom = rawTransport l E g ≫ ηX := by
    ext U z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b x =>
      change φ.hom.app U (purTwistIntegralTensor Y l E U b x) =
        (toSheafify (ProEt.topology X) (integralRaw l E X).presheaf).app
          ((proEtaleBaseChange g).op.obj U)
          (rawTransportApp l E g U (b ⊗ₜ[_, _] x))
      rw [rawTransportApp_tmul]
      change φ.hom.app U (purTwistIntegralTensor Y l E U b x) =
        purTwistIntegralTensor X l E ((proEtaleBaseChange g).op.obj U) _
          ((AlgebraicGeometry.Scheme.root_direct l g).hom.app U x)
      refine (hform U.unop b x).trans ?_
      rw [hroot]
      rfl
  apply ((ProEt.topology Y).W_sheafToPresheaf_map_iff_isIso φ).mp
  apply (ProEt.topology Y).W.of_precomp ηY φ.hom
    ((ProEt.topology Y).W_toSheafify (integralRaw l E Y).presheaf)
  rw [heq]
  exact (ProEt.topology Y).W.comp_mem _ _
    (((ProEt.topology Y).W_iff _).2 inferInstance) hη

end WeilConjectures
