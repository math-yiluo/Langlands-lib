/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralDiscreteTransport
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralRootScalar
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientTensor

/-! # Additive transport input for the first integral root line

This is the additive sheaf comparison used to construct the module comparison.
(blueprint: lem-weil-frobenius-integral-root-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage
  MorphismProperty.Over.pullback constantSheaf Padic
attribute [local instance_reducible] PurCompactSupport.completed

private theorem rootTransport_isIso
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    IsIso r := by
  rw [hr]
  let c := ((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose
  have hc : ∀ n, IsIso (c.app n) := by
    intro n
    dsimp only [c]
    rw [((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose_spec n.unop]
    exact ((proEtaleRootsOfUnityInverseImageIso g).2.2.2 inferInstance
      (l ^ (n.unop + 1)) (pow_pos (Fact.out : l.Prime).pos _)).1
  have : IsIso c := (NatTrans.isIso_iff_isIso_app c).2 hc
  have := proEtaleIso_inverseLimitComparison g AddCommGrpCat.{u + 1}
    (proEtaleRootsOfUnityTower Y l Fact.out)
  infer_instance

private theorem integralTransportScalar_of_tensors
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)))
    (hp : ∀ (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
      (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
      (x : (purTwistZlOne Y l).obj.obj (op V)),
      φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a
            (purTwistIntegralTensor Y l E (op V) b x)) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) (purTwistIntegralTensor Y l E (op V) b x))) :
    ∀ (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
      (t : (purTwistIntegralModule Y l E).val.obj (op V)),
      φ.hom.app (op V)
        (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a t) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) t) := by
  intro U a t
  let := purTwistIntegralAction Y l E (op U)
  let := purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj U))
  let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap Y l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap Y l))).obj (purTwistZlModule Y l))
  let FY := (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E)
  let FX := (SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)
  let F := (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj FX
  let η : P.presheaf ⟶ FY.obj := toSheafify (ProEt.topology Y) P.presheaf
  have : Presheaf.IsLocallySurjective (ProEt.topology Y) η := by
    dsimp only [η]
    infer_instance
  apply F.isSeparated _ _ (Presheaf.imageSieve_mem (ProEt.topology Y) η t)
  rintro V f ⟨y, hy⟩
  let := purTwistIntegralAction Y l E (op V)
  let := purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))
  let a' := (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f.op a
  let t' : (purTwistIntegralModule Y l E).val.obj (op V) :=
    (purTwistIntegralModule Y l E).val.map f.op t
  have hn (z : FY.obj.obj (op U)) :
      F.obj.map f.op (φ.hom.app (op U) z) =
        φ.hom.app (op V) (FY.obj.map f.op z) :=
    (ConcreteCategory.congr_hom (φ.hom.naturality f.op) z).symm
  have hL : F.obj.map f.op (φ.hom.app (op U) (a • t)) =
      φ.hom.app (op V) (a' • t') := by
    rw [hn]
    exact congrArg (φ.hom.app (op V))
      (purTwistIntegralAction_restriction Y l E f.op a t)
  have hc : (completedIntegralCoefficientSheafUnrestricted l E X).obj.map
        ((proEtaleBaseChange g).op.map f.op)
        ((sfCompletedCoefficientMap l E g).hom.app (op U) a) =
      (sfCompletedCoefficientMap l E g).hom.app (op V) a' :=
    (ConcreteCategory.congr_hom
      ((sfCompletedCoefficientMap l E g).hom.naturality f.op) a).symm
  have hR : F.obj.map f.op
        (@SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj U))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op U) a)
          (φ.hom.app (op U) t)) =
      @SMul.smul _ _
        (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
        ((sfCompletedCoefficientMap l E g).hom.app (op V) a')
        (φ.hom.app (op V) t') := by
    exact (purTwistIntegralAction_restriction X l E
      ((proEtaleBaseChange g).op.map f.op)
      ((sfCompletedCoefficientMap l E g).hom.app (op U) a)
      (φ.hom.app (op U) t)).trans
      (congrArg₂ (fun c z ↦ @SMul.smul _ _
        (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul c z)
        hc (hn t))
  refine hL.trans (Eq.trans ?_ hR.symm)
  change η.app (op V) y = t' at hy
  rw [← hy]
  clear hy
  let ψ : (purTwistIntegralOne Y l E).val.obj (op V) →+
      (purTwistIntegralOne X l E).val.obj (op ((proEtaleBaseChange g).obj V)) :=
    (φ.hom.app (op V)).hom
  let e : P.obj (op V) →+ (purTwistIntegralOne Y l E).val.obj (op V) :=
    (η.app (op V)).hom
  let c : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op ((proEtaleBaseChange g).obj V)) :=
    (sfCompletedCoefficientMap l E g).hom.app (op V) a'
  change ψ (a' • e y) = c • ψ (e y)
  induction y using TensorProduct.inductionOn with
  | add y z h y' => simp only [map_add, smul_add, h, y']
  | tmul b x => exact hp V a' b x

/-- The additive inverse-image transport of the first completed integral root line.

Source: literature/stacks-project/sites-modules.tex, Tags 03EK and 03EL; expanded DAG
clause 2 of `prose-10-21`.
Proof: finite root comparisons commute with transitions, hence their inverse limit gives
an additive isomorphism. Tensor presentation transport extends it across the constant
integral coefficients and the completed coefficient pushout. The resulting additive map
is semilinear for the completed coefficient comparison and has the displayed formula on
pure root tensors. This is the additive part of the module transport; the parent theorem
performs the adjunction step turning it into a module isomorphism.
(blueprint: new-weil-frobenius-integral-root-transport-additive). -/
theorem frobeniusIntegralRootTransport_additive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    ∃ φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)),
      IsIso φ ∧
      (∀ (V : Y.ProEt) (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (op V)) (x : (purTwistZlOne Y l).obj.obj (op V)),
        φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a
            (purTwistIntegralTensor Y l E (op V) 1 x)) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V)) 1
            (r.hom.app (op ((proEtaleBaseChange g).obj V))
            (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
              (purTwistZlOne Y l)).hom.app (op V) x)))) ∧
      (∀ (V : Y.ProEt) (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (op V)) (t : (purTwistIntegralModule Y l E).val.obj (op V)),
        φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a t) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) t)) := by
  obtain ⟨φ, hφ, hform, hdiscrete⟩ :=
    frobeniusIntegralDiscreteTransport l E g r hr (rootTransport_isIso l g r hr)
  have hB (V : Y.ProEt) (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
      (t : (purTwistIntegralModule Y l E).val.obj (op V)) :
      φ.hom.app (op V) (((purTwistIntegralCompletionMap Y l E).hom.app (op V) b) • t) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V)
            ((purTwistIntegralCompletionMap Y l E).hom.app (op V) b))
          (φ.hom.app (op V) t) := by
    exact (congrArg (φ.hom.app (op V))
      ((purTwistIntegralAction_existsUnique Y l E).exists.choose_spec.2.1 (op V) b t)).trans
      (hdiscrete V b t)
  have hR (V : Y.ProEt) (a : (purTwistZlCompletion Y l).obj.obj (op V))
      (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
      (x : (purTwistZlOne Y l).obj.obj (op V)) :
      φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul
            ((purTwistCompletedScalarMap Y l E).hom.app (op V) a)
            (purTwistIntegralTensor Y l E (op V) b x)) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V)
            ((purTwistCompletedScalarMap Y l E).hom.app (op V) a))
          (φ.hom.app (op V) (purTwistIntegralTensor Y l E (op V) b x)) := by
    rw [(purTwistIntegralAction_existsUnique Y l E).exists.choose_spec.2.2]
    rw [hform, hform]
    exact frobeniusIntegralRootScalar l E g r hr V a b x
  have hp (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
      (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
      (x : (purTwistZlOne Y l).obj.obj (op V)) :
      φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a
            (purTwistIntegralTensor Y l E (op V) b x)) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) (purTwistIntegralTensor Y l E (op V) b x)) := by
    let := purTwistIntegralAction Y l E (op V)
    let := purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))
    let := ((purTwistConstantIntegersMap Y l E).hom.app (op V)).hom.toAlgebra
    let := ((purTwistZlCompletionMap Y l).hom.app (op V)).hom.toAlgebra
    let ψ : (purTwistIntegralOne Y l E).val.obj (op V) →+
        (purTwistIntegralOne X l E).val.obj (op ((proEtaleBaseChange g).obj V)) :=
      (φ.hom.app (op V)).hom
    let σ : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V) →+*
        (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (op ((proEtaleBaseChange g).obj V)) :=
      ((sfCompletedCoefficientMap l E g).hom.app (op V)).hom
    let d : (purTwistIntegralConstant Y l E).obj.obj (op V) →+*
        (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V) :=
      ((purTwistIntegralCompletionMap Y l E).hom.app (op V)).hom
    let c : (purTwistZlCompletion Y l).obj.obj (op V) →+*
        (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V) :=
      ((purTwistCompletedScalarMap Y l E).hom.app (op V)).hom
    have hB' (s : (purTwistIntegralConstant Y l E).obj.obj (op V))
        (t : (purTwistIntegralOne Y l E).val.obj (op V)) :
        ψ (d s • t) = σ (d s) • ψ t := hB V s t
    have hR' (z : (purTwistZlCompletion Y l).obj.obj (op V)) :
        ψ (c z • purTwistIntegralTensor Y l E (op V) b x) =
          σ (c z) • ψ (purTwistIntegralTensor Y l E (op V) b x) := hR V z b x
    change ψ (a • purTwistIntegralTensor Y l E (op V) b x) =
      σ a • ψ (purTwistIntegralTensor Y l E (op V) b x)
    obtain ⟨w, rfl⟩ := (purTwistCoefficientTensor Y l E (op V)).surjective a
    induction w using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, add_smul, hy, hz]
    | tmul s z =>
      change ψ ((d s * c z) • purTwistIntegralTensor Y l E (op V) b x) =
        σ (d s * c z) • ψ (purTwistIntegralTensor Y l E (op V) b x)
      rw [mul_smul, hB', hR', map_mul, mul_smul]
  have hscalar := integralTransportScalar_of_tensors l E g φ hp
  refine ⟨φ, hφ, ?_, hscalar⟩
  intro V a x
  exact (hscalar V a (purTwistIntegralTensor Y l E (op V) 1 x)).trans (by
    rw [hform]
    rw [map_one])

end WeilConjectures
