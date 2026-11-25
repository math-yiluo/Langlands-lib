/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # Transport used to evaluate scalar mates

Source: Stacks 03DA, 0D6E, 0E8I and 0940.
(blueprint: def-pur-strict-scalar-finite-evaluation-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf CategoryTheory.Limits.limit
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of the separately derived proper/open functor on constant towers.
Source: Stacks 0D6E, 0E8I, 0940
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
def constantImageEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    image l E c ⋙ ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n ≅
      ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n ⋙
        PurCompactSupport.image (constants l E) c := by
  have := evalR_isIso (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g n
  exact Functor.isoWhiskerLeft
      (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i)
      (asIso (evalR (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g n)) ≪≫
    Functor.isoWhiskerRight
      (evalJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i n) _

/-- The ring homomorphism defining the constant integral quotient.
Source: Stacks 03CO
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
def constantFiniteRingMap (m : ℕ) :
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) :=
  CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E m)).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))

/-- The constant integral quotient as a coefficient change at a positive exponent.
Source: Stacks 03CO
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
def constantFiniteChange (m : ℕ) (hm : 1 ≤ m) :
    PurCompactSupport.Change (constants l E) (PurCompactSupport.finite l E m hm) where
  map W := (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (constantFiniteRingMap l E m)
  square g := (proEtaleConstantInverseImageMap_naturality g
    (constantFiniteRingMap l E m)).symm

/-- The completed projection recovers the constant quotient leg.
Source: Stacks 03CO; the limit cone identity
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
theorem constantFiniteChange_projection (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    integralConstantToCompletionOfUniverses l E W ≫
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (PurCompactSupport.projection l E m hm W) =
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantFiniteChange l E m hm).map W) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  change integralConstantToCompletionOfUniverses l E W ≫
    (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (PurCompactSupport.projection l E (n + 1) hm W) =
        integralConstantQuotientOfUniverses l E W n
  have hp : PurCompactSupport.projection l E (n + 1) hm W =
      completedIntegralCommRingProjectionUnrestricted l E W n := by
    simp only [PurCompactSupport.projection, eqToHom_refl, Category.comp_id]
    congr 1
  rw [hp]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg (fun q ↦ (q.hom.app U).hom x)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))

/-- Restricting first to the completion and then to its constant subring is the
same normalized restriction as restricting along the constant quotient.
Source: Stacks 03DA
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
def positiveRestrictionIdentification (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    positiveRestriction l E W m hm ≅
      pbcDerivedRestrict ((constantFiniteChange l E m hm).map W) := by
  let a := integralConstantToCompletionOfUniverses l E W
  let b := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (PurCompactSupport.projection l E m hm W)
  let d := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantFiniteChange l E m hm).map W)
  have h : a ≫ b = d := constantFiniteChange_projection l E W m hm
  let e : ordinaryPositiveRestriction l E W m hm ≅
      pbcRestrict ((constantFiniteChange l E m hm).map W) :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (b.hom.app U).hom
          (d.hom.app U).hom
          (congrArg (fun t ↦ (t.hom.app U).hom) h.symm) (M.val.obj U)).symm)
        (fun {_ _} f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  exact Functor.mapDerivedCategoryNatIso e

/-- Finite proper/open image commutes with the actual positive coefficient
restriction. The direction here goes from constant-coefficient image to finite image.
Source: Stacks 0D6E, 0E8I
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
def positiveImageRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (m : ℕ) (hm : 1 ≤ m) :
    positiveRestriction l E X m hm ⋙ PurCompactSupport.image (constants l E) c ≅
      PurCompactSupport.image (PurCompactSupport.finite l E m hm) c ⋙
        positiveRestriction l E Y m hm :=
  Functor.isoWhiskerRight (positiveRestrictionIdentification l E X m hm) _ ≪≫
    PurCompactSupport.restriction (constantFiniteChange l E m hm) c ≪≫
    Functor.isoWhiskerLeft _ (positiveRestrictionIdentification l E Y m hm).symm

/-- Evaluation of the input reduction before applying any geometric functor.
Source: Stacks 0940
(blueprint: def-pur-strict-scalar-finite-evaluation-transport). -/
def reductionEvaluation (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) (n : ℕ) :
    reduction l E W S ⋙
        ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W n ≅
      pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
        (Nat.le_add_left 1 n) W) ⋙ finiteRestriction l E W n :=
  Functor.isoWhiskerLeft S.reduction (evaluationRestriction l E W n) ≪≫
    Functor.isoWhiskerRight (S.reductionEvaluation n) _ ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E W n).symm _

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

end WeilConjectures.PurStrictScalar
