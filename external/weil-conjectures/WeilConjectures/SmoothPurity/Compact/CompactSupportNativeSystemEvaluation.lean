/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange

/-! # Canonical evaluation of native compact-support systems

Source: Stacks 03DI, 0D6E; Bhatt--Scholze 6.7.6
(blueprint: def-weil-compact-support-native-system-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The section-normalized comparison of the two ordinary direct-image models.
Source: Stacks 03DI, 03D2
(blueprint: def-weil-compact-support-native-system-evaluation). -/
def compactSupportDirectModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    ProEtale.StrictTower.moduleDirectImage (ULift.{u + 1, u} A) f ≅
      proEtaleConstantModuleDirectImage f A := by
  apply SheafOfModules.pushforwardCongr
  apply Sheaf.hom_ext
  apply congrArg (fun z : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A) ↦
    Functor.whiskerRight z.hom (forget₂ CommRingCat RingCat))
  exact ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

/-- The comparison of open extensions determined by their adjunction units.
Source: Stacks 03DI, 03D2
(blueprint: def-weil-compact-support-native-system-evaluation). -/
def compactSupportOpenModel {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    ProEtale.StrictTower.moduleJ (ULift.{u + 1, u} A) j ≅
      sfIntrinsicExtensionByZero j A := by
  exact (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} A) j).leftAdjointUniq
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm)

/-- The positive coefficient ring in the native sequence-site presentation.
Source: Stacks 03DI, 0D6E
(blueprint: def-weil-compact-support-native-system-evaluation). -/
@[instance_reducible]
def compactSupportSystemLevel (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The adjacent quotient in the native sequence-site presentation.
Source: Stacks 03DI, 0D6E
(blueprint: def-weil-compact-support-native-system-evaluation). -/
@[instance_reducible]
def compactSupportSystemQuotient (n : ℕ) :
    compactSupportSystemLevel l E (n + 1) ⟶ compactSupportSystemLevel l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift

/-- The canonical geometric evaluation, with the native adjunction normalization.
Source: Stacks 03DI, 0D6E
(blueprint: def-weil-compact-support-native-system-evaluation). -/
def compactSupportSystemEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g) ⋙
      coefficientSequenceDerivedEvaluation.{u, u} l E Y n ≅
    coefficientSequenceDerivedEvaluation.{u, u} l E X n ⋙
      sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) := by
  have := proEtaleConstantModuleDirectImage_additive c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  have := sfIntrinsicExtensionByZero_additive c.i
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let J := ProEtale.VaryingRing.J R q c.i
  let P := ProEtale.VaryingRing.P R q c.g
  let eP := ProEtale.VaryingRing.evalP R q c.g n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel c.g (Padic.coefficientExtensionRing l E (n + 1))))
  let eJ := ProEtale.VaryingRing.evalJ R q c.i n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel c.i (Padic.coefficientExtensionRing l E (n + 1))))
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft J eP ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eJ _ ≪≫
      Functor.associator _ _ _

end WeilConjectures
