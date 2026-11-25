/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations

/-!
# Finite pullback composition in the integral tower presentation

Source: Stacks Project, Tag 0D6D, and Modules on Sites, Tag 03D3
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).

The general ring-sheaf comparison remains publicly imported. The additional interface
identifies the coefficient-sized tower pullback with the same constant-ring pullback,
with its tensor-unit normalization, and exposes the constant-coefficient specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two presentations of finite pullback have a unique unit-preserving identification.
Source: Stacks Tag 0D6D and Modules on Sites, Tag 03D3
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition).
Proof: both right adjoints are sectionwise direct image with the constant-section
coefficient action. The inverse-image adjunction identifies their coefficient maps:
both adjoints send every constant section to itself. Thus their right adjoints agree
canonically on sections. Take the corresponding mate between the left adjoints.
The mate equation is the displayed unit equation. The adjunction Hom bijection makes
this equation determine the comparison uniquely. It is invertible because the
right-adjoint comparison is invertible. This identifies the termwise pullbacks used
in the K-flat composition construction of Tag 0D6D, on all complexes and chain maps. -/
theorem integralFinitePullbackModel_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! a : integralOperationsLevelPullback l E f n ≅
        proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f,
      ∀ (M : integralOperationsFiniteModules l E Y n) (U : Y.ProEt)
        (m : M.val.obj (op U)),
        (a.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
            (((coefficientProEtaleModuleAdjunction f
              (CommRingCat.of (ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (n + 1))))).unit.app M).val.app (op U) m) =
          ((proEtaleConstantRingAdjunction
            (Padic.coefficientExtensionRing l E (n + 1)) f).unit.app M).val.app (op U) m := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} A))
  let adj₂ := proEtaleConstantRingAdjunction A f
  -- The adjoint of the inverse-image coefficient map is the original constant-section map.
  have hρ : proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
      coefficientProEtaleDirectRingMap.{u, u} f (CommRingCat.of (ULift.{u + 1} A)) := by
    change (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      (proEtaleCoefficientInverseImageMap f A) = _
    exact ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
      (proEtaleCoefficientDirectImageMap f A)
  let d : proEtaleConstantRingPushforward A f ≅
      coefficientProEtaleModuleDirectImage.{u, u} f (CommRingCat.of (ULift.{u + 1} A)) :=
    SheafOfModules.pushforwardCongr (by
      exact congrArg (fun q ↦
        (sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q) hρ)
  -- Conjugating the sectionwise identity gives the unit-normalized pullback comparison.
  let a := (conjugateIsoEquiv adj₂ adj₁).symm d
  have ha : ∀ (M : integralOperationsFiniteModules l E Y n) (U : Y.ProEt)
      (m : M.val.obj (op U)),
      (a.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
        ((adj₁.unit.app M).val.app (op U) m) =
          (adj₂.unit.app M).val.app (op U) m := by
    intro M U m
    exact (congrArg (fun z ↦ z.val.app (op U) m)
      (unit_conjugateEquiv_symm adj₂ adj₁ d.hom M)).symm
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext M
  -- The unit equation determines each component through the adjunction Hom bijection.
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (hb M U.unop m).trans (ha M U.unop m).symm

/-- The uniquely unit-normalized change of presentation for finite pullback.
Source: Stacks Tags 03D3 and 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition). -/
def integralFinitePullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsLevelPullback l E f n ≅
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  Classical.choose (integralFinitePullbackModel_existsUnique l E f n).exists

/-- The published finite composition, specialized to the actual constant quotient rings.
It has direction composite pullback to iterated pullback, as in Tag 0D6D.
Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition). -/
def integralFiniteCanonicalPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (h ≫ k) ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) k ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) h :=
  (proEtaleConstantRingPullbackComposition h k
    (Padic.coefficientExtensionRing l E (n + 1))).symm

end WeilConjectures
