/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePowerFlat
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
import all WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
import WeilConjectures.AlgebraicGeometry.Completed.CompletedLineDerived
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSingleSupport

import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.SmoothPurity.Supporting.FirstRootCoefficientScalarComparison
import WeilConjectures.SmoothPurity.Supporting.Scalar.OrdinaryScalarTensorLineTransport
import WeilConjectures.SmoothPurity.Scalar.ScalarSemilinearDualExt

/-! # Coefficient Tate twists

Source: blueprint `sec-smooth-purity/sk-def-sf-admissible/def-coefficient-twists-detailed.md`,
order 1505; current main-20261015 source: `sec-proetale-coefficients/sk-def-sp-tate-twist/`,
order 1864 (blueprint: definition-tate-twists).

The intrinsic rational and common-stage functors are provided by
`WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted`;
this module supplies their shared signed lines and ordinary tensor/scalar comparison.

## Main definitions and statements

- `WeilConjectures.coefficientTateTwists`
- `WeilConjectures.coefficientTwistPower`
- `WeilConjectures.coefficientTwistLine`
- `WeilConjectures.coefficientTwistLine_exact`
- `WeilConjectures.IsCanonicalTwistScalarMaps`
- `WeilConjectures.twistSheafScalarComparison`

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

universe d u v c
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
attribute [-instance] integralOperationsCommHasDerivedCategory
attribute [-instance] scalarSiteSmall scalarSiteSheafify scalarSiteLocallyBijective

/-- Transport the binary tensor comparison to a specified ordinary scalar functor.
The section formula also supplies uniqueness by local tensor generation. -/
private theorem tensorLineScalarComparison
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v} RingCat.{max c v})]
    [HasSheafify J AddCommGrpCat.{max c v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v}]
    {R T : Sheaf J CommRingCat.{max c v}} (α : R ⟶ T)
    (F : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings α M)
    (hmF : ∀ {M M'} (f : M ⟶ M'), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom α M f ≫ eqToHom (hF M').symm)
    (N : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (P : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (B : F.obj N ≅ P)
    (c : ∀ U : Cᵒᵖ, N.val.obj U → P.val.obj U)
    (hc : ∀ U y, B.hom.val.app U (tensorSection α F hF N U 1 y) = c U y) :
    ∃! b : SheafOfModules.siteSheafTensorRight N ⋙ F ≅
      F ⋙ SheafOfModules.siteSheafTensorRight P,
      ∀ M U s x y, (b.hom.app M).val.app U
          (tensorSection α F hF _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)) =
        SheafOfModules.siteSheafTensorTmul (F.obj M) P U
          (tensorSection α F hF M U s x)
          (c U y) := by
  exact ordinaryScalarTensorLineTransport α F hF hmF
    (tensorSection α F hF) (fun _ _ _ _ ↦ rfl) N P B c hc

attribute [local instance 3000] integralTowerHasDerivedCategory

variable (X : Scheme.{u})

/-- Tensor powers of the coefficient line, with the unit at exponent zero.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
abbrev coefficientTwistPower {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℕ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
  SheafOfModules.scalarTensorPower R L

/-- Positive powers and internal duals of the coefficient line.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def coefficientTwistLine {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℤ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | Int.ofNat n => coefficientTwistPower X L n
  | Int.negSucc n => SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
      (coefficientTwistPower X L (n + 1)) (SheafOfModules.unit.{u, u + 1, u + 1} _)

/-- Tensor with an integer power or dual of a rank-one line is exact and additive.
Source: blueprint order 1505; Stacks Tags 03EK and 03RV
(blueprint: definition-tate-twists).
Proof: on a cover trivializing L, each positive tensor power is the unit module,
and internal Hom into the unit is also the unit. Thus tensor with every integer
power is locally the identity. Exactness can be checked locally; additivity follows
on sectionwise tensor generators and passes through sheafification. -/
theorem coefficientTwistLine_exact
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)).Additive ∧
    PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)) ∧
    PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)) := by
  classical
  obtain ⟨I, U, hU, hL⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (R := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (M := L) (r := 1)).mp inferInstance
  have hcharts : ∃ (I : Type (u + 1)) (U : I → X.ProEt),
      (ProEt.topology X).CoversTop U ∧ ∀ i,
        Nonempty (L.over (U i) ≅ SheafOfModules.unit
          (((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (U i))) :=
    ⟨I, U, hU, fun i => ⟨(hL i).some ≪≫ SheafOfModules.freeUniqueIso (ULift.{u + 1} (Fin 1))⟩⟩
  have hflat := SheafOfModules.SignedLineDerivedBaseChange.signed_line_power_flat.{u + 1, u, u + 1}
    R L hcharts m
  have hline : SheafOfModules.signedLinePower.{u + 1, u, u + 1} L m =
      coefficientTwistLine X L m := by
    cases m <;> rfl
  rw [hline] at hflat
  change PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
      (A := R) (coefficientTwistLine X L m)) ∧
    PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
      (A := R) (coefficientTwistLine X L m)) at hflat
  exact ⟨(CategoryTheory.rightExactFunctor_le_additiveFunctor _ _) _ hflat.2, hflat⟩

variable (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E] (S : Scheme.{u})
  [∀ x : S, Invertible (ℓ : S.residueField x)]

/-- The published integral first line has rank one; reuse its recorded theorem.
Source: blueprint order 1505; Stacks 03PK
(blueprint: definition-tate-twists). -/
instance coefficientTwistIntegralRank :
    (purTwistIntegralModule S ℓ E).IsFiniteLocallyFreeOfRank 1 :=
  (pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.1

/-- The published ordinary finite reduction has rank one.
Source: blueprint order 1505; Stacks 03PK
(blueprint: definition-tate-twists). -/
instance coefficientTwistFiniteRank (n : ℕ) :
    (purTwistFiniteOne S ℓ E n).IsFiniteLocallyFreeOfRank 1 :=
  ((pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.2 n).2.1

/-- The finite coefficient twist at quotient exponent n+1.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
abbrev finiteCoefficientTwist (n : ℕ) (m : ℤ) :
    SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S n) :=
  coefficientTwistLine S (purTwistFiniteOne S ℓ E n) m

/-- Derived tensor by the finite twisting line.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def finiteComplexTwist (n : ℕ) (m : ℤ) :
    proEtaleDerivedCategory S (Padic.coefficientExtensionRing ℓ E (n + 1)) ⥤
      proEtaleDerivedCategory S (Padic.coefficientExtensionRing ℓ E (n + 1)) := by
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).1
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).2.1
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).2.2
  exact (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (A := integralCoefficientCommRingSheaf ℓ E S n)
    (finiteCoefficientTwist ℓ E S n m)).mapDerivedCategory

/-- Tensor by the completed integral line on module sheaves.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def integralSheafTwist (m : ℤ) : integralTowerModules ℓ E S ⥤ integralTowerModules ℓ E S :=
  SheafOfModules.siteSheafTensorRight
    (A := completedIntegralCommRingSheafUnrestricted ℓ E S)
    (coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m)

/-- Additivity of tensor with the integral line.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
instance integralSheafTwist_additive (m : ℤ) : (integralSheafTwist ℓ E S m).Additive :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).1

/-- Tensor with the integral line preserves finite limits.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
instance integralSheafTwist_finiteLimits (m : ℤ) :
    PreservesFiniteLimits (integralSheafTwist ℓ E S m) :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).2.1

/-- Tensor with the integral line preserves finite colimits.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
instance integralSheafTwist_finiteColimits (m : ℤ) :
    PreservesFiniteColimits (integralSheafTwist ℓ E S m) :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).2.2

/-- Derived tensor by the completed integral twisting line. Since the line is flat,
termwise tensor already computes derived tensor for every unbounded complex.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def integralComplexTwist (m : ℤ) :
    completedIntegralDerivedCategory ℓ E S D hℓ ⥤
      completedIntegralDerivedCategory ℓ E S D hℓ :=
  (integralSheafTwist ℓ E S m).mapDerivedCategory

/-- The integral twist placed in degree zero.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def integralCoefficientTwist (m : ℤ) :
    completedIntegralDerivedCategory ℓ E S D hℓ :=
  (DerivedCategory.singleFunctor _ 0).obj
    (coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m)

/-- Every integral twist is bounded constructible and derived complete.
Source: blueprint order 1505 (blueprint: definition-tate-twists).
Proof: trivialize on a primitive-root pro-etale cover. Powers and duals are again
rank-one lines, and their finite reductions are finite locally constant with common
support interval [0,0]. The compatible finite reductions recover the completed line,
so its canonical derived-completeness comparison is invertible. -/
theorem integralCoefficientTwist_constructible (m : ℤ) :
    boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S
      (integralCoefficientTwist D ℓ hℓ E S m) := by
  classical
  let L := coefficientTwistLine S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m
  have hL : L.IsFiniteLocallyFreeOfRank 1 := by
    let hroot : (purTwistIntegralModule S ℓ E).IsFiniteLocallyFreeOfRank 1 :=
      (pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.1
    let hsmall : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    have h := @SheafOfModules.OrdinaryLineScalar.signed_power_rank.{u, u + 1}
      S hsmall (completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) hroot m
    cases m <;> exact h
  obtain ⟨hred, hcomplete⟩ := completedLine_derived S ℓ E L hL D hℓ
  refine ⟨hcomplete, 0, 0, le_rfl, ?_⟩
  intro n
  let a := completedIntegralCommRingProjectionUnrestricted ℓ E S n
  let N := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a L
  have hN : N.IsFiniteLocallyFreeOfRank 1 := by
    let := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).mpr hL
    exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one N).mp
      (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted ℓ E S)
        (integralCoefficientCommRingSheaf ℓ E S n) a L).1
  let := Padic.finite_coefficientExtensionRing ℓ E (n + 1) (Nat.succ_pos n)
  have hconst := (finiteLocallyFreeLine_models S
    (Padic.coefficientExtensionRing ℓ E (n + 1)) N hN).2.1
  obtain ⟨hfin, hc, hs, _⟩ := constructible_single_support S
    (Padic.coefficientExtensionRing ℓ E (n + 1)) N hconst _ (hred n).some
  refine ⟨⟨hfin, hc⟩, ?_⟩
  intro i hi
  have hi0 : i = 0 := hs hi
  subst i
  exact ⟨le_rfl, le_rfl⟩

/-- The coefficient line as a module sheaf, for every integer exponent.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
abbrev integralTwistLine (m : ℤ) : integralTowerModules ℓ E S :=
  coefficientTwistLine S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m

section ScalarComparison

variable (L : Type u) [Field L] [Algebra (Padic ℓ) L]
  [FiniteDimensional (Padic ℓ) L] (ι : E →ₐ[Padic ℓ] L)

/-- The constant integer inclusion induced by the specified coefficient embedding.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def twistConstantIntegerMap : purTwistIntegralConstant S ℓ E ⟶
    purTwistIntegralConstant S ℓ L :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((integralScalarIntegerInclusion ℓ E L ι).comp ULift.ringEquiv.toRingHom)))

/-- Semilinear maps from the E-lines to the L-lines, before scalar extension.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
abbrev TwistScalarMaps := ∀ m : ℤ,
  integralTwistLine ℓ E S m ⟶
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap ℓ E L ι S))).obj (integralTwistLine ℓ L S m)

/-- The roots-of-unity, unit, tensor-power and dual-evaluation normalization.
These equations specify maps, rather than merely coherent isomorphisms.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def IsCanonicalTwistScalarMaps (c : TwistScalarMaps ℓ E S L ι) : Prop :=
  (∀ (U : S.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted ℓ E S).obj.obj U),
    (c 0).val.app U a = (integralCompletedScalarMap ℓ E L ι S).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S ℓ E).obj.obj U)
      (x : (purTwistZlModule S ℓ).val.obj U),
    (c 1).val.app U (purTwistIntegralTensor S ℓ E U b x) =
      purTwistIntegralTensor S ℓ L U ((twistConstantIntegerMap ℓ E S L ι).hom.app U b) x) ∧
  (∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) (n + 1)).val.obj U)
      (y : (purTwistIntegralModule S ℓ E).val.obj U),
    (c (Int.ofNat (n + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul
          (A := completedIntegralCommRingSheafUnrestricted ℓ E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U
        ((c (Int.ofNat (n + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine ℓ E S (Int.negSucc n)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) (n + 1)).val.obj U),
    (((c (Int.negSucc n)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (n + 1))).val.app U x) =
      (integralCompletedScalarMap ℓ E L ι S).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

private theorem twist_firstLine_cover
    (F : Type u) [Field F] [Algebra (Padic ℓ) F]
    [FiniteDimensional (Padic ℓ) F] :
    ∃ (I : Type (u + 1)) (U : I → S.ProEt),
      (ProEt.topology S).CoversTop U ∧ ∀ i,
        Nonempty ((purTwistIntegralModule S ℓ F).over (U i) ≅ SheafOfModules.unit
          ((completedIntegralCoefficientSheafUnrestricted ℓ F S).over (U i))) := by
  obtain ⟨I, U, hU, hL⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := purTwistIntegralModule S ℓ F) (r := 1)).mp
      (coefficientTwistIntegralRank ℓ F S)
  exact ⟨I, U, hU, fun i ↦
    ⟨(hL i).some ≪≫ SheafOfModules.freeUniqueIso (ULift.{u + 1} (Fin 1))⟩⟩

private theorem twistScalarComparison_data :
    ∃ B : ∀ m : ℤ,
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (integralCompletedScalarMap ℓ E L ι S) (integralTwistLine ℓ E S m) ≅
            integralTwistLine ℓ L S m,
      let c : TwistScalarMaps ℓ E S L ι := fun m ↦
        SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
          (integralCompletedScalarMap ℓ E L ι S)
            (integralTwistLine ℓ E S m) ≫
          (SheafOfModules.restrictScalars.{u + 1}
            ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (integralCompletedScalarMap ℓ E L ι S))).map (B m).hom
      IsCanonicalTwistScalarMaps ℓ E S L ι c ∧
        ∀ d : TwistScalarMaps ℓ E S L ι,
          IsCanonicalTwistScalarMaps ℓ E S L ι d → d = c := by
  classical
  let : HasSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} S
  let : HasWeakSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} S
  let α := integralCompletedScalarMap ℓ E L ι S
  let res := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
  obtain ⟨b, hb, huniq⟩ := firstRootCoefficientScalarComparison ℓ E S L ι
  obtain ⟨B, hB, heval, _⟩ :=
    SheafOfModules.exists_signedLineComparison.{u + 1, u, u + 1} α
      (purTwistIntegralModule S ℓ E) (purTwistIntegralModule S ℓ L)
      (twist_firstLine_cover ℓ S E) (twist_firstLine_cover ℓ S L) b
  let c : TwistScalarMaps ℓ E S L ι := fun m ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α (integralTwistLine ℓ E S m) ≫
      res.map (B m).hom
  have hc : IsCanonicalTwistScalarMaps ℓ E S L ι c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U a
      change (B 0).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 a) = _
      rw [hB.1]
      have hz := SheafOfModules.scalarExtensionUnitIso_tmul α U 1 a
      rw [one_mul] at hz
      exact hz
    · intro U a x
      change (B 1).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1
        (purTwistIntegralTensor S ℓ E U a x)) = _
      rw [hB.2.1]
      exact hb U a x
    · intro n U x y
      have hfirst := congrArg
        (fun f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
            α (purTwistIntegralModule S ℓ E) ⟶ purTwistIntegralModule S ℓ L ↦
          f.val.app U (SheafOfModules.scalarExtensionSection α
            (purTwistIntegralModule S ℓ E) U 1 y)) hB.2.1.symm
      exact (hB.2.2.1 n U 1 x y).trans (congrArg
        (fun z : (purTwistIntegralModule S ℓ L).val.obj U ↦
          SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted ℓ L S)
            (coefficientTwistPower S (purTwistIntegralModule S ℓ L) (n + 1))
            (purTwistIntegralModule S ℓ L) U
            ((B (Int.ofNat (n + 1))).hom.val.app U
              (SheafOfModules.scalarExtensionSection α
                (coefficientTwistPower S (purTwistIntegralModule S ℓ E) (n + 1)) U 1 x)) z)
        hfirst)
    · intro n U f x
      change (((B (Int.negSucc n)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 f)).app
            (Opposite.op (Over.mk (𝟙 U.unop))))
          ((B (Int.ofNat (n + 1))).hom.val.app U
            (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 x)) = _
      simpa only [α, integralTwistLine, coefficientTwistLine, coefficientTwistPower,
        SheafOfModules.signedLinePower, mul_one] using heval n U 1 1 f x
  refine ⟨B, hc, ?_⟩
  intro d hd
  have h1 : d 1 = c 1 := by
    have hd1 := huniq (d 1) hd.2.1
    change d 1 = SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
      res.map b.hom at hd1
    change d 1 = SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
      res.map (B 1).hom
    rw [hB.2.1]
    exact hd1
  have hpos : ∀ n : ℕ, d (Int.ofNat n) = c (Int.ofNat n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (hd.1 U a).trans (hc.1 U a).symm
    | one => exact h1
    | more n _ ih =>
      apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1}
        (integralTwistLine ℓ E S (Int.ofNat (n + 1))) (purTwistIntegralModule S ℓ E)
      intro U x y
      have hx := congrArg (fun z : integralTwistLine ℓ E S (Int.ofNat (n + 1)) ⟶
          res.obj (integralTwistLine ℓ L S (Int.ofNat (n + 1))) ↦ z.val.app U x) ih
      have hy := congrArg (fun z : integralTwistLine ℓ E S 1 ⟶
          res.obj (integralTwistLine ℓ L S 1) ↦ z.val.app U y) h1
      exact (hd.2.2.1 n U x y).trans ((congrArg₂
        (fun a b ↦ SheafOfModules.siteSheafTensorTmul
          (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U a b)
        hx hy).trans (hc.2.2.1 n U x y).symm)
  funext m
  cases m with
  | ofNat n => exact hpos n
  | negSucc n =>
    apply scalarSemilinearDualExt S α
      (integralTwistLine ℓ E S (Int.negSucc n))
      (integralTwistLine ℓ E S (Int.ofNat (n + 1)))
      (integralTwistLine ℓ L S (Int.ofNat (n + 1))) (B (Int.ofNat (n + 1)))
    intro U f x
    change ((d (Int.negSucc n)).val.app U f).app
        (Opposite.op (Over.mk (𝟙 U.unop))) ((c (Int.ofNat (n + 1))).val.app U x) =
      ((c (Int.negSucc n)).val.app U f).app
        (Opposite.op (Over.mk (𝟙 U.unop))) ((c (Int.ofNat (n + 1))).val.app U x)
    have hx := congrArg (fun z : integralTwistLine ℓ E S (Int.ofNat (n + 1)) ⟶
        res.obj (integralTwistLine ℓ L S (Int.ofNat (n + 1))) ↦ z.val.app U x)
      (hpos (n + 1))
    exact (congrArg (fun z ↦ ((d (Int.negSucc n)).val.app U f).app
      (Opposite.op (Over.mk (𝟙 U.unop))) z) hx.symm).trans
        ((hd.2.2.2 n U f x).trans (hc.2.2.2 n U f x).symm)

/-- There is exactly one normalized semilinear family on the signed Tate lines.
Source: blueprint order 1505 (blueprint: definition-tate-twists).
Proof: at zero take the completed coefficient inclusion. At one send the root
limit tensor b to the same root limit tensor its integer image. The balanced
relations agree by the finite residue characterizations of the completed actions.
For positive powers tensor these maps recursively. For negative powers use the
unique dual map whose evaluation is the image of the original evaluation.
On a cover trivializing the root line these maps are the coefficient inclusion,
so the positive maps generate the target line and the dual map is unique.
The formulas commute with restrictions and glue; tensor sheafification and the
local generation of each positive line prove uniqueness in every degree. -/
theorem twistScalarMaps_existsUnique :
    ∃! c : TwistScalarMaps ℓ E S L ι, IsCanonicalTwistScalarMaps ℓ E S L ι c := by
  obtain ⟨B, hc, hu⟩ := twistScalarComparison_data ℓ E S L ι
  exact ⟨_, hc, hu⟩

/-- The signed scalar maps fixed by root tensors, powers and dual evaluation.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def twistScalarMaps : TwistScalarMaps ℓ E S L ι :=
  (twistScalarMaps_existsUnique ℓ E S L ι).exists.choose

/-- Scalar extension of each line is the target line, with the specified map.
Source: blueprint order 1505 (blueprint: definition-tate-twists).
Proof: extend the semilinear map by balancing, sending s tensor x to s times c(x).
On a trivializing cover this is multiplication R_L tensor R_E to R_L and has
inverse z to z tensor one. Glue the local inverses. Pure tensors generate locally,
so the displayed formula uniquely determines the isomorphism, also at zero. -/
theorem twistLineScalarIso_existsUnique (m : ℤ) :
    ∃! c : (integralOrdinaryScalar ℓ E L ι S).obj (integralTwistLine ℓ E S m) ≅
        integralTwistLine ℓ L S m,
      ∀ (U : S.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
        (x : (integralTwistLine ℓ E S m).val.obj U),
        c.hom.val.app U
            (integralOrdinaryTensorSection ℓ E L ι S _ U s x) =
          s • (@id ((integralTwistLine ℓ L S m).val.obj U)
            ((twistScalarMaps ℓ E S L ι m).val.app U x)) := by
  classical
  let α := integralCompletedScalarMap ℓ E L ι S
  let hF := (integralOrdinaryScalarWitness ℓ E L ι S).choose_spec.choose
  let q (N : integralTowerModules ℓ E S) :
      (integralOrdinaryScalar ℓ E L ι S).obj N ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α N :=
    eqToIso (hF N) ≪≫ SheafOfModules.ScalarHomOrdinary.extensionIso α N
  have hq (N : integralTowerModules ℓ E S) (U : S.ProEtᵒᵖ) (x : N.val.obj U) :
      (q N).hom.val.app U (integralOrdinaryTensorSection ℓ E L ι S N U 1 x) =
        SheafOfModules.scalarExtensionSection α N U 1 x := by
    change (SheafOfModules.ScalarHomOrdinary.extensionIso α N).hom.val.app U
      ((eqToHom (hF N)).val.app U ((eqToHom (hF N).symm).val.app U _)) = _
    have hcancel := congrArg (fun f ↦ f.val.app U
      ((toSheafify (ProEt.topology S)
        (SheafOfModules.changeOfRingsPresheaf α N).presheaf).app U
          ((1 : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
            ⊗ₜ[(completedIntegralCommRingSheafUnrestricted ℓ E S).obj.obj U,
              (α.hom.app U).hom] x))) (eqToIso (hF N)).inv_hom_id
    change (eqToHom (hF N)).val.app U ((eqToHom (hF N).symm).val.app U _) = _ at hcancel
    rw [hcancel]
    exact SheafOfModules.ScalarHomOrdinary.extensionIso_unit α N U x
  obtain ⟨B, hc, hu⟩ := twistScalarComparison_data ℓ E S L ι
  have hsame := hu (twistScalarMaps ℓ E S L ι)
    (twistScalarMaps_existsUnique ℓ E S L ι).exists.choose_spec
  let e := q (integralTwistLine ℓ E S m) ≪≫ B m
  have he : ∀ (U : S.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
      (x : (integralTwistLine ℓ E S m).val.obj U),
      e.hom.val.app U (integralOrdinaryTensorSection ℓ E L ι S _ U s x) =
        s • (@id ((integralTwistLine ℓ L S m).val.obj U)
          ((twistScalarMaps ℓ E S L ι m).val.app U x)) := by
    intro U s x
    rw [scalar_tensor_one, map_smul]
    change s • ((B m).hom.val.app U ((q _).hom.val.app U
      (integralOrdinaryTensorSection ℓ E L ι S _ U 1 x))) = _
    rw [hq, hsame]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply tensorSection_ext α (integralOrdinaryScalar ℓ E L ι S) hF
    (integralTwistLine ℓ E S m) (integralTwistLine ℓ L S m)
  intro U x
  change e'.hom.val.app U (integralOrdinaryTensorSection ℓ E L ι S _ U 1 x) =
    e.hom.val.app U (integralOrdinaryTensorSection ℓ E L ι S _ U 1 x)
  rw [he', he]

/-- The canonical scalar-extension isomorphism for the signed line.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def twistLineScalarIso (m : ℤ) :
    (integralOrdinaryScalar ℓ E L ι S).obj (integralTwistLine ℓ E S m) ≅
      integralTwistLine ℓ L S m :=
  (twistLineScalarIso_existsUnique ℓ E S L ι m).exists.choose

/-- Tensor and scalar extension commute by the normalized balanced map.
Source: blueprint order 1505 (blueprint: definition-tate-twists).
Proof: send s tensor (x tensor y) to (s tensor x) tensor c(y), with c the
normalized semilinear line map. Its inverse is the ordinary tensor associator
followed by the inverse canonical line comparison. The balanced formulas commute
with restrictions and module maps. They sheafify to a natural isomorphism.
Local pure-tensor generation uniquely determines every component. -/
theorem twistSheafScalarComparison_existsUnique (m : ℤ) :
    ∃! b : integralSheafTwist ℓ E S m ⋙ integralOrdinaryScalar ℓ E L ι S ≅
        integralOrdinaryScalar ℓ E L ι S ⋙ integralSheafTwist ℓ L S m,
      ∀ (N : integralTowerModules ℓ E S) (U : S.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
        (x : N.val.obj U) (y : (integralTwistLine ℓ E S m).val.obj U),
        (b.hom.app N).val.app U
            (integralOrdinaryTensorSection ℓ E L ι S _ U s
              (SheafOfModules.siteSheafTensorTmul
                (A := completedIntegralCommRingSheafUnrestricted ℓ E S) N _ U x y)) =
          SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U
            (integralOrdinaryTensorSection ℓ E L ι S N U s x)
            ((twistScalarMaps ℓ E S L ι m).val.app U y) := by
  exact tensorLineScalarComparison (integralCompletedScalarMap ℓ E L ι S)
    (integralOrdinaryScalar ℓ E L ι S)
    (integralOrdinaryScalarWitness ℓ E L ι S).choose_spec.choose
    (integralOrdinaryScalarWitness ℓ E L ι S).choose_spec.choose_spec.choose
    (integralTwistLine ℓ E S m) (integralTwistLine ℓ L S m)
    (twistLineScalarIso ℓ E S L ι m)
    (fun U y ↦ @id ((integralTwistLine ℓ L S m).val.obj U)
      ((twistScalarMaps ℓ E S L ι m).val.app U y))
    (fun U y ↦ by
      change (twistLineScalarIso ℓ E S L ι m).hom.val.app U
          (integralOrdinaryTensorSection ℓ E L ι S _ U 1 y) = _
      simpa only [twistLineScalarIso, one_smul] using
        (twistLineScalarIso_existsUnique ℓ E S L ι m).exists.choose_spec U 1 y)

/-- The ordinary natural comparison fixed on local pure tensors.
Source: blueprint order 1505 (blueprint: definition-tate-twists). -/
def twistSheafScalarComparison (m : ℤ) :
    integralSheafTwist ℓ E S m ⋙ integralOrdinaryScalar ℓ E L ι S ≅
      integralOrdinaryScalar ℓ E L ι S ⋙ integralSheafTwist ℓ L S m :=
  (twistSheafScalarComparison_existsUnique ℓ E S L ι m).exists.choose

end ScalarComparison

variable (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω]
  [IsAlgClosure (Padic ℓ) Ω]

end WeilConjectures
