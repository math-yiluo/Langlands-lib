/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement

import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackTransitionFactorization
import WeilConjectures.Algebra.Homology.SmoothPurity.DiagonalConeTransitionHomotopy

/-! # Pro-zero cone of the normalized finite scalar pullback map

Source: Stacks Tags 07A4 and 0941, and the cofinal uniformizer-filtration
argument of lem-pur-integral-scalar-pullback-roos-quasi-iso.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted

attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The cone of the finite scalar pullback comparison has eventually nullhomotopic
transitions, before taking products or a Roos complex.
Source: Stacks, sites-cohomology.tex, Tags 07A4 and 0941; derived.tex Tag 08TC;
proetale.tex Tag 099N. This is the finite-filtration part of the parent argument.
(blueprint: lem-pur-integral-scalar-pullback-cone-pro-zero).

Proof: write the image of the source uniformizer as a unit times the e-th power
of the target uniformizer, where e is positive. The completed constant-sheaf
quotient identification and tensor associativity identify the source tower with
the subsequence of the target tower at e(n+1)-1. The identification is compatible
with inverse image and all strict transitions. The generator equation identifies
alpha with the transition from this subsequence to level n: the balanced tensor
and inverse-image universal properties determine a map from the displayed generators.
For fixed n choose m at least e(n+1)-1. The transition from target level m to n
then factors through the subsequence at n. On the mapping cones the induced
transition is nullhomotopic: its degree-minus-one off-diagonal entry is this
factorization map, and the cone differential gives its two diagonal entries;
the remaining entries cancel because the factorization is a chain map.
Consequently this cone transition is zero after localization. K-flatness and flat
terms allow the displayed finite tensors to compute the derived reductions.
For e=1 alpha is an isomorphism and its cone is contractible; zero complexes and
empty sites obey the same formulas. Neither products nor completeness of P enter.
-/
theorem integralScalarPullbackConeProZero {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P)
    (α : ((integralOperationsPullbackTowerFunctor l E f).obj P) ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOperationsPullbackTowerFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P))
    (hα :
      ∀ (n : ℕ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app (op n)).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel.{u, u} l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator.{u, u} l E f n
              (((unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator.{u, u} l L f n
          (((unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection.{u, u} l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x))) :
    letI : EssentiallySmall.{u+1} X.ProEt := essentiallySmallSelf.{0, u, u+1} _
    letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
        AddCommGrpCat.{u+1} := integralCoefficientAbSheafify.{u, u} X
    letI : (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
        AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} X
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      Nonempty (Homotopy (V := integralTowerModules.{u, u} l L X)
        ((CochainComplex.mappingCone (C := ℕᵒᵖ ⥤ integralTowerModules.{u, u} l L X)
          (@koszulTowerComplexMap.{u+1, u, u+1} X.ProEt inferInstance
            (AlgebraicGeometry.Scheme.ProEt.topology X)
            (essentiallySmallSelf.{0, u, u+1} _)
            (completedIntegralCommRingSheafUnrestricted.{u, u} l L X) _ _ α)).asFunctor.map
            (homOfLE h).op) 0) := by
  intro n
  obtain ⟨m, h, b, hb₁, hb₂⟩ :=
    integralScalarPullbackTransitionFactorization l E L ι f P α hα n
  refine ⟨m, h, ?_⟩
  apply HomologicalComplex.diagonalConeTransitionHomotopy
    (@koszulTowerComplexMap.{u+1, u, u+1} X.ProEt inferInstance
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (essentiallySmallSelf.{0, u, u+1} _)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l L X) _ _ α)
    (homOfLE h).op b
  · intro i
    exact congrArg (fun k ↦ k.f i) hb₁
  · intro i
    exact congrArg (fun k ↦ k.f i) hb₂

end WeilConjectures
