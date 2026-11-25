/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralBoundary.NativeIntegralBoundaryIsomorphisms

/-! Natural boundary comparisons for the integral compact-support scalar morphism. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
  WeilConjectures.LocallyFiniteAdicCompactSupport.actual
  WeilConjectures.PurCompactSupport.image
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

private theorem native_integral_source_boundary [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient l (PadicAlgCl l) E) X) :
    IntegralSourceBoundary l D hl P c target E K
      ((NativeIntegralBoundary.sourceIntegral l D hl P c target stage E).hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient l (PadicAlgCl l) E) X).obj K)) := by
  let L := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient l (PadicAlgCl l) E) X).obj K
  let R := (sfRationalConstructibleLocalization l
    (Coefficient l (PadicAlgCl l) E) X).obj L
  obtain ⟨A, B, r, hr, h₀⟩ :=
    NativeIntegralBoundary.sourceRational_component l D hl P c target stage E R
  let a₀ := (target.J ⋙ (sections l Y).mapDerivedCategory).map
    ((NativeIntegralBoundary.sourceRational l D hl P c stage E).hom.app R)
  let a₁ := (target.integral E).hom.app
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E)).obj L)
  let a₂ := (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
    ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
      D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app L)
  let M₁ := (target.J ⋙ (sections l Y).mapDerivedCategory).obj
    ((GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
      ((sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (Coefficient l (PadicAlgCl l) E)).obj R))
  let M₂ := (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E)).obj L).obj
  refine ⟨A, B, r, ?_, M₁, M₂, a₀, a₁, a₂, h₀,
    ArrowHEq.refl _, ArrowHEq.refl _, ?_⟩
  · exact hr
  · exact NativeIntegralBoundary.sourceIntegral_hom_app l D hl P c target stage E L

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
private theorem native_integral_target_boundary [G : NativeGeometry.{u} l]
    (source : Realization l X) (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient l (PadicAlgCl l) E) X) :
    IntegralTargetBoundary l c source E K
      ((NativeIntegralBoundary.targetIntegral l c source E).hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient l (PadicAlgCl l) E) X).obj K)) := by
  let L := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient l (PadicAlgCl l) E) X).obj K
  let R := (sfRationalConstructibleLocalization l
    (Coefficient l (PadicAlgCl l) E) X).obj L
  let a₄ := (PurCompactSupport.image (nativeCoefficients l) c).map
    ((source.integral E).inv.app L)
  let a₅ := (operationTransport l c).inv.app
    (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj R))
  let M₅ := (PurCompactSupport.image (nativeCoefficients l) c).obj
    ((sections l X).mapDerivedCategory.obj
      (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj R)))
  refine ⟨M₅, a₄, a₅, ArrowHEq.refl _, ArrowHEq.refl _, ?_⟩
  exact NativeIntegralBoundary.targetIntegral_hom_app l c source E L

-- The component formulas compare cached presentations of the coefficient categories.
/-- Construct the two natural boundary isomorphisms and their prescribed components.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15.
Proof: on the source boundary, compose the stage inclusion and rationalLeft
comparisons, localization of the integral action, the target integral realization,
and derived extension of inverse sfQcqsCompactSupportRealization. On the target
boundary, compose compact support of the inverse source integral realization with
inverse operationTransport. Evaluate on each integral finite-Tor object. The stage
comparison gives the recorded rational arrow; the localization comparison has
identity components. Functoriality of identities gives the first three arrows and
the last two arrows, respectively. This construction contains no scalar mate.
(blueprint: lem-sf-native-integral-scalar-boundaries). -/
theorem native_integral_scalar_boundaries [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l)) :
    ∃ (b :
    sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⋙
        (sections l Y).mapDerivedCategory ≅
      (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y))
      (d :
    (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c ≅
      sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c) ⋙
        (sections l Y).mapDerivedCategory),
      ∀ K : finiteTorConstructibleIntegralCategory l
          (Coefficient l (PadicAlgCl l) E) X,
    IntegralSourceBoundary l D hl P c target E K
      (b.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient l (PadicAlgCl l) E) X).obj K)) ∧
    IntegralTargetBoundary l c source E K
      (d.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient l (PadicAlgCl l) E) X).obj K)) := by
  exact ⟨NativeIntegralBoundary.sourceIntegral l D hl P c target stage E,
    NativeIntegralBoundary.targetIntegral l c source E, fun K ↦
      ⟨native_integral_source_boundary l D hl P c target stage E K,
        native_integral_target_boundary l c source E K⟩⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
