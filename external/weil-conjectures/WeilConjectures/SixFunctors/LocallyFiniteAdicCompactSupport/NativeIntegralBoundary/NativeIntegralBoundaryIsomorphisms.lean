/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralBoundary.NativeIntegralBoundaryRational

/-! Canonical constructions used in normalized integral scalar boundaries. -/

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

namespace NativeIntegralBoundary

/-- The first boundary isomorphism before inserting the scalar mate.
Source: Bhatt--Scholze, Remark 6.8.15; composition of the prescribed realizations.
(blueprint: def-sf-native-integral-boundary-isomorphisms). -/
def sourceIntegral [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⋙
        (sections l Y).mapDerivedCategory ≅
      (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y) :=
  Functor.isoWhiskerLeft
      (sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X)
      (Functor.isoWhiskerRight (sourceRational l D hl P c stage E)
        (target.J ⋙ (sections l Y).mapDerivedCategory)) ≪≫
    Functor.isoWhiskerRight (finiteActionLocalization l D hl c E)
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
        target.J ⋙ (sections l Y).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft
      (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (Coefficient l (PadicAlgCl l) E)) (target.integral E) ≪≫
    Functor.isoWhiskerRight
      (sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
        D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).symm
      (pbcDerivedExtend ((target.coefficient E).integralMap l Y))

/-- The final boundary isomorphism after the scalar mate.
Source: Bhatt--Scholze, Remark 6.8.15; composition of the prescribed realizations.
(blueprint: def-sf-native-integral-boundary-isomorphisms). -/
def targetIntegral [G : NativeGeometry.{u} l]
    (source : Realization l X) (E : Index l (PadicAlgCl l)) :
    (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c ≅
      sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c) ⋙
        (sections l Y).mapDerivedCategory :=
  Functor.isoWhiskerRight (source.integral E).symm
      (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
    Functor.isoWhiskerLeft
      (sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J)
      (operationTransport l c).symm

/-- Component equation of the first boundary, with the localization identity removed.
Source: Bhatt--Scholze, Remark 6.8.15; evaluation of the natural comparison.
(blueprint: def-sf-native-integral-boundary-isomorphisms). -/
theorem sourceIntegral_hom_app [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l))
    (L : sfIntegralConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
    (sourceIntegral l D hl P c target stage E).hom.app L =
      (target.J ⋙ (sections l Y).mapDerivedCategory).map
          ((sourceRational l D hl P c stage E).hom.app
            ((sfRationalConstructibleLocalization l
              (Coefficient l (PadicAlgCl l) E) X).obj L)) ≫
        (target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient l (PadicAlgCl l) E)).obj L) ≫
        (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app L) := by
  let a := (target.J ⋙ (sections l Y).mapDerivedCategory).map
    ((sourceRational l D hl P c stage E).hom.app
      ((sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X).obj L))
  let b := (target.integral E).hom.app
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E)).obj L)
  let d := (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
    ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
      D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app L)
  have h := finiteActionLocalization_map_hom_app l D hl c target E L
  have hc := congrArg (fun q ↦ a ≫ q ≫ b ≫ d) h
  unfold sourceIntegral
  exact hc.trans (congrArg (fun q ↦ a ≫ q) (Category.id_comp (b ≫ d)))

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Component equation of the final boundary.
Source: Bhatt--Scholze, Remark 6.8.15; evaluation of the natural comparison.
(blueprint: def-sf-native-integral-boundary-isomorphisms). -/
theorem targetIntegral_hom_app [G : NativeGeometry.{u} l]
    (source : Realization l X) (E : Index l (PadicAlgCl l))
    (L : sfIntegralConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
    (targetIntegral l c source E).hom.app L =
      (PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app L) ≫
        (operationTransport l c).inv.app
          (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient l (PadicAlgCl l) E) X).obj L))) := rfl

attribute [irreducible] sourceIntegral targetIntegral

end NativeIntegralBoundary
end WeilConjectures.LocallyFiniteAdicCompactSupport
