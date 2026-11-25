/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.FiniteStageActionCanonicalComparison

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

attribute [local irreducible] ScalarLocalization.category

set_option allowUnsafeReducibility true in
attribute [local reducible] ScalarLocalization.category in
/-- Integral finite compact support commutes with raw localization.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-native-integral-boundary-rational-construction). -/
def finiteActionLocalization (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          (Coefficient l (PadicAlgCl l) E) ≅
      sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          (Coefficient l (PadicAlgCl l) E) ⋙
        sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) Y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
      sfCompactSupportFiniteFunctor, Functor.comp_map, Functor.comp_obj, Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    unfold sfCompactSupportFiniteHomMap
    rfl)

/-- The localization comparison has identity components after realization.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-native-integral-boundary-rational-construction). -/
theorem finiteActionLocalization_map_hom_app [G : NativeGeometry.{u} l]
    (target : Realization l Y) (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ target.J ⋙
      (sections l Y).mapDerivedCategory).map
        ((finiteActionLocalization l D hl c E).hom.app K) = 𝟙 _ := by
  change (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ target.J ⋙
    (sections l Y).mapDerivedCategory).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- The canonical finite-stage rational boundary comparison.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-native-integral-boundary-rational-construction). -/
def sourceRational (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l)) :=
  finiteStageActionComparisonOfOperations l (PadicAlgCl l) X Y stage.system
    (fun E ↦ P.ring.operation c (.rational (finiteField l E)))
    (fun E ↦ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E))
    (fun E ↦ P.ring.rationalLeft c (finiteField l E)) stage.finite E

/-- The rational boundary component is the prescribed rationalLeft arrow.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-native-integral-boundary-rational-construction). -/
theorem sourceRational_component [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l))
    (A : sfRationalConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
    ∃ (B B' : sfRationalConstructibleCategory l (Coefficient l (PadicAlgCl l) E) Y)
      (r : B ⟶ B'), ArrowHEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app A) ∧
      ArrowHEq ((target.J ⋙ (sections l Y).mapDerivedCategory).map
        ((sourceRational l D hl P c stage E).hom.app A))
        ((target.J ⋙ (sections l Y).mapDerivedCategory).map
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r)) := by
  refine ⟨_, _, (P.ring.rationalLeft c (finiteField l E)).hom.app A,
    ArrowHEq.refl _, ?_⟩
  exact finiteStageActionComparisonOfOperations_map l (PadicAlgCl l) X Y stage.system
    (fun E ↦ P.ring.operation c (.rational (finiteField l E)))
    (fun E ↦ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E))
    (fun E ↦ P.ring.rationalLeft c (finiteField l E)) stage.finite E
    (target.J ⋙ (sections l Y).mapDerivedCategory) A

attribute [irreducible] sourceRational finiteActionLocalization

end NativeIntegralBoundary
end WeilConjectures.LocallyFiniteAdicCompactSupport
