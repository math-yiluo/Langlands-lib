/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarComponentFactorization

/-! # Boundary-isomorphism component factorization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
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

attribute [local irreducible] Padic CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
attribute [local instance 2000] Shrink.instField

set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
  WeilConjectures.LocallyFiniteAdicCompactSupport.actual
  WeilConjectures.PurCompactSupport.image
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.LocallyFiniteAdicRealization.sections
  AlgebraicGeometry.Scheme.completedAdicDerivedChange

-- Compare the cached finite-stage types without unfolding their constructions.
/-- The boundary-isomorphism interface to the normalized component factorization.
Source: Bhatt--Scholze, Remark 6.8.15.
Proof: evaluate each boundary isomorphism on the inclusion of K. These are exactly
arrows of the generic factorization theorem. Unfold only the rationalization and
full-subcategory inclusions to identify their types, then apply that theorem to
the supplied integral normalization and the two boundary component formulas.
(blueprint: lem-sf-native-integral-boundary-iso-factorization). -/
theorem integralComponent_factorization_of_isos [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l))
    (change : ∀ j : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) j)) (nativeCoefficients l))
    (hs : (change E).map X = (source.coefficient E).integralMap l X)
    (ht : (change E).map Y = (target.coefficient E).integralMap l Y)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (alpha : finiteSource l D hl P c target stage E ⟶ finiteTarget l c source E)
    (b : sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⋙
        (sections l Y).mapDerivedCategory ≅
      (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y))
    (d : (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c ≅
      sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c) ⋙
        (sections l Y).mapDerivedCategory)
    (hb : IntegralSourceBoundary l D hl P c target E K
      (b.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient l (PadicAlgCl l) E) X).obj K)))
    (hd : IntegralTargetBoundary l c source E K
      (d.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient l (PadicAlgCl l) E) X).obj K)))
    (hm : IntegralComponent l D hl P c source target change E K
      (alpha.app ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l))
        (finiteField l E) X).obj K))) :
    (sections l Y).mapDerivedCategory.map
        (alpha.app ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l))
          (finiteField l E) X).obj K)) =
      b.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient l (PadicAlgCl l) E) X).obj K) ≫
      nativeScalarComponent l c source target E (change E) hs ht K.obj ≫
      d.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient l (PadicAlgCl l) E) X).obj K) := by
  apply integralComponent_factorization.{u} l D hl P c source target E change hs ht K
  · exact hb
  · exact hd
  · exact hm

end WeilConjectures.LocallyFiniteAdicCompactSupport
