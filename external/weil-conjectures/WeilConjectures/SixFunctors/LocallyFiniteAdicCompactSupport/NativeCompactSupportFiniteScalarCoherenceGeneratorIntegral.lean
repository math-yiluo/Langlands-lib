/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarBoundaries
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralBoundaryIsoFactorization
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralStageComponent
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralBoundaryTransitionPasting
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralFiniteTorScalarObject
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Integral finite-Tor generator case of finite scalar coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.LocallyFiniteAdicCompactSupport.actual
  WeilConjectures.PurCompactSupport.image
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.LocallyFiniteAdicRealization.sections
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
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

private theorem reflect_factored_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Faithful] {A B A' B' : C}
    (t : A ⟶ A') (r : B ⟶ B') (mi : A ⟶ B) (mE : A' ⟶ B')
    (fi : F.obj A ⟶ F.obj B) (fE : F.obj A' ⟶ F.obj B')
    (hi : F.map mi = fi) (hE : F.map mE = fE)
    (h : F.map t ≫ fE = fi ≫ F.map r) : t ≫ mE = mi ≫ r := by
  apply F.map_injective
  calc
    F.map (t ≫ mE) = F.map t ≫ F.map mE := F.map_comp _ _
    _ = F.map t ≫ fE := congrArg (fun a ↦ F.map t ≫ a) hE
    _ = fi ≫ F.map r := h
    _ = F.map mi ≫ F.map r := congrArg (fun a ↦ a ≫ F.map r) hi.symm
    _ = F.map (mi ≫ r) := (F.map_comp _ _).symm

-- The component formulas compare cached finite-stage and native presentations.
/-- The integral finite-Tor numerator calculation underlying the generator transition.
Source: Proposition 6.8.14 and Remark 6.8.15, the integral numerator calculation.
The statement fixes the common-stage object to the rationalization of one finite-Tor
integral object, which is strictly smaller than the arbitrary-stage generator theorem.
(blueprint: lem-sf-native-compact-support-finite-scalar-coherence-generator-integral) -/
theorem native_compact_support_finite_scalar_coherence_generator_integral
    [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : ∀ E, (change E).map X = (source.coefficient E).integralMap l X)
    (ht : ∀ E, (change E).map Y = (target.coefficient E).integralMap l Y)
    (alpha : ∀ E : Index l (PadicAlgCl l),
      finiteSource l D hl P c target stage E ≅ finiteTarget l c source E)
    (hα : ∀ (E : Index l (PadicAlgCl l))
      (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      IntegralComponent l D hl P c source target change E K
        ((alpha E).hom.app
          ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)))
    (i E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X)
    (Aobj : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X i)
    (hA : Aobj =
      (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K)
    (h : i ≤ E) :
    (stage.system.functor ⋙ target.J).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          (⟨i, Aobj⟩ : generalAlgebraicallyClosedConstructibleCategory l
            (PadicAlgCl l) X) h).hom) ≫
      (alpha E).hom.app
        (((⟨i, Aobj⟩ : generalAlgebraicallyClosedConstructibleCategory l
          (PadicAlgCl l) X).toStage h)) =
      (alpha i).hom.app Aobj ≫
      (source.J ⋙ actual l c).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          (⟨i, Aobj⟩ : generalAlgebraicallyClosedConstructibleCategory l
            (PadicAlgCl l) X) h).hom) := by
  classical
  subst Aobj
  let Ki := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient.{u} l (PadicAlgCl l) i) X).obj K
  -- Choose the witnesses without eliminating existentials into the large coherence goal.
  have hscalar := finiteTorScalarObject l D hl X i E h K
  let KE := hscalar.choose
  have hKE := hscalar.choose_spec.1
  have hM := hscalar.choose_spec.2
  have hbound := native_integral_scalar_boundaries l D hl P c source target stage i
  let bi := hbound.choose
  let di := hbound.choose_spec.choose
  have hboundi := hbound.choose_spec.choose_spec
  have hfi := integralComponent_factorization_of_isos l D hl P c source target stage i
    change (hs i) (ht i) K (alpha i).hom bi di (hboundi K).1 (hboundi K).2 (hα i K)
  have hcomponent := integralStageComponent l D hl P c source target stage change i E h
    (hs E) (ht E) K KE hKE (alpha E).hom (hα E KE)
  let bE' := hcomponent.choose
  let dE' := hcomponent.choose_spec.choose
  have hbE' := hcomponent.choose_spec.choose_spec.1
  have hdE' := hcomponent.choose_spec.choose_spec.2.1
  have hfE' := hcomponent.choose_spec.choose_spec.2.2
  have hdiagram := integralBoundaryTransitionPasting l D hl P c source target stage
    change hs ht i E h K KE hKE hM (bi.hom.app Ki) bE' (di.hom.app Ki) dE'
    (hboundi K).1 hbE' (hboundi K).2 hdE'
  let : (sections l Y).mapDerivedCategory.IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory _
  exact reflect_factored_square (sections l Y).mapDerivedCategory _ _ _ _ _ _
    hfi hfE' hdiagram

end WeilConjectures.LocallyFiniteAdicCompactSupport
