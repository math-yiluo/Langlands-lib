/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarBoundaries
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Canonical construction and six-arrow normalization of integral scalar morphisms. -/

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

attribute [local irreducible] ScalarLocalization.category

private def liftNatTrans
    {A B T : Type*} [Category A] [Category B] [Category T]
    (J : B ⥤ T) [J.Full] [J.Faithful] {F H : A ⥤ B}
    (sigma : F ⋙ J ⟶ H ⋙ J) : F ⟶ H where
  app K := J.preimage (sigma.app K)
  naturality K L f := by
    apply J.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    exact sigma.naturality f

private theorem map_liftNatTrans
    {A B T : Type*} [Category A] [Category B] [Category T]
    (J : B ⥤ T) [J.Full] [J.Faithful] {F H : A ⥤ B}
    (sigma : F ⋙ J ⟶ H ⋙ J) (K : A) :
    J.map ((liftNatTrans J sigma).app K) = sigma.app K :=
  J.map_preimage _

private theorem sixArrow_combine
    {T : Type*} [Category T] {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : T}
    (a₀ : M₀ ⟶ M₁) (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃)
    (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅) (a₅ : M₅ ⟶ M₆)
    (b : M₀ ⟶ M₃) (d : M₄ ⟶ M₆)
    (hb : b = a₀ ≫ a₁ ≫ a₂) (hd : d = a₄ ≫ a₅) :
    b ≫ a₃ ≫ d = a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ := by
  subst b d
  simp only [Category.assoc]

/-- Construct a normalized integral morphism from a scalar natural transformation.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15.
Proof: compose the finite stage inclusion and rationalLeft comparisons, localization
of the integral action, the target integral realization, the inverse compact-support
realization, the supplied scalar map, and the inverse source and operation realizations.
Full faithfulness of the derived section equivalence lifts this natural composite.
Evaluating its components and applying associativity gives the displayed factors and
six prescribed arrows. No invertibility of the supplied scalar map is assumed.
(blueprint: lem-sf-native-integral-scalar-morphism-normalization). -/
theorem native_integral_scalar_morphism_normalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l))
    (sx : (PurCompactSupport.completed l (Coefficient l (PadicAlgCl l) E)).ring X ⟶
      (nativeCoefficients l).ring X)
    (sy : (PurCompactSupport.completed l (Coefficient l (PadicAlgCl l) E)).ring Y ⟶
      (nativeCoefficients l).ring Y)
    (hs : sx = (source.coefficient E).integralMap l X)
    (ht : sy = (target.coefficient E).integralMap l Y)
    (beta : PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient l (PadicAlgCl l) E)) c ⋙ pbcDerivedExtend sy ⟶
      pbcDerivedExtend sx ⋙ PurCompactSupport.image (nativeCoefficients l) c) :
    ∃ tau : sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⟶
      sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c),
      ∀ K : finiteTorConstructibleIntegralCategory l
          (Coefficient l (PadicAlgCl l) E) X,
        (∃ (b : (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
                (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J)).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) ≅
            (PurCompactSupport.image (PurCompactSupport.completed l
              (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
              pbcDerivedExtend sy).obj K.obj)
          (d : (pbcDerivedExtend sx ⋙
              PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ≅
            (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
                (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c)).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))),
          (sections l Y).mapDerivedCategory.map
              (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) =
            b.hom ≫ beta.app K.obj ≫ d.hom) ∧
        IntegralScalarFormula l D hl P c source target E K
          (beta.app K.obj)
          (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
            (Coefficient l (PadicAlgCl l) E) X).obj K)) := by
  subst sx sy
  refine (native_integral_scalar_boundaries l D hl P c source target stage E).elim ?_
  intro b hb
  refine hb.elim ?_
  intro d hboundaries
  let sigma := b.hom ≫ Functor.whiskerLeft
    (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι beta ≫ d.hom
  let : (sections l Y).mapDerivedCategory.IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory _
  let tau := liftNatTrans (sections l Y).mapDerivedCategory
    (F := sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J))
    (H := sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c)) sigma
  have htau (K : sfIntegralConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
      (sections l Y).mapDerivedCategory.map (tau.app K) = sigma.app K :=
    map_liftNatTrans (sections l Y).mapDerivedCategory
      (F := sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J))
      (H := sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c)) sigma K
  refine ⟨tau, fun K ↦ ⟨?_, ?_⟩⟩
  · let L := (PurCompactSupport.finiteTorIntegralInclusion l
      (Coefficient l (PadicAlgCl l) E) X).obj K
    exact ⟨b.app L, d.app L, htau L⟩
  · rcases (hboundaries K).1 with
      ⟨A, B, r, hr, M₁, M₂, a₀, a₁, a₂, ha₀, ha₁, ha₂, hb⟩
    rcases (hboundaries K).2 with ⟨M₅, a₄, a₅, ha₄, ha₅, hd⟩
    refine ⟨A, B, r, hr, ?_⟩
    let M₃ := (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient l (PadicAlgCl l) E)) c ⋙
      pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj K.obj
    let M₄ := (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
      PurCompactSupport.image (nativeCoefficients l) c).obj K.obj
    refine ⟨M₁, M₂, M₃, M₄, M₅, ?_⟩
    refine ⟨a₀, ?_⟩
    refine ⟨a₁, a₂, beta.app K.obj, a₄, a₅, ?_⟩
    refine ⟨ha₀, ha₁, ha₂, ArrowHEq.refl _, ha₄, ha₅, ?_⟩
    let L := (PurCompactSupport.finiteTorIntegralInclusion l
      (Coefficient l (PadicAlgCl l) E) X).obj K
    refine (htau L).trans ?_
    change b.hom.app L ≫ beta.app K.obj ≫ d.hom.app L = _
    exact sixArrow_combine a₀ a₁ a₂ (beta.app K.obj) a₄ a₅
      (b.hom.app L) (d.hom.app L) hb hd

end WeilConjectures.LocallyFiniteAdicCompactSupport
