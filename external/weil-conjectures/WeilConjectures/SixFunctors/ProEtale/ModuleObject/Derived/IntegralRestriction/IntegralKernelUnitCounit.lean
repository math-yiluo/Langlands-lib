/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelTateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import all WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveNormalizedUnitCounitRestriction
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralLocalizingProperBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineFromPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportPullback
/-! # The fixed integral diagonal unit and trace counit

Source: sk-thm-int-restriction-line.proof.md, paragraph (1).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
attribute [local instance 20000] CategoryTheory.Mod.derivedMonoidalCategory
attribute [local instance 30000] instCategoryDerivedCategory CategoryTheory.Mod.instCategory
attribute [local instance 1] ProjectionMorphismData.category
/-- The prescribed twist-shift is the twist in the ambient diagonal formulas.
Source: the positive integral Tate-line convention in paragraph (1).
(blueprint: def-integral-kernel-unit-counit). -/
def integralAmbientTwistIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullTwistShift ℓ E f 1 ≅
      moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f ⋙
        RationalP1.twist (Profinite.padicIntegersRingObj ℓ E.val) X
          (spIntegralTwist X ℓ E) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let e := (DerivedCategory.singleFunctor (Modules Λ X) 0).mapIso
    (positiveTateLineIso ℓ E X)
  exact Functor.isoWhiskerLeft (moduleObjectDerivedPullback Λ f)
    (Functor.isoWhiskerRight ((curriedTensor _).flip.mapIso e) (shiftFunctor _ (2 : ℤ)))

/-- A pair of transformations on the two specified restricted functors.
Source: paragraph (1), displayed unit and counit.
(blueprint: def-integral-kernel-unit-counit). -/
def IntegralUnitCounitType
    (Y : Scheme.{u})
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K)) : Type (u + 2) :=
  (𝟭 _ ⟶ restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
    restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq) ×
  (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
    restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⟶ 𝟭 _)

/-- Componentwise normalization by the four-arrow diagonal insertion and inverse
projection followed by the trace. Every map is fixed; only invertibility proofs are
existential. Source: paragraph (1), formulas v, B and e.
(blueprint: def-integral-kernel-unit-counit). -/
def IntegralUnitCounitNormalized
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) (a : IntegralUnitCounitType ℓ E Y hq hr) : Prop :=
  (∀ M, ∃ hb hp,
    HEq ((a.1.app M).hom ≫
      (integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveLine Y ↘ Y)).obj M.obj))
      (RationalP1.unitComponent (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (family.integral E)
        (by
          simpa only [traceTate] using
            (integralShiftedLinePullIso ℓ E (RationalP1.secondProjection Y))) M.obj hb hp)) ∧
  (∀ K, ∃ hp,
    HEq (a.2.app K).hom
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y ↘ Y)).map
          ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app K.obj) ≫
      RationalP1.counitComponent (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (family.integral E) K.obj hp))

/-- Keep the shifted-line comparison in the original ambient model. -/
private def integral_formula_line_iso (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)] :
    (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
      (RationalP1.secondProjection Y)).obj
      (((DerivedCategory.singleFunctor
        (Modules (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)) 0).obj
        (spIntegralTwist (ProjectiveLine Y) ℓ E)) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.padicIntegersRingObj ℓ E.val) (diagonalSurface Y)) 0).obj
        (spIntegralTwist (diagonalSurface Y) ℓ E)) ⟦(2 : ℤ)⟧ := by
  simpa only [traceTate] using
    (integralShiftedLinePullIso ℓ E (RationalP1.secondProjection Y))

attribute [local irreducible] RationalP1.unitComponent RationalP1.counitComponent
  RationalP1.twistProjectionMap RationalP1.firstProjection RationalP1.secondProjection
  RationalP1.square condensedAmbientExchange RationalP1.tensorShiftIso RationalP1.twist
  rationalTwistFunctor RationalP1.projectionMateMap RationalP1.projectionMap
  spIntegralTwist integralAmbientTwistIso integralShiftedLinePullIso
  AlgebraicGeometry.ProEtale.upperStarFromPoint CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section ProjectionInversion

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

@[irreducible] private def nativeExchangeInversion
    {X' X Y' Y : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : ChosenCartesianSquare g' p' p g) (K : IntegralCompactSupport.Ambient Λ X) : Prop :=
  IsIso ((condensedAmbientExchange Λ sq).app K)

@[irreducible] private def nativeProjectionInversion
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : DerivedCategory (Modules Λ X)) (B : DerivedCategory (Modules Λ S)) : Prop :=
  IsIso (moduleObjectProjectionMate Λ f A B)

@[irreducible] private def unitExchangeInversion (Y : Scheme.{u})
    (M : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y)) : Prop :=
  nativeExchangeInversion Λ (RationalP1.square Y) M

@[irreducible] private def unitNativeMateInversion (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (M : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y)) : Prop :=
  nativeProjectionInversion Λ (RationalP1.secondProjection Y)
    ((moduleObjectDerivedPullback Λ (RationalP1.firstProjection Y)).obj M)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)

@[irreducible] private def counitNativeMateInversion (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (K : IntegralCompactSupport.Ambient Λ Y) : Prop :=
  nativeProjectionInversion Λ (ProjectiveLine Y ↘ Y)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) K

private theorem mate_inversion {X S : Scheme.{u}} (f : X ⟶ S)
    (A : IntegralCompactSupport.Ambient Λ X) (B : IntegralCompactSupport.Ambient Λ S)
    (h : IsIso (moduleObjectProjectionMap Λ f A B)) :
    IsIso (moduleObjectProjectionMate Λ f A B) := by
  unfold moduleObjectProjectionMate moduleObjectDerivedTensorComparison
  exact h

private theorem normalized_mate_inversion
    (a : RationalP1.ProjectionMateFamily Λ) (ha : RationalP1.ProjectionMateNormalized Λ a)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : IntegralCompactSupport.Ambient Λ X) (B : IntegralCompactSupport.Ambient Λ S)
    (h : IsIso (moduleObjectProjectionMate Λ f A B)) : IsIso (a f A B) := by
  unfold RationalP1.ProjectionMateNormalized RationalP1.ProjectionMateFamily
    RationalP1.internalMonoidal RationalP1.internalTensorBundle
    RationalP1.nativeTensorBundle at *
  dsimp only at ha
  rw [eq_of_heq (ha f A B)]
  exact h

private theorem unit_inversions_of_native (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (M : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (hb : unitExchangeInversion Λ Y M) (hp : unitNativeMateInversion Λ Y L M) :
    ∀ e, RationalP1.UnitInversionCondition Λ Y L e M := by
  intro e
  unfold unitExchangeInversion nativeExchangeInversion at hb
  unfold unitNativeMateInversion nativeProjectionInversion at hp
  have : IsIso (RationalP1.projectionMateMap Λ (RationalP1.secondProjection Y)
      ((moduleObjectDerivedPullback Λ (RationalP1.firstProjection Y)).obj M)
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) := by
    unfold RationalP1.projectionMateMap
    exact normalized_mate_inversion Λ _
      (RationalP1.projectionMate_existsUnique Λ).exists.choose_spec
      (RationalP1.secondProjection Y) _ _ hp
  refine ⟨hb, ?_⟩
  unfold RationalP1.twistProjectionMap
  infer_instance

private theorem counit_inversion_of_native (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (K : IntegralCompactSupport.Ambient Λ Y)
    (hp : counitNativeMateInversion Λ Y L K) :
    RationalP1.CounitInversionCondition Λ Y L K := by
  unfold counitNativeMateInversion nativeProjectionInversion at hp
  unfold RationalP1.CounitInversionCondition RationalP1.projectionMap
  exact RationalP1.normalized_projection_isIso Λ _
    (RationalP1.projection_existsUnique Λ).exists.choose_spec (ProjectiveLine Y ↘ Y) K _ hp

end ProjectionInversion

private theorem comp_iso_cancel {C : Type*} [Category* C] {X Y Z : C}
    (f : X ⟶ Y) (e : Z ≅ Y) : (f ≫ e.inv) ≫ e.hom = f := by
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Apply the integral projection formula before specializing the geometry. -/
private theorem integral_projection_mate_isIso
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsProper f]
    (A : DerivedCategory (Modules (Profinite.padicIntegersRingObj ℓ E.val) X))
    (B : DerivedCategory (Modules (Profinite.padicIntegersRingObj ℓ E.val) S))
    (hA : IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X A)
    (hB : IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) S B) :
    nativeProjectionInversion (Profinite.padicIntegersRingObj ℓ E.val) f A B := by
  unfold nativeProjectionInversion
  exact mate_inversion (Profinite.padicIntegersRingObj ℓ E.val) f A B
    ((integralProperProjectionFormula ℓ E k f).2.2 A B hA hB)

/-- Keep the native source and the localizing target models. -/
private theorem integral_projection_mate_isIso_mixed
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsProper f]
    (A : DerivedCategory (Modules (Profinite.padicIntegersRingObj ℓ E.val) X))
    (B : IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) S)
    (hA : IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X A)
    (hB : IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) S B) :
    nativeProjectionInversion (Profinite.padicIntegersRingObj ℓ E.val) f A B := by
  unfold nativeProjectionInversion
  exact mate_inversion (Profinite.padicIntegersRingObj ℓ E.val) f A B
    ((integralProperProjectionFormula ℓ E k f).2.2 A B hA hB)

/-- Apply the integral exchange theorem before specializing the square. -/
private theorem integral_exchange_isIso
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X' X Y' Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    [p.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [p'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    [IsProper p] (sq : ChosenCartesianSquare g' p' p g)
    (K : IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) X)
    (hK : IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X K) :
    nativeExchangeInversion (Profinite.padicIntegersRingObj ℓ E.val) sq K := by
  unfold nativeExchangeInversion
  exact (integralLocalizing_properBaseChange ℓ k E sq K hK).2.2

/-- Convert pullback preservation before specializing the source schemes. -/
private theorem integral_pull_localizing
    (k : Type u) [Field k]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))]
    (M : IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) S)
    (hM : IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) S M) :
    IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X
      ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).obj M) := by
  let space (Z : Scheme.{u}) [Z.Over (Spec (.of k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
      [IsSeparated (Z ↘ Spec (.of k))] : IntegralCompactSupport.Spaces k :=
    ⟨Over.mk (Z ↘ Spec (.of k)),
      inferInstanceAs (IsSeparated (Z ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (Z ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (Z ↘ Spec (.of k)))⟩
  exact (IntegralCompactSupport.pullback_of_ctf_eq k ℓ E
    (X := space X) (Y := space S)
    (ObjectProperty.homMk (f.asOver (Spec (.of k))))).2 M hM

section CachedTransportInstances

attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory

section PairTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem localizing_preservation_of_iso
    {X Y : Scheme.{u}}
    (T V : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ X)
    (e : T ≅ V)
    (hT : ∀ K, IntegralCompactSupport.localizing Λ Y K →
      IntegralCompactSupport.localizing Λ X (T.obj K)) :
    ∀ K : (IntegralCompactSupport.localizing Λ Y).FullSubcategory,
      IntegralCompactSupport.localizing Λ X (V.obj K.obj) := by
  have hP := (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X)).2.2.2.1
  let : (IntegralCompactSupport.localizing Λ X).IsClosedUnderIsomorphisms := hP.2.1
  intro K
  exact (IntegralCompactSupport.localizing Λ X).prop_of_iso (e.app K.obj)
    (hT K.obj K.property)

end PairTransport

end CachedTransportInstances

section RawScalarTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Check the naturality square before specializing the coefficient ring.
private theorem transported_unit_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (ep : (moduleObjectDerivedPullback Λ (RationalP1.secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    {M N : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y)} (f : M ⟶ N)
    (hM : RationalP1.UnitInversionCondition Λ Y L ep M)
    (hN : RationalP1.UnitInversionCondition Λ Y L ep N) :
    f ≫ (RationalP1.unitComponent Λ Y L d ep N hN.1 hN.2 ≫
        e.inv.app ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj N)) =
      (RationalP1.unitComponent Λ Y L d ep M hM.1 hM.2 ≫
        e.inv.app ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ≫
          T.map ((IntegralCompactSupport.push Λ (ProjectiveLine Y ↘ Y)).map f) := by
  exact RationalP1.compose_square
    (RationalP1.unitComponent_naturality Λ Y L d ep f hM hN)
    (e.inv.naturality ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map f))

-- Check the naturality square before specializing the coefficient ring.
private theorem transported_counit_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    {K K' : IntegralCompactSupport.Ambient Λ Y} (f : K ⟶ K')
    (hK : RationalP1.CounitInversionCondition Λ Y L K)
    (hK' : RationalP1.CounitInversionCondition Λ Y L K') :
    (IntegralCompactSupport.push Λ (ProjectiveLine Y ↘ Y)).map (T.map f) ≫
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
          (e.hom.app K') ≫ RationalP1.counitComponent Λ Y L d K' hK') =
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (e.hom.app K) ≫ RationalP1.counitComponent Λ Y L d K hK) ≫ f := by
  exact RationalP1.compose_square
    (RationalP1.map_square (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y))
      (e.hom.naturality f))
    (RationalP1.counitComponent_naturality Λ Y L d f hK hK')

private def transported_unit_app (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (ep : (moduleObjectDerivedPullback Λ (RationalP1.secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    (M : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (hM : RationalP1.UnitInversionCondition Λ Y L ep M) :
    M ⟶ T.obj ((IntegralCompactSupport.push Λ (ProjectiveLine Y ↘ Y)).obj M) :=
  RationalP1.unitComponent Λ Y L d ep M hM.1 hM.2 ≫
    e.inv.app ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)

private def transported_counit_app (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    (K : IntegralCompactSupport.Ambient Λ Y)
    (hK : RationalP1.CounitInversionCondition Λ Y L K) :
    (IntegralCompactSupport.push Λ (ProjectiveLine Y ↘ Y)).obj (T.obj K) ⟶ K :=
  (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (e.hom.app K) ≫
    RationalP1.counitComponent Λ Y L d K hK

private theorem transported_unit_app_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (ep : (moduleObjectDerivedPullback Λ (RationalP1.secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    {M N : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y)} (f : M ⟶ N)
    (hM : RationalP1.UnitInversionCondition Λ Y L ep M)
    (hN : RationalP1.UnitInversionCondition Λ Y L ep N) :
    f ≫ transported_unit_app Λ Y L d ep T e N hN =
      transported_unit_app Λ Y L d ep T e M hM ≫
        T.map ((IntegralCompactSupport.push Λ (ProjectiveLine Y ↘ Y)).map f) :=
  transported_unit_naturality Λ Y L d ep T e f hM hN

private theorem transported_counit_app_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    {K K' : IntegralCompactSupport.Ambient Λ Y} (f : K ⟶ K')
    (hK : RationalP1.CounitInversionCondition Λ Y L K)
    (hK' : RationalP1.CounitInversionCondition Λ Y L K') :
    (IntegralCompactSupport.push Λ (ProjectiveLine Y ↘ Y)).map (T.map f) ≫
        transported_counit_app Λ Y L d T e K' hK' =
      transported_counit_app Λ Y L d T e K hK ≫ f :=
  transported_counit_naturality Λ Y L d T e f hK hK'

private theorem transported_unit_app_normalized (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (ep : (moduleObjectDerivedPullback Λ (RationalP1.secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    (M : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (hM : RationalP1.UnitInversionCondition Λ Y L ep M) :
    RationalP1.UnitComponentNormalized Λ Y L d ep M
      (transported_unit_app Λ Y L d ep T e M hM ≫
        e.hom.app ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) :=
  ⟨hM.1, hM.2, heq_of_eq
    (comp_iso_cancel (RationalP1.unitComponent Λ Y L d ep M hM.1 hM.2)
      (e.app ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)))⟩

private theorem transported_counit_app_normalized (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (T : IntegralCompactSupport.Ambient Λ Y ⥤ IntegralCompactSupport.Ambient Λ (ProjectiveLine Y))
    (e : T ≅ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      RationalP1.twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    (K : IntegralCompactSupport.Ambient Λ Y)
    (hK : RationalP1.CounitInversionCondition Λ Y L K) :
    ∃ hp, HEq (transported_counit_app Λ Y L d T e K hK)
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (e.hom.app K) ≫
        RationalP1.counitComponent Λ Y L d K hp) := ⟨hK, HEq.rfl⟩

end RawScalarTransport

section IntegralAssembly

variable
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y)

private def fixedUnitNormalized
    (η : 𝟭 _ ⟶ restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
      restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq) : Prop :=
  ∀ M, RationalP1.UnitComponentNormalized (Profinite.padicIntegersRingObj ℓ E.val) Y
    (fun X ↦ spIntegralTwist X ℓ E) (family.integral E)
    (integral_formula_line_iso ℓ E Y) M.obj
    ((η.app M).hom ≫ (integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y ↘ Y)).obj M.obj))

private def fixedCounitNormalized
    (ε : restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
      restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⟶ 𝟭 _) : Prop :=
  ∀ K, ∃ hp, HEq (ε.app K).hom
    ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
      (ProjectiveLine Y ↘ Y)).map
        ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app K.obj) ≫
      RationalP1.counitComponent (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (family.integral E) K.obj hp)

private theorem fixed_normalization_iff
    (η : 𝟭 _ ⟶ restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
      restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq)
    (ε : restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
      restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⟶ 𝟭 _) :
    IntegralUnitCounitNormalized ℓ E Y hq hr family (η, ε) ↔
      fixedUnitNormalized ℓ E Y hq hr family η ∧
        fixedCounitNormalized ℓ E Y hq hr family ε := Iff.rfl

private def fixedUnitApp (family : Family ℓ Y)
    (hI : ∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj)
    (M : (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
      (ProjectiveLine Y)).FullSubcategory) :
    M ⟶ ((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
      restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj M) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  let ep := integral_formula_line_iso ℓ E Y
  exact ObjectProperty.homMk
    (transported_unit_app Λ Y L (family.integral E) ep _ e M.obj (hI M))

private theorem fixedUnitApp_naturality (family : Family ℓ Y)
    (hI : ∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj)
    {M N : (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
      (ProjectiveLine Y)).FullSubcategory} (f : M ⟶ N) :
    f ≫ fixedUnitApp ℓ E Y hq hr family hI N =
      fixedUnitApp ℓ E Y hq hr family hI M ≫
        (restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
      restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).map f := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  let ep := integral_formula_line_iso ℓ E Y
  exact ObjectProperty.hom_ext _
    (transported_unit_app_naturality Λ Y L (family.integral E) ep _ e f.hom
      (hI M) (hI N))

private def fixedUnit (family : Family ℓ Y)
    (hI : ∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj) :
    𝟭 _ ⟶ restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
      restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq :=
  { app := fixedUnitApp ℓ E Y hq hr family hI
    naturality := fun _ _ f ↦ fixedUnitApp_naturality ℓ E Y hq hr family hI f }

private theorem fixedUnit_comparison_eq (family : Family ℓ Y)
    (hI : ∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj)
    (M : (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
      (ProjectiveLine Y)).FullSubcategory) :
    ((fixedUnit ℓ E Y hq hr family hI).app M).hom ≫
      (integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveLine Y ↘ Y)).obj M.obj) =
      transported_unit_app (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (family.integral E)
        (integral_formula_line_iso ℓ E Y) (pullTwistShift ℓ E (ProjectiveLine Y ↘ Y) 1)
        (integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)) M.obj (hI M) ≫
      (integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveLine Y ↘ Y)).obj M.obj) := rfl

private theorem fixedUnit_normalized (family : Family ℓ Y)
    (hI : ∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj) :
    fixedUnitNormalized ℓ E Y hq hr family (fixedUnit ℓ E Y hq hr family hI) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  let ep := integral_formula_line_iso ℓ E Y
  intro M
  exact Eq.mpr (congrArg
    (RationalP1.UnitComponentNormalized Λ Y L (family.integral E) ep M.obj)
    (fixedUnit_comparison_eq ℓ E Y hq hr family hI M))
    (transported_unit_app_normalized Λ Y L (family.integral E) ep _ e M.obj (hI M))

private def fixedCounitApp (family : Family ℓ Y)
    (hJ : ∀ K : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory,
      RationalP1.CounitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) K.obj)
    (K : (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
      Y).FullSubcategory) :
    ((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
      restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).obj K) ⟶ K := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  exact ObjectProperty.homMk
    (transported_counit_app Λ Y L (family.integral E) _ e K.obj (hJ K))

omit [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
  [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)] in
private theorem fixedCounitApp_naturality (family : Family ℓ Y)
    (hJ : ∀ K : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory,
      RationalP1.CounitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) K.obj)
    {K K' : (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
      Y).FullSubcategory} (f : K ⟶ K') :
    (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
      restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).map f ≫
        fixedCounitApp ℓ E Y hq hr family hJ K' =
      fixedCounitApp ℓ E Y hq hr family hJ K ≫ f := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  exact ObjectProperty.hom_ext _
    (transported_counit_app_naturality Λ Y L (family.integral E) _ e f.hom
      (hJ K) (hJ K'))

private def fixedCounit (family : Family ℓ Y)
    (hJ : ∀ K : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory,
      RationalP1.CounitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) K.obj) :
    restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
      restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⟶ 𝟭 _ :=
  { app := fixedCounitApp ℓ E Y hq hr family hJ
    naturality := fun _ _ f ↦ fixedCounitApp_naturality ℓ E Y hq hr family hJ f }

omit [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
  [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)] in
private theorem fixedCounit_normalized (family : Family ℓ Y)
    (hJ : ∀ K : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory,
      RationalP1.CounitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) K.obj) :
    fixedCounitNormalized ℓ E Y hq hr family (fixedCounit ℓ E Y hq hr family hJ) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  intro K
  exact transported_counit_app_normalized Λ Y L (family.integral E) _ e K.obj (hJ K)

private theorem fixedUnit_unique
    (η η' : 𝟭 _ ⟶ restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
      restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq)
    (hη : fixedUnitNormalized ℓ E Y hq hr family η)
    (hη' : fixedUnitNormalized ℓ E Y hq hr family η') : η = η' := by
  apply NatTrans.ext
  funext M
  apply ObjectProperty.hom_ext
  apply (cancel_mono ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app
    ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
      (ProjectiveLine Y ↘ Y)).obj M.obj))).1
  obtain ⟨hb, hp, h⟩ := hη M
  obtain ⟨hb', hp', h'⟩ := hη' M
  exact eq_of_heq (h.trans h'.symm)

omit [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
  [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)] in
private theorem fixedCounit_unique
    (ε ε' : restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
      restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⟶ 𝟭 _)
    (hε : fixedCounitNormalized ℓ E Y hq hr family ε)
    (hε' : fixedCounitNormalized ℓ E Y hq hr family ε') : ε = ε' := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  obtain ⟨hp, h⟩ := hε K
  obtain ⟨hp', h'⟩ := hε' K
  exact eq_of_heq (h.trans h'.symm)

private theorem integral_pair_of_inversions (family : Family ℓ Y)
    (hI : ∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj)
    (hJ : ∀ K : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory,
      RationalP1.CounitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) K.obj) :
    ∃! a : IntegralUnitCounitType ℓ E Y hq hr,
      IntegralUnitCounitNormalized ℓ E Y hq hr family a := by
  let η := fixedUnit ℓ E Y hq hr family hI
  let ε := fixedCounit ℓ E Y hq hr family hJ
  have hη := fixedUnit_normalized ℓ E Y hq hr family hI
  have hε := fixedCounit_normalized ℓ E Y hq hr family hJ
  refine ⟨(η, ε), (fixed_normalization_iff ℓ E Y hq hr family η ε).2 ⟨hη, hε⟩, ?_⟩
  intro b hb
  have h := (fixed_normalization_iff ℓ E Y hq hr family b.1 b.2).1 hb
  exact Prod.ext (fixedUnit_unique ℓ E Y hq hr family _ _ h.1 hη)
    (fixedCounit_unique ℓ E Y hq hr family _ _ h.2 hε)

end IntegralAssembly

-- Check the geometric witnesses separately from the transformation data.
/-- The fixed exchange and two projections are invertible on the localizing objects. -/
private theorem integral_inversion_conditions
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    :
    (∀ M : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)).FullSubcategory,
      RationalP1.UnitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (integral_formula_line_iso ℓ E Y) M.obj) ∧
    (∀ K : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory,
      RationalP1.CounitInversionCondition (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) K.obj) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let P := IntegralCompactSupport.localizing Λ (ProjectiveLine Y)
  let Q := IntegralCompactSupport.localizing Λ Y
  let q : ProjectiveLine Y ⟶ Y := ProjectiveLine Y ↘ Y
  let e := integralAmbientTwistIso ℓ E q
  let : (ProjectiveLine Y).Over (Spec (.of k)) := inferInstance
  let : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨RationalP1.secondProjection Y ≫ q ≫ (Y ↘ Spec (.of k))⟩
  have : q.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (RationalP1.secondProjection Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (RationalP1.firstProjection Y).IsOver (Spec (.of k)) := by
    constructor
    change RationalP1.firstProjection Y ≫ (q ≫ (Y ↘ Spec (.of k))) =
      RationalP1.secondProjection Y ≫ q ≫ (Y ↘ Spec (.of k))
    simpa only [RationalP1.firstProjection, RationalP1.secondProjection,
      Category.assoc] using
      congrArg (fun f : diagonalSurface Y ⟶ Y ↦ f ≫ (Y ↘ Spec (.of k)))
        (pullback.condition (f := q) (g := q))
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (q ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (q ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (q ≫ (Y ↘ Spec (.of k))))
  have : IsProper (RationalP1.secondProjection Y) :=
    inferInstanceAs (IsProper (pullback.snd q q))
  have : LocallyOfFiniteType (diagonalSurface Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (RationalP1.secondProjection Y ≫ q ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (diagonalSurface Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact
      (RationalP1.secondProjection Y ≫ q ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (diagonalSurface Y ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated
      (RationalP1.secondProjection Y ≫ q ≫ (Y ↘ Spec (.of k))))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hG : ∀ K : Q.FullSubcategory,
      P ((moduleObjectDerivedPullback Λ q ⋙
        RationalP1.twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
          K.obj) :=
    localizing_preservation_of_iso Λ _ _ e hq
  have hline := RationalP1.line_localizing_of_preservation Λ q
    (spIntegralTwist (ProjectiveLine Y) ℓ E) (fun K hK ↦ hG ⟨K, hK⟩)
  have hpull (M : P.FullSubcategory) : IntegralCompactSupport.localizing Λ
      (diagonalSurface Y)
      ((moduleObjectDerivedPullback Λ (RationalP1.firstProjection Y)).obj M.obj) :=
    integral_pull_localizing ℓ E k (RationalP1.firstProjection Y) M.obj M.property
  let ep : (moduleObjectDerivedPullback Λ (RationalP1.secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (spIntegralTwist (ProjectiveLine Y) ℓ E)) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (spIntegralTwist (diagonalSurface Y) ℓ E)) ⟦(2 : ℤ)⟧ := integral_formula_line_iso ℓ E Y
  have hI : ∀ M : P.FullSubcategory,
      RationalP1.UnitInversionCondition Λ Y (fun X ↦ spIntegralTwist X ℓ E) ep M.obj := by
    intro M
    have hb : unitExchangeInversion Λ Y M.obj := by
      unfold unitExchangeInversion
      exact integral_exchange_isIso ℓ E k (RationalP1.square Y) M.obj M.property
    have hp : unitNativeMateInversion Λ Y (fun X ↦ spIntegralTwist X ℓ E) M.obj := by
      unfold unitNativeMateInversion
      exact integral_projection_mate_isIso ℓ E k (RationalP1.secondProjection Y) _ _
        (hpull M) hline
    exact unit_inversions_of_native Λ Y (fun X ↦ spIntegralTwist X ℓ E) M.obj hb hp ep
  have hJ : ∀ K : Q.FullSubcategory,
      RationalP1.CounitInversionCondition Λ Y (fun X ↦ spIntegralTwist X ℓ E) K.obj := by
    intro K
    have hp : counitNativeMateInversion Λ Y (fun X ↦ spIntegralTwist X ℓ E) K.obj := by
      unfold counitNativeMateInversion
      exact integral_projection_mate_isIso_mixed ℓ E k q _ _ hline K.property
    exact counit_inversion_of_native Λ Y (fun X ↦ spIntegralTwist X ℓ E) K.obj hp
  exact ⟨hI, hJ⟩

-- Specializing the ambient formulas requires extended typeclass and reduction search.
/-- The fixed diagonal and trace formulas form a unique natural pair.
Source: paragraph (1), construction of eta and epsilon.
(blueprint: lem-integral-unit-counit-construction).
Proof: proper base change inverts the self-square exchange on the localizing closure.
The proper projection formula inverts the q projection and the p2 twisted projection;
the shifted integral line belongs to the closure. The Cartesian Tate comparison fixes
its endpoints. Compose the section comparison, inverse diagonal tensor comparison,
diagonal class, inverse twisted projection, and inverse exchange to form eta.
For epsilon, invert the q projection and contract with the normalized trace.
Naturality of every factor proves naturality of these pastes. Fullness restricts them
using hq and hr. Extensionality of natural transformations and the two component
normalizations prove uniqueness; only invertibility proofs are existential. -/
theorem integralUnitCounit_existsUnique
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) :
    ∃! a : IntegralUnitCounitType ℓ E Y hq hr,
      IntegralUnitCounitNormalized ℓ E Y hq hr family a := by
  obtain ⟨hI, hJ⟩ := integral_inversion_conditions ℓ E k Y hq
  exact integral_pair_of_inversions ℓ E Y hq hr family hI hJ

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
