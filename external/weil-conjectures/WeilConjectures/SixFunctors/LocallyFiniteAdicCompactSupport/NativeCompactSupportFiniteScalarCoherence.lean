/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportFiniteScalarCoherenceGenerator
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # Integral scalar-mate steps for native compact support -/

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

/-- Normalized scalar-mate components commute with finite coefficient-stage transitions.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; step 9 of the
native compact-support finite comparison plan.
(blueprint: lem-sf-native-compact-support-finite-scalar-coherence).

Proof: represent the rational input by an integral constructible object. Residue Tor
makes it an integral finite-Tor input. Insert the two IntegralComponent formulas and
the source and target common_field formulas. P.fields.rational_normalized identifies
the StageAction scalar with the localization of the integral scalar comparison.
The normalized coefficient construction and its rational coherence identify successive
scalar comparisons, including the identity extension. The completed finite-free scalar
comparison and tensor associator send b tensor a tensor m to ba tensor m on both paths;
the tensor units insert one. The pasted-mates counit identity identifies the proper
factors, and the open tensor map identifies the open factors. Cancel the intervening
realization isomorphisms to obtain the stated equation. Naturality on integral
numerators extends the calculation to inverse uniformizer powers. This proves the
transition equation at finite stages, without descent on arbitrary common-field Homs. -/
theorem native_compact_support_finite_scalar_coherence [G : NativeGeometry.{u} l]
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
          ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)))
    (A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (E : Index l (PadicAlgCl l)) (h : A.stage ≤ E) :
    (stage.system.functor ⋙ target.J).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          A h).hom) ≫ (alpha E).hom.app (A.toStage h) =
      (alpha A.stage).hom.app A.obj ≫ (source.J ⋙ actual l c).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom)
    := by
  classical
  let primeUnit : IsUnit (l : Γ(X, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using
      (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((primeUnit.map (X.presheaf.germ ⊤ x trivial).hom).map
          (X.residue x).hom)).invertible
  rcases A with ⟨i, K⟩
  let Kint : sfIntegralConstructibleCategory l
      (Coefficient.{u} l (PadicAlgCl l) i) X :=
    CategoryTheory.ScalarLocalization.obj K
  let K' : finiteTorConstructibleIntegralCategory l
      (Coefficient.{u} l (PadicAlgCl l) i) X :=
    ⟨Kint.obj, by
      rw [← (integral_residue_tor D l hl
        (Coefficient.{u} l (PadicAlgCl l) i) X).2]
      exact Kint.property⟩
  have hK' :
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K' = K := by
    rfl
  rw [← hK']
  exact native_compact_support_finite_scalar_coherence_generator l D hl P c
    source target stage change hs ht alpha hα i E
      ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K') h

end WeilConjectures.LocallyFiniteAdicCompactSupport
