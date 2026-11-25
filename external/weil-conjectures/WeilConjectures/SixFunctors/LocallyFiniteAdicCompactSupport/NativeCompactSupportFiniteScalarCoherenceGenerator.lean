/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportFiniteScalarCoherenceGeneratorIntegral
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # Generator case of finite scalar coherence -/

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

/-- The finite scalar transition identity on one rationalized finite-Tor generator.
Source: Proposition 6.8.14 and Remark 6.8.15, the generator calculation in step 9
of the native compact-support finite comparison plan.

Proof: represent the source object by the prescribed finite-Tor integral object and
insert the two six-arrow `IntegralComponent` formulas from the finite-stage
comparison. The coefficient cocycle, finite-free tensor comparison and pasted-mates
normalizations identify the two composites; cancellation of the realization
isomorphisms gives the displayed transition equation. The calculation is on one
integral numerator, before the formal representative reduction to arbitrary stage
objects. (blueprint: lem-sf-native-compact-support-finite-scalar-coherence-generator) -/
 theorem native_compact_support_finite_scalar_coherence_generator [G : NativeGeometry.{u} l]
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
    (i E : Index l (PadicAlgCl l))
    (Aobj : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X i)
    (h : i ≤ E) :
    (stage.system.functor ⋙ target.J).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          (⟨i, Aobj⟩ :
            generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X) h).hom) ≫
      (alpha E).hom.app
        (((⟨i, Aobj⟩ :
          generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h)) =
      (alpha i).hom.app
        Aobj ≫
      (source.J ⋙ actual l c).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          (⟨i, Aobj⟩ :
            generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X) h).hom) := by
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
  let Kint : sfIntegralConstructibleCategory l
      (Coefficient.{u} l (PadicAlgCl l) i) X :=
    CategoryTheory.ScalarLocalization.obj Aobj
  let K' : finiteTorConstructibleIntegralCategory l
      (Coefficient.{u} l (PadicAlgCl l) i) X :=
    ⟨Kint.obj, by
      rw [← (integral_residue_tor D l hl
        (Coefficient.{u} l (PadicAlgCl l) i) X).2]
      exact Kint.property⟩
  have hK' :
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K' = Aobj := by
    rfl
  rw [← hK']
  exact native_compact_support_finite_scalar_coherence_generator_integral l D hl P c
    source target stage change hs ht alpha hα i E K' Aobj hK' h

end WeilConjectures.LocallyFiniteAdicCompactSupport
