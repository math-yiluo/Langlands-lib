/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientChange
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralLocalization
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportFiniteScalarCoherence

/-! # Finite-stage native compact-support scalar comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
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
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.LocallyFiniteAdicRealization.sections
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

/-- Realizations at the three schemes with one compatible family of coefficient maps.
Source: Bhatt--Scholze, Proposition 6.8.14, and normalized completion inclusions.
(blueprint: lem-sf-native-compact-support-finite-comparison). -/
structure CoefficientFamily [G : NativeGeometry.{u} l] where
  source : Realization l X
  target : Realization l Y
  middle : Realization l c.Z
  change : ∀ E : Index l (PadicAlgCl l),
    PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l)
  change_source : ∀ E : Index l (PadicAlgCl l),
    (change E).map X = (source.coefficient E).integralMap l X
  change_target : ∀ E : Index l (PadicAlgCl l),
    (change E).map Y = (target.coefficient E).integralMap l Y
  change_middle : ∀ E : Index l (PadicAlgCl l),
    (change E).map c.Z = (middle.coefficient E).integralMap l c.Z

/-- Finite-stage comparisons, natural on rational arrows and compatible with stage changes.
Source: Bhatt--Scholze, Remark 6.8.15, and the proper/open scalar counit mate.
(blueprint: lem-sf-native-compact-support-finite-comparison). -/
structure FiniteComparison [G : NativeGeometry.{u} l]
    (stage : StageAction l D hl P c) (F : CoefficientFamily l c) where
  alpha : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
      stage.system.functor ⋙ F.target.J ≅
    GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ F.source.J ⋙ actual l c
  transition : ∀ (A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (E : Index l (PadicAlgCl l)) (h : A.stage ≤ E),
    (stage.system.functor ⋙ F.target.J).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          A h).hom) ≫ (alpha E).hom.app (A.toStage h) =
      (alpha A.stage).hom.app A.obj ≫ (F.source.J ⋙ actual l c).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom)
  integral : ∀ (gamma : stage.system.functor ⋙ F.target.J ≅ F.source.J ⋙ actual l c),
    (∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      HEq (gamma.hom.app A) ((alpha A.stage).hom.app A.obj)) →
    IntegralNormalization l D hl P c F.source F.target stage F.change gamma

-- Forgetting endpoint certificates compares two coefficient-category presentations.
private theorem integralNormalization_of_components [G : NativeGeometry.{u} l]
    (F : CoefficientFamily l c) (stage : StageAction l D hl P c)
    (alpha : ∀ E : Index l (PadicAlgCl l),
      finiteSource l D hl P c F.target stage E ≅ finiteTarget l c F.source E)
    (hnormal : ∀ (E : Index l (PadicAlgCl l))
      (K : finiteTorConstructibleIntegralCategory l
        (Coefficient.{u} l (PadicAlgCl l) E) X),
      IntegralComponent l D hl P c F.source F.target F.change E K
        ((alpha E).hom.app
          ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)))
    (gamma : stage.system.functor ⋙ F.target.J ≅ F.source.J ⋙ actual l c)
    (hgamma : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      HEq (gamma.hom.app A) ((alpha A.stage).hom.app A.obj)) :
    IntegralNormalization l D hl P c F.source F.target stage F.change gamma := by
  intro E K
  have h := hgamma ((GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
      ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K))
  have hcomponent := eq_of_heq h
  exact (hnormal E K).elim fun A hA ↦ hA.elim fun B hB ↦ hB.elim fun r hr ↦
    hr.2.elim fun M₁ hM₁ ↦ hM₁.elim fun M₂ hM₂ ↦ hM₂.elim fun M₃ hM₃ ↦
    hM₃.elim fun M₄ hM₄ ↦ hM₄.elim fun M₅ hM₅ ↦
    hM₅.elim fun a₀ ha₀ ↦ ha₀.elim fun a₁ ha₁ ↦ ha₁.elim fun a₂ ha₂ ↦
    ha₂.elim fun a₃ ha₃ ↦ ha₃.elim fun a₄ ha₄ ↦ ha₄.elim fun a₅ ha₅ ↦
    ⟨A, B, r, hr.1.heq, M₁, M₂, M₃, M₄, M₅,
      a₀, a₁, a₂, a₃, a₄, a₅, ha₅.1.heq, ha₅.2.1.heq, ha₅.2.2.1.heq,
      ha₅.2.2.2.1.heq, ha₅.2.2.2.2.1.heq, ha₅.2.2.2.2.2.1.heq,
      (congrArg (sections l Y).mapDerivedCategory.map hcomponent).trans ha₅.2.2.2.2.2.2⟩

/-- The proper/open scalar mate is invertible on finite rational constructible inputs.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15;
steps 1--10 of the native compact-support realization plan.
(blueprint: lem-sf-native-compact-support-finite-comparison).

Proof: choose normalized realizations of X, Y and Z as in the constructible realization
lemma. At every scheme the completed-integral coefficient map sends an integral function
to that same locally finite function, so it commutes with pullback. This gives change,
and its values on X, Y and Z agree with the chosen coefficient presentations.
For integral K first extend by zero. The open reduction comparison and uniform open
interval theorem show that this remains complete constructible. The stratified-perfect
characterization gives boundedness below, and integral residue Tor gives the uniform
finite-level Tor bounds. The integral compactification-system realization and completed
direct-image limit comparison identify the recorded integral operation with actual
proper image of this open extension, with its chosen quotient projections.
Apply localized direct-image comparison to this bounded-below open object, then the
bounded-push comparison from the finite coefficient field to the algebraic closure.
The flat coefficient associator and pasted-mates identity identify their composite with
the single proper scalar counit mate. Open scalar change is the K-flat tensor map
b tensor j_!m mapped to j_!(b restricted tensor m), which is invertible.
Compose these two maps and conjugate by the source and target integral realization
isomorphisms and operationTransport. The resulting component has exactly the original
six-arrow formula of
IntegralNormalization; every factor is invertible. Any comparison
whose components are these finite-stage components has this formula, giving integral.
Integral naturality extends to fractions by inverting the uniformizer scalar, giving
alpha E on the raw rational category. The prescribed P rationalLeft and scalar q identify
these maps with the recorded operation. The common-field normalizations of both
realizations, the P coefficient cocycle, finite-free completed scalar comparison and
pasted counit identities show compatibility with isoToStage: both composites send a
pure tensor b tensor a tensor m to ba tensor m. Thus transition holds on all rational
objects. The construction remains at finite stages; descent on arbitrary common-field
Hom classes and native constructibility preservation are separate arguments. -/
theorem native_compact_support_finite_comparison [G : NativeGeometry.{u} l]
    (stage : StageAction l D hl P c) :
    ∃ F : CoefficientFamily l c, Nonempty (FiniteComparison l D hl P c stage F) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  have hchar : l ≠ ringChar D.k₀ := by
    simpa only [ringChar.eq D.k₀ D.p] using hl
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (X ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (Y ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (c.g ≫ Y ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (c.g ≫ Y ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (c.g ≫ Y ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (c.g ≫ Y ↘ Spec (.of D.k))
    infer_instance
  obtain ⟨source⟩ := locally_finite_adic_constructible_realization
    D.k₀ D.k l hchar (Over.mk (X ↘ Spec (.of D.k)))
  obtain ⟨target⟩ := locally_finite_adic_constructible_realization
    D.k₀ D.k l hchar (Over.mk (Y ↘ Spec (.of D.k)))
  obtain ⟨middle⟩ := locally_finite_adic_constructible_realization
    D.k₀ D.k l hchar (Over.mk (c.g ≫ Y ↘ Spec (.of D.k)))
  let change (E : Index l (PadicAlgCl l)) :=
    (native_completed_coefficient_change l (Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E)).choose
  have hchange (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E)
        (embedding l E)) : (change E).map T = C.integralMap l T :=
    (native_completed_coefficient_change l (Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E)).choose_spec T C
  let F : CoefficientFamily l c :=
    { source := source
      target := target
      middle := middle
      change := change
      change_source := fun E ↦ hchange E X (source.coefficient E)
      change_target := fun E ↦ hchange E Y (target.coefficient E)
      change_middle := fun E ↦ hchange E c.Z (middle.coefficient E) }
  have primeUnit : IsUnit (l : Γ(X, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((primeUnit.map (X.presheaf.germ ⊤ x trivial).hom).map (X.residue x).hom)).invertible
  have finiteIso (E : Index l (PadicAlgCl l)) :=
    native_compact_support_integral_localization l D hl P c F.source F.target stage
      F.change hchange E
  let alpha (E : Index l (PadicAlgCl l)) := (finiteIso E).choose
  have halpha (E : Index l (PadicAlgCl l)) := (finiteIso E).choose_spec
  refine ⟨F, ⟨{ alpha := alpha, transition := ?_, integral := ?_ }⟩⟩
  · exact native_compact_support_finite_scalar_coherence l D hl P c
      F.source F.target stage F.change F.change_source F.change_target alpha halpha
  · exact integralNormalization_of_components l D hl P c F stage alpha halpha

end WeilConjectures.LocallyFiniteAdicCompactSupport
