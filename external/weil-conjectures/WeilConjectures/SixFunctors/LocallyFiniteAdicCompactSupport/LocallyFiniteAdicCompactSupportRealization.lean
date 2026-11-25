/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleRealization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstruction
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.Compactification.RefinementCategory

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

import WeilConjectures.CategoryTheory.StageSystem.StageComparisonNaturality
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportGeometry
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteCompactSupportStageAction
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportFiniteComparison

/-! # Ordinary locally finite adic compact-support realization

Source: current blueprint, prose-10-20, common-field
comparisons; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-locally-finite-adic-compact-support-realization).

The auxiliary coefficient closure in the finite-stage construction is lifted only to
use its published interface. Every finite field below is a subfield of PadicAlgCl,
and the descended functor acts on the original, unlifted common-stage category.
The section presentation fixes the scalar comparison as a mate of actual operations.
-/

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

/-- The canonical scalar-extension comparison is a natural isomorphism of ordinary
common-stage and native derived compact-support functors. Neither X nor Y is assumed
separated over the field. Source: blueprint common-field comparisons;
Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-compact-support-realization).

Proof:
1. Obtain the normalized native ring and section geometry from
lem-sf-native-compact-support-geometry. This construction is independent of the finite
field datum and does not impose absolute separatedness on either scheme.
2. Use lem-sf-locally-finite-compact-support-stage-action to assemble the rational
operations of P and their prescribed scalar comparisons into a stage morphism.
3. Apply lem-sf-native-compact-support-finite-comparison to obtain the three coefficient
realizations, compatible coefficient changes and finite-stage comparison isomorphisms.
Their integral components have the original six-arrow proper/open scalar-mate formula.
4. At a pair A use the component of the finite-stage comparison at A.stage and A.obj.
Theorem lem-sf-stage-comparison-naturality proves naturality on every common-stage arrow:
factor its representative into a source transition, a same-stage arrow and an inverse
target transition, and use the finite comparison's transition equation and naturality.
NatIso.ofComponents therefore gives alpha. Its integral components are the prescribed
finite-stage components, so the six-arrow normalization is retained verbatim.
5. A native constructible object is isomorphic to a source-realized stage object by the
source image clause. The stage morphism sends that object to a target-stage object.
Compose alpha with compact support applied to the given isomorphism; the target image
clause gives constructibility of actual compact support. This includes zero objects,
empty schemes and identity coefficient extensions. -/
theorem locally_finite_adic_compact_support_realization :
    ∃ G : NativeGeometry.{u} l,
      @Nonempty (CompactSupportComparison l D hl P c (G := G)) := by
  obtain ⟨G⟩ := native_compact_support_geometry.{u} l
  let := G
  obtain ⟨stage⟩ := locally_finite_compact_support_stage_action l D hl P c
  obtain ⟨F, ⟨e⟩⟩ := native_compact_support_finite_comparison l D hl P c stage
  let alpha : stage.system.functor ⋙ F.target.J ≅ F.source.J ⋙ actual l c :=
    NatIso.ofComponents (fun A ↦ (e.alpha A.stage).app A.obj)
      (fun f ↦ StageSystem.stageComparison_naturality
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
        (stage.system.functor ⋙ F.target.J) (F.source.J ⋙ actual l c)
        e.alpha e.transition f)
  refine ⟨G, ⟨{
    source := F.source
    target := F.target
    middle := F.middle
    stage := stage
    change := F.change
    change_source := F.change_source
    change_target := F.change_target
    change_middle := F.change_middle
    alpha := alpha
    integral := ?_
    preserves := ?_ }⟩⟩
  · exact e.integral alpha (fun _ ↦ HEq.rfl)
  · intro K hK
    obtain ⟨A, ⟨i⟩⟩ := (F.source.image K).mp hK
    apply (F.target.image ((actual l c).obj K)).mpr
    exact ⟨stage.system.functor.obj A,
      ⟨alpha.app A ≪≫ (actual l c).mapIso i⟩⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
