/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteTorAffineProjectiveCharts
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteTorPullbackAffineProjectiveCharts
import WeilConjectures.SixFunctors.GeneratorReduction.AffineTreeCompleteDetection
import WeilConjectures.SixFunctors.GeneratorReduction.BoundedProjectiveComplexCompleteUnrestricted
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion

/-! # Completeness of ordinary pullback on the primitive integral domain

Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Project, Tag 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary completed-coefficient pullback of a primitive integral input is complete.
Source: Bhatt--Scholze, Lemmas 6.5.5 and 6.5.9(5); Stacks Tag 099N(5);
primitive pullback step of lem-sf-primitive-completion-effectivity.
(blueprint: lem-sf-finite-tor-ordinary-pull-complete).

Proof: for a finite-Tor constructible input, use affine open covers and a finite
constructible stratification of the residue complex. On weakly contractible affine
covers of the strata, lift its finite-projective residue model to a bounded
finite-projective completed-coefficient model. Pull back this model along f.
Inverse image followed by coefficient extension preserves finite sums, summands,
and the coefficient unit, so the pulled model is still bounded finite-projective.
Its quotient tower has the coefficient quotient transitions. The coefficient unit
is the limit of its surjective quotient tower; finite sums, summands and finite
cones preserve derived completeness. Thus the pulled model is complete. Pullback
commutes with the open-closed triangles, giving completeness on each affine open
of X and hence on X by locality. For the scalar tensor unit, uniqueness of the
K-flat tensor presentation identifies it with the regular coefficient sheaf in
degree zero. Ordinary ringed pullback takes that regular sheaf to the target
regular sheaf, whose surjective quotient tower proves completeness as above.
Identity morphisms, empty schemes and zero complexes use the same constructions.
No equality of derived arrows is inferred from finite evaluations. -/
theorem finiteTorOrdinaryPullComplete {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hs : IsSeparated f) (ht : LocallyOfFiniteType f) (hq : QuasiCompact f)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (hK : finiteTorConstructibleIntegral l E Y K ∨
      K = (IntegralSystemRealization.calculus l E Y).integralClosed.monoidal.tensorUnit) :
    IntegralOnSlice.IsComplete l E X none
      ((IntegralSystemRealization.ringedPull l E f).obj K) := by
  apply affineTreeCompleteDetection.{u, u} l E X
  intro U hU
  let := hU
  obtain ⟨tree, htree⟩ :=
    finiteTorPullbackAffineProjectiveCharts l E f hs ht hq K (by
      rcases hK with hK | hK
      · left
        intro V hV
        let := hV
        obtain ⟨tree, htree⟩ := finiteTorAffineProjectiveCharts l E Y K K hK hK V
        refine ⟨tree, ?_⟩
        intro S p hp hS
        obtain ⟨c, A, hqc, hqs, hcover, hmodels⟩ := htree S p hp hS
        exact ⟨c, A, hqc, hqs, hcover, fun i ↦ hmodels i K (.inl rfl)⟩
      · exact Or.inr hK) U
  refine ⟨tree, ?_⟩
  intro S p hp hS
  obtain ⟨c, A, hqc, hqs, hcover, hmodels⟩ := htree S p hp hS
  refine ⟨c, A, hqc, hqs, hcover, ?_⟩
  intro i
  obtain ⟨P, hbP, hP, ⟨eP⟩⟩ := hmodels i
  have hc := boundedProjectiveComplex_complete.{u, u} l E (A i).left P hbP hP
  have hu := (IntegralOnSlice.canonicalCompletionUnitCriterion.{u, u} l E (A i).left _).mpr hc
  let η := IntegralOnSlice.completionUnit.{u, u} l E (A i).left none
  let F := IntegralOnSlice.completion.{u, u} l E (A i).left none
  apply (IntegralOnSlice.canonicalCompletionUnitCriterion.{u, u} l E (A i).left _).mp
  have : IsIso (η.app (DerivedCategory.Q.obj P)) := hu
  have hn := η.naturality eP.hom
  have : IsIso (η.app _ ≫ F.map eP.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map eP.hom)

end WeilConjectures.GeneratorReduction
