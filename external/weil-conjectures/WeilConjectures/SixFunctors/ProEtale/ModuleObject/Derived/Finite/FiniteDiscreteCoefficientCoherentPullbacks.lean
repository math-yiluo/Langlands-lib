/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientSquareCoherence

/-! # Coherent pullbacks for the common coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The common coefficient realization has coherent derived inverse-image comparisons.
Source: Bhatt--Scholze, Proposition 5.3.2; Stacks Project, Tag 09AK
(blueprint: lem-weil-pbc-finite-discrete-coherent-pullbacks).

Proof in words. On module-valued sheaves take the conjugate of the canonical
restriction identity for the etale/pro-etale site inclusion. Encode internal modules
sectionwise with the same G. The equality hG identifies underlying restrictions, and
full faithfulness of G lifts their identities to module morphisms. The constant ring
isomorphisms are pulled back from the fixed eR at the profinite point; naturality of
constant-sheaf pullback and associativity of pullback from that point identify the
scalar maps for every scheme morphism. Thus the encoding intertwines inverse images.
Apply these exact functors termwise to complexes and localize at quasi-isomorphisms.
Identify the exact internal pullback with its total left derived functor. Restrict the
etale source to D+ and include the target in the full derived category. For a square,
the two restriction composites agree by sq.w. Conjugation preserves this identity,
as do termwise application, localization and restriction to D+. The canonical derived
composition isomorphisms give precisely the displayed equation, including its equality
transport. No direct-image or right-mate assertion is made here. -/
theorem finiteDiscreteCoefficient_coherentPullbacks [DiscreteTopology B] [Finite B] :
    Nonempty (FiniteDiscreteCoherentPullbacks B
      (finiteDiscreteCoefficientEquivalence B eR G hG)) := by
  exact ⟨{
    pullback := finiteDiscreteCoefficientPullbackIso B eR G hG
    square := finiteDiscreteCoefficientPullbackIso_square B eR G hG }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
