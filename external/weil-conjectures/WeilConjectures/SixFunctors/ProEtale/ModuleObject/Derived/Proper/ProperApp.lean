/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarBaseChangeCompatibility

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralReductionConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralExchangeReduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousExchangeIntegralModel

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Pointwise proper base change for the condensed finite coefficient.

Source: the finite-coefficient realization and the proper exchange theorem in the proof of
`nt-target-proetale-e` (blueprint: new-proper-continuous-basechange-app).
For every bounded constructible object, the finite-coefficient proper base-change component is
invertible; the inverse is transported through the realization comparisons. This is strictly the
componentwise part of the natural-transformation theorem; assembly is handled separately.
-/
theorem isIso_boundedConstructibleBaseChange_continuousMap_app [IsProper f]
    (sq : IsPullback g' f' f g) :
    ∀ K : _,
      IsIso ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
        (sq.toCommSq.asOver (Spec (.of k)))).app K) := by
  intro K
  let : IsNoetherian (Spec (.of k)) := {}
  let : IsNoetherian Y' := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType
    (Y' ↘ Spec (.of k))
  let : TopologicalSpace.NoetherianSpace Y' := by infer_instance
  obtain ⟨M, ⟨e⟩⟩ := continuousExchange_integral_model ℓ E k sq K
  have hred := integralExchange_reduction_isIso ℓ E k sq M
  have hM : IsIso ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
      (sq.toCommSq.asOver (Spec (.of k)))).app M) :=
    integralReduction_reflects_isIso ℓ E Y' _ hred
  have hscalar : IsIso ((integralScalarExtension ℓ E Y').map
      ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
        (sq.toCommSq.asOver (Spec (.of k)))).app M).hom) :=
    inferInstance
  have hE : IsIso ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
      (sq.toCommSq.asOver (Spec (.of k)))).app K).hom :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 hscalar
  exact (ObjectProperty.isIso_hom_iff _).mp hE

/-- Pointwise proper base change for the condensed algebraic-closure coefficient.

Source: the finite-coefficient realization, filtered two-colimit, and proper exchange
compatibility in the proof of `nt-target-proetale-qbar`
(blueprint: new-proper-qbar-basechange-app).
For every bounded constructible object, descend to a finite coefficient stage, apply finite-stage
proper base change, and transport the inverse through coefficient-change comparisons and the
two-colimit presentation. This is strictly the componentwise part; assembly is separate.
-/
theorem isIso_boundedConstructibleBaseChange_padicAlgCl_app [IsProper f]
    (sq : IsPullback g' f' f g) :
    ∀ K : _,
      IsIso ((boundedConstructibleBaseChange ℓ (sq.toCommSq.asOver (Spec (.of k)))).app K) := by
  intro K
  let : IsNoetherian (Spec (.of k)) := {}
  let : IsNoetherian X := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  let : TopologicalSpace.NoetherianSpace X := by infer_instance
  obtain ⟨E, K₀, ⟨e⟩⟩ :=
    AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj X ℓ K
  let csq : AlgebraicGeometry.ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have hcompat := constructibleToQbar_baseChange_compatibility ℓ k E f g f' g' csq
  have hfinite := isIso_boundedConstructibleBaseChange_continuousMap_app
    ℓ E k sq K₀
  have hsource : IsIso (constructibleToQbarSourceHom ℓ k E f g K₀) :=
    (hcompat.2.2 K₀).1
  have htarget : IsIso (constructibleToQbarTargetHom ℓ k E f' g' K₀) :=
    (hcompat.2.2 K₀).2.1
  let : IsIso (constructibleToQbarSourceHom ℓ k E f g K₀ ≫
      (boundedConstructibleBaseChange ℓ (sq.toCommSq.asOver (Spec (.of k)))).app
        ((AlgebraicGeometry.ProEtale.constructibleToPadicAlgCl X ℓ E).obj K₀)) := by
    rw [(hcompat.2.2 K₀).2.2]
    infer_instance
  have hcomp : IsIso ((boundedConstructibleBaseChange ℓ (sq.toCommSq.asOver (Spec (.of k)))).app
        ((AlgebraicGeometry.ProEtale.constructibleToPadicAlgCl X ℓ E).obj K₀)) :=
    IsIso.of_isIso_comp_left (constructibleToQbarSourceHom ℓ k E f g K₀) _
  exact (NatTrans.isIso_app_iff_of_iso
    (boundedConstructibleBaseChange ℓ (sq.toCommSq.asOver (Spec (.of k)))) e).1 hcomp

end AlgebraicGeometry.ProEtale.CondensedRing
