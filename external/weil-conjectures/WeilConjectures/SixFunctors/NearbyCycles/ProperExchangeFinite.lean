/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange
import WeilConjectures.Tactic.ExactModProofs

/-!

# The proper exchange of nearby cycles with finite coefficients

Let `T` be a finite discrete commutative ring (for instance `𝒪_E/ϖⁿ`) and `T̲ = C(-, T)` its
condensed ring. For a morphism of models `φ : M ⟶ N` over `f : X ⟶ Y` and `f' : X' ⟶ Y'`
(`NearbyCyclesModel.Hom`) whose morphism of total spaces and `f` are proper, whose squares of
special fibres and of identifications `ε` are cartesian and whose inclusion `j_M` of the geometric
generic fibre is quasi-compact and quasi-separated, the pushforward exchange
`χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` is an isomorphism at every complex bounded below of étale origin
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`). This is
blueprint `prose-E-03` (2), "proper exchange", SGA 7 XIII 2.1.7, for a model
over an arbitrary trait (no hypothesis on the base is needed).

By `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isIso_baseChangeMap`, `χ_f` is
invertible at `K` once the base change morphisms of the square of identifications at `K` and of
the square of special fibres at `Rj_{M*} Lε_M^* K` are; both are instances of proper base change
with finite coefficients
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_finiteCoefficient`), the second at
`Rj_{M*} Lε_M^* K`, which is again of étale origin
(`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj`,
`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **The proper exchange of nearby cycles with finite coefficients** (blueprint
`prose-E-03` (2); SGA 7 XIII 2.1.7): let `φ : M ⟶ N` be a morphism of models
whose morphism of total spaces and `f` are proper, whose squares of special fibres and of
identifications `ε` are cartesian, and whose inclusion `j_M` of the geometric generic fibre is
quasi-compact and quasi-separated. Then the pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` with
coefficients in a finite ring `T` is an isomorphism at every complex `K` bounded below of étale
origin: by proper base change along `ε_N` and along `i_N`, both sides are
`i_N^* Rt_* Rj_{M*} Lε_M^* K`. -/
theorem isIso_pushforwardExchange_app_of_isProper_finiteCoefficient (φ : M.Hom N f f')
    [IsProper φ.total] [IsProper f] [QuasiCompact M.j] [QuasiSeparated M.j]
    (hi : IsPullback M.i f' φ.total N.i) (hε : IsPullback M.ε φ.generic f N.ε)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K)) :
    IsIso ((φ.pushforwardExchange (Profinite.continuousMapRingObj T)).app K) := by
  have h₁ := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T hε K hK
  have h₂ := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T M.j
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.ε hK)
  have h₃ := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T hi _ h₂
  have key := φ.isIso_pushforwardExchange_app_of_isIso_baseChangeMap
    (Profinite.continuousMapRingObj T) K (by exact_mod_proofs h₁) (by exact_mod_proofs h₃)
  exact_mod_proofs key

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
