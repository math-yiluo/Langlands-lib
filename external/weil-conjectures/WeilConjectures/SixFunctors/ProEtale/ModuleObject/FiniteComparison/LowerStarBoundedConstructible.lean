/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleDictionary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar

/-!
# Finiteness of `Rf_*` for finite condensed coefficients

Let `T` be a finite discrete commutative ring killed by an integer `N` invertible in a field `k`,
and `f : X ⟶ Y` a separated morphism of finite type to a `k`-scheme of finite type. This file
proves that the derived pushforward `Rf_*` on module objects over the condensed coefficient ring
`Λ_X = p_X^* T̲` preserves bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_finite`), directly from
Deligne's finiteness theorem on the étale site, through the comparison of the condensed and the
étale readings of the finite coefficient categories:

* a bounded constructible condensed complex `K` is of étale origin under the identification
  `Φ = finiteCoefficientDerivedEquivalence` with complexes of sheaves of `T`-modules
  (`ProEtale.isEtaleOrigin_of_isConstructible`);
* `Φ` commutes with `Rf_*` (`ProEtale.finiteCoefficientDerivedLowerStarIso`), and the pro-étale
  `Rf_*` preserves the bounded constructible complexes of étale origin
  (`ProEtale.boundedConstructible_rightDerivedLowerStar`, from the étale finiteness theorem);
* conversely, the condensed reading `Φ⁻¹ (ν^* N)` of a bounded constructible étale complex `N` is
  bounded constructible (`ProEtale.CondensedRing.boundedConstructible_inverse_obj_of_etale`, in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading`).

This is the torsion step of blueprint `proposition-six-operations-dctf--5`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Deligne's finiteness theorem for `Rf_*` with finite condensed coefficients**: for a finite
discrete commutative ring `T` killed by an integer `N` invertible in the field `k`, a `k`-scheme
`Y` of finite type and a separated morphism `f : X ⟶ Y` of finite type, the derived pushforward
on module objects over `p_X^* T̲` preserves bounded constructible complexes. This is the torsion
step of blueprint `proposition-six-operations-dctf--5`, read on the étale site through the
comparison of the condensed and étale finite coefficient categories. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_finite {k : Type u} [Field k] (N : ℕ)
    (hN : (N : k) ≠ 0) (hT : (N : T) = 0) {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [QuasiCompact s] (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) Y)
      ((R((f)_*⟦Profinite.continuousMapRingObj T⟧)).obj K) := by
  have hN0 : ((N : ULift.{u + 1} T)) = 0 := ULift.ext (by simpa using hT)
  have hA (M : ModuleCat.{u + 1} (ULift.{u + 1} T)) : N • 𝟙 M = 0 := by
    ext x
    rw [ModuleCat.hom_nsmul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply,
      ← Nat.cast_smul_eq_nsmul (ULift.{u + 1} T), hN0, zero_smul, ModuleCat.hom_zero,
      LinearMap.zero_apply]
  obtain ⟨L, hL, ⟨e⟩⟩ := boundedConstructible_rightDerivedLowerStar (ULift.{u + 1} T) N hN hA s f
    (isEtaleOrigin_of_isConstructible T hK)
  exact (boundedConstructible _).prop_of_iso
    ((finiteCoefficientDerivedEquivalence Y T).inverse.mapIso
      (e ≪≫ ((finiteCoefficientDerivedLowerStarIso T f).app K)) ≪≫
      ((finiteCoefficientDerivedEquivalence Y T).unitIso.app _).symm)
    (boundedConstructible_inverse_obj_of_etale T hL)

end AlgebraicGeometry.ProEtale.CondensedRing
