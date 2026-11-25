/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.BoundedConstructibleFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperNoetherian

/-!
# Finiteness of proper direct images over a Noetherian base, finite condensed coefficients

Let `k` be a field, `T` a finite discrete ring whose exponent is invertible in `k`, `S` a
Noetherian `k`-scheme and `q : X ⟶ S` proper. The derived pushforward `Rq_*` on module objects
over the condensed ring `T̲` preserves bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isProper_of_finite`):
a bounded constructible `K` is of étale origin, `Φ K ≅ ν^* K'`
(`ProEtale.isEtaleOrigin_of_isConstructible`), `Rq_* ν^* K' ≅ ν^* Rq_* K'`
(`ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`), and `Rq_* K'` is bounded
constructible by the finiteness theorem for proper morphisms (SGA 4, XIV, 1.1;
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`).

This is used over the strictly henselian trait `Spec k'⟦t⟧`, a Noetherian `k'`-scheme which is
not of finite type over `k'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Finiteness of proper direct images over a Noetherian base** (SGA 4, XIV, 1.1), for finite
condensed coefficients: over a Noetherian scheme `S` over a field `k` in which the exponent of
`T` is invertible, the derived pushforward along a proper morphism preserves bounded
constructible complexes of `T̲`-modules. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isProper_of_finite {k : Type u}
    [Field k] [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k))] {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [IsNoetherian S] (q : X ⟶ S) [IsProper q]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) S)
      ((R((q)_*⟦Profinite.continuousMapRingObj T⟧)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := isEtaleOrigin_of_isConstructible T hK
  exact (boundedConstructible_iff_of_finite T _).2
    ⟨_, Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian aS q hK',
      ⟨(rightDerivedLowerStarMapDerivedCategoryObjIso _ q K' hK'.1.1).symm ≪≫
        (R(ProEtale.lowerStar _ q)).mapIso e ≪≫ (finiteCoefficientDerivedLowerStarIso T q).app K⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
