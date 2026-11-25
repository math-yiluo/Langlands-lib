/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleRetract
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Bounded constructible complexes with finite condensed coefficients

Let `T` be a finite discrete commutative ring and `Φ = ProEtale.finiteCoefficientDerivedEquivalence`
the identification of complexes of module objects over the condensed ring `T̲` with complexes of
pro-étale sheaves of `T`-modules. A complex `K` of `T̲`-modules is bounded constructible if and
only if `Φ K` is of étale origin, `D(ν^*)` of a bounded constructible étale complex
(`ProEtale.CondensedRing.boundedConstructible_iff_of_finite`). Consequently the bounded
constructible complexes of `T̲`-modules form a triangulated subcategory
(`ProEtale.CondensedRing.isTriangulated_boundedConstructible_of_finite`) which is stable under
retracts (`ProEtale.CondensedRing.boundedConstructible_of_retract_of_finite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X : Scheme.{u}}

/-- A complex of `T̲`-modules (`T` finite) is bounded constructible if and only if its reading
`Φ K` as a complex of pro-étale sheaves of `T`-modules is of étale origin. -/
lemma boundedConstructible_iff_of_finite
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
        ((finiteCoefficientDerivedEquivalence X T).functor.obj K) := by
  refine ⟨isEtaleOrigin_of_isConstructible T, fun ⟨E, hE, ⟨e⟩⟩ ↦ ?_⟩
  exact (boundedConstructible _).prop_of_iso
    ((finiteCoefficientDerivedEquivalence X T).inverse.mapIso e ≪≫
      ((finiteCoefficientDerivedEquivalence X T).unitIso.app K).symm)
    (boundedConstructible_inverse_obj_of_etale T hE)

/-- The bounded constructible complexes of `T̲`-modules (`T` finite) form a triangulated
subcategory: they are the inverse image under the triangulated equivalence `Φ` of the
complexes of étale origin. -/
instance isTriangulated_boundedConstructible_of_finite :
    (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X)).IsTriangulated
    := by
  have h : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) =
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).inverseImage
        D((finiteCoefficientModEquivalence X T).functor) := by
    ext K
    exact boundedConstructible_iff_of_finite T K
  rw [h]
  have : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T))
      X).IsTriangulated :=
    ProEtale.DerivedCategory.isTriangulated_boundedConstructible (Λ := ULift.{u + 1} T) X
  infer_instance

/-- The bounded constructible complexes of `T̲`-modules (`T` finite) are stable under retracts. -/
lemma boundedConstructible_of_retract_of_finite
    {K K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))} (r : Retract K K')
    (hK' : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K') :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K :=
  (boundedConstructible_iff_of_finite T K).2
    (DerivedCategory.boundedConstructible_of_retract
      (r.map (finiteCoefficientDerivedEquivalence X T).functor)
      ((boundedConstructible_iff_of_finite T K').1 hK'))

end AlgebraicGeometry.ProEtale.CondensedRing
