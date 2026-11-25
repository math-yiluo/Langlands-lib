/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsDetection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin

/-!
# Deligne's finiteness criterion at closed points, pro-étale form

Let `k` be a separably closed field, `p : X ⟶ Spec k` proper, `T` a finite discrete ring whose
exponent is invertible in `k`, and `hᵢ : Wᵢ ⟶ X` finitely many morphisms from Noetherian schemes
whose images contain the non-closed points of `X`. A complex `C` of modules over the condensed
coefficient ring `T̲` on `X_proét` which is bounded below of étale origin is bounded constructible
as soon as its pullbacks `Lhᵢ^* C` and its direct image `Rp_* C` are
(`boundedConstructible_of_leftDerivedUpperStar_of_rightDerivedLowerStar_of_isProper`).

Writing `Φ C ≅ ν^* G` for a bounded below étale complex `G`, this is the étale criterion
`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper`:
`ν^*` is fully faithful on `D⁺`
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`)
and commutes with `Lhᵢ^*`, and `Rp_* G ≅ Rν_* Rp_* ν^* G`, so the bounded constructibility of the
pro-étale complexes `Lhᵢ^* C` and `Rp_* C`, which are of étale origin
(`AlgebraicGeometry.ProEtale.isEtaleOrigin_of_isConstructible`), is that of `Lhᵢ^* G` and
`Rp_* G`; conversely `C ≅ Φ⁻¹ ν^* G` is bounded constructible if `G` is
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_inverse_obj_of_etale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Deligne's finiteness criterion at closed points** (SGA 4½, [Th. finitude], proof of 3.2;
finite condensed coefficients). Over a separably closed field `k`, let `p : X ⟶ Spec k` be proper
and `hᵢ : Wᵢ ⟶ X` finitely many morphisms from Noetherian schemes whose images contain the
non-closed points of `X`. A complex `C` of `T̲`-modules on `X_proét`, bounded below of étale
origin, is bounded constructible as soon as the pullbacks `Lhᵢ^* C` and the direct image
`Rp_* C` are. -/
theorem boundedConstructible_of_leftDerivedUpperStar_of_rightDerivedLowerStar_of_isProper
    {k : Type u} [Field k] [IsSepClosed k]
    [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k))] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C))
    (hW : ∀ i, boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) (W i))
      ((L(CondensedRing.upperStar (Profinite.continuousMapRingObj T) (h i))).obj C))
    (hΓ : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (Spec (.of k))) ((R((p)_*⟦Profinite.continuousMapRingObj T⟧)).obj C)) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) C := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} T)
  obtain ⟨G, ⟨m, hm⟩, ⟨e⟩⟩ := hC
  have : G.IsGE m := hm
  -- a bounded below étale complex whose comparison is the reading of a bounded constructible
  -- condensed complex is bounded constructible
  have key {Y : Scheme.{u}} (E : DerivedCategory (Sheaf Y.smallEtaleTopology A))
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) Y)))
      (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) Y) K)
      (e' : E ≅ (R(ν_*(Y)[A])).obj ((finiteCoefficientDerivedEquivalence Y T).functor.obj K)) :
      Etale.DerivedCategory.boundedConstructible A Y E := by
    obtain ⟨E', hE', ⟨e''⟩⟩ := isEtaleOrigin_of_isConstructible T hK
    have := isIso_derivedComparisonAdjunction_unit_app A Y E' hE'.1.1
    exact (Etale.DerivedCategory.boundedConstructible A Y).prop_of_iso
      (asIso ((derivedComparisonAdjunction A Y).unit.app E') ≪≫
        (R(ν_*(Y)[A])).mapIso e'' ≪≫ e'.symm) hE'
  have hunit := isIso_derivedComparisonAdjunction_unit_app A X G ⟨m, hm⟩
  have hG : Etale.DerivedCategory.boundedConstructible A X G := by
    refine Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper p h hcov
      G m (fun i ↦ ?_) ?_
    · have : ((L(Etale.upperStar A (h i))).obj G).IsGE m :=
        Etale.isGE_leftDerivedUpperStar_obj A (h i) G m
      have := isIso_derivedComparisonAdjunction_unit_app A (W i)
        ((L(Etale.upperStar A (h i))).obj G) ⟨m, inferInstance⟩
      exact key _ _ (hW i)
        (asIso ((derivedComparisonAdjunction A (W i)).unit.app _) ≪≫
          (R(ν_*(W i)[A])).mapIso (((derivedComparisonUpperStarUpperStarIso A (h i)).app G).symm ≪≫
            (L(ProEtale.upperStar A (h i))).mapIso e ≪≫
              ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso (h i) T).app C).symm))
    · exact key _ _ hΓ
        ((R(Etale.lowerStar A p)).mapIso (asIso ((derivedComparisonAdjunction A X).unit.app G)) ≪≫
          ((rightDerivedLowerStarCompComparisonLowerStarIso A p).app _).symm ≪≫
            (R(ν_*(Spec (.of k))[A])).mapIso ((R(ProEtale.lowerStar A p)).mapIso e ≪≫
              (finiteCoefficientDerivedLowerStarIso T p).app C))
  exact (boundedConstructible _).prop_of_iso
    (((finiteCoefficientDerivedEquivalence X T).inverse.mapIso e) ≪≫
      ((finiteCoefficientDerivedEquivalence X T).unitIso.app C).symm)
    (boundedConstructible_inverse_obj_of_etale T hG)

end AlgebraicGeometry.ProEtale.CondensedRing
