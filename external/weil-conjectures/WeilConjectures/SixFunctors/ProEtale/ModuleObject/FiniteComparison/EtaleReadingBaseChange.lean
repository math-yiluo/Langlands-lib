/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.CategoryTheory.Adjunction.MateOfNatIsoLeft
public import WeilConjectures.CategoryTheory.Adjunction.MatePasting
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.MatesUnit
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonBaseChangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperStarCoherence

/-!
# The étale reading of `𝒪_E ⧸ ℓⁿ`-coefficients and proper base change

Write `ρ_X : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)`, `M ↦ Rν_* Φ(M)`, for the étale reading
(`ProEtale.CondensedRing.finiteEtaleReading`). This file shows that the comparison of `ρ` with
the pushforwards (`ProEtale.CondensedRing.finiteEtaleReadingLowerStarIso`, defined through
K-injective resolutions) is the mate of its comparison with the pullbacks
(`ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso`), under the adjunctions `Lp^* ⊣ Rp_*`
on bounded constructible condensed complexes and on étale complexes
(`ProEtale.CondensedRing.mateEquiv_finiteEtaleReadingUpperStarIso_inv`). The three layers of
`ρ = Rν_* ∘ Φ ∘ ι` are treated separately:

* the inclusion `ι` of bounded constructible complexes: the adjunction on bounded constructible
  complexes is a restriction (`CategoryTheory.mateEquiv_restrictFullyFaithful`);
* the finite-coefficient comparison `Φ`
  (`ProEtale.mateEquiv_leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso_inv`): the
  derived comparisons of exact functors are mates when the underived ones are
  (`CategoryTheory.Adjunction.mateEquiv_derivedAdjunction_restrict`);
* the comparison `Rν_*` (`ProEtale.mateEquiv_rightDerivedComparisonBaseChange`).

Combined with the cube law of mates (`CategoryTheory.mateEquiv_app_cube`) and the compatibility
of the pullback comparisons with pullback squares
(`ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso_cube`), the étale reading carries the
base change map `Ex_*` of bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes to the étale
base change map `Etale.derivedBaseChangeMap`
(`ProEtale.CondensedRing.finiteEtaleReading_map_baseChange`). This is the `ρ`-part of the
compatibility of reduction modulo `ℓⁿ` with proper base change (blueprint
`proposition-compatibility-purity-base-change`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section FiniteCoefficient

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The commutation of the finite-coefficient comparison `Φ` with the pushforwards is compatible
with the units of the adjunctions `f^* ⊣ f_*`: it is the mate of the inverse of the commutation
with the pullbacks. -/
lemma unit_app_comp_lowerStarFiniteCoefficientModEquivalenceIso_hom_app
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)) :
    (finiteCoefficientModEquivalence Y T).functor.map
        ((CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f).unit.app
          N) ≫
      (lowerStarFiniteCoefficientModEquivalenceIso f T).hom.app
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj T) f).obj N) =
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).unit.app
        ((finiteCoefficientModEquivalence Y T).functor.obj N) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).map
        ((upperStarFiniteCoefficientModEquivalenceIso f T).symm.hom.app N) := by
  refine (unit_app_comp_map_conjugateIsoEquiv_symm_inv_app
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
    (finiteCoefficientModEquivalence Y T) (finiteCoefficientModEquivalence X T)
    (lowerStarFiniteCoefficientModEquivalenceIso f T) _ (fun b ↦ ?_) N).symm
  simp

/-- **The commutation of `Φ` with the derived pushforwards is the mate of its commutation with
the derived pullbacks**: under the derived adjunctions `Lf^* ⊣ Rf_*` on module objects over
`T̲` and on pro-étale sheaves of `T`-modules, the mate of the inverse of
`leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso` is the inverse of
`finiteCoefficientDerivedLowerStarIso`. -/
theorem mateEquiv_leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso_inv :
    (mateEquiv
        (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f)
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
        (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T).inv) =
      (finiteCoefficientDerivedLowerStarIso T f).inv := by
  have h := Adjunction.mateEquiv_derivedAdjunction_restrict
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f)
    (upperStarFiniteCoefficientModEquivalenceIso f T).symm
    (lowerStarFiniteCoefficientModEquivalenceIso f T)
    (unit_app_comp_lowerStarFiniteCoefficientModEquivalenceIso_hom_app T f)
    (fun _ _ ↦ inferInstance)
  have hX : (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T).inv =
      (Functor.isoWhiskerLeft (finiteCoefficientModEquivalence Y T).functor.mapDerivedCategory
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T))
            f).leftDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategorySquareIso
          (upperStarFiniteCoefficientModEquivalenceIso f T).symm ≪≫
        Functor.isoWhiskerRight (CondensedRing.upperStar (Profinite.continuousMapRingObj T)
          f).leftDerivedFunctorIsoMapDerivedCategory.symm
          (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory).hom := by
    ext N
    simp [leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso,
      Functor.mapDerivedCategoryNatIso_symm,
      CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
      ProEtale.leftDerivedUpperStarIsoMapDerivedCategory]
    rfl
  rw [hX]
  exact h

end FiniteCoefficient

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Mate

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The pushforward comparison of the étale reading is the mate of its pullback comparison**:
under the adjunctions `Lp^* ⊣ Rp_*` on bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes and
on étale complexes, the mate of the inverse of `finiteEtaleReadingUpperStarIso` (a 2-cell
`ρ_Y ⋙ Lp^*_{ét} ⟶ Lp^* ⋙ ρ_X`) is `finiteEtaleReadingLowerStarIso`. -/
theorem mateEquiv_finiteEtaleReadingUpperStarIso_inv (p : X ⟶ Y) :
    (mateEquiv (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n p)
        (Etale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left)
        (finiteEtaleReadingUpperStarIso ℓ E n p).inv) =
      (finiteEtaleReadingLowerStarIso ℓ E n p).hom := by
  have h₁ : (mateEquiv (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction
      ℓ E n p) (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n) p.left)
      (boundedConstructibleUpperStarCompatibility (Profinite.integersModPowRingObj ℓ E n) ℓ
        p).inv) =
      (IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility ℓ E n p).hom :=
    (mateEquiv_restrictFullyFaithful
      (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n) p.left)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility (Profinite.integersModPowRingObj ℓ E n) ℓ
        p).symm
      (IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility ℓ E n p).symm)
  ext K
  refine (app_eq_comp_of_eq_mateEquiv_pasting
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n p)
    (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n) p.left)
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left)
    (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left)
    (boundedConstructibleUpperStarCompatibility (Profinite.integersModPowRingObj ℓ E n) ℓ p).inv
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso p.left
      (PadicAlgCl.integersModPow ℓ E n)).inv
    (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
      p.left) (finiteEtaleReadingUpperStarIso ℓ E n p).inv ?_ _ rfl _ h₁.symm _
    (mateEquiv_leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso_inv
      (PadicAlgCl.integersModPow ℓ E n) p.left).symm _
    (mateEquiv_rightDerivedComparisonBaseChange
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left).symm K).trans ?_
  · ext M
    simp [finiteEtaleReadingUpperStarIso_inv_app]
  · simp [finiteEtaleReadingLowerStarIso, finiteEtaleReading]

end Mate

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The étale reading carries the base change map to the étale base change map.** For a
commutative square `g' ≫ f = f' ≫ g` (no hypothesis on `f`; proper base change concerns
cartesian squares with `f` proper), the base change map
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` of bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes (the mate
of the pullback square comparison `boundedConstructiblePullbackSquareComparison`) at `K` is
carried by the étale reading `ρ` to the étale base change map `Etale.derivedBaseChangeMap` at
`ρ_X K`, through the pullback comparisons `finiteEtaleReadingUpperStarIso` for `g`, `g'` and the
pushforward comparisons `finiteEtaleReadingLowerStarIso` for `f`, `f'`. -/
theorem finiteEtaleReading_map_baseChange (sq : CommSq g' f' f g)
    (K : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (finiteEtaleReadingUpperStarIso ℓ E n g).inv.app
        ((IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n f).obj K) ≫
      (finiteEtaleReading ℓ E n Y').map
        ((mateEquiv (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
          (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
          (boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ
            sq).hom).app K) ≫
      (finiteEtaleReadingLowerStarIso ℓ E n f').hom.app
        ((boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ g').obj K) =
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g.left).map
        ((finiteEtaleReadingLowerStarIso ℓ E n f).hom.app K) ≫
      (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).app
          ((finiteEtaleReading ℓ E n X).obj K) ≫
      R(Etale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f'.left).map
        ((finiteEtaleReadingUpperStarIso ℓ E n g').inv.app K) := by
  have h := mateEquiv_app_cube
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
    (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f'.left)
    (boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ
      sq).hom
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
      (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).hom
    (finiteEtaleReadingUpperStarIso ℓ E n f).inv (finiteEtaleReadingUpperStarIso ℓ E n f').inv
    (finiteEtaleReadingUpperStarIso ℓ E n g).inv (finiteEtaleReadingUpperStarIso ℓ E n g').inv
    (finiteEtaleReadingUpperStarIso_cube ℓ E n sq) K
  have hf := NatTrans.congr_app (mateEquiv_finiteEtaleReadingUpperStarIso_inv ℓ E n f) K
  have hf' := NatTrans.congr_app (mateEquiv_finiteEtaleReadingUpperStarIso_inv ℓ E n f')
    ((boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ g').obj K)
  erw [hf, hf'] at h
  exact h

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
