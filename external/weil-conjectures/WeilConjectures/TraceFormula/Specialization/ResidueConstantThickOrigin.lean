/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantSmoothExchange
public import WeilConjectures.TraceFormula.Specialization.ThickOrigin
public import WeilConjectures.TraceFormula.Specialization.ThickOriginPowUnit
import WeilConjectures.Tactic.ExactModProofs

/-!

# The thick origin with finite coefficients

Let `T` be a finite discrete commutative ring in which a prime `ℓ ≠ char k'` vanishes, for instance
the residue field `𝔽_E` of a finite extension `E` of `ℚ_ℓ`. This file proves the thick origin
(blueprint `lemma-case-z-v-x-m--1`) with coefficients `T̲`: for `m ≥ 1`, the defect
`C_{𝔸¹, V(x^m)}(T̲)` of the constant complex vanishes
(`ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient`).

The argument is that of `ThickOriginPowUnit.lean` for `ℚ̄_ℓ`, with the finite-coefficient forms of
its three inputs:
* the smooth exchange for the deformation of the reduced origin
  (`isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient`),
  which shows that its specialization unit is invertible
  (`isIso_deformationModel_polyAffineThickOrigin_one_unit_finiteCoefficient`);
* the proper exchange of nearby cycles along the power map, at the unit, which is of étale origin
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`);
* proper base change at the unit and topological invariance along a universally homeomorphic
  fibre
  (`isIso_leftDerivedUpperStar_map_unit_app_unit_of_isPullback_finiteCoefficient`).

## Main results

- `ProEtale.CondensedRing.isIso_upperStar_zeroSection_unit_polyAffineThickOrigin_finiteCoefficient`:
  the restriction `Le^* σ_𝒟` of the specialization unit of the deformation of the thick origin to
  the zero section is an isomorphism.
- `ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient`:
  the thick origin with finite coefficients.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The unit of the derived category of module objects with finite coefficients is of étale
origin, and so is its derived pullback along any morphism. -/
lemma plusEtaleOrigin_leftDerivedUpperStar_obj_unit {A B : Scheme.{u}} (f : A ⟶ B) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) A
      ((finiteCoefficientDerivedEquivalence A T).functor.obj ((L((f)^*⟦
        Profinite.continuousMapRingObj.{u} T⟧)).obj (𝟙_ _))) :=
  (isEtaleOrigin_of_isConstructible T
    (boundedConstructible_leftDerivedUpperStar_obj_unit _ f)).plusEtaleOrigin

set_option maxHeartbeats 1000000 in
-- the statements of the unit identity and of the goal carry different elaborations of proofs
/-- **The restricted unit of a pushforward along a universally homeomorphic fibre** (arbitrary
coefficients): for a commutative square of schemes `e' ≫ ν = q ≫ e` with `q` a universal
homeomorphism, if the base change morphism `Le^* Rν_* ⟶ Rq_* Le'^*` is invertible at `Lν^* Λ`, then
the restriction `Le^*(η_ν) : Le^* Λ ⟶ Le^* Rν_* Lν^* Λ` of the unit of `Lν^* ⊣ Rν_*` at the unit is
an isomorphism. By the unit identity of the base change morphism, `Le^*(η_ν)` followed by the base
change morphism is the unit `η_q`, invertible by topological invariance, followed by `Rq_*` of the
pullback comparison. -/
theorem isIso_leftDerivedUpperStar_map_unit_app_unit_of_isIso_baseChangeMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {W D Z F : Scheme.{u}} {ν : W ⟶ D} {e : Z ⟶ D} {e' : F ⟶ W} {q : F ⟶ Z}
    (sq : CommSq e' q ν e) [IsUniversalHomeomorphism q]
    (hBC : IsIso ((baseChangeMap Λ sq).app ((L((ν)^*⟦Λ⟧)).obj (𝟙_ _)))) :
    IsIso (L((e)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ ν).unit.app (𝟙_ _))) := by
  have key := Adjunction.map_unit_app_comp_exchangeRight_app
    (derivedUpperStarLowerStarAdjunction Λ ν) (derivedUpperStarLowerStarAdjunction Λ q)
    (pullbackSquareComparison Λ sq) (𝟙_ _)
  have key' : L((e)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ ν).unit.app (𝟙_ _)) ≫
      (baseChangeMap Λ sq).app ((L((ν)^*⟦Λ⟧)).obj (𝟙_ _)) =
      (derivedUpperStarLowerStarAdjunction Λ q).unit.app ((L((e)^*⟦Λ⟧)).obj (𝟙_ _)) ≫
        (R((q)_*⟦Λ⟧)).map ((pullbackSquareComparison Λ sq).hom.app (𝟙_ _)) := by
    rw [baseChangeMap]
    exact_mod_proofs key
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ q
  have : ((q)^*⟦Λ⟧).leftDerivedFunctor.IsEquivalence :=
    Functor.isEquivalence_of_iso (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  have : IsIso (derivedUpperStarLowerStarAdjunction Λ q).unit :=
    (derivedUpperStarLowerStarAdjunction Λ q).unit_isIso_of_L_fully_faithful
  have : IsIso (L((e)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ ν).unit.app (𝟙_ _)) ≫
      (baseChangeMap Λ sq).app ((L((ν)^*⟦Λ⟧)).obj (𝟙_ _))) := by
    rw [key']
    infer_instance
  exact (isIso_comp_right_iff _ _).1 this

/-- **The restricted unit of a proper pushforward, with finite coefficients**: for a cartesian
square of schemes `e' ≫ ν = q ≫ e` with `ν` proper and `q` a universal homeomorphism, the
restriction `Le^*(η_ν) : Le^* T̲ ⟶ Le^* Rν_* Lν^* T̲` of the unit of `Lν^* ⊣ Rν_*` at the unit is an
isomorphism: the base change morphism is invertible at `Lν^* T̲` by proper base change, the unit
being of étale origin. -/
theorem isIso_leftDerivedUpperStar_map_unit_app_unit_of_isPullback_finiteCoefficient
    {W D Z F : Scheme.{u}} {ν : W ⟶ D} {e : Z ⟶ D} {e' : F ⟶ W} {q : F ⟶ Z}
    (sq : IsPullback e' q ν e) [IsProper ν] [IsUniversalHomeomorphism q] :
    IsIso (L((e)^*⟦Profinite.continuousMapRingObj.{u} T⟧).map
      ((derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj.{u} T) ν).unit.app
        (𝟙_ _))) := by
  have hBC := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T sq _
    (plusEtaleOrigin_leftDerivedUpperStar_obj_unit T ν)
  have key := isIso_leftDerivedUpperStar_map_unit_app_unit_of_isIso_baseChangeMap
    (Profinite.continuousMapRingObj.{u} T) sq.toCommSq (by exact_mod_proofs hBC)
  exact_mod_proofs key

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The specialization unit of the deformation of the reduced origin, with finite
coefficients**: for the deformation to the normal cone `𝒟` of the origin `V(x) ⊆ 𝔸¹_k` over
`Spec k'⟦t⟧`, the specialization unit `σ : T̲ ⟶ Ψ(T̲)` is an isomorphism. The total space of `𝒟` is
smooth over the trait, so by the smooth exchange with finite coefficients the pullback exchange of
`𝒟 ⟶ 𝒟_⊥ (Spec k)` is invertible at the unit, and the specialization unit of the trait is an
isomorphism. -/
theorem isIso_deformationModel_polyAffineThickOrigin_one_unit_finiteCoefficient
    (hT : (ℓ : T) = 0) :
    IsIso ((deformationModel (polyAffine k 1) (polyAffineThickOrigin k 1) k').unit
      (Profinite.continuousMapRingObj.{u} T)) := by
  have hφ := isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient k' T
    (polyAffineThickOriginOneModelHom (k := k) k') (isPullback_deformationGenericMap _ _ k') hT
    (K := 𝟙_ _) (boundedConstructible_leftDerivedUpperStar_obj_unit _ _)
  have : IsIso (point k).hom := inferInstanceAs (IsIso (𝟙 _))
  have := isIso_deformationModel_bot_unit_of_isIso (Profinite.continuousMapRingObj.{u} T)
    (point k) k'
  have h := (polyAffineThickOriginOneModelHom (k := k) k').map_unit_comp_pullbackExchange_app
    (Profinite.continuousMapRingObj.{u} T)
  revert hφ h this
  normalize_precoherent
  intro hφ hN h
  have := hφ
  exact isIso_of_comp_eq_comp_comp h

/-- The specialization unit of the power model `𝒲` of the thick origin, with finite coefficients,
is an isomorphism: its restriction along the universal homeomorphism `c` is the specialization unit
of the deformation of the origin. -/
theorem isIso_thickOriginPowSourceModel_unit_finiteCoefficient (hT : (ℓ : T) = 0) {m : ℕ}
    (hm : m ≠ 0) :
    IsIso ((thickOriginPowSourceModel k k' hm).unit (Profinite.continuousMapRingObj.{u} T)) := by
  have : IsIso ((thickOriginToPowSourceModel k k' hm).total) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso ((thickOriginToPowSourceModel k k' hm).generic) := inferInstanceAs (IsIso (𝟙 _))
  exact NearbyCyclesModel.isIso_unit_of_hom _ (thickOriginToPowSourceModel k k' hm)
    (isIso_deformationModel_polyAffineThickOrigin_one_unit_finiteCoefficient T k' hT)

/-- **The specialization unit of the thick origin on the zero section, with finite
coefficients**: for the deformation `𝒟` of `V(x^m) ⊆ 𝔸¹_k` over `Spec k'⟦t⟧`, the restriction
`Le^* σ_𝒟` of the specialization unit to the zero section is an isomorphism. -/
theorem isIso_upperStar_zeroSection_unit_polyAffineThickOrigin_finiteCoefficient
    (hT : (ℓ : T) = 0) {m : ℕ} (hm : m ≠ 0) :
    IsIso (L(((zeroSectionSpecialFibreMap (polyAffine k 1) (polyAffineThickOrigin k m)
      k').left)^*⟦Profinite.continuousMapRingObj.{u} T⟧).map ((deformationModel (polyAffine k 1)
        (polyAffineThickOrigin k m) k').unit (Profinite.continuousMapRingObj.{u} T))) := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨_, _⟩ := quasiCompact_deformationModel_j k' (polyAffine k 1) (polyAffineThickOrigin k 1)
  have : QuasiCompact (thickOriginPowSourceModel k k' hm).j :=
    inferInstanceAs (QuasiCompact
      (deformationModel (polyAffine k 1) (polyAffineThickOrigin k 1) k').j)
  have : QuasiSeparated (thickOriginPowSourceModel k k' hm).j :=
    inferInstanceAs (QuasiSeparated
      (deformationModel (polyAffine k 1) (polyAffineThickOrigin k 1) k').j)
  have hχ := NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T
    (thickOriginPowModelHom k k' hm) (isPullback_powModelHom_i k' hm _ _ _ _ _ _ _)
    (isPullback_powModelHom_ε k' hm _ _ _ _ _ _ _ (IdealSheafData.deformationSpacePowMap_proj _))
    _ (plusEtaleOrigin_leftDerivedUpperStar_obj_unit T (𝟙 (polyAffine k 1).left))
  have he := isIso_leftDerivedUpperStar_map_unit_app_unit_of_isPullback_finiteCoefficient T
    (isPullback_thickOriginPowFibre_left k k' hm)
  have hM := isIso_thickOriginPowSourceModel_unit_finiteCoefficient (k := k) T k' hT hm
  have ho := NearbyCyclesModel.isIso_upperStar_unit_of_pushforwardExchange _
    (thickOriginPowModelHom k k' hm) hχ hM (thickOriginPowImagePoint k k' hm) he
  rw [thickOriginPowImagePoint_eq] at ho
  have : IsUniversalHomeomorphism (thickOriginZeroSectionPoint k k' m (Nat.pos_of_ne_zero hm) ≫
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥
        k').hom) := by
    rw [constantFamilySpecialPoint_hom]
    infer_instance
  have : IsUniversalHomeomorphism (thickOriginZeroSectionPoint k k' m (Nat.pos_of_ne_zero hm)) :=
    IsUniversalHomeomorphism.of_comp _
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥ k').hom
  exact isIso_leftDerivedUpperStar_map_of_comp _ _ _ _ ho

/-- **The thick origin with finite coefficients** (blueprint `lemma-case-z-v-x-m--1`, with
coefficients in a finite ring `T` killed by a prime `ℓ ≠ char k'`): for `m ≥ 1`, the defect
`C_{𝔸¹, V(x^m)}(T̲)` of the constant complex vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient
    (hT : (ℓ : T) = 0) {m : ℕ} (hm : 0 < m) :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T) (𝟙_ _)) := by
  have := isIso_upperStar_zeroSection_unit_polyAffineThickOrigin_finiteCoefficient (k := k) T k' hT
    hm.ne'
  exact isZero_specializationDefect_polyAffineThickOrigin_unit (k := k) _ k' hm

end AlgebraicGeometry.ProEtale.CondensedRing
