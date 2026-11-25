/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.TraceFormula.Specialization.DefectExchangeSquares
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeLocal
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent
public import WeilConjectures.TraceFormula.Specialization.OpenExchange
import WeilConjectures.Tactic.ExactModProofs

/-!

# The smooth exchange of nearby cycles with finite coefficients

Let `T` be a finite discrete commutative ring in which a prime `ℓ` vanishes, for instance the
residue field `𝔽_E` of a finite extension `E` of `ℚ_ℓ`, and let `k'` be a separably closed field
of characteristic different from `ℓ`. For a morphism `φ : 𝒟_J X ⟶ 𝒟_I Y` of deformation models
over `Spec k'⟦t⟧` whose morphism of total spaces is smooth and whose square of geometric generic
fibres is cartesian, the pullback exchange `α_φ : Lg_s^* Ψ_Y ⟶ Ψ_X Lg^*` with coefficients `T̲` is
invertible at every complex `K` on `Y` such that `Lε^* K` is bounded constructible, for instance
the unit
(`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient`).
This is the finite-coefficient analogue of
`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth`: smooth base change
along the projections `𝔸ⁿ ⟶ 𝒴` for the inclusion `j` of the geometric generic fibre holds for
complexes of `T̲`-modules (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth_of_finite`),
`ℓ` being invertible on the total space of the deformation.

Consequently, the vanishing of the defect of the unit is stable under smooth pullback
(`ProEtale.CondensedRing.isZero_specializationDefect_unit_of_smooth_finiteCoefficient`), the
smooth exchange step of blueprint `lemma-vanishing-generic-points-principal-divisor` with finite
coefficients.

## Main results

- `ProEtale.CondensedRing.isUnit_natCast_deformationTotal`: `ℓ` is invertible on the total space
  of a deformation model over `Spec k'⟦t⟧` when `ℓ ≠ char k'`.
- `ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient`:
  the smooth exchange of nearby cycles with finite coefficients.
- `ProEtale.CondensedRing.isZero_specializationDefect_unit_of_smooth_finiteCoefficient`: smooth
  pullback of the vanishing of the defect of the unit.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A prime `ℓ` different from the characteristic of a field `K` of prime characteristic is
nonzero in `K`. -/
lemma natCast_ne_zero_of_ringChar_ne {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]
    [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)] : (ℓ : K) ≠ 0 := by
  intro h
  have hdvd := (ringChar.spec K ℓ).1 h
  rcases (Nat.dvd_prime (Fact.out : ℓ.Prime)).1 hdvd with h₁ | h₁
  · exact (Fact.out : (ringChar K).Prime).ne_one h₁
  · exact (Fact.out : ringChar K ≠ ℓ) h₁

variable (k' : Type u) [Field k']

/-- A prime `ℓ` different from the characteristic of `k'` is invertible on the trait
`Spec k'⟦t⟧`. -/
lemma isUnit_natCast_trait {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] : IsUnit ((ℓ : ℕ) : Γ(trait k', ⊤)) := by
  have h : IsUnit ((ℓ : ℕ) : PowerSeries k') := by
    rw [← map_natCast (algebraMap k' (PowerSeries k'))]
    exact (Ne.isUnit natCast_ne_zero_of_ringChar_ne).map _
  rw [← map_natCast (ΓSpecIso (CommRingCat.of (PowerSeries k'))).inv.hom]
  exact h.map _

variable {k : Type u} [Field k] [Algebra k k']

/-- A prime `ℓ` different from the characteristic of `k'` is invertible on the total space of the
deformation model `𝒟_I Y` over the trait `Spec k'⟦t⟧`. -/
lemma isUnit_natCast_deformationTotal {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] (Y : Over (Spec (.of k))) (I : Y.left.IdealSheafData) :
    IsUnit ((ℓ : ℕ) : Γ((deformationModel Y I k').total, ⊤)) := by
  rw [← map_natCast (deformationTotalToTrait Y I k').appTop.hom]
  exact (isUnit_natCast_trait k').map _

/-- The inclusion of the geometric generic fibre of a deformation model is quasi-compact and
quasi-separated. -/
lemma quasiCompact_deformationModel_j (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (I : Y.left.IdealSheafData) :
    QuasiCompact (deformationModel Y I k').j ∧ QuasiSeparated (deformationModel Y I k').j := by
  have := noetherianSpace_left_of_over Y
  rw [deformationModel_j, deformationGenericToTotal]
  exact ⟨inferInstance, inferInstance⟩

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Smooth base change along affine spaces for the geometric generic fibre, with finite
coefficients**: for the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation
model `𝒴 = 𝒟_I Y` and the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`, the base change morphism
`Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with coefficients in a finite ring `T` killed by `ℓ ≠ char k'` is
invertible at every bounded constructible complex: `ℓ` is invertible on `𝒴`
(`isUnit_natCast_deformationTotal`), and `j` is quasi-compact and quasi-separated. -/
theorem isIso_baseChangeMap_affineSpace_deformationModel_app_finiteCoefficient
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ) (hT : (ℓ : T) = 0)
    {E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (deformationModel Y I k').generic)
      Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) (deformationModel Y I k').generic))}
    (hE : boundedConstructible _ E) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj.{u} T)
      (IsPullback.of_hasPullback (deformationModel Y I k').j
        (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
          (deformationModel Y I k').total)).toCommSq).app E) := by
  have := noetherianSpace_left_of_over Y
  have : QuasiCompact (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : QuasiSeparated (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : Smooth (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
      (deformationModel Y I k').total) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _
  exact isIso_baseChangeMap_app_of_smooth_of_finite T _ (IsPullback.of_hasPullback _ _)
    (Fact.out : ℓ.Prime).ne_zero
    (isUnit_natCast_deformationTotal k' Y I) hT E hE

/-- **The smooth exchange of nearby cycles with finite coefficients** (blueprint
`prose-E-03` (1), smooth case, for a finite coefficient ring `T` killed by a
prime `ℓ ≠ char k'`): for a morphism `φ : 𝒟_J X ⟶ 𝒟_I Y` of deformation models whose morphism of
total spaces is smooth and whose square of geometric generic fibres is cartesian, the pullback
exchange `α_φ : Lg_s^* Ψ_Y ⟶ Ψ_X Lg^*` is invertible at every `K` such that `Lε^* K` is bounded
constructible (e.g. the unit), by smooth base change along the inclusion `j` of the geometric
generic fibre. -/
theorem isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData} {g : X.left ⟶ Y.left}
    {g' : (deformationSpecialFibre X J k').left ⟶ (deformationSpecialFibre Y I k').left}
    (φ : (deformationModel X J k').Hom (deformationModel Y I k') g g') [Smooth φ.total]
    (hj : IsPullback φ.generic (deformationModel X J k').j (deformationModel Y I k').j φ.total)
    (hT : (ℓ : T) = 0)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) Y.left))}
    (hK : boundedConstructible _
      ((L(((deformationModel Y I k').ε)^*⟦Profinite.continuousMapRingObj.{u} T⟧)).obj K)) :
    IsIso ((φ.pullbackExchange (Profinite.continuousMapRingObj.{u} T)).app K) := by
  have : CompactSpace (deformationModel X J k').total :=
    QuasiCompact.compactSpace_of_compactSpace (deformationTotalToTrait X J k')
  have : QuasiSeparatedSpace (deformationModel X J k').total :=
    quasiSeparatedSpace_of_quasiSeparated (deformationTotalToTrait X J k')
  have h₂ := isIso_baseChangeMap_app_of_smooth (Profinite.continuousMapRingObj.{u} T) hj _
    fun n ↦ isIso_baseChangeMap_affineSpace_deformationModel_app_finiteCoefficient k' T I n hT hK
  rw [Subsingleton.elim hj.toCommSq φ.commSq_j] at h₂
  have key := φ.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app
    (Profinite.continuousMapRingObj.{u} T) K (by exact_mod_proofs h₂)
  exact_mod_proofs key

/-- The unit of the derived category of module objects on any scheme is bounded constructible,
and so is its derived pullback along any morphism. -/
lemma boundedConstructible_leftDerivedUpperStar_obj_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A B : Scheme.{u}} (f : A ⟶ B) :
    boundedConstructible _ ((L((f)^*⟦Λ⟧)).obj
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
        (condensedRingObj Λ B))))) :=
  (boundedConstructible _).prop_of_iso (leftDerivedUpperStarUnitIso Λ f).symm
    (boundedConstructible_tensorUnit Λ A)

/-- The derived pullback of the derived pullback of the unit is bounded constructible. -/
lemma boundedConstructible_leftDerivedUpperStar_obj_leftDerivedUpperStar_obj_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    boundedConstructible _ ((L((f)^*⟦Λ⟧)).obj ((L((g)^*⟦Λ⟧)).obj
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
        (condensedRingObj Λ C)))))) :=
  (boundedConstructible _).prop_of_iso
    ((L((f)^*⟦Λ⟧)).mapIso (leftDerivedUpperStarUnitIso Λ g)).symm
    (boundedConstructible_leftDerivedUpperStar_obj_unit Λ f)

/-- **Smooth pullback of the vanishing of the defect of the unit, with finite coefficients** (the
smooth exchange step of blueprint `lemma-vanishing-generic-points-principal-divisor`): let
`f : X ⟶ X₀` be smooth, `Z₀ = V(I₀) ⊆ X₀` and `Z = f⁻¹ Z₀`. If `C_{X₀,Z₀}(T̲) = 0`, then
`C_{X,Z}(T̲) = 0`, for a finite coefficient ring `T` killed by `ℓ ≠ char k'`. The smooth exchanges
of the deformations of `f` and of `f_Z` are invertible at the unit
(`isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient`), so that
`C_{X,Z}(Lf^* T̲) ≅ Lf_Z^* C_{X₀,Z₀}(T̲)`. -/
theorem isZero_specializationDefect_unit_of_smooth_finiteCoefficient [IsSepClosed k']
    {X X₀ : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (f : X ⟶ X₀) [Smooth f.left] (I₀ : X₀.left.IdealSheafData) (hT : (ℓ : T) = 0)
    (h : IsZero (specializationDefect X₀ I₀ k' (Profinite.continuousMapRingObj.{u} T) (𝟙_ _))) :
    IsZero (specializationDefect X (I₀.comap f.left) k' (Profinite.continuousMapRingObj.{u} T)
      (𝟙_ _)) := by
  have : Smooth (comapDeformationModelHom f I₀ k').total :=
    smooth_deformationTotalMap k' f (siteIdeal_map_appLE_le_comap f I₀) rfl
  have : Smooth (centreDeformationModelHom f I₀ k').total :=
    smooth_deformationTotalMap k' (centreMap f I₀) (siteIdeal_map_appLE_le_bot_centreMap f I₀)
      (IdealSheafData.comap_bot _).symm
  have hf := isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient k' T
    (comapDeformationModelHom f I₀ k') (isPullback_deformationGenericMap _ _ k') hT
    (boundedConstructible_leftDerivedUpperStar_obj_unit _ _)
  have hg := isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient k' T
    (centreDeformationModelHom f I₀ k') (isPullback_deformationGenericMap _ _ k') hT
    (boundedConstructible_leftDerivedUpperStar_obj_leftDerivedUpperStar_obj_unit _ _
      (centreι X₀ I₀).left)
  obtain ⟨e⟩ := nonempty_specializationDefect_upperStar_iso_of_isIso f I₀ k'
    (Profinite.continuousMapRingObj.{u} T) (𝟙_ _) (by exact_mod_proofs hf) (by exact_mod_proofs hg)
  obtain ⟨e'⟩ := nonempty_specializationDefect_iso X (I₀.comap f.left) k'
    (Profinite.continuousMapRingObj.{u} T) (leftDerivedUpperStarUnitIso _ f.left)
  exact (Functor.map_isZero _ h).of_iso (e'.symm ≪≫ e)

end AlgebraicGeometry.ProEtale.CondensedRing
