/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantSmoothExchange
public import WeilConjectures.TraceFormula.Specialization.ThickOriginReducedUnit

/-!

# The specialization unit of the constant family of a smooth scheme

Let `Y` be a smooth separated `k`-scheme of finite type and `Y × S` its constant family over the
trait `S = Spec k'⟦t⟧`, the deformation of the zero ideal of `Y`
(`ProEtale.CondensedRing.deformationModel Y ⊥ k'`). The structure morphism `Y ⟶ Spec k` induces a
morphism of deformation models `Y × S ⟶ S × Spec k = 𝒟_⊥ (Spec k)` whose morphism of total spaces
is smooth, being a base change of `Y ⟶ Spec k`. By the smooth exchange of nearby cycles its
pullback exchange is invertible at the unit, and the specialization unit of the constant family of
the point is invertible; so the specialization unit `σ_Y : Λ ⟶ Ψ_{Y × S}(Λ)` is an isomorphism.
This is the case `L = Λ` of blueprint `lemma-nearby-cycles-constant-family` for smooth `Y`.

## Main results

- `ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_smooth`: for `ℚ̄_ℓ`-coefficients.
- `ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_smooth_finiteCoefficient`: for
  coefficients in a finite ring `T` killed by a prime `ℓ ≠ char k'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (k' : Type u) [Field k'] [Algebra k k']

/-- The morphism from the constant family `Y × S` to the constant family of the point, induced by
the structure morphism `Y ⟶ Spec k`. -/
noncomputable abbrev constantFamilyToPointModelHom :=
  deformationModelHom (Over.homMk Y.hom : Y ⟶ point k) (siteIdeal_bot_map_appLE_le _ ⊥) k'

/-- For `Y` smooth over `k`, the morphism of total spaces from the constant family `Y × S` to the
constant family of the point is smooth: it is the base change of `Y ⟶ Spec k`. -/
instance smooth_constantFamilyToPointModelHom_total [Smooth Y.hom] :
    Smooth (constantFamilyToPointModelHom Y k').total :=
  have : Smooth (Over.homMk Y.hom : Y ⟶ point k).left := inferInstanceAs (Smooth Y.hom)
  smooth_deformationTotalMap k' _ _ (IdealSheafData.comap_bot _).symm

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- **The constant family of a smooth scheme** (blueprint `lemma-nearby-cycles-constant-family`,
for `L = ℚ̄_ℓ` and `Y` smooth): for a smooth separated `k`-scheme `Y` of finite type, the
specialization unit `σ_Y : ℚ̄_ℓ ⟶ Ψ_{Y × S}(ℚ̄_ℓ)` of the constant family `Y × S` is an
isomorphism. The pullback exchange of `Y × S ⟶ 𝒟_⊥ (Spec k)` is invertible at the unit by the
smooth exchange, and the specialization unit of the constant family of the point is an
isomorphism. -/
theorem isIso_deformationModel_bot_unit_of_smooth [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] [Smooth Y.hom] :
    IsIso ((deformationModel Y ⊥ k').unit (Profinite.padicAlgClRingObj ℓ)) := by
  have hφ := isIso_pullbackExchange_deformationModel_app_of_smooth k'
    (constantFamilyToPointModelHom Y k') (isPullback_deformationGenericMap _ _ k')
    (K := 𝟙_ _) (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)).property
  have : IsIso (point k).hom := inferInstanceAs (IsIso (𝟙 _))
  have := isIso_deformationModel_bot_unit_of_isIso (Profinite.padicAlgClRingObj ℓ) (point k) k'
  have h := (constantFamilyToPointModelHom Y k').map_unit_comp_pullbackExchange_app
    (Profinite.padicAlgClRingObj ℓ)
  revert hφ h this
  normalize_precoherent
  intro hφ hN h
  have := hφ
  exact isIso_of_comp_eq_comp_comp h

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The constant family of a smooth scheme, with finite coefficients** (blueprint
`lemma-nearby-cycles-constant-family`, for `L = T̲` and `Y` smooth, with `T` a finite ring killed
by a prime `ℓ ≠ char k'`): for a smooth separated `k`-scheme `Y` of finite type, the
specialization unit `σ_Y : T̲ ⟶ Ψ_{Y × S}(T̲)` of the constant family `Y × S` is an isomorphism. -/
theorem isIso_deformationModel_bot_unit_of_smooth_finiteCoefficient [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] [Smooth Y.hom] (hT : (ℓ : T) = 0) :
    IsIso ((deformationModel Y ⊥ k').unit (Profinite.continuousMapRingObj.{u} T)) := by
  have hφ := isIso_pullbackExchange_deformationModel_app_of_smooth_finiteCoefficient k' T
    (constantFamilyToPointModelHom Y k') (isPullback_deformationGenericMap _ _ k') hT
    (K := 𝟙_ _) (boundedConstructible_leftDerivedUpperStar_obj_unit _ _)
  have : IsIso (point k).hom := inferInstanceAs (IsIso (𝟙 _))
  have := isIso_deformationModel_bot_unit_of_isIso (Profinite.continuousMapRingObj.{u} T)
    (point k) k'
  have h := (constantFamilyToPointModelHom Y k').map_unit_comp_pullbackExchange_app
    (Profinite.continuousMapRingObj.{u} T)
  revert hφ h this
  normalize_precoherent
  intro hφ hN h
  have := hφ
  exact isIso_of_comp_eq_comp_comp h

end AlgebraicGeometry.ProEtale.CondensedRing
