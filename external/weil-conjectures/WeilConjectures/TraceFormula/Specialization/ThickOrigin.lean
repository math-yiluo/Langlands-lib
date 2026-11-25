/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericDivisorConstantFamily
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorUnit
public import WeilConjectures.TraceFormula.Specialization.ThickOriginBaseChange
public import WeilConjectures.TraceFormula.Specialization.ThickOriginCentre

/-!

# The constant family of a thickened point

Let `Y` be a `k`-scheme whose structure morphism `Y ⟶ Spec k` is a universal homeomorphism, for
instance the thick origin `Z = V(x^m) = Spec k[x]/(x^m)` of the affine line. The total space
`Y × S` of the constant family of `Y` over the trait `S = Spec k'⟦t⟧` is then a universal
homeomorphism onto `S`, and so is its geometric generic fibre onto the geometric generic point.
By base change along universal homeomorphisms
(`ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism`)
the pullback exchange of the projection `Y × S ⟶ S` is invertible, so the specialization unit
`σ_Y` of the constant family is an isomorphism
(`ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_isUniversalHomeomorphism`; the case of
blueprint `lemma-nearby-cycles-constant-family--1` needed for blueprint `lemma-case-z-v-x-m--1`).

Consequently, for a closed subscheme `Z = V(I)` of `X` whose structure morphism is a universal
homeomorphism, the zero-section map `ε_{X,Z}(Λ)` of the constant complex is an isomorphism, and the
defect `C_{X,Z}(Λ)` vanishes, as soon as the restriction `Le^* σ_{𝒟_Z X}` of the specialization
unit of the deformation to the zero section is an isomorphism
(`ProEtale.CondensedRing.isIso_zeroSectionMap_unit_of_isUniversalHomeomorphism`,
`ProEtale.CondensedRing.isZero_specializationDefect_unit_of_isUniversalHomeomorphism`). This
applies to the thick origin `V(x^m) ⊆ 𝔸¹_k`
(`ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit`).

## Implementation notes

The remaining hypothesis, that `Le^* σ_{𝒟}` is an isomorphism, is proved for `ℚ̄_ℓ` in
`ThickOriginPowUnit.lean` (`isIso_upperStar_zeroSection_unit_polyAffineThickOrigin`). For the thick
origin the total space of `𝒟` is `Spec k'⟦t⟧[x, u]/(tu - x^m)` (Rees algebra
`k[x, t, x^m/t]`), the zero section is `u = 0` and its special fibre is topologically the
origin, so the hypothesis is the computation of the nearby cycles of `Λ` at the singular point
of `tu = x^m`, whose Milnor fibre is the disc `|x| < |t|^{1/m}`; away from the zero section
`σ_{𝒟}` is not an isomorphism when `m ≥ 2` is prime to the characteristic, so no global
argument applies.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The deformation space `D_⊥ Y ≅ 𝔸¹_Y` of the zero ideal of a `k`-scheme `Y` is a universal
homeomorphism onto `𝔸¹_k` if `Y ⟶ Spec k` is. -/
instance isUniversalHomeomorphism_deformationSpaceToAffineLine_bot (Y : Over (Spec (.of k)))
    [IsUniversalHomeomorphism Y.hom] :
    IsUniversalHomeomorphism (deformationSpaceToAffineLine Y ⊥) := by
  have : IsUniversalHomeomorphism (AffineSpace.map (ULift.{u} (Fin 1)) Y.hom) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map Y.hom).flip inferInstance
  unfold deformationSpaceToAffineLine
  infer_instance

/-- The total space `Y × S` of the constant family of a `k`-scheme `Y` is a universal
homeomorphism onto the trait `S` if `Y ⟶ Spec k` is. -/
instance isUniversalHomeomorphism_deformationTotalToTrait_bot (Y : Over (Spec (.of k)))
    [IsUniversalHomeomorphism Y.hom] : IsUniversalHomeomorphism (deformationTotalToTrait Y ⊥ k') :=
  inferInstanceAs (IsUniversalHomeomorphism (pullback.snd _ _))

/-- **The constant family of a universally homeomorphic point** (blueprint
`lemma-nearby-cycles-constant-family--1`, the case needed for blueprint `lemma-case-z-v-x-m--1`): if
the structure morphism of `Y` is a universal homeomorphism, e.g. `Y = Spec k[x]/(x^m)`, the
specialization unit `σ_Y` of the constant family `Y × S` is an isomorphism. The pullback exchange
of the projection `Y × S ⟶ S` is invertible by base change along the universal homeomorphism
`Y × S ⟶ S`, and the point case `ProEtale.CondensedRing.isIso_traitModel_unit` concludes. -/
theorem isIso_deformationModel_bot_unit_of_isUniversalHomeomorphism [IsSepClosed k']
    (Y : Over (Spec (.of k))) [IsUniversalHomeomorphism Y.hom] :
    IsIso ((deformationModel Y ⊥ k').unit Λ) := by
  have : IsUniversalHomeomorphism (constantFamilyModelHom Y k').total :=
    inferInstanceAs (IsUniversalHomeomorphism (deformationTotalToTrait Y ⊥ k'))
  have := (constantFamilyModelHom Y k').isIso_pullbackExchange_of_isUniversalHomeomorphism Λ
    (IsPullback.of_hasPullback (deformationTotalToTrait Y ⊥ k') (traitGenericPoint k')).flip
  exact isIso_deformationModel_bot_unit_of_isIso_pullbackExchange_app Λ Y k'

variable (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)

/-- **The zero-section map of the constant complex along a thickened point** (the
constant-coefficient step of blueprint `lemma-case-z-v-x-m--1`): if the structure morphism of the
centre `Z = V(I)` is a universal homeomorphism and the restriction `Le^* σ_{𝒟_Z X}` of the
specialization unit of the deformation to the zero section is an isomorphism, then the zero-section
map `ε_{X,Z}(Λ)` is an isomorphism. -/
theorem isIso_zeroSectionMap_unit_of_isUniversalHomeomorphism [IsSepClosed k']
    [IsUniversalHomeomorphism (centre X I).hom]
    [IsIso (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
      ((deformationModel X I k').unit Λ))] :
    IsIso (zeroSectionMap X I k' Λ (𝟙_ _)) := by
  have := isIso_deformationModel_bot_unit_of_isUniversalHomeomorphism Λ k' (centre X I)
  exact isIso_zeroSectionMap_unit X I k' Λ

/-- **The defect of the constant complex along a thickened point** (blueprint
`lemma-case-z-v-x-m--1`, conditional form): if the structure morphism of the centre `Z = V(I)` is a
universal homeomorphism and the restriction `Le^* σ_{𝒟_Z X}` of the specialization unit of the
deformation to the zero section is an isomorphism, then `C_{X,Z}(Λ) = 0`. -/
theorem isZero_specializationDefect_unit_of_isUniversalHomeomorphism [IsSepClosed k']
    [IsUniversalHomeomorphism (centre X I).hom]
    [IsIso (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
      ((deformationModel X I k').unit Λ))] :
    IsZero (specializationDefect X I k' Λ (𝟙_ _)) :=
  (isZero_specializationDefect_iff X I k' Λ _).2
    (isIso_zeroSectionMap_unit_of_isUniversalHomeomorphism Λ k' X I)

/-- **The thick origin** (blueprint `lemma-case-z-v-x-m--1`, conditional form): for `m ≥ 1`, the
defect `C_{𝔸¹, V(x^m)}(Λ)` of the constant complex vanishes as soon as the restriction
`Le^* σ_{𝒟}` of the specialization unit of the deformation `𝒟` of `V(x^m) ⊆ 𝔸¹` to the zero
section is an isomorphism. The centre `V(x^m)` is a universally homeomorphic point
(`ProEtale.CondensedRing.isUniversalHomeomorphism_centre_polyAffineThickOrigin`), so the
specialization unit of its constant family is an isomorphism. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_unit [IsSepClosed k'] {m : ℕ}
    (hm : 0 < m)
    [IsIso (L(((zeroSectionSpecialFibreMap (polyAffine k 1) (polyAffineThickOrigin k m)
      k').left)^*⟦Λ⟧).map ((deformationModel (polyAffine k 1) (polyAffineThickOrigin k m)
      k').unit Λ))] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k' Λ (𝟙_ _)) := by
  have := isUniversalHomeomorphism_centre_polyAffineThickOrigin k hm
  exact isZero_specializationDefect_unit_of_isUniversalHomeomorphism Λ k' _ _

end AlgebraicGeometry.ProEtale.CondensedRing
