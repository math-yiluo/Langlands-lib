/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DefectLocal

/-!

# The zero-section map on the unit

For the constant complex `Λ`, the zero-section map `ε_{X,Z}(Λ)` is compared with the specialization
units through the unit law of the pullback exchange (blueprint `sec-Base-change-for-nearby-cycles`
(2)): `ε_{X,Z}(Λ) ∘ Le^* σ_{𝒟_Z X} = Ψ_{Z × S}(ε_i) ∘ σ_{Z × S} ∘ ε_e⁻¹`. Hence `ε_{X,Z}(Λ)` is an
isomorphism as soon as the specialization unit of the constant family `Z × S` and the restriction
of the specialization unit of `𝒟_Z X` to the zero section are
(`ProEtale.CondensedRing.isIso_zeroSectionMap_unit`; the constant-coefficient step of blueprint
`lemma-case-z-v-x-m--1`).

For `ℚ̄_ℓ`-coefficients, the two reduction steps of the constant case of blueprint
`lemma-vanishing-generic-points-principal-divisor` are proved from the exchange properties of the
defect:
* along a smooth `f : X ⟶ X₀`, `C_{X₀,Z₀}(ℚ̄_ℓ) = 0` implies `C_{X, f⁻¹ Z₀}(ℚ̄_ℓ) = 0`
  (`ProEtale.CondensedRing.isZero_specializationDefect_unit_of_smooth`); with `f = h : X ⟶ 𝔸¹`
  and `Z₀ = V(x^m)`, this reduces the constant case to the thick origin
  `C_{𝔸¹, V(x^m)}(ℚ̄_ℓ) = 0`;
* `C_{X,Z}(ℚ̄_ℓ) = 0` implies `C_{X,Z}(j_! ℚ̄_ℓ) = 0` for the complement `j : X ∖ Z ⟶ X`
  (`ProEtale.CondensedRing.isZero_specializationDefect_lowerShriek_unit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The zero-section map on the unit** (constant-coefficient step of blueprint
`lemma-case-z-v-x-m--1`): if the specialization unit `σ_{Z × S}` of the constant family of the
centre is an isomorphism, and so is the restriction `Le^* σ_{𝒟_Z X}` of the specialization unit of
the deformation to the zero section, then the zero-section map `ε_{X,Z}(Λ)` is an isomorphism. -/
theorem isIso_zeroSectionMap_unit
    [hM : IsIso ((deformationModel (centre X I) ⊥ k').unit Λ)]
    [hN : IsIso (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
      ((deformationModel X I k').unit Λ))] :
    IsIso (zeroSectionMap X I k' Λ (𝟙_ _)) := by
  have h := (zeroSectionDeformationModelHom X I k').map_unit_comp_pullbackExchange_app Λ
  have h' : zeroSectionMap X I k' Λ (𝟙_ _) =
      inv (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
        ((deformationModel X I k').unit Λ)) ≫
        ((leftDerivedUpperStarUnitIso Λ (zeroSectionSpecialFibreMap X I k').left).hom ≫
          (deformationModel (centre X I) ⊥ k').unit Λ ≫
          ((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).map
            (leftDerivedUpperStarUnitIso Λ (centreι X I).left).inv) := by
    rw [← h, IsIso.inv_hom_id_assoc]
    rfl
  rw [h']
  infer_instance


/-! ### Constant coefficients: smooth pullback and extension by zero -/

section Constant

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Smooth pullback of the vanishing of the defect of the constant complex** (the smooth exchange
step of blueprint `lemma-vanishing-generic-points-principal-divisor`): let `f : X ⟶ X₀` be smooth,
`Z₀ = V(I₀)` a closed subscheme of `X₀` and `Z = f⁻¹ Z₀`. If `C_{X₀,Z₀}(ℚ̄_ℓ) = 0`, then
`C_{X,Z}(ℚ̄_ℓ) = 0`. This uses the smooth exchange `C_{X,Z}(Lf^* L) ≅ Lf_Z^* C_{X₀,Z₀}(L)` and
`Lf^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
theorem isZero_specializationDefect_unit_of_smooth {X X₀ : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (f : X ⟶ X₀) [Smooth f.left] (I₀ : X₀.left.IdealSheafData)
    (h : IsZero (specializationDefect X₀ I₀ k' (Profinite.padicAlgClRingObj ℓ) (𝟙_ _))) :
    IsZero (specializationDefect X (I₀.comap f.left) k' (Profinite.padicAlgClRingObj ℓ)
      (𝟙_ _)) := by
  obtain ⟨e⟩ := nonempty_specializationDefect_upperStar_iso f I₀ k'
    (𝟙_ (Dᵇc(X₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  obtain ⟨e'⟩ := nonempty_specializationDefect_iso X (I₀.comap f.left) k'
    (Profinite.padicAlgClRingObj ℓ) (leftDerivedUpperStarUnitIso _ f.left)
  exact (Functor.map_isZero _ h).of_iso (e'.symm ≪≫ e)

/-- **Extension by zero of the constant complex** (the closed vanishing step of blueprint
`lemma-vanishing-generic-points-principal-divisor`): for the open complement `j : U = X ∖ Z ⟶ X` of
the centre, if `C_{X,Z}(ℚ̄_ℓ) = 0` then `C_{X,Z}(j_! ℚ̄_ℓ) = 0`. -/
theorem isZero_specializationDefect_lowerShriek_unit {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (I : X.left.IdealSheafData)
    (h : IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) (𝟙_ _))) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X I.support.compl)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj (𝟙_ _))).obj) := by
  obtain ⟨e⟩ := nonempty_specializationDefect_lowerShriek_upperStar_iso X I k'
    (overRestrictι X I.support.compl) (isCompl_range_overRestrictι_centreι I)
    (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  exact h.of_iso e

end Constant

end AlgebraicGeometry.ProEtale.CondensedRing
