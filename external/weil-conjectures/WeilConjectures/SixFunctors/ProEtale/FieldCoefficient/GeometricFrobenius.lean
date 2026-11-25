/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Module
public import WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius

/-!
# Pushforward and pullback of `Λ`-adic sheaves along a base change to `k̄` commute with the
Frobenius

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

This is the counterpart, for sheaves of modules over the constant sheaves `Λ_X`
(`AlgebraicGeometry.ProEtale.FieldSheaf`), of
`WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius`.
For a morphism `φ : X₀ ⟶ Y₀` of schemes over a finite field `k`, with base change
`φ̄ : X ⟶ Y` to the geometric fibers, the pushforward and the pullback along `φ̄` commute with
the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldLowerStarEquivalence`: the pushforward along an isomorphism
  is an equivalence.
- `AlgebraicGeometry.ProEtale.fieldUpperStarIsoLowerStarInv`: `e^* ≅ (e⁻¹)_*` for an
  isomorphism `e`.
- `AlgebraicGeometry.ProEtale.fieldLowerStarGeometricFiberMapCompFrobeniusIso` and
  `AlgebraicGeometry.ProEtale.fieldUpperStarGeometricFiberMapCompFrobeniusIso`: the exchange
  isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

section Iso

variable {X Y : Scheme.{u}}

/-- The pushforward of sheaves of `Λ`-modules along an isomorphism `e : X ≅ Y` is an
equivalence, with inverse the pushforward along `e.inv`. -/
noncomputable def fieldLowerStarEquivalence (e : X ≅ Y) : FieldSheaf Λ X ≌ FieldSheaf Λ Y :=
  CategoryTheory.Equivalence.mk (e.hom)_*ᶠ[Λ] (e.inv)_*ᶠ[Λ]
    ((fieldLowerStarId Λ X).symm ≪≫ fieldLowerStarCongr Λ e.hom_inv_id.symm ≪≫
      (fieldLowerStarComp Λ e.hom e.inv).symm)
    (fieldLowerStarComp Λ e.inv e.hom ≪≫ fieldLowerStarCongr Λ e.inv_hom_id ≪≫ fieldLowerStarId Λ Y)

omit [IsUltrametricDist Λ] in
@[simp]
lemma fieldLowerStarEquivalence_functor (e : X ≅ Y) :
    (fieldLowerStarEquivalence Λ e).functor = (e.hom)_*ᶠ[Λ] :=
  rfl

omit [IsUltrametricDist Λ] in
@[simp]
lemma fieldLowerStarEquivalence_inverse (e : X ≅ Y) :
    (fieldLowerStarEquivalence Λ e).inverse = (e.inv)_*ᶠ[Λ] :=
  rfl

/-- The pullback along an isomorphism `e` is the pushforward along its inverse: both are left
adjoint to the pushforward along `e.hom`. -/
noncomputable def fieldUpperStarIsoLowerStarInv (e : X ≅ Y) : (e.hom)^*ᶠ[Λ] ≅ (e.inv)_*ᶠ[Λ] :=
  (fieldUpperStarLowerStarAdjunction Λ e.hom).leftAdjointUniq
    (fieldLowerStarEquivalence Λ e).symm.toAdjunction

instance isEquivalence_fieldLowerStar (g : X ⟶ Y) [IsIso g] : (g)_*ᶠ[Λ].IsEquivalence :=
  (fieldLowerStarEquivalence Λ (asIso g)).isEquivalence_functor

instance isEquivalence_fieldUpperStar (g : X ⟶ Y) [IsIso g] : (g)^*ᶠ[Λ].IsEquivalence :=
  Functor.isEquivalence_of_iso (fieldUpperStarIsoLowerStarInv Λ (asIso g)).symm

end Iso

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The pushforward along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*` of sheaves of `Λ`-modules: both composites are the pushforward along
`φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`. -/
noncomputable def fieldLowerStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_*ᶠ[Λ] ⋙ (g.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ≅
      (f.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ⋙ (Scheme.Hom.geometricFiberMap φ h)_*ᶠ[Λ] :=
  fieldLowerStarComp Λ _ _ ≪≫
    fieldLowerStarCongr Λ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    (fieldLowerStarComp Λ _ _).symm

/-- The pullback along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*` of sheaves of `Λ`-modules: identifying `(Fr⁻¹)_*` with `Fr^*`, both
composites are the pullback along `Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def fieldUpperStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)^*ᶠ[Λ] ⋙ (f.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ≅
      (g.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*ᶠ[Λ] :=
  Functor.isoWhiskerLeft _
      (fieldUpperStarIsoLowerStarInv Λ f.geometricGaloisFrobenius.asIso).symm ≪≫
    (fieldUpperStarComp Λ _ _).symm ≪≫
    fieldUpperStarCongr Λ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm ≪≫
    fieldUpperStarComp Λ _ _ ≪≫
    Functor.isoWhiskerRight (fieldUpperStarIsoLowerStarInv Λ g.geometricGaloisFrobenius.asIso) _

end AlgebraicGeometry.ProEtale
