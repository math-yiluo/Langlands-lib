/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius

/-!
# Pushforward and pullback of `ℓ`-adic sheaves along a base change to `k̄` commute with the
Frobenius

This is the counterpart, for sheaves of modules over the constant `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.AdicSheaf`), of
`WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius`.
For a morphism `φ : X₀ ⟶ Y₀` of schemes over a finite field `k`, with base change
`φ̄ : X ⟶ Y` to the geometric fibers, the pushforward and the pullback along `φ̄` commute with
the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`.

## Main definitions

- `AlgebraicGeometry.ProEtale.adicLowerStarEquivalence`: the pushforward along an isomorphism
  is an equivalence.
- `AlgebraicGeometry.ProEtale.adicUpperStarIsoLowerStarInv`: `e^* ≅ (e⁻¹)_*` for an
  isomorphism `e`.
- `AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` and
  `AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso`: the exchange
  isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

section Iso

variable {X Y : Scheme.{u}}

/-- The pushforward of sheaves of `ℚ̄_ℓ`-modules along an isomorphism `e : X ≅ Y` is an
equivalence, with inverse the pushforward along `e.inv`. -/
noncomputable def adicLowerStarEquivalence (e : X ≅ Y) : AdicSheaf l X ≌ AdicSheaf l Y :=
  CategoryTheory.Equivalence.mk (e.hom)_*ᵃ[l] (e.inv)_*ᵃ[l]
    ((adicLowerStarId l X).symm ≪≫ adicLowerStarCongr l e.hom_inv_id.symm ≪≫
      (adicLowerStarComp l e.hom e.inv).symm)
    (adicLowerStarComp l e.inv e.hom ≪≫ adicLowerStarCongr l e.inv_hom_id ≪≫ adicLowerStarId l Y)

@[simp]
lemma adicLowerStarEquivalence_functor (e : X ≅ Y) :
    (adicLowerStarEquivalence l e).functor = (e.hom)_*ᵃ[l] :=
  rfl

@[simp]
lemma adicLowerStarEquivalence_inverse (e : X ≅ Y) :
    (adicLowerStarEquivalence l e).inverse = (e.inv)_*ᵃ[l] :=
  rfl

/-- The pullback along an isomorphism `e` is the pushforward along its inverse: both are left
adjoint to the pushforward along `e.hom`. -/
noncomputable def adicUpperStarIsoLowerStarInv (e : X ≅ Y) : (e.hom)^*ᵃ[l] ≅ (e.inv)_*ᵃ[l] :=
  (adicUpperStarLowerStarAdjunction l e.hom).leftAdjointUniq
    (adicLowerStarEquivalence l e).symm.toAdjunction

instance isEquivalence_adicLowerStar (g : X ⟶ Y) [IsIso g] : (g)_*ᵃ[l].IsEquivalence :=
  (adicLowerStarEquivalence l (asIso g)).isEquivalence_functor

instance isEquivalence_adicUpperStar (g : X ⟶ Y) [IsIso g] : (g)^*ᵃ[l].IsEquivalence :=
  Functor.isEquivalence_of_iso (adicUpperStarIsoLowerStarInv l (asIso g)).symm

end Iso

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The pushforward along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*` of sheaves of `ℚ̄_ℓ`-modules: both composites are the pushforward along
`φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`. -/
noncomputable def adicLowerStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_*ᵃ[l] ⋙ (g.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ≅
      (f.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ⋙ (Scheme.Hom.geometricFiberMap φ h)_*ᵃ[l] :=
  adicLowerStarComp l _ _ ≪≫
    adicLowerStarCongr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    (adicLowerStarComp l _ _).symm

/-- The pullback along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*` of sheaves of `ℚ̄_ℓ`-modules: identifying `(Fr⁻¹)_*` with `Fr^*`, both
composites are the pullback along `Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def adicUpperStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)^*ᵃ[l] ⋙ (f.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ≅
      (g.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l f.geometricGaloisFrobenius.asIso).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫
    adicUpperStarCongr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm ≪≫
    adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l g.geometricGaloisFrobenius.asIso) _

end AlgebraicGeometry.ProEtale
