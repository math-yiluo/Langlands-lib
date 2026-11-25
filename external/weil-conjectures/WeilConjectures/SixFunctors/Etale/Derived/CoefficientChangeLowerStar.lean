/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateIterated
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsRestrictScalarsMate

/-!
# The proper direct image carries derived base changes to derived base changes

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings with `Λ` finite and `p : Z ⟶ Y` a proper
morphism. If `η : K ⟶ Res K'` exhibits `K'` as the derived base change `K ⊗ᴸ_Λ Λ'`, then
`Rp_* η`, followed by the coefficient comparison `Rp_* Res ≅ Res Rp_*`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso`), exhibits
`Rp_* K'` as `Rp_* K ⊗ᴸ_Λ Λ'`
(`AlgebraicGeometry.Etale.isDerivedBaseChange_rightDerivedLowerStar_map_comp`).

Write `Ψ = - ⊗ᴸ_Λ Λ'` for the derived extension of scalars, left adjoint to `Res`. The base change
map `Ψ (Rp_* K) ⟶ Rp_* (Ψ K)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarExtendScalarsMap`)
is the mate of the commutation `Lp^* Ψ ≅ Ψ Lp^*`; it is the transpose along `Ψ ⊣ Res` of
`Rp_* η_K` followed by the coefficient comparison, since the commutations of `Lp^*` with `Ψ` and
with `Res` are mates along `Ψ ⊣ Res` and the coefficient comparison of `Rp_*` is the mate of the
one of `Lp^*`. For proper `p` the base change map is an isomorphism by the projection formula.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section

variable {Z Y : Scheme.{u}} (p : Z ⟶ Y)

/-- The base change map `Ψ (Rp_* K) ⟶ Rp_* (Ψ K)` of derived extension of scalars along the
derived direct image: the mate of the commutation `Lp^* ∘ Ψ ≅ Ψ ∘ Lp^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`). -/
noncomputable def rightDerivedLowerStarExtendScalarsMap :
    R((p)_*[ModuleCat.{u + 1} Λ]) ⋙ L(sheafExtendScalars ρ Y) ⟶
      L(sheafExtendScalars ρ Z) ⋙ R((p)_*[ModuleCat.{u + 1} Λ']) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction _ p) (derivedUpperStarLowerStarAdjunction _ p)
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso ρ p).hom

/-- **Derived extension of scalars commutes with `Rp_*` for proper `p`**: for a finite ring `Λ`,
the base change map `Ψ (Rp_* K) ⟶ Rp_* (Ψ K)` is an isomorphism. Restricted to `Λ`, it is the
projection map `Rp_* K ⊗ᴸ Λ'_Y ⟶ Rp_* (K ⊗ᴸ Λ'_Z)`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app [Finite Λ] [IsProper p]
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap ρ p).app K) := by
  let := ρ.toAlgebra
  exact isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app Λ Λ' p K

/-- `Rp_*` of the unit of `Ψ ⊣ Res`, followed by the coefficient comparison of `Rp_*`, is the unit
at `Rp_* K` followed by the restriction of scalars of the base change map
`Ψ (Rp_* K) ⟶ Rp_* (Ψ K)`. -/
@[reassoc]
lemma map_unit_app_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app (d : ℕ)
    (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      Limits.IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedEtaleSheafExtendScalarsAdjunction ρ Z).unit.app K) ≫
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd).hom.app
        ((L(sheafExtendScalars ρ Z)).obj K) =
    (leftDerivedEtaleSheafExtendScalarsAdjunction ρ Y).unit.app
        ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
        ((rightDerivedLowerStarExtendScalarsMap ρ p).app K) :=
  (Adjunction.unit_app_comp_map_mateEquiv_app _ _ _ _
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso ρ p) _
    (mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv ρ p) _
    (mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso
      ρ p d hd) K).symm

end

/-- **The proper direct image carries derived base changes to derived base changes.** For a
finite coefficient ring `Λ`, a morphism `ρ : Λ →+* Λ'` and a proper `p : Z ⟶ Y`, if
`η : K ⟶ Res K'` exhibits `K'` as `K ⊗ᴸ_Λ Λ'`, then `Rp_* η` followed by the comparison
`Rp_* Res ≅ Res Rp_*` exhibits `Rp_* K'` as `Rp_* K ⊗ᴸ_Λ Λ'`. -/
theorem isDerivedBaseChange_rightDerivedLowerStar_map_comp [Finite Λ] {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsProper p] (d : ℕ)
    (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      Limits.IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    {K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Sheaf.IsDerivedBaseChange ((R((p)_*[ModuleCat.{u + 1} Λ])).map η ≫
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd).hom.app K') := by
  let adj := leftDerivedEtaleSheafExtendScalarsAdjunction ρ Z
  let φ := (adj.homEquiv K K').symm η
  have hφ : η = adj.unit.app K ≫ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).map φ := by
    rw [show adj.unit.app K ≫ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).map φ =
      adj.homEquiv K K' φ from (adj.homEquiv_unit K K' φ).symm]
    simp [φ]
  have : IsIso φ := Sheaf.IsDerivedBaseChange.isIso
    (isDerivedBaseChange_leftDerivedEtaleSheafExtendScalarsAdjunction_unit ρ Z K) hη φ hφ.symm
  have := isIso_rightDerivedLowerStarExtendScalarsMap_app ρ p K
  have hnat := (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd).hom.naturality φ
  dsimp only [Functor.comp_map] at hnat
  rw [hφ, Functor.map_comp, Category.assoc, hnat,
    map_unit_app_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app_assoc,
    ← Functor.map_comp]
  exact Sheaf.IsDerivedBaseChange.comp_map_iso
    (isDerivedBaseChange_leftDerivedEtaleSheafExtendScalarsAdjunction_unit ρ Y _)
    (asIso ((rightDerivedLowerStarExtendScalarsMap ρ p).app K ≫
      (R((p)_*[ModuleCat.{u + 1} Λ'])).map φ))

end AlgebraicGeometry.Etale
