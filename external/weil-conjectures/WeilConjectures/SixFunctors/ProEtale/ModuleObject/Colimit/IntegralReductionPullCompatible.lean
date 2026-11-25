/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullDelta
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionProperLowerStar

/-!

# Reduction modulo `ℓⁿ` commutes with the derived pushforward

The two compatibilities of (Pull) with the natural reduction triangle
`M --ℓⁿ--> M --η--> Res (red M) --δ--> M[1]` hold for every morphism of schemes `f`
(`ProEtale.CondensedRing.integersModPowPullUnitCompatible`,
`ProEtale.CondensedRing.integersModPowPullδCompatible`): they are instances of the compatibilities
of (Pull) with the units and the connecting morphisms for an arbitrary coefficient change
(`ProEtale.CondensedRing.upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app`,
`ProEtale.CondensedRing.upperStar_map_derivedExtendScalarsTriangleδ_app`). Hence reduction modulo
`ℓⁿ` commutes with the derived pushforward along any morphism
(`ProEtale.CondensedRing.isIso_derivedLowerStarIntegersModPowReduction`), and with the pushforward
of bounded constructible complexes along any morphism of separated `k`-schemes of finite type
(`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction'`), in
particular along proper ones (blueprint `lemma-change-coefficients-direct-image` for
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Derived

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **(Pull) is compatible with the units of `red ⊣ Res`**, for every morphism of schemes. -/
theorem integersModPowPullUnitCompatible : IntegersModPowPullUnitCompatible ℓ E n f :=
  upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) f

/-- **(Pull) is compatible with the connecting morphisms of the natural reduction triangles**,
for every morphism of schemes. -/
theorem integersModPowPullδCompatible : IntegersModPowPullδCompatible ℓ E n f :=
  upperStar_map_derivedExtendScalarsTriangleδ_app
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) f ((ℓ : ℤ) ^ n)
    (zsmul_id_comp_integersModPowReduction Y ℓ E n) (zsmul_id_comp_integersModPowReduction X ℓ E n)
    (shortExact_integersModPowReduction Y ℓ E n) (shortExact_integersModPowReduction X ℓ E n)

/-- **Reduction modulo `ℓⁿ` commutes with the derived pushforward along any morphism**:
`Rf_*^{𝒪_E} ⋙ red_Y ⟶ red_X ⋙ Rf_*^{𝒪_E ⧸ ℓⁿ}` is an isomorphism. -/
theorem isIso_derivedLowerStarIntegersModPowReduction :
    IsIso (derivedLowerStarIntegersModPowReduction ℓ E n f) :=
  isIso_derivedLowerStarIntegersModPowReduction_of_compatible ℓ E n f
    (integersModPowPullUnitCompatible ℓ E n f) (integersModPowPullδCompatible ℓ E n f)

end Derived

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [TopologicalSpace.NoetherianSpace Z.left]
  [TopologicalSpace.NoetherianSpace Y.left] (d : Z ⟶ Y)

/-- **Reduction modulo `ℓⁿ` commutes with the pushforward on bounded constructible complexes**
(blueprint `lemma-change-coefficients-direct-image` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`), for every morphism `d` of
separated `k`-schemes of finite type. -/
theorem isIso_boundedConstructibleLowerStarIntegersModPowReduction' :
    IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d) :=
  isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n d
    (integersModPowPullUnitCompatible ℓ E n d.left) (integersModPowPullδCompatible ℓ E n d.left)

/-- **Reduction modulo `ℓⁿ` commutes with the proper pushforward on bounded constructible
complexes** (blueprint `lemma-change-coefficients-direct-image` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`):
`Rg_* ⋙ red_Y ⟶ red_Z ⋙ Rg_*` is an isomorphism for a proper morphism `g`. -/
theorem isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_isProper
    (g : Z ⟶ Y) [IsProper g.left] :
    IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n g) :=
  isIso_boundedConstructibleLowerStarIntegersModPowReduction' ℓ E n g

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing

