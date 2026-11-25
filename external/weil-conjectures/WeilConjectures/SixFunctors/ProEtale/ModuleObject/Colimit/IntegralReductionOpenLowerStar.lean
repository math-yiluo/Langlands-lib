/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangulated
public import WeilConjectures.CategoryTheory.Triangulated.AdjunctionUnitLocal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStar

/-!

# Reduction modulo `ℓⁿ` preserves objects local for an open immersion

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`j : U ⟶ X` an open immersion. Call `N ∈ D(Mod_{Λ_X})` *`j`-local* if the unit
`N ⟶ Rj_* Lj^* N` is an isomorphism, i.e. if `N` lies in the essential image of the fully
faithful `Rj_*`. This file shows that the reduction modulo `ℓⁿ`,
`N ↦ N ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ`, sends `j`-local `𝒪_{E,X}`-complexes to `j`-local
`(𝒪_E ⧸ ℓⁿ)_X`-complexes
(`isIso_derivedUpperStarLowerStarAdjunction_unit_app_integersModPowReduction`).

The restriction of scalars `Res` of the reduction of `N` sits in the reduction triangle
`N --ℓⁿ--> N ⟶ Res (N ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⟶ N[1]`, so it is `j`-local by two out of three. Locality
descends along `Res`, which reflects zero objects and commutes with `Lj^*` and with `Rj_*`
(`CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app_map`). The commutation of `Res`
with `Rj_*`, for a coefficient change which need not be flat, is the conjugate of the commutation
(Pull) of the derived extension of scalars with the derived pullback
(`ProEtale.CondensedRing.rightDerivedLowerStarComapIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Comap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Restriction of scalars commutes with the derived pushforward**, for an arbitrary
coefficient change `a : Λ ⟶ Λ'`: `Rf_*^{Λ'} ⋙ D(Res_{a_Y}) ≅ D(Res_{a_X}) ⋙ Rf_*^Λ`, the conjugate
of (Pull) `Lf^* ⋙ L(Ext) ≅ L(Ext) ⋙ Lf^*` (`derivedUpperStarExtendScalarsIso`) along the
composite adjunctions. Unlike `ProEtale.CondensedRing.derivedComapLowerStarIso`, no flatness of
`Λ'` over `Λ` is needed. -/
noncomputable def rightDerivedLowerStarComapIso :
    R((f)_*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a Y)) ≅
      D(Mod.comap (coefficientMap a X)) ⋙ R((f)_*⟦Λ⟧) :=
  conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
      (derivedUpperStarLowerStarAdjunction Λ' f))
    ((derivedUpperStarLowerStarAdjunction Λ f).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
    (derivedUpperStarExtendScalarsIso a f)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
/-- The derived restriction of scalars reflects zero objects: it commutes with homology, and the
restriction of scalars of module objects reflects zero objects. -/
lemma isZero_of_isZero_mapDerivedCategory_comap {X : Scheme.{u}}
    {G : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))}
    (hG : IsZero (D(Mod.comap (coefficientMap a X)).obj G)) : IsZero G :=
  (DerivedCategory.isZero_iff _).2 fun i ↦ Mod.isZero_of_isZero_comap _
    (((DerivedCategory.isZero_iff _).1 hG i).of_iso
      (((Mod.comap (coefficientMap a X)).mapDerivedCategoryHomologyFunctorIso i).app G))

/-- If `Lj^*` kills `G`, it kills the restriction of scalars of `G`: `Lj^*` commutes with the
restriction of scalars (`derivedComapUpperStarIso`). -/
lemma isZero_leftDerivedUpperStar_obj_mapDerivedCategory_comap {U X : Scheme.{u}} (j : U ⟶ X)
    {G : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))}
    (hG : IsZero (L((j)^*⟦Λ'⟧).obj G)) :
    IsZero (L((j)^*⟦Λ⟧).obj (D(Mod.comap (coefficientMap a X)).obj G)) :=
  (D(Mod.comap (coefficientMap a U)).map_isZero
    (hG.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ' j).app G).symm)).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app _ ≪≫
      (derivedComapUpperStarIso a j).symm.app G)

end Comap

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  (n : ℕ)

/-- **Reduction modulo `ℓⁿ` preserves `j`-local objects**: for an open immersion `j : U ⟶ X` and
`N ∈ D(Mod_{𝒪_{E,X}})` such that the unit `N ⟶ Rj_* Lj^* N` is an isomorphism, the unit at the
reduction `N ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ` is an isomorphism. By the reduction triangle and two out of
three, the restriction of scalars of the reduction is `j`-local, and locality descends along the
restriction of scalars. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_app_integersModPowReduction
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hN : IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E)
      j).unit.app N)) :
    IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n)
      j).unit.app (L(Mod.extendScalars (integersModPowReduction X ℓ E n)).obj N)) := by
  obtain ⟨g, h, hT⟩ := exists_distinguished_integersModPowReduction X ℓ E n N
  exact (derivedUpperStarLowerStarAdjunction _ j).isIso_unit_app_of_isIso_unit_app_map
    (derivedUpperStarLowerStarAdjunction _ j) _ _
    (rightDerivedLowerStarComapIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) j)
    (fun _ ↦ isZero_of_isZero_mapDerivedCategory_comap _)
    (fun _ ↦ isZero_leftDerivedUpperStar_obj_mapDerivedCategory_comap _ j) _
    ((derivedUpperStarLowerStarAdjunction _ j).isIso_unit_app_obj₃_of_distTriang _ hT hN hN)

end AlgebraicGeometry.ProEtale.CondensedRing
