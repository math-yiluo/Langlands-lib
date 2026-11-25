/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleNatural
public import WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionOpenLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-!

# Reduction modulo `ℓⁿ` and the derived pushforward, along the natural reduction triangle

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E`, and `f : X ⟶ Y` a morphism of
schemes. Write `red = - ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ` for the reduction modulo `ℓⁿ` and `Res` for the
restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`. This file sets up the comparison
```
γ : Rf_*^{𝒪_E} ⋙ red_Y ⟶ red_X ⋙ Rf_*^{𝒪_E ⧸ ℓⁿ}
```
on the full derived categories (`ProEtale.CondensedRing.derivedLowerStarIntegersModPowReduction`),
the mate of the inverse of the pullback comparison (Pull)
`β = ProEtale.integersModPowReductionUpperStarIso`, and reduces its invertibility, for an
*arbitrary* morphism `f`, to two compatibilities of (Pull) with the natural reduction triangle
`M --ℓⁿ--> M --η--> Res (red M) --δ--> M[1]` (`Mod.derivedExtendScalarsTriangle_distinguished`):

* `ProEtale.CondensedRing.IntegersModPowPullUnitCompatible`: (Pull) is compatible with the units
  `η` of `red ⊣ Res`, through the commutation `ι : Res ⋙ Lf^* ≅ Lf^* ⋙ Res` of the restriction of
  scalars with the pullbacks;
* `ProEtale.CondensedRing.IntegersModPowPullδCompatible`: the connecting morphisms `δ` commute
  with `Lf^*` along `ι` and (Pull).

Under these, `γ` is an isomorphism
(`ProEtale.CondensedRing.isIso_derivedLowerStarIntegersModPowReduction_of_compatible`), by
`CategoryTheory.isIso_mateEquiv_of_reductionTriangle`: `Res (γ_K)` is the third component of a
morphism from the reduction triangle of `Rf_* K` to `Rf_*` of the reduction triangle of `K`,
whose first two components are identities.

Both compatibilities are statements about `Lf^*` and (Pull) only: no information on `Rf_*` is
needed. They hold on K-flat complexes at the level of complexes, where (Pull) is the underived
pullback comparison `ProEtale.CondensedRing.pullIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- The natural connecting morphism `δ : Res (red M) ⟶ M[1]` of the reduction triangle
`M --ℓⁿ--> M --η--> Res (red M) --δ--> M[1]` on `D(X_proét, 𝒪_E)`. -/
noncomputable abbrev integersModPowReductionδ (X : Scheme.{u}) :=
  Mod.derivedExtendScalarsTriangleδ (φ := integersModPowReduction X ℓ E n) ((ℓ : ℤ) ^ n)
    (zsmul_id_comp_integersModPowReduction X ℓ E n) (shortExact_integersModPowReduction X ℓ E n)

/-- **The natural reduction triangle** on `D(X_proét, 𝒪_E)`:
`M --ℓⁿ--> M --η--> Res (red M) --δ--> M[1]` is distinguished. -/
lemma integersModPowReduction_distinguished {X : Scheme.{u}}
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    Triangle.mk (((ℓ : ℤ) ^ n) • 𝟙 M)
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E n)).unit.app
          M)
        ((integersModPowReductionδ ℓ E n X).app M) ∈ distTriang _ :=
  Mod.derivedExtendScalarsTriangle_distinguished _ _ _ M

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Reduction modulo `ℓⁿ` and the pushforward** on the derived categories: the comparison
`γ : Rf_*^{𝒪_E} ⋙ red_Y ⟶ red_X ⋙ Rf_*^{𝒪_E ⧸ ℓⁿ}`, the mate of the inverse of (Pull)
`ProEtale.integersModPowReductionUpperStarIso` under the adjunctions `Lf^* ⊣ Rf_*`. -/
noncomputable def derivedLowerStarIntegersModPowReduction :
    R((f)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
        L(Mod.extendScalars (integersModPowReduction Y ℓ E n)) ⟶
      L(Mod.extendScalars (integersModPowReduction X ℓ E n)) ⋙
        R((f)_*⟦Profinite.integersModPowRingObj ℓ E n⟧) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction _ f) (derivedUpperStarLowerStarAdjunction _ f)
    (integersModPowReductionUpperStarIso ℓ E n f).inv

/-- **(Pull) is compatible with the units of `red ⊣ Res`**: for `M ∈ D(Y_proét, 𝒪_E)`, the
pullback of the unit `M ⟶ Res (red M)`, followed by the commutation `ι` of `Res` with `Lf^*`,
is the unit at `Lf^* M` followed by `Res` of (Pull). -/
def IntegersModPowPullUnitCompatible : Prop :=
  ∀ M, L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction Y ℓ E n)).unit.app
        M) ≫
      (derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
        f).hom.app (L(Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj M) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E n)).unit.app
        (L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj M) ≫
      D(Mod.comap (integersModPowReduction X ℓ E n)).map
        ((integersModPowReductionUpperStarIso ℓ E n f).hom.app M)

/-- **The connecting morphisms of the reduction triangles commute with the pullback**: for
`M ∈ D(Y_proét, 𝒪_E)`, `Lf^*` of `δ_M`, followed by the commutation of `Lf^*` with the shift, is
the commutation `ι` of `Res` with `Lf^*`, followed by `Res` of the inverse of (Pull) and
`δ_{Lf^* M}`. -/
def IntegersModPowPullδCompatible : Prop :=
  ∀ M, L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).map ((integersModPowReductionδ ℓ E n Y).app M) ≫
      (L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).commShiftIso (1 : ℤ)).hom.app M =
    (derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
        f).hom.app (L(Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj M) ≫
      D(Mod.comap (integersModPowReduction X ℓ E n)).map
        ((integersModPowReductionUpperStarIso ℓ E n f).inv.app M) ≫
      (integersModPowReductionδ ℓ E n X).app (L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj M)

/-- The derived restriction of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` reflects isomorphisms: it
commutes with cohomology, and the restriction of scalars reflects isomorphisms. -/
instance (X : Scheme.{u}) :
    (Mod.comap (integersModPowReduction X ℓ E n) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) _ ⥤ Mod _ _).mapDerivedCategory.ReflectsIsomorphisms
    where
  reflects g _ := by
    rw [DerivedCategory.isIso_iff]
    intro i
    have : IsIso ((Mod.comap (integersModPowReduction X ℓ E n)).map
        ((DerivedCategory.homologyFunctor _ i).map g)) :=
      (NatIso.isIso_map_iff
        ((Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategoryHomologyFunctorIso i) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (Mod.comap (integersModPowReduction X ℓ E n))

/-- **Reduction modulo `ℓⁿ` commutes with the derived pushforward along any morphism**, given the
compatibilities of (Pull) with the units and with the connecting morphisms of the natural
reduction triangles. -/
theorem isIso_derivedLowerStarIntegersModPowReduction_of_compatible
    (hη : IntegersModPowPullUnitCompatible ℓ E n f) (hδ : IntegersModPowPullδCompatible ℓ E n f) :
    IsIso (derivedLowerStarIntegersModPowReduction ℓ E n f) :=
  isIso_mateEquiv_of_reductionTriangle
    (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction Y ℓ E n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E n))
    (derivedUpperStarLowerStarAdjunction _ f) (derivedUpperStarLowerStarAdjunction _ f)
    (integersModPowReductionUpperStarIso ℓ E n f)
    (derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) f)
    (integersModPowReductionδ ℓ E n Y) (integersModPowReductionδ ℓ E n X) ((ℓ : ℤ) ^ n)
    (integersModPowReduction_distinguished ℓ E n) (integersModPowReduction_distinguished ℓ E n)
    hη hδ

end AlgebraicGeometry.ProEtale.CondensedRing
