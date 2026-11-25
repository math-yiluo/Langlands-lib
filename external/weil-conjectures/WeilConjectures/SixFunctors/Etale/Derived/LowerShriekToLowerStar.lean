/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monad.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtaleFlat

/-!
# The derived comparison from extension by zero to pushforward

For an open immersion `j` the derived extension by zero `D(j_!)` maps to the derived
pushforward `Rj_*`; composing with the proper pushforward of a compactification `(i, g)` of
`f` gives the *forget-supports* map

`Rf_! = Rg_* D(i_!) ⟶ Rg_* Ri_*`,

whose target is right adjoint to `Li^* Lg^*`. For a proper `f` the open immersion `i` is also a
closed immersion (`AlgebraicGeometry.Compactification.isClosedImmersion_openImmersion`), the
comparison `D(i_!) ⟶ Ri_*` of a clopen immersion is an isomorphism, and hence so is the
forget-supports map. Composed with `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_* = Rf_*` it identifies `Rf_!` with
`Rf_*`. In that case a class `K ⟶ Rf_! N` is transposed into a morphism `Lf^* K ⟶ N` by the
adjunction `Lf^* ⊣ Rf_*`.

The comparison for an open immersion is the transpose, under `D(j^*) ⊣ Rj_*`, of the inverse
of the unit `K ⟶ D(j^*) D(j_!) K`, which is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit`).

## Main definitions

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`: `Rf_! ≅ Rf_*` for
  a proper `f`.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsIsoOfIsProper`: `RΓ_c(X/Y, -) ≅ RΓ(X, -)`
  for a proper `f`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar`: `D(j_!) ⟶ Rj_*` is
  an isomorphism for an immersion `j` that is both open and closed.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`: the
  forget-supports map is an isomorphism for a proper `f`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived comparison `D(j_!) ⟶ Rj_*` along an open immersion `j`: the transpose, under
`D(j^*) ⊣ Rj_*`, of the inverse of the unit `K ⟶ D(j^*) D(j_!) K` of `D(j_!) ⊣ D(j^*)`. It is
the derived counterpart of the comparison `j_! ⟶ j_*` of sheaves. Componentwise it is the
composite

```
          η_{D(j_!) K}                         Rj_* (η'_K)⁻¹
D(j_!) K ─────────────▶ Rj_* D(j^*) D(j_!) K ───────────────▶ Rj_* K
```

of the unit `η` of `D(j^*) ⊣ Rj_*` and the inverse of the unit `η'` of `D(j_!) ⊣ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : D((j)_!open[A]) ⟶ R((j)_*[A]) :=
  Functor.whiskerLeft D((j)_!open[A]) (mapDerivedUpperStarLowerStarAdjunction A j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (inv (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit)
        R((j)_*[A])

/-- For an immersion `j` that is both open and closed, the derived comparison
`D(j_!) ⟶ Rj_*` is an isomorphism.

Such a `j` is finite and étale, so `j_*` is left adjoint to `j^*`
(`AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`): it is exact, so
`Rj_* ≅ D(j_*)`, and it is a second left adjoint of `j^*`, so `j_! ≅ j_*`. Being a closed
immersion, `j_*` is fully faithful, so `D(j^*) Rj_* ≅ D(j^* j_*) ≅ 𝟭` and the counit of
`D(j^*) ⊣ Rj_*` is an isomorphism. Hence the unit of `D(j^*) ⊣ Rj_*` is an isomorphism on
`Rj_* K ≅ D(j_!) K`, which is what the comparison needs. -/
instance isIso_derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekToLowerStar A j) := by
  let adj := Etale.upperStarLowerStarAdjunction A j
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  have : PreservesLimitsOfSize.{0, 0} (j)_*[A] := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (j)_*[A] := PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  let eR : R((j)_*[A]) ≅ D((j)_*[A]) := ((j)_*[A]).rightDerivedFunctorIsoMapDerivedCategory
  let adjD := mapDerivedUpperStarLowerStarAdjunction A j
  have : IsIso adjD.counit := adjD.isIso_counit_of_iso
    (Functor.isoWhiskerRight eR _ ≪≫ (Functor.mapDerivedCategoryCompIso _ _) ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.counit) ≪≫ Functor.mapDerivedCategoryIdIso _)
  let e : D((j)_!open[A]) ≅ R((j)_*[A]) :=
    Functor.mapDerivedCategoryNatIso
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).leftAdjointUniq
        (Etale.lowerStarUpperStarAdjunctionOfIsFinite A j)) ≪≫ eR.symm
  have hK (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) :
      IsIso (adjD.unit.app (D((j)_!open[A]).obj K)) := by
    rw [NatTrans.isIso_app_iff_of_iso _ (e.app K)]
    have : IsIso (adjD.unit.app (R((j)_*[A]).obj K) ≫ R((j)_*[A]).map (adjD.counit.app K)) := by
      rw [adjD.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (R((j)_*[A]).map (adjD.counit.app K))
  have : IsIso (Functor.whiskerLeft D((j)_!open[A]) adjD.unit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K ↦ hK K
  unfold derivedOpenImmersionLowerShriekToLowerStar
  infer_instance

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The *forget-supports* map `Rf_! ⟶ Ri_* ⋙ Rg_*` for the chosen compactification `(i, g)` of
`f`: the proper pushforward `Rg_*` applied to the comparison `D(i_!) ⟶ Ri_*` of the open
immersion `i`. Its target is right adjoint to `Lg^* ⋙ Li^*`. -/
noncomputable def rightDerivedLowerShriekToLowerStarComp :
    R(f)_![A] ⟶ R(((HasCompactification.compactification f).i)_*[A]) ⋙
      R(((HasCompactification.compactification f).g)_*[A]) :=
  Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A _) _

/-- For a proper `f`, the open immersion `i` of the chosen compactification is also a closed
immersion. -/
instance isClosedImmersion_compactification_i [IsProper f] :
    IsClosedImmersion (HasCompactification.compactification f).i :=
  (HasCompactification.compactification f).isClosedImmersion_openImmersion ‹_›

/-- For a proper morphism `f`, the forget-supports map `Rf_! ⟶ Ri_* ⋙ Rg_*` of the chosen
compactification `(i, g)` is an isomorphism:
```
      i          g
  X ─────▶ X̄ ─────▶ Y        f = i ≫ g,  i open immersion,  g proper
  └──────────────────▶
           f

  Rf_! = D(i_!) ⋙ Rg_* ──(D(i_!) ⟶ Ri_*) ▷ Rg_*──▶ Ri_* ⋙ Rg_*
```
Since `f` is proper, `i` is also a closed immersion
(`AlgebraicGeometry.Etale.isClosedImmersion_compactification_i`), so the comparison
`D(i_!) ⟶ Ri_*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar`). -/
instance isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper [IsProper f] :
    IsIso (rightDerivedLowerShriekToLowerStarComp A f) := by
  have := isIso_derivedOpenImmersionLowerShriekToLowerStar A
    (HasCompactification.compactification f).i
  exact Functor.isIso_whiskerRight _ _

/-- For a proper morphism `f`, compactly supported and ordinary direct image agree,
`Rf_! ≅ Rf_*`: the forget-supports map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`, followed
by `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_* = Rf_*`:
```
          forget supports                rightDerivedLowerStarComp
   Rf_! ─────────────────▶ Ri_* ⋙ Rg_* ─────────────────────────▶ R(i ≫ g)_* ═══ Rf_*
```
-/
noncomputable def rightDerivedLowerShriekIsoRightDerivedLowerStar [IsProper f] :
    R(f)_![A] ≅ R((f)_*[A]) :=
  asIso (rightDerivedLowerShriekToLowerStarComp A f) ≪≫
    rightDerivedLowerStarComp A _ _ ≪≫
      rightDerivedLowerStarCongr A (HasCompactification.compactification f).comm.symm

lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_hom [IsProper f] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom =
      rightDerivedLowerShriekToLowerStarComp A f ≫ (rightDerivedLowerStarComp A _ _).hom ≫
        (rightDerivedLowerStarCongr A (HasCompactification.compactification f).comm.symm).hom :=
  rfl

/-- For a proper morphism `f : X ⟶ Y`, compactly supported and ordinary global sections agree,
`RΓ_c(X/Y, -) ≅ RΓ(X, -)`: the composite of `Rf_! ≅ Rf_*` with the Leray isomorphism
`RΓ(Y, Rf_* -) ≅ RΓ(X, -)`. -/
noncomputable def compactlySupportedGlobalSectionsIsoOfIsProper [HasSmallSiteSheafify A]
    [IsProper f] :
    compactlySupportedGlobalSections A f ≅ rightDerivedGlobalSections A X :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar A f) _ ≪≫
    rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f

/-- The *transpose* of a class `γ : K ⟶ Rf_! N` along the forget-supports map: the morphism
`Li^* Lg^* K ⟶ N` adjoint, under `Li^* Lg^* ⊣ Rg_* Ri_*`, to
`K ⟶ Rf_! N ⟶ Rg_* Ri_* N`, where `(i, g)` is the chosen compactification of `f`.

For a proper `f` the forget-supports map is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`)
and this is the adjunction `Lf^* ⊣ Rf_*`, transported along `Rf_! ≅ Rf_*`. -/
noncomputable def rightDerivedLowerShriekTranspose
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {N : DerivedCategory (Sheaf X.smallEtaleTopology A)} (γ : K ⟶ (R(f)_![A]).obj N) :
    (L(((HasCompactification.compactification f).i)^*[A])).obj
        ((L(((HasCompactification.compactification f).g)^*[A])).obj K) ⟶ N :=
  (((derivedUpperStarLowerStarAdjunction A _).comp
    (derivedUpperStarLowerStarAdjunction A _)).homEquiv _ _).symm
      (γ ≫ (rightDerivedLowerShriekToLowerStarComp A f).app N)

end Etale

end AlgebraicGeometry
