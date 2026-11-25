/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-!

# The proper base change theorem

Consider a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the
proper base change theorem in étale cohomology: for every object `K` of the bounded below
derived category `D⁺(X_ét, Ab)` of abelian sheaves all of whose cohomology sheaves are torsion
(`AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`), the derived base-change
morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` is an isomorphism. No
hypothesis is imposed on `g`. This is [SGA 4, Exp. XII, Thm 5.1] and Stacks Project, Tag 0DDE.

The theorem is proved for sheaves of modules over an arbitrary coefficient ring `Λ`, with
torsion referring to the underlying abelian groups
(`AlgebraicGeometry.Etale.DerivedCategory.Plus.moduleTorsionHomology`). The abelian statement
is the case `Λ = ULift ℤ`, transported along the equivalence between sheaves of
`ULift ℤ`-modules and abelian sheaves of `WeilConjectures.SixFunctors.BaseChange.DerivedForget`.
For a coefficient ring `Λ` which is torsion as an additive group — in particular for the finite
rings `Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion, and the
base-change transformation itself is an isomorphism of functors.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`: proper base change for a bounded below
  complex of abelian sheaves with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`: proper base change
  for a bounded below complex of sheaves of `Λ`-modules with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`: for a torsion
  coefficient ring, the base-change transformation of a proper cartesian square is an
  isomorphism of functors.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`: the same
  on the unbounded derived categories.

## References

- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
- Stacks Project, Lemma 59.91.12, the derived statement,
  <https://stacks.math.columbia.edu/tag/0DDE>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- A sheaf of `Λ`-modules on the small étale site is torsion if and only if its underlying
abelian sheaf is: both conditions say that every section is locally torsion. -/
lemma Scheme.isTorsionSheaf_sheafCompose_forget₂_obj_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheaf
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) ↔
      IsTorsionModuleSheaf F := by
  rw [isTorsionSheaf_iff_isTorsion, isTorsionModuleSheaf_iff_isTorsion]

/-- **The proper base change theorem** in étale cohomology for sheaves of `Λ`-modules: for a
cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper and every bounded below complex `K ∈ D⁺(X_ét, Λ)` all of whose
cohomology sheaves are torsion as abelian sheaves, the derived base change map

`BC_sq(K) : g^*(Rf_* K) ⟶ Rf'_*(g'^* K)`

is an isomorphism in `D⁺(Y'_ét, Λ)`. No hypothesis is imposed on `g`. -/
theorem Etale.isIso_baseChange_of_isProper_of_torsionHomology [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.hasTorsionBaseChange_of_isProper Λ f sq K hK

/-- **The proper base change theorem** in étale cohomology: for a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper and every bounded below complex `K ∈ D⁺(X_ét, Ab)` of abelian sheaves all of
whose cohomology sheaves are torsion, the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

is an isomorphism in `D⁺(Y'_ét, Ab)`. No hypothesis is imposed on `g`. This is
[SGA 4, Exp. XII, Thm 5.1]. It is deduced from
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology` for `Λ = ULift ℤ`,
through the equivalence between sheaves of `ULift ℤ`-modules and abelian sheaves. -/
@[stacks 0DDE]
theorem Etale.isIso_baseChange_of_isProper [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : Etale.DerivedCategory.Plus.torsionHomology X K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) := by
  obtain ⟨K', ⟨e⟩⟩ := Etale.exists_forget₂_mapDerivedCategoryPlus_obj_iso K
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus, ← NatTrans.isIso_app_iff_of_iso _ e,
    Etale.isIso_derivedBaseChangeMapPlus_app_forget₂_iff]
  refine Etale.isIso_baseChange_of_isProper_of_torsionHomology _ sq K' fun n ↦ ?_
  rw [← Scheme.isTorsionSheaf_sheafCompose_forget₂_obj_iff]
  have := hK n
  exact IsTorsionSheaf.of_iso ((DerivedCategory.Plus.homologyFunctor _ n).mapIso e.symm ≪≫
    (((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      AddCommGrpCat.{u + 1})).mapDerivedCategoryPlusHomologyFunctorIso n).app K').symm)

/-- **Proper base change as an isomorphism of functors**: if the coefficient ring `Λ` is
torsion as an additive group — in particular if `Λ` is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then
for a cartesian square with `f` proper the base-change transformation

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the bounded below derived categories is an isomorphism: every complex of sheaves of
`Λ`-modules automatically has torsion cohomology. -/
@[stacks 095T]
theorem Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ) [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have : ∀ K, IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    fun K ↦ Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
      (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X hΛ K)
  exact NatIso.isIso_of_isIso_app _

section FiniteCohomologicalDimension

open scoped AlgebraicGeometry.Etale

open ZeroObject

/-- **Geometric points detect zero sheaves**: an étale sheaf of `Λ`-modules on `Y` whose
pullbacks to all the geometric points `Spec Ω ⟶ Y`, `Ω` the algebraic closure of a residue
field of `Y`, vanish is zero
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective` applied to
`M ⟶ 0`). -/
theorem Etale.isZero_of_forall_isZero_upperStar_algClosurePoint {T : Scheme.{u}}
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : ∀ t : T, IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj M)) :
    IsZero M := by
  have hz : IsZero (0 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := isZero_zero _
  have : IsIso (hz.from_ M) := by
    refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
      (fun t ↦ T.algClosurePoint t)
      (fun t ↦ ⟨t, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
      fun t ↦ ?_
    have hz' : IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj 0) :=
      Functor.map_isZero _ hz
    exact ⟨⟨hz'.to_ _, (H t).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  exact IsZero.of_iso hz (asIso (hz.from_ M))

/-- **Proper pushforward has pointwise finite cohomological dimension** for a coefficient ring
`Λ` which is torsion as an additive group: for `f : X ⟶ Y` proper and a point `y` of `Y`, there
is `d` such that `t^* R^q f_* G = 0` for every `q > d` and every étale sheaf `G` of `Λ`-modules on
`X`, where `t : Spec Ω ⟶ Y` is the geometric point at `y` and `R^q f_*` is the classical right
derived functor.

By proper base change (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`)
`t^* R^q f_* G ≅ R^q h_* (G|)` for the geometric fibre `h : X ×_Y Spec Ω ⟶ Spec Ω`, which is
proper over the algebraically closed field `Ω`, hence of some finite dimension `e`
(`AlgebraicGeometry.exists_topologicalKrullDim_le`); one takes `d = 2e`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`). -/
theorem Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper (hΛ : IsAddTorsion Λ)
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (t : T) :
    ∃ d : ℕ, ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj
        (((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q |>.obj G)) := by
  let x := T.algClosurePoint t
  let sq := IsPullback.of_hasPullback p x
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have : IsProper (pullback.snd p x) := MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (pullback.snd p x)
  refine ⟨2 * d, fun G q hq ↦ ?_⟩
  have hvan := Etale.isZero_higherDirectImage_of_two_mul_lt hΛ (pullback.snd p x)
    (pullback.snd p x) (𝟙 _) (Category.comp_id _) d hd
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p x)).obj G) q (by omega)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  refine IsZero.of_iso hvan
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapIso
        ((p)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso G q).symm ≪≫
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlusHomologyFunctorIso q).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.obj K) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd p x)).rightDerivedFunctorPlus.mapIso
          (((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst p x)).mapDerivedCategoryPlusSingleFunctor 0).app G)))

end FiniteCohomologicalDimension

/-- **Proper base change on the unbounded derived categories**: if the coefficient ring `Λ` is
torsion as an additive group, then for a cartesian square with `f` proper the derived base
change map

`Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the unbounded derived categories `D(-_ét, Λ)` is an isomorphism. This is the unbounded
upgrade of `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`.

At each geometric point of `Y'` the higher direct images along the proper map `f'` vanish above
twice the dimension of the fibre
(`AlgebraicGeometry.Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper`), so `f'_*`
sends exact complexes of `f'_*`-acyclic sheaves to exact complexes. Representing an object by a
K-injective complex `J` with injective terms, `g'^* J` is a complex of `f'_*`-acyclic sheaves by
the bounded below theorem, and the derived base change map at `J` is the termwise underived base
change map (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isIso_baseChangeMap`), an
isomorphism by `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`.

This is blueprint `theorem-results-from-etale-theory--1` (for `Λ` torsion, i.e. a `ℤ/n`-algebra). -/
theorem Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ)
    [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    Etale.isIso_baseChangeMap_of_isProper Λ sq
  refine Etale.isIso_derivedBaseChangeMap_of_isIso_baseChangeMap _ sq.toCommSq
    (fun M hM hM' ↦ ?_) (fun I _ ↦ ?_)
  · choose d hd using Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper Λ hΛ f'
    exact hM.map_of_rightAcyclic_of_forall_isZero _
      (fun y ↦ Etale.upperStar (ModuleCat.{u + 1} Λ) (Y'.algClosurePoint y))
      (Etale.isZero_of_forall_isZero_upperStar_algClosurePoint Λ) d hd hM'
  · have : IsTorsionModuleSheaf I := .of_isTorsion hΛ _
    exact (Etale.HasTorsionBaseChange.hasInjectiveAcyclicity Λ f
      (Etale.hasTorsionBaseChange_of_isProper Λ f)).rightAcyclic Λ sq I

end AlgebraicGeometry
