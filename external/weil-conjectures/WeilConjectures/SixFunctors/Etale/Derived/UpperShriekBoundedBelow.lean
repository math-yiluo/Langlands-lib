/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FibreDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# The right adjoint of `Rf_!` preserves bounded below objects

For a finite coefficient ring `Λ` and a morphism `f : X ⟶ Y` admitting a compactification
`X ⟶[i] Z ⟶[g] Y` with `Y` quasi-compact, the derived lower shriek `Rf_! = Rg_* ∘ D(i_!)` on the
unbounded derived categories has finite cohomological amplitude: it sends `D^{≤ n}` into
`D^{≤ n + N}` for a fixed `N`. Consequently any right adjoint of `Rf_!`, in particular the
exceptional inverse image `Rf^!`, sends `D^{≥ n}` into `D^{≥ n - N}` and preserves bounded below
objects [SGA 4, Exp. XVIII, 3.1.7].

The amplitude bound is a uniform, unbounded variant of blueprint
`theorem-results-from-etale-theory--5`, bounded by the fibres of the compactification:

* the geometric fibres of the proper morphism `g` have uniformly bounded dimension `e`, as `Y` is
  quasi-compact (`AlgebraicGeometry.exists_topologicalKrullDim_le_of_isPullback_of_compactSpace`);
* by proper base change the higher direct images `R^q g_*` vanish for `q > 2e` at every geometric
  point, hence everywhere
  (`AlgebraicGeometry.Etale.exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace`);
* so the unbounded `Rg_*` sends `D^{≤ n}` into `D^{≤ n + 2e}`
  (`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj`), and `D(i_!)` is t-exact.

## Main statements

- `AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj`
- `AlgebraicGeometry.Etale.plus_obj_of_rightDerivedLowerShriek_adjunction`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- At a geometric point `t` of `T`, the higher direct images `R^q p_* G` along a proper
morphism `p : S ⟶ T` vanish for `q > 2d` as soon as the geometric fibre `S ×_T Spec Ω` has
dimension at most `d`: by proper base change
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`) they are the
higher direct images along the geometric fibre
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`). This is the argument of
`AlgebraicGeometry.Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper` with an
explicit dimension bound. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_isProper_of_le (hΛ : IsAddTorsion Λ)
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (t : T) (d : ℕ)
    (hd : topologicalKrullDim ↥(pullback p (T.algClosurePoint t) : Scheme.{u}) ≤
      (d : WithBot ℕ∞))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 2 * d < q) :
    IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj
      (((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q |>.obj G)) := by
  let x := T.algClosurePoint t
  let sq := IsPullback.of_hasPullback p x
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have : IsProper (pullback.snd p x) := MorphismProperty.pullback_snd _ _ inferInstance
  have hvan := Etale.isZero_higherDirectImage_of_two_mul_lt hΛ (pullback.snd p x)
    (pullback.snd p x) (𝟙 _) (Category.comp_id _) d hd
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p x)).obj G) q (by exact_mod_cast hq)
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

/-- **Proper pushforward has finite cohomological dimension over a quasi-compact base**, for a
coefficient ring `Λ` which is torsion as an additive group: for `p : S ⟶ T` proper with `T`
quasi-compact there is `d` with `R^q p_* G = 0` for every étale sheaf `G` of `Λ`-modules on `S`
and every `q > d`. The geometric fibres of `p` have dimension bounded by some `e`
(`AlgebraicGeometry.exists_topologicalKrullDim_le_of_isPullback_of_compactSpace`), and one takes
`d = 2e` (`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_isProper_of_le`);
geometric points detect zero sheaves
(`AlgebraicGeometry.Etale.isZero_of_forall_isZero_upperStar_algClosurePoint`). -/
theorem exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace (hΛ : IsAddTorsion Λ)
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] [CompactSpace T] :
    ∃ d : ℕ, ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G) := by
  obtain ⟨e, he⟩ := exists_topologicalKrullDim_le_of_isPullback_of_compactSpace p
  refine ⟨2 * e, fun G q hq ↦ isZero_of_forall_isZero_upperStar_algClosurePoint Λ _ fun t ↦ ?_⟩
  exact isZero_upperStar_rightDerived_lowerStar_of_isProper_of_le Λ hΛ p t e
    (he _ _ _ _ (IsPullback.of_hasPullback p (T.algClosurePoint t))) G q hq

/-- **Finite cohomological amplitude of `Rf_!`** over a quasi-compact base, a uniform
unbounded variant of blueprint `theorem-results-from-etale-theory--5` with the fibres of the
compactification in place of those of `f`. For a finite coefficient ring `Λ` and a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f` with `Y` quasi-compact, there is `N`
such that the derived lower shriek `Rf_! = Rg_* ∘ D(i_!)` on the unbounded derived categories
sends objects `≤ n` to objects `≤ n + N`, for every `n`. The extension by zero is exact, and
`Rg_*` has amplitude `N = 2e` for `e` a bound on the dimension of the geometric fibres of `g`
(`AlgebraicGeometry.Etale.exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace`,
`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj`). -/
theorem exists_isLE_rightDerivedLowerShriekOfCompactification_obj [Finite Λ] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) [CompactSpace Y] :
    ∃ N : ℕ, ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      K.IsLE n → ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K).IsLE (n + N) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have := c.isProper
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ hΛ c.g
  refine ⟨d, fun K n hK ↦ ?_⟩
  have : (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K).IsLE n :=
    ((c.i)_!open[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K n
  exact ((c.g)_*[ModuleCat.{u + 1} Λ]).isLE_rightDerivedFunctor_obj.{u + 1} d hd _ n

/-- **A right adjoint of `Rf_!` preserves bounded below objects** [SGA 4, Exp. XVIII, 3.1.7].
For a finite coefficient ring `Λ`, `f : X ⟶ Y` admitting a compactification with `Y`
quasi-compact, and any right adjoint `G` of the derived lower shriek `Rf_!` on the unbounded
derived categories (such as the exceptional inverse image `Rf^!`), `G` sends bounded below objects
to bounded below objects: if `Rf_!` sends `D^{≤ n}` into `D^{≤ n + N}`
(`AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj`), then `G`
sends `D^{≥ n}` into `D^{≥ n - N}` (`CategoryTheory.Adjunction.isGE_obj_of_isLE`). -/
theorem plus_obj_of_rightDerivedLowerShriek_adjunction [Finite Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adj : R(f)_![ModuleCat.{u + 1} Λ] ⊣ G)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus (G.obj K) := by
  obtain ⟨N, hN⟩ := exists_isLE_rightDerivedLowerShriekOfCompactification_obj Λ
    (HasCompactification.compactification f)
  obtain ⟨n, hn⟩ := hK
  exact ⟨n - N, adj.isGE_obj_of_isLE _ _ N hN K n⟩

end Etale

end AlgebraicGeometry
